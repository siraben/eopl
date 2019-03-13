{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

import Control.Monad hiding (MonadPlus(..))
import Control.Monad.Except hiding (MonadPlus(..))

import Data.Char

newtype Parser a = Parser (String -> [(a, String)])

item :: Parser Char
item = Parser $ \case
                   "" -> []
                   (c:cs) -> [(c, cs)]


parse (Parser p) = p

instance Functor Parser where
  fmap f (Parser cs) = Parser (\s -> [(f a, b) | (a, b) <- cs s])

instance Applicative Parser where
  pure = return
  (Parser cs1) <*> (Parser cs2) = Parser (\s -> [(f a, s2) | (f, s1) <- cs1 s, (a, s2) <- cs2 s1])

class Monad m => MonadZero m where
  zero :: m a

instance Monad Parser where
  return a = Parser $ \cs -> [(a, cs)]
  p >>= f = Parser $ \cs -> concat [parse (f a) cs' |
                                  (a,cs') <- parse p cs]

class MonadZero m => MonadPlus m where
  (<|>) :: m a -> m a -> m a

instance MonadZero Parser where
  zero = Parser (const [])

instance MonadPlus Parser where
  p <|> q = Parser (\cs -> parse p cs ++ parse q cs)

(+++) :: Parser a -> Parser a -> Parser a
p +++ q = Parser (\cs -> case parse (p <|> q) cs of
                     []     -> []
                     (x:xs) -> [x])
          
sat :: (Char -> Bool) -> Parser Char
sat p = do {c <- item;  if p c then return c else zero}
  
char :: Char -> Parser Char
char c = sat (c ==)

string :: String -> Parser String
string "" = return ""
string (c : cs) = do
  char c
  string cs
  return (c : cs)

many :: Parser a -> Parser [a]
many p = many1 p +++ return []

many1 :: Parser a -> Parser [a]
many1 p = do
  a <- p
  as <- many p
  return (a : as)

sepby :: Parser a -> Parser b -> Parser [a]
p `sepby` sep = (p `sepby1` sep) +++ return []

sepby1 :: Parser a -> Parser b -> Parser [a]
p `sepby1` sep = do
  a <- p
  as <- many $ do { sep; p }
  return (a : as)

chainl :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = (p `chainl1` op) +++ return a


chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainl1` op = do {
  a <- p;
  rest a
}
  where rest a = (do 
          f <- op
          b <- p
          rest (f a b))
          +++ return a

digit :: Parser Char
digit = sat isDigit

parens :: Parser a -> Parser a
parens m = do
  symb "("
  n <- m
  symb ")"
  return n

space :: Parser String
space = many $ sat isSpace

token :: Parser a -> Parser a
token p = do
  a <- p
  space
  return a

symb :: String -> Parser String
symb = token . string

apply :: Parser a -> String -> [(a, String)]
apply p = parse $ do {space; p}

-- |The type of variables.
type Var = String

-- |The expression type.
data Expr = NumLiteral Integer
          | StrLiteral String
          | BoolL Bool
          | Emptylist
          | BeginEnd
          | Mult Expr Expr
          | Add Expr Expr
          | Sub Expr Expr
          | Zerop Expr
          | Div Expr
          | Nullp Expr
          | Cons Expr Expr
          | Begin Expr Expr
          | Car Expr
          | Cdr Expr
          | Equalp Expr Expr
          | Greaterp Expr Expr
          | Lessp Expr Expr
          | If Expr Expr Expr
          | VarLit Var
          | Let Var Expr Expr
          | Letrec [Var] [Var] [Expr] Expr
          | Proc Var Expr
          | Call Expr Expr
          deriving Show

-- |The environment type.
data Env = EmptyEnv
         | ExtendEnv Var Val Env
         | ExtendEnvRec [Var] [Var] [Expr] Env
         deriving Show

-- |The value type.
data Val = Nil
         | Cell Val Val
         | Num Integer
         | Str String
         | Boolean Bool
         | Procedure Var Expr Env
         deriving Show

envLookup :: Var -> Env -> Result Val
envLookup a EmptyEnv = throwError $ "Unbound variable: " ++ show a
envLookup v (ExtendEnv var val rest) = if var == v then return val else envLookup var rest

type Exception = String

-- reifyProc :: Val -> (Val -> Maybe Val)
reifyProc (Procedure var body env) val = runExceptT $ eval body $ ExtendEnv var val env

appProc :: (Val -> Result Val) -> Result Val -> Result Val
appProc = (=<<)
  
newtype Eval a = Eval (Env -> Maybe a)

type Result = ExceptT String Maybe

eval :: Expr -> Env -> Result Val
eval expr env = case expr of
  BoolL b -> return $ Boolean b
  NumLiteral  a -> return $ Num a
  VarLit a  -> envLookup a env
    
  If p c a -> do
    x <- eval p env
    case x of
      Boolean True -> eval c env
      Boolean False -> eval a env

  Let varName varBody letBody -> do
    val <- eval varBody env
    eval letBody $ ExtendEnv varName val env
  Proc var body -> return $ Procedure var body env
  -- Call rator rand -> do
  --   fun <- eval rator env
  --   res <- appProc (reifyProc fun) (eval rand env)
  --   return res
                 
  _ -> throwError "Unknown expression"


nat :: Parser Integer
nat = do
  xs <- many1 digit
  return (read xs :: Integer)

natural :: Parser Integer
natural = token nat

binOp :: String -> (Expr -> Expr -> Expr) -> Parser Expr
binOp keyword op = do
  symb keyword
  symb "("
  e1 <- parseExpr
  symb ","
  e2 <- parseExpr
  symb ")"
  return $ op e1 e2

constExpr = NumLiteral <$> natural

constLit k c = do
  k
  return c

trueExpr :: Parser Expr
trueExpr = constLit (symb "true") (BoolL True)

falseExpr :: Parser Expr
falseExpr = constLit (symb "false") (BoolL False)

boolExpr :: Parser Expr
boolExpr = trueExpr <|> falseExpr

ifExpr :: Parser Expr
ifExpr = do
  symb "if"
  pred <- parseExpr
  symb "then"
  conseq <- parseExpr
  symb "else"
  If pred conseq <$> parseExpr

parseId = token $ many $ sat isAlphaNum

varExpr = VarLit <$> parseId

letExpr = do
  symb "let"
  v <- parseId
  symb "="
  e <- parseExpr
  symb "in"
  Let v e <$> parseExpr

procExpr = do
  symb "proc"
  symb "("
  v <- parseId
  symb ")"
  Proc v <$> parseExpr

callExpr = do
  symb "("
  e1 <- parseExpr
  e2 <- parseExpr
  symb ")"
  return $ Call e1 e2

builtins = [("+", Add)]

builtinExpr :: Parser Expr
builtinExpr = foldr (\(s, op) rest -> binOp s op <|> rest) zero builtins

parseExpr :: Parser Expr
parseExpr = constExpr
        <|> builtinExpr
        <|> ifExpr
        <|> boolExpr
        <|> letExpr
        <|> procExpr
        <|> callExpr
        <|> varExpr
        -- <|> commentExpr
        -- <|> consExpr
        -- <|> consStreamExpr

-- readExpr :: String -> Maybe Expr
readExpr s = case parse parseExpr s of
  x : _ -> Just x
  _ -> Nothing
  
emptyEnv = EmptyEnv

reval :: String -> Result Val
reval s = case parse parseExpr s of
            (res, "") : _ ->  eval res emptyEnv
            (_, rest) : _ -> throwError $ "Unexpected characters: " ++ rest
            
reportResult (Just (Right val)) = putStrLn ("Result: " ++ show val)
reportResult (Just (Left e)) = putStrLn ("Error: " ++ e)

main :: IO ()
main = forever $ do
  putStr "> "
  exp <- getLine
  reportResult $ runExceptT $ reval exp

