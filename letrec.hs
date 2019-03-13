{-# LANGUAGE LambdaCase #-}

import           Control.Monad           hiding ( MonadPlus(..) )
import           Data.Char
import           Data.List
import           System.IO
import           System.Exit

newtype Parser a = Parser (String -> [(a, String)])

item :: Parser Char
item = Parser $ \case
  ""       -> []
  (c : cs) -> [(c, cs)]

parse (Parser p) = p

instance Functor Parser where
  fmap f (Parser cs) = Parser (\s -> [ (f a, b) | (a, b) <- cs s ])

instance Applicative Parser where
  pure = return
  (Parser cs1) <*> (Parser cs2) =
    Parser (\s -> [ (f a, s2) | (f, s1) <- cs1 s, (a, s2) <- cs2 s1 ])

class Monad m => MonadZero m where
  zero :: m a

instance Monad Parser where
  return a = Parser $ \cs -> [(a, cs)]
  p >>= f = Parser $ \cs -> concat [ parse (f a) cs' | (a, cs') <- parse p cs ]

class MonadZero m => MonadPlus m where
  (<|>) :: m a -> m a -> m a

instance MonadZero Parser where
  zero = Parser (const [])

instance MonadPlus Parser where
  p <|> q = Parser (\cs -> parse p cs ++ parse q cs)

(+++) :: Parser a -> Parser a -> Parser a
p +++ q = Parser
  (\cs -> case parse (p <|> q) cs of
    []       -> []
    (x : xs) -> [x]
  )

sat :: (Char -> Bool) -> Parser Char
sat p = do
  c <- item
  if p c then return c else zero

char :: Char -> Parser Char
char c = sat (c ==)

string :: String -> Parser String
string ""       = return ""
string (c : cs) = do
  char c
  string cs
  return (c : cs)

many :: Parser a -> Parser [a]
many p = many1 p +++ return []

many1 :: Parser a -> Parser [a]
many1 p = do
  a  <- p
  as <- many p
  return (a : as)

sepby :: Parser a -> Parser b -> Parser [a]
p `sepby` sep = (p `sepby1` sep) +++ return []

sepby1 :: Parser a -> Parser b -> Parser [a]
p `sepby1` sep = do
  a  <- p
  as <- many $ do
    sep
    p
  return (a : as)

chainl :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = (p `chainl1` op) +++ return a


chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainl1` op = do
  a <- p
  rest a
 where
  rest a =
    (do
        f <- op
        b <- p
        rest (f a b)
      )
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

upTo :: Char -> Parser String
upTo c = many $ sat (/= c)

apply :: Parser a -> String -> [(a, String)]
apply p = parse $ do
  space
  p

-- |The type of variables.
type Var = String

-- |The expression type.
data Expr = NumLiteral Integer
          | StrLiteral String
          | BoolLiteral Bool
          | Emptylist
          | BeginEnd
          | Mult Expr Expr
          | Add Expr Expr
          | Sub Expr Expr
          | Zerop Expr
          | Div Expr Expr
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
          | Break

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

envLookup :: Var -> Env -> Result Val
envLookup searchVar EmptyEnv = raise $ UnboundVariable searchVar
envLookup searchVar (ExtendEnv currVar val rest) =
  if searchVar == currVar then return val else envLookup searchVar rest

envLookup searchVar env@(ExtendEnvRec pnames bvars pbodies rest) =
  case elemIndex searchVar pnames of
    Just n  -> return $ Procedure (bvars !! n) (pbodies !! n) env
    Nothing -> envLookup searchVar rest



reifyProc :: Val -> Val -> Result Val
reifyProc (Procedure var body env) val = eval body $ ExtendEnv var val env

appProc :: (Val -> Result Val) -> Result Val -> Result Val
appProc = (=<<)

data Exceptional e a =
     Success a
   | Failure e
   deriving Show

instance Functor (Exceptional e) where
  fmap f (Success a) = Success $ f a
  fmap f (Failure e) = Failure e

instance Applicative (Exceptional e) where
  pure = Success
  Success f <*> Success b = Success $ f b

instance Monad (Exceptional e) where
  return = Success
  Failure l >>= _ = Failure l
  Success r >>= k = k r

raise :: e -> Exceptional e a
raise = Failure

catch :: Exceptional e a -> (e -> Exceptional e a) -> Exceptional e a
catch (Failure l) h = h l
catch (Success r) _ = Success r

data Exception = TypeError String Expr
               | UnboundVariable Var
               | Unimplemented Expr
               | EmptyExpr
               | OtherError String

instance Show Exception where
  show (TypeError s e) =
    "Type error, expected an expression of type "
      ++ s
      ++ " but got the expression "
      ++ show e
  show EmptyExpr             = "Empty expression"
  show (UnboundVariable v  ) = "Unbound variable: " ++ v
  show (Unimplemented   e  ) = "No evaluation rule for " ++ show e
  show (OtherError      msg) = msg

type Result = Exceptional Exception

evalNumBinOp :: (Integer -> Integer -> Integer) ->
                 Expr -> Expr -> Env -> Result Val
evalNumBinOp f exp1 exp2 env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case e1 of
    Num n -> case e2 of
      Num m -> return $ Num $ f n m
      _     -> raise $ TypeError "number" exp2
    _ -> raise $ TypeError "number" exp1


evalBoolBinOp :: (Integer -> Integer -> Bool) ->
                 Expr -> Expr -> Env -> Result Val
evalBoolBinOp f exp1 exp2 env = do
  e1 <- eval exp1 env
  e2 <- eval exp2 env
  case e1 of
    Num n -> case e2 of
      Num m -> return $ Boolean $ f n m
      _     -> raise $ TypeError "number" exp2
    _ -> raise $ TypeError "number" exp1


eval :: Expr -> Env -> Result Val
eval (BoolLiteral b) _   = return $ Boolean b
eval (NumLiteral  a) _   = return $ Num a
eval (VarLit      a) env = envLookup a env
eval (If p c a     ) env = do
  be <- eval p env
  case be of
    Boolean b -> eval (if b then c else a) env
    _         -> raise $ TypeError "Boolean" p

eval (Let varName varBody letBody) env = do
  val <- eval varBody env
  eval letBody $ ExtendEnv varName val env

eval (Letrec pnames bvars pbodies body) env =
  eval body $ ExtendEnvRec pnames bvars pbodies env

eval (Proc var   body) env = return $ Procedure var body env
eval (Call rator rand) env = do
  fun <- eval rator env
  appProc (reifyProc fun) $ eval rand env

eval (Add n1 m1) env = evalNumBinOp (+) n1 m1 env
eval (Mult n1 m1) env = evalNumBinOp (*) n1 m1 env
eval (Sub n1 m1) env = evalNumBinOp (-) n1 m1 env
eval (Zerop e) env = do
  v <- eval e env
  case v of
    Num n -> return $ Boolean $ n == 0
    _ -> raise $ TypeError "number" e

eval Break env = raise $ OtherError $ show env
eval expr  _   = raise $ Unimplemented expr

showOp :: String -> Expr -> String
showOp name arg = concat [name, "(", show arg, ")"]

showBinOp :: String -> Expr -> Expr -> String
showBinOp name a b = concat [name, "(", show a, ", ", show b, ")"]

instance Show Val where
  show (Boolean b)          = show b
  show (Num     a)          = show a
  show Nil                  = "()"
  show (Procedure name _ _) = "#<procedure " ++ name ++ ">"
  show _                    = "#<value>"

instance Show Expr where
  show (NumLiteral  n)     = show n
  show (BoolLiteral b)     = show b
  show Emptylist           = "emptylist"
  show (Proc     var expr) = "proc(" ++ show var ++ show expr
  show (Sub      a   b   ) = showBinOp "-" a b
  show (Add      a   b   ) = showBinOp "+" a b
  show (Mult     a   b   ) = showBinOp "*" a b
  show (Div      a   b   ) = showBinOp "/" a b
  show (Greaterp a   b   ) = showBinOp ">" a b
  show (Lessp    a   b   ) = showBinOp "<" a b
  show (Equalp   a   b   ) = showBinOp "=" a b
  show (Zerop    a       ) = showOp "zero?" a
  show (Nullp    a       ) = showOp "null?" a
  show (Car      a       ) = showOp "car" a
  show (Cdr      a       ) = showOp "cdr" a
  show (Begin    a   b   ) = concat ["begin ", show a, "; ", show b, "end"]
  show (Call     a   b   ) = concat ["(", show a, " ", show b]
  show (If a b c) = concat ["if ", show a, "then ", show b, "else ", show c]

  show (Let v e1 e2      ) = concat ["let ", v, " = ", show e1, " in ", show e2]


  show (VarLit a         ) = a

  show e                   = "???"

raiseOtherError = raise . OtherError

nat :: Parser Integer
nat = do
  xs <- many1 digit
  return (read xs :: Integer)

natural :: Parser Integer
natural = token nat

binOpExpr :: String -> (Expr -> Expr -> Expr) -> Parser Expr
binOpExpr keyword op = do
  symb keyword
  symb "("
  e1 <- parseExpr
  symb ","
  e2 <- parseExpr
  symb ")"
  return $ op e1 e2


opExpr :: String -> (Expr -> Expr) -> Parser Expr
opExpr keyword op = do
  symb keyword
  symb "("
  arg <- parseExpr
  symb ")"
  return $ op arg


constExpr = NumLiteral <$> natural

constLit k c = do
  k
  return c

trueExpr = constLit (symb "true") (BoolLiteral True)

falseExpr = constLit (symb "false") (BoolLiteral False)

breakExpr = constLit (symb "break") Break

boolExpr = trueExpr <|> falseExpr

ifExpr = do
  symb "if"
  pred <- parseExpr
  symb "then"
  conseq <- parseExpr
  symb "else"
  If pred conseq <$> parseExpr

parseId = token $ many1 $ sat isAlphaNum

varExpr = VarLit <$> parseId

letExpr = do
  symb "let"
  v <- parseId
  symb "="
  e <- parseExpr
  symb "in"
  Let v e <$> parseExpr

letrecClauseExpr = do
  pname <- parseId
  symb "("
  bvar <- parseId
  symb ")"
  symb "="
  pbody <- parseExpr
  return (pname, bvar, pbody)

letrecExpr = do
  symb "letrec"
  clauses <- many letrecClauseExpr
  symb "in"
  lrbody <- parseExpr
  let names  = map (\(a, _, _) -> a) clauses
      vars   = map (\(_, b, _) -> b) clauses
      bodies = map (\(_, _, c) -> c) clauses

  return $ Letrec names vars bodies lrbody


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

builtinBinOps = [("+", Add), ("*", Mult), ("-", Sub), ("cons", Cons), ("=", Equalp), (">", Greaterp), ("<", Lessp)]

builtinBinOpExpr :: Parser Expr
builtinBinOpExpr = foldr (\(s, op) rest -> binOpExpr s op <|> rest) zero builtinBinOps

builtinOps = [("zero?", Zerop), ("null?", Nullp), ("car", Car), ("cdr", Cdr)]

builtinOpExpr :: Parser Expr
builtinOpExpr = foldr (\(s, op) rest -> opExpr s op <|> rest) zero builtinOps

commentExpr :: Parser Expr
commentExpr = do
  symb "["
  upTo ']'
  symb "]"
  parseExpr

parseExpr :: Parser Expr
parseExpr =
  constExpr
    <|> builtinBinOpExpr
    <|> builtinOpExpr
    <|> ifExpr
    <|> boolExpr
    <|> letExpr
    <|> procExpr
    <|> callExpr
    <|> commentExpr
    <|> breakExpr
    <|> letrecExpr
    <|> varExpr
        -- <|> consExpr
        -- <|> consStreamExpr

readExpr :: String -> Maybe Expr
readExpr s = case parse parseExpr s of
  (res, "") : _ -> Just res
  _             -> Nothing

emptyEnv = EmptyEnv

reval :: String -> Result Val
reval s = case parse parseExpr s of
  (res, ""  ) : _ -> eval res emptyEnv
  (_  , rest) : _ -> raiseOtherError $ "Unexpected characters: " ++ rest
  []              -> raise EmptyExpr

reportResult (Success a) = print a
reportResult (Failure e) = putStrLn $ "Error: " ++ show e

repl :: IO ()
repl = do
  putStr "LETREC> "
  hFlush stdout
  done <- isEOF
  if done
  then do { putStrLn "Exiting."; exitSuccess }
  else do
    exp <- getLine
    if exp == "" then repl else reportResult $ reval exp
    repl

main :: IO ()
main = do
  putStrLn "Welcome to the LETREC interpreter. Control-d to exit."
  repl
