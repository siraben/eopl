{-# LANGUAGE LambdaCase #-}
module LetrecParser where
import           Data.Char
import           LetrecTypes

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
  as <- many $ do { sep; p }
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


negnat = do
  string "-"
  n <- natural
  return $ - n

constExpr = do
  x <- natural <|> negnat
  return $ NumLiteral x

constExprs = [("true", BoolLiteral True),
              ("false", BoolLiteral False),
              ("emptylist", Emptylist),
              ("break", Break)]

constLit k c = do
  k
  return c

builtinConstExpr :: Parser Expr
builtinConstExpr = foldr (\(s, const) rest -> constLit (symb s) const <|> rest) zero constExprs

ifExpr = do
  symb "if"
  pred <- parseExpr
  symb "then"
  conseq <- parseExpr
  symb "else"
  If pred conseq <$> parseExpr

parseId = token $ many1 $ sat isAlphaNum

varExpr = VarLit <$> parseId

decomposeMultiLet :: [(Var, Expr)] -> Expr -> Expr
decomposeMultiLet l e = foldr (\(s, op) rest -> Let s op rest) e l
  
letExpr = do
  symb "let"
  v <- many letClauseExpr
  symb "in"
  e <- parseExpr
  return $ uncurry decomposeMultiLet (v, e) 
  

letClauseExpr = do
  var <- parseId
  symb "="
  binding <- parseExpr
  return (var, binding)

letrecClauseExpr = do
  pname <- parseId
  symb "("
  bvar <- parseId
  symb ")"
  symb "="
  pbody <- parseExpr
  return (pname, bvar, pbody)

letrecCommentExpr = do { commentExpr; letrecClauseExpr }
  
letrecExpr = do
  symb "letrec"
  clauses <- many $ letrecClauseExpr <|> letrecCommentExpr
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

desugarMultiProc vars body = foldr Proc body vars
procsExpr = do
  symb "proc*"
  symb "("
  vars <- sepby parseId (symb ",")
  symb ")"
  body <- parseExpr
  return $ desugarMultiProc vars body

-- decomposeMultiCall :: [(Expr)] -> Expr -> Expr
decomposeMultiCall op [] = error "Procedure has no arguments."
decomposeMultiCall op [arg] = Call op arg
decomposeMultiCall op (arg1 : rest) = decomposeMultiCall (Call op arg1) rest

-- decomposeMultiCall2 args = foldl Call  args

callsExpr = do
  symb "("
  e <- parseExpr
  -- Force the list "es", containing the arguments, to be at least one.
  es <- many1 parseExpr
  symb ")"
  return $ decomposeMultiCall e es

callExpr = do
  symb "("
  e1 <- parseExpr
  e2 <- parseExpr
  symb ")"
  return $ Call e1 e2

builtinBinOps = [("+", Add), ("*", Mult), ("-", Sub), ("cons", Cons), ("=", Equalp), (">", Greaterp), ("<", Lessp), ("cons_stream", ConsStream), ("/", Div)]

builtinBinOpExpr :: Parser Expr
builtinBinOpExpr = foldr (\(s, op) rest -> binOpExpr s op <|> rest) zero builtinBinOps

builtinOps = [("zero?", Zerop), ("null?", Nullp), ("car", Car), ("cdr", Cdr)]

builtinOpExpr :: Parser Expr
builtinOpExpr = foldr (\(s, op) rest -> opExpr s op <|> rest) zero builtinOps

commentExpr :: Parser String
commentExpr = do
  symb "["
  upTo ']'
  symb "]"

toplevelCommentExpr = do { commentExpr; parseExpr }

reifyExprList :: [Expr] -> Expr
reifyExprList [] = Emptylist
reifyExprList (x : xs) = Cons x $ reifyExprList xs
listExpr = do
  symb "list"
  symb "("
  xs <- sepby parseExpr (symb ",")
  symb ")"
  return $ reifyExprList xs
  
parseExpr :: Parser Expr
parseExpr =
        constExpr
    <|> builtinConstExpr
    <|> builtinBinOpExpr
    <|> builtinOpExpr
    <|> ifExpr
    <|> letExpr
    <|> procExpr
    <|> procsExpr
    <|> listExpr
    <|> callExpr
    <|> callsExpr
    <|> toplevelCommentExpr
    <|> letrecExpr
    <|> varExpr

readExpr :: String -> Maybe Expr
readExpr s = case parse parseExpr s of
  (res, "") : _ -> Just res
  _             -> Nothing
