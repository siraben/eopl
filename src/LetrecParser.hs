{-|
Module      : LetrecParser
Description : The parser for LETREC.

This is an implementation of combinator parsing from scratch,
including various instance declarations for the 'Functor', 'Monad',
'Applicative', 'MonadZero' and 'MonadPlus' typeclasses.
-}

{-# LANGUAGE LambdaCase #-}
module LetrecParser where
import           Data.Char
import           LetrecTypes

newtype Parser a = Parser (String -> [(a, String)])

-- |Consume a single character.
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

-- |A monad with a zero (i.e. "failure").
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

-- |Given two parsers @p@ and @q@, create a new parser such @q@ is
-- tried if @p@ failed.
(+++) :: Parser a -> Parser a -> Parser a
p +++ q = Parser
  (\cs -> case parse (p <|> q) cs of
    []       -> []
    (x : xs) -> [x]
  )

-- |Lift a predicate into a parser.
sat :: (Char -> Bool) -> Parser Char
sat p = do
  c <- item
  if p c then return c else zero

-- |Consume a specific character.
char :: Char -> Parser Char
char c = sat (c ==)

-- |Consume a specific string.
string :: String -> Parser String
string ""       = return ""
string (c : cs) = do
  char c
  string cs
  return (c : cs)

-- |Turns a parser into its Kleene star variant.
many :: Parser a -> Parser [a]
many p = many1 p +++ return []

-- |Turns a parser into its Kleene plus variant.
many1 :: Parser a -> Parser [a]
many1 p = do
  a  <- p
  as <- many p
  return (a : as)

-- |Given two parsers @a@, @b@, return a parser @c@ such that it
-- accepts the language given by @a@ separated by @b@, and drops the
-- results of the separator.
sepby :: Parser a -> Parser b -> Parser [a]
p `sepby` sep = (p `sepby1` sep) +++ return []

-- |Like 'sepby', but at least one non-separator element must be
-- parsed.
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

-- |Parse a numeric digit.
digit :: Parser Char
digit = sat isDigit

-- |Parser leading whitespace.
space :: Parser String
space = many $ sat isSpace

-- |Lifts a parser into a whitespace-prefixed accepting one.
token :: Parser a -> Parser a
token p = p <* space

-- |Parse a symbol, consuming leading whitespace.
symb :: String -> Parser String
symb = token . string

-- |Parse characters up to the given terminator.
upTo :: Char -> Parser String
upTo c = many $ sat (/= c)

-- |Parse a number.
nat :: Parser Integer
nat = read <$> many1 digit

-- |Like 'nat' but consumes leading whitespace.
natural :: Parser Integer
natural = token nat

-- |Given the name of a LETREC binary operator, and its constructor,
-- return its parser.
binOpExpr :: String -> (Expr -> Expr -> Expr) -> Parser Expr
binOpExpr keyword op = do
  symb keyword
  symb "("
  e1 <- parseExpr
  symb ","
  e2 <- parseExpr
  symb ")"
  return $ op e1 e2

-- |Like 'binOpExpr' but for unary operators.
opExpr :: String -> (Expr -> Expr) -> Parser Expr
opExpr keyword op = do
  symb keyword
  symb "("
  arg <- parseExpr
  symb ")"
  return $ op arg

-- |Parse a negative number.
negnat = string "-" *> (negate <$> natural)

-- |Parse a LETREC number.
numExpr = NumLiteral <$> (natural <|> negnat)

-- |The list of reserved LETREC constants.
constExprs = [("true", BoolLiteral True),
              ("false", BoolLiteral False),
              ("emptylist", Emptylist),
              ("break", Break)]

-- |Apply a parser, then when it succeeds, return a constant.
constLit k c = k *> return c

-- |Parse a built-in constant (as defined in 'constExprs').
builtinConstExpr :: Parser Expr
builtinConstExpr = foldr (\(s, const) rest -> constLit (symb s) const <|> rest)
                         zero
                         constExprs

-- |Parse an @if@ expression, of the form:
-- @if <expr> else <exr> then <expr>@.
ifExpr = do
  symb "if"
  pred <- parseExpr
  symb "then"
  conseq <- parseExpr
  symb "else"
  If pred conseq <$> parseExpr

-- |Parse a LETREC identifier, a space-delimited word consisting of
-- alpha-numeric characters.
parseId = token $ many1 $ sat isAlphaNum

-- |Parse a variable, a wrapper for 'parseId'.
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

decomposeMultiCall op []            = error "Procedure has no arguments."
decomposeMultiCall op [arg]         = Call op arg
decomposeMultiCall op (arg1 : rest) = decomposeMultiCall (Call op arg1) rest

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

builtinBinOps = [("+", Add), ("*", Mult), ("-", Sub),
                 ("cons", Cons), ("=", Equalp), (">", Greaterp),
                 ("<", Lessp), ("cons_stream", ConsStream), ("/", Div)]

builtinBinOpExpr :: Parser Expr
builtinBinOpExpr = foldr (\(s, op) rest -> binOpExpr s op <|> rest) zero builtinBinOps

-- |A mapping of symbols for unary operators to their constructors of
-- type ('Expr' -> 'Expr')
builtinOps = [("zero?", Zerop), ("null?", Nullp), ("car", Car), ("cdr", Cdr)]

-- |Parse a built-in unary operator, as declared in 'builtinOps'.
builtinOpExpr :: Parser Expr
builtinOpExpr = foldr (\(s, op) rest -> opExpr s op <|> rest) zero builtinOps

-- |Parse a comment, defined as a string starting with @[@, containing
-- any number of intermediate characters, and ending with a @]@.
commentExpr :: Parser String
commentExpr = symb "[" *> upTo ']' *> symb "]"
  
-- |Parse a top-level comment, then parse an expression.
toplevelCommentExpr = commentExpr *> parseExpr

reifyExprList :: [Expr] -> Expr
reifyExprList []       = Emptylist
reifyExprList (x : xs) = Cons x $ reifyExprList xs
listExpr = do
  symb "list"
  symb "("
  xs <- sepby parseExpr (symb ",")
  symb ")"
  return $ reifyExprList xs

-- |Parse an expression.
parseExpr :: Parser Expr
parseExpr =
        numExpr
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

-- |Parse a string into a LETREC 'Expr', but return @Nothing@ if there
-- was unconsumed input.
readExpr :: String -> Maybe Expr
readExpr s = case parse parseExpr s of
  (res, "") : _ -> Just res
  _             -> Nothing
