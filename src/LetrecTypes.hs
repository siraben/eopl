module LetrecTypes where

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
          | ConsStream Expr Expr
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
          | Procs [Var] Expr
          | Call Expr Expr
          | Calls Expr [Expr]
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

-- |The exceptional type, isomorphic to Either.
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

-- |The exception type.
data Exception = TypeError String Expr
               | UnboundVariable Var
               | Unimplemented Expr
               | EmptyExpr
               | OtherError String

instance Show Exception where
  show (TypeError s e) =
    "Type error, expected type "
      ++ s
      ++ " but got "
      ++ show e
  show EmptyExpr             = "Unknown expression"
  show (UnboundVariable v  ) = "Unbound variable: " ++ v
  show (Unimplemented   e  ) = "No evaluation rule for " ++ show e
  show (OtherError      msg) = msg

type Result = Exceptional Exception

-- |Print a unary operation.
showOp :: String -> Expr -> String
showOp name arg = concat [name, "(", show arg, ")"]

showBinOp :: String -> Expr -> Expr -> String
showBinOp name a b = concat [name, "(", show a, ", ", show b, ")"]

showCell :: Val -> String
showCell Nil = ""
showCell (Cell a b) = show a ++ case b of
                                  rest@(Cell _ _) -> " " ++ showCell rest
                                  Nil -> ""
                                  val -> " . " ++ show val

instance Show Val where
  show (Boolean b)          = show b
  show (Num     a)          = show a
  show (Procedure name _ _) = "#<procedure " ++ name ++ ">"
  show e@(Cell _ _) = "(" ++ showCell e ++ ")"
  show _                    = "#<value>"

show_letrec_clauses [] [] [] = ""
show_letrec_clauses (n : ns) (b : bs) (bo : bos) = concat [n, "(", b, " ) =", show bo, show_letrec_clauses ns bs bos]

show_args [] = ""
show_args [a] = show a
show_args (a : as) = show a ++ " " ++ show_args as

show_vars [] =  []
show_vars [v] = v ++ ") "
show_vars (v : vs) = v ++ ", " ++ show_vars vs

instance Show Expr where
  show (NumLiteral  n)     = show n
  show (BoolLiteral b)     = show b
  show Emptylist           = "emptylist"
  show (Proc     var expr) = "(proc(" ++ var ++ ") " ++ show expr ++ ")"
  show (Procs   vars expr) = "proc*(" ++ show_vars vars ++ show expr
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
  show (Call     a   b   ) = concat ["(", show a, " ", show b, ")"]
  
  show (Calls    a   b   ) = concat $ ["(", show a, " ", show_args b, ")"]
  
  show (If a b c) = concat ["if ", show a, "then ", show b, "else ", show c]

  show (Let v e1 e2      ) = concat ["let ", v, " = ", show e1, " in ", show e2]

  show (Letrec names bvars bodies body) = concat ["letrec", show_letrec_clauses names bvars bodies, " in ", show body]
  show (VarLit a         ) = a

  show e                   = "???"

raiseOtherError = raise . OtherError
