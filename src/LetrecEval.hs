{-|
Module      : LetrecEval
Description : The evaluator for LETREC.

This evaluator is an environment-passing evaluator, returning values
of type 'Result' 'Val', so that the evaluator can signal exceptions in
a pure manner.
-}
module LetrecEval where

import           Data.List
import           LetrecTypes

-- |Lift a numeric binary operation to work with expressions.  Raises
-- an 'TypeError' if either of the expressions do not evaluate to
-- something of type @Num n@.
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


-- |Like 'evalNumBinOp', but lifts a predicate function on numbers.
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

-- |The environment-passing evaluator for LETREC.
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
  case fun of
    Procedure _ _ _ -> appProc (reifyProc fun) $ eval rand env
    _               -> raise $ TypeError "procedure" rator

eval (Add n m) env = evalNumBinOp (+) n m env
eval (Mult n m) env = evalNumBinOp (*) n m env
eval (Sub n m) env = evalNumBinOp (-) n m env
eval (Lessp n m) env = evalBoolBinOp (<) n m env
eval (Greaterp n m) env = evalBoolBinOp (>) n m env
eval (Equalp n m) env = evalBoolBinOp (==) n m env

eval (Div ne me) env = do
  n <- eval ne env
  m <- eval me env
  case m of
    Num 0 -> raiseOtherError $ "Divide by 0"
    Num m -> case n of
               Num n -> return $ Num $ div n m
               _     -> raise $ TypeError "number" ne
    _ -> raise $ TypeError "number" me

eval (Zerop e) env = do
  v <- eval e env
  case v of
    Num n -> return $ Boolean $ n == 0
    _     -> raise $ TypeError "number" e

eval Break env = raiseOtherError $ "Break received, environment: " ++ show env

eval (Cons x y) env = do
  x <- eval x env
  y <- eval y env
  return $ Cell x y

eval (ConsStream x y) env = do
  x <- eval x env
  return $ Cell x $ Procedure "_" y env

eval e@(Car c) env = do
  c <- eval c env
  case c of
    Cell car cdr -> return car
    _            -> raise $ TypeError "cell" e

eval e@(Cdr c) env = do
  c <- eval c env
  case c of
    Cell car cdr -> return cdr
    _            -> raise $ TypeError "cell" e

eval Emptylist _ = return Nil
eval (Nullp e) env = do
  v <- eval e env
  case v of
    Nil        -> return $ Boolean True
    (Cell _ _) -> return $ Boolean False
    _          -> raise $ TypeError "cell" e

eval expr  _   = raise $ Unimplemented expr

-- |Look up a variable in the given environment, raising
-- 'UnboundVariable' if the variable is not found.
envLookup :: Var -> Env -> Result Val
envLookup searchVar EmptyEnv = raise $ UnboundVariable searchVar
envLookup searchVar (ExtendEnv currVar val rest) =
  if searchVar == currVar then return val else envLookup searchVar rest

envLookup searchVar env@(ExtendEnvRec pnames bvars pbodies rest) =
  case elemIndex searchVar pnames of
    Just n  -> return $ Procedure (bvars !! n) (pbodies !! n) env
    Nothing -> envLookup searchVar rest

-- |Convert a 'Procedure' into a function that takes a 'Val' and
-- returns a 'Result' 'Val'.
reifyProc :: Val -> Val -> Result Val
reifyProc (Procedure var body env) val = eval body $ ExtendEnv var val env

-- |Apply a procedure.
appProc :: (Val -> Result Val) -> Result Val -> Result Val
appProc = (=<<)

