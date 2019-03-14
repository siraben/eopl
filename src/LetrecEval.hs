module LetrecEval where

import LetrecTypes
import           Data.List

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
