
open Int

type Var = string

datatype Val =
         Nil
         | Cell of Val * Val
         | Num of int
         | Bool of bool
         | String of string
         | Symbol of string
         | Procedure of Var * Expr * Env

and Env = EmptyEnv
        | ExtendEnv of Var * Val * Env
        | ExtendEnvRec of Var * Var * Expr * Env

and Expr = Const of int
         | ConstBool of bool
         | Emptylist
         | Sub of Expr * Expr
         | Add of Expr * Expr
         | Mult of Expr * Expr
         | Div of Expr * Expr              
         | Zerop of Expr
         | Nullp of Expr
         | Cons of Expr * Expr
         | Car of Expr
         | Cdr of Expr
         | Equalp of Expr * Expr
         | Greaterp of Expr * Expr
         | Lessp of Expr * Expr
         | If of Expr * Expr * Expr
         | Var of Sym
         | Let of Var * Expr * Expr
         | Letrec of Var * Var * Expr * Expr
         | Proc of Var * Expr
         | Call of Expr * Expr
   

exception UnboundVariable

fun lookup (var : Var) (env : Env) =
    case env of
        EmptyEnv => raise UnboundVariable
      | ExtendEnv (a, b, restenv) =>
        if var = a
        then b
        else lookup var restenv
      | ExtendEnvRec (pname, bvar, pbody, senv) =>
        if var = pname
        then Procedure (bvar,pbody,env)
        else lookup var senv


exception ToBoolExtractFailed
exception ToNumExtractFailed
exception ToProcExtractFailed

fun val_to_num (e : Val) =
    case e of
      Num n => n
    | _ => raise ToNumExtractFailed

fun val_to_bool (e : Val) =
    case e of
      Bool b => b
    | _ => raise ToBoolExtractFailed


fun apply_proc (p : Val -> Val) (v : Val) = (p v)

exception TypeError

fun eval (e : Expr) (p : Env) =
    let
      fun val_to_proc (e : Val) =
      case e of
         Procedure (var, body, env) => (fn value => (eval body (ExtendEnv (var, value, env))))
         | _ => raise ToProcExtractFailed
      in
    case e of
      Const n => Num n
    | ConstBool b => Bool b
    | Emptylist => Nil
    | Var v => lookup v p
    (* Cons should evaluate its arguments! *)
    | Cons (exp1, exp2) =>
      Cell ((eval exp1 p), (eval exp2 p))
    | Car exp => let val res = (eval exp p) in
                 case res of
                   Cell (a,_) => a
                 | _ => raise TypeError
                 end
    | Cdr exp => let val res = (eval exp p) in
                 case res of
                   Cell (_,a) => a
                 | _ => raise TypeError
                 end
    | Nullp exp => let val res = (eval exp p) in
                 case res of
                   Nil =>  Bool true
                 | _ =>    Bool false
                 end

    | Sub (exp1, exp2) => Num (val_to_num (eval exp1 p)
                            -
                            val_to_num (eval exp2 p))

    | Add (exp1, exp2) => Num (val_to_num (eval exp1 p)
                            +
                            val_to_num (eval exp2 p))

    | Mult (exp1, exp2) => Num (val_to_num (eval exp1 p)
                            *
                            val_to_num (eval exp2 p))

    | Div (exp1, exp2) => Num ((val_to_num (eval exp1 p)) div
                            val_to_num (eval exp2 p))
    | Zerop e => Bool ((val_to_num (eval e p)) = 0)
    | Equalp (exp1, exp2) => Bool ((val_to_num (eval exp1 p)) = (val_to_num (eval exp2 p)))
    | Greaterp (exp1, exp2) => Bool ((val_to_num (eval exp1 p)) >  (val_to_num (eval exp2 p)))
    | Lessp (exp1, exp2) => Bool ((val_to_num (eval exp1 p)) < (val_to_num (eval exp2 p)))
                 
    | If (pred, conseq, alt) => if (val_to_bool (eval pred p))
                                then (eval conseq p)
                                else (eval alt p)
    | Let (var, exp1, body) =>
      eval body (ExtendEnv (var, (eval exp1 p), p))
    | Letrec (pname, bvar, pbody, lrbody) =>
      eval lrbody (ExtendEnvRec (pname, bvar, pbody, p))
      
    | Proc (var, body) => Procedure (var, body, p)
    | Call (rator, rand) =>

      let
         val proc = (val_to_proc (eval rator p))
         val arg  = (eval rand p)
      in
         apply_proc proc arg
      end
      end

        

open Char

fun car (x::xs) = x
  | car nil     = raise Empty

fun cdr (x::xs) = xs
  | cdr nil     = raise Empty

fun cons x y = x :: y

val headStr : string -> char =
    (fn s => (car (explode s)))

val tailStr : string -> string =
    (fn s => (implode (cdr (explode s))))

val cons_string : char -> string -> string =
    (fn c => fn s => (implode (cons c (explode s))))

datatype 'a Parser = Parser of string -> (('a * string) list)

fun parse (Parser p) = p

signature MONAD =
sig
    type 'a monad
    val return : 'a -> 'a monad
    val >>= : 'a monad -> ('a -> 'b monad) -> 'b monad
end

structure ParserM : MONAD =
struct
  type 'a monad = 'a Parser
  val return = (fn a => (Parser (fn cs => [(a,cs)])))
  val >>= =
      (fn p =>
          (fn f =>
              (Parser
                   (fn cs =>
                       (List.concat
                            (map (fn (a,csp) =>
                                     (parse (f a) csp))
                                 (parse p cs)))))))
end

open ParserM
infix `>>=`
fun a `>>=` b = >>= a b
val item : char Parser =
    Parser (fn s =>
               case (explode s)
                of [] => []
                 | (c::cs) => [(c, (implode cs))])

val fail = Parser (fn s => [])

infix ++
fun p ++ q = Parser (fn cs => (parse p cs) @ (parse q cs))

infix +++
fun p +++ q = Parser (fn cs => case parse (p ++ q) cs
                                of []  => []
                                 | (x::xs) => [x])

val sat : (char -> bool) -> char Parser =
 (fn p =>
    (>>= item
          (fn c =>
              (if p c then return c else fail))))

val char : char -> char Parser =
    (fn c => sat (fn d => c = d))

val rec string : string -> string Parser =
 fn s => (case (explode s)
           of [] => return ""
            | (c::cs) => (>>= (char c)
                               (fn _ =>
                                   (>>= (string (implode cs))
                                         (fn _ =>
                                             return s)))))

(*   string (c:cs) = do {char c; string cs; return (c:cs)}        *)

fun manyn p = many1n p +++ return nil
and many1n p =
    (>>= p
          (fn x =>
              (>>= (manyn p)
                    (fn xs =>
                        (return (cons x xs))))))

fun many p = many1 p +++ return ""
and many1 p =
    (>>= p
          (fn x =>
              (>>= (many p)
                    (fn xs =>
                        return (cons_string x xs)))))



(* sepby         :: Parser a -> Parser b -> Parser [a] *)
fun sepbyn p sep  = (sepby1n p sep) +++ return nil
and sepby1n p sep =
    (>>= p
          (fn x =>
              (>>= (manyn (>>= sep
                                 (fn _ => (>>= p (fn a => return a)))))
                    (fn xs => (return (x::xs))))))

fun sepby p sep  = (sepby1 p sep) +++ return ""
and sepby1 p sep =
    (>>= p
          (fn x =>
              (>>= (many (>>= sep
                                (fn _ => (>>= p (fn a => return a)))))
                    (fn xs => (return (cons_string x xs))))))


val space : string Parser = (many (sat isSpace))

val token : 'a Parser -> 'a Parser =
    (fn p =>
        (>>= p
              (fn a =>
                  (>>= space
                        (fn _ =>
                            (return a))))))

val symb : string -> string Parser = (fn cs => (token (string cs)))

val apply : 'a Parser -> string -> ('a * string) list =
    (fn p => (parse (>>= space (fn _ => (>>= p (fn a => return a))))))

val |> =
    (fn m =>
        (fn p =>
            (>>= m
                  (fn a =>
                      (if (p a) then (return a) else fail)))))
val digit =
    (>>= (|> item isDigit)
          (fn a => (return a)))

val negnat =
     (>>= (char #"-")
       (fn _ =>
         (>>= (many1 digit)
           (fn xs => (case (Int.fromString xs)
                      of SOME x => (return (~x))
                      |  NONE   => fail)))))
val nat =
  ((>>= (many1 digit)
          (fn xs => (case (Int.fromString xs)
                      of SOME x => (return x)
                      |  NONE   => fail))) +++ negnat)

val natural = (token nat)


val try_read =
let fun ParseConst _ = (>>= natural (fn n => return (Const n)))
and ParseTrue _ = (>>= (symb "true") (fn _ => (return (ConstBool true))))
and ParseFalse _ = (>>= (symb "false") (fn _ => (return (ConstBool false))))
and ParseBoolean _ = ((ParseTrue ()) +++ (ParseFalse ()))
and ParseIf _ =
    (>>= (symb "if")
      (fn _ =>
         (>>= (ParseExpr ())
           (fn pred =>
             (>>= (symb "then")
               (fn _ =>
                 (>>= (ParseExpr ())
                   (fn conseq =>
                     (>>= (symb "else")
                       (fn _ =>
                         (>>= (ParseExpr ())
                           (fn alt =>
                             (return (If (pred,conseq,alt)))))))))))))))

and ParseZerop _ =
    (>>= (symb "zero?")
      (fn _ =>
        (>>= (symb "("))
        (fn _ =>
         (>>= (ParseExpr ())
         (fn exp1 =>
          (>>= (symb ")")
           (fn _ =>
              (return (Zerop exp1)))))))))

and ParseNullp _ =
    (>>= (symb "null?")
      (fn _ =>
        (>>= (symb "("))
        (fn _ =>
         (>>= (ParseExpr ())
         (fn exp1 =>
          (>>= (symb ")")
           (fn _ =>
              (return (Nullp exp1)))))))))


and ParseCar _ =
    (>>= (symb "car")
      (fn _ =>
        (>>= (symb "("))
        (fn _ =>
         (>>= (ParseExpr ())
         (fn exp1 =>
          (>>= (symb ")")
           (fn _ =>
              (return (Car exp1)))))))))


and ParseCdr _ =
    (>>= (symb "cdr")
      (fn _ =>
        (>>= (symb "("))
        (fn _ =>
         (>>= (ParseExpr ())
         (fn exp1 =>
          (>>= (symb ")")
           (fn _ =>
              (return (Cdr exp1)))))))))

and ParseSub _ =
  (>>= (symb "-")
    (fn _ =>
       (>>= (symb "("))
       (fn _ =>
         (>>= (ParseExpr ())
            (fn exp1 =>
               (>>= (symb ",")
                  (fn _ =>
                    (>>= (ParseExpr ())
                    (fn exp2 =>
                      (>>= (symb ")")
                        (fn _ =>
                          (return (Sub (exp1,exp2))))))))))))))

and ParseMult _ =
  (>>= (symb "*")
    (fn _ =>
       (>>= (symb "("))
       (fn _ =>
         (>>= (ParseExpr ())
            (fn exp1 =>
               (>>= (symb ",")
                  (fn _ =>
                    (>>= (ParseExpr ())
                    (fn exp2 =>
                      (>>= (symb ")")
                        (fn _ =>
                          (return (Mult (exp1,exp2))))))))))))))

and ParseAdd _ =
  (>>= (symb "+")
    (fn _ =>
       (>>= (symb "("))
       (fn _ =>
         (>>= (ParseExpr ())
            (fn exp1 =>
               (>>= (symb ",")
                  (fn _ =>
                    (>>= (ParseExpr ())
                    (fn exp2 =>
                      (>>= (symb ")")
                        (fn _ =>
                          (return (Add (exp1,exp2))))))))))))))

and ParseDiv _ =
  (>>= (symb "/")
    (fn _ =>
       (>>= (symb "("))
       (fn _ =>
         (>>= (ParseExpr ())
            (fn exp1 =>
               (>>= (symb ",")
                  (fn _ =>
                    (>>= (ParseExpr ())
                    (fn exp2 =>
                      (>>= (symb ")")
                        (fn _ =>
                          (return (Div (exp1,exp2))))))))))))))

and ParseEqualp _ =
  (>>= (symb "=")
    (fn _ =>
       (>>= (symb "("))
       (fn _ =>
         (>>= (ParseExpr ())
            (fn exp1 =>
               (>>= (symb ",")
                  (fn _ =>
                    (>>= (ParseExpr ())
                    (fn exp2 =>
                      (>>= (symb ")")
                        (fn _ =>
                          (return (Equalp (exp1,exp2))))))))))))))

and ParseGreaterp _ =
  (>>= (symb ">")
    (fn _ =>
       (>>= (symb "("))
       (fn _ =>
         (>>= (ParseExpr ())
            (fn exp1 =>
               (>>= (symb ",")
                  (fn _ =>
                    (>>= (ParseExpr ())
                    (fn exp2 =>
                      (>>= (symb ")")
                        (fn _ =>
                          (return (Greaterp (exp1,exp2))))))))))))))


and ParseLessp _ =
  (>>= (symb "<")
    (fn _ =>
       (>>= (symb "("))
       (fn _ =>
         (>>= (ParseExpr ())
            (fn exp1 =>
               (>>= (symb ",")
                  (fn _ =>
                    (>>= (ParseExpr ())
                    (fn exp2 =>
                      (>>= (symb ")")
                        (fn _ =>
                          (return (Lessp (exp1,exp2))))))))))))))


and ParseCons _ =
  (>>= (symb "cons")
    (fn _ =>
       (>>= (symb "("))
       (fn _ =>
         (>>= (ParseExpr ())
            (fn exp1 =>
               (>>= (symb ",")
                  (fn _ =>
                    (>>= (ParseExpr ())
                    (fn exp2 =>
                      (>>= (symb ")")
                        (fn _ =>
                          (return (Cons (exp1,exp2))))))))))))))

and ParseId _ =
  (>>= (token (many (sat isAlphaNum)))
     (fn v => (return v)))

and ParseEmptyList _ =
  (>>= (symb "emptylist")
     (fn v => (return Emptylist)))

and ParseVar _ =
  (>>= (ParseId ())
     (fn v => (return (Var v))))

and ParseLet _ =
  (>>= (symb "let")
   (fn _ =>
  (>>= (ParseId ())
    (fn v =>
      (>>= (symb "=")
         (fn _ =>
           (>>= (ParseExpr ())
             (fn e =>
                (>>= (symb "in")
                   (fn _ =>
                     (>>= (ParseExpr ())
                       (fn e2 =>
                         (return (Let (v,e,e2)))))))))))))))


and ParseLetRec _ =
  (>>= (symb "letrec")
   (fn _ =>
  (>>= (ParseId ())
    (fn pname =>
      (>>= (symb "(")
        (fn _ =>
          (>>= (ParseId ())
          (fn bvar =>
            (>>= (symb ")")
            (fn _ =>
      (>>= (symb "=")
         (fn _ =>
           (>>= (ParseExpr ())
             (fn pbody =>
                (>>= (symb "in")
                   (fn _ =>
                     (>>= (ParseExpr ())
                       (fn lrbody =>
                         (return (Letrec (pname,bvar,pbody,lrbody)))))))))))))))))))))

and ParseProc _ =
  (>>= (symb "proc")
     (fn _ =>
       (>>= (symb "(")
         (fn _ =>
           (>>= (ParseId ())
             (fn v =>
                (>>= (symb ")")
                  (fn _ =>
                    (>>= (ParseExpr ())
                      (fn e =>
                         (return (Proc (v, e)))))))))))))

and ParseCall _ =
   (>>= (symb "(")
      (fn _ =>
        (>>= (ParseExpr ())
           (fn e1 =>
               (>>= (ParseExpr ())
                 (fn e2 =>
                   (>>= (symb ")")
                    (fn _ => (return (Call (e1, e2)))))))))))

and ParseComment _ =
   (>>= (symb "[")
      (fn _ =>
         (>>= (many (sat (fn x => (not (x = #"]")))))
              (fn _ => (>>= (symb "]") (fn _ => (ParseExpr ())))))))

and ParseExpr _ = (ParseIf ())
              +++ (ParseConst ())
              +++ (ParseBoolean ())              
              +++ (ParseComment ())              
              +++ (ParseCons ())
              +++ (ParseCar ())
              +++ (ParseCdr ())
              +++ (ParseNullp ())
              +++ (ParseEmptyList ())
              +++ (ParseZerop ())
              +++ (ParseGreaterp ())
              +++ (ParseLessp ())              
              +++ (ParseEqualp ())                            
              +++ (ParseSub ())
              +++ (ParseMult ())
              +++ (ParseAdd ())
              +++ (ParseDiv ())                            
              +++ (ParseLet ())
              +++ (ParseLetRec ())              
              +++ (ParseProc ())
              +++ (ParseCall ())
              +++ (ParseVar ())
in
 (fn s => parse (ParseExpr ()) s)
end




fun show (x : (Expr * string) list) = #1 (car x)

val read = (show o try_read)

fun evalo e = eval e EmptyEnv

val run = (evalo o read)

fun readfile(filename) =
    let val file = TextIO.openIn filename
        val content = TextIO.inputAll file
        val _ = TextIO.closeIn file
    in content
    end

fun runfile(filename) = (run o readfile) filename


fun cell_to_string c =
    case c of
      Nil => "()"
    | Cell (a, b) => "(" ^ val_to_string(a) ^ " . " ^ val_to_string(b) ^ ")"
    | _ => raise TypeError

and val_to_string(v) = case v of
                   Bool a      => Bool.toString a
                 | Num a       => Int.toString a
                 | Nil         => "()"
                 | Cell (a,b)  => cell_to_string (Cell (a,b))
                 | Procedure (name, _, _) => "#<procedure " ^ name ^">"
                 | _           => "#<value>"
(* Read evaluate print a file*)
fun repf(filename) = print ("Result of evaluation: " ^ (val_to_string o run o readfile) filename ^ "\n")
