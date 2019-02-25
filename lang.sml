Control.Print.printDepth := 100;
open Int

type Var = string

datatype Val =
         Nil
         | Cell of Val * Val
         | Num of int
         | Bool of bool
         | String of string
         | Symbol of string
         | Ref of int
         | Procedure of Var * Expr * Env

and Env = EmptyEnv
        | ExtendEnv of Var * Val * Env
        | ExtendEnvRec of Var * Var * Expr * Env

and Expr = Const of int
         | ConstBool of bool
         | Emptylist
         | BeginEnd
         | Sub of Expr * Expr
         | Add of Expr * Expr
         | Mult of Expr * Expr
         | Div of Expr * Expr
         | Zerop of Expr
         | Nullp of Expr
         | Cons of Expr * Expr
         | Begin of Expr * Expr
         | Car of Expr
         | Cdr of Expr
         | Equalp of Expr * Expr
         | Greaterp of Expr * Expr
         | Lessp of Expr * Expr
         | If of Expr * Expr * Expr
         | Var of string
         | Let of Var * Expr * Expr
         | Letrec of Var * Var * Expr * Expr
         | Proc of Var * Expr
         | Call of Expr * Expr
         | Newref of Expr
         | Deref of Expr
         | Setref of Expr * Expr


exception UnboundVariable
exception UnimplementedOperation

fun lookup (var : Var) (env : Env) =
    case env of
        EmptyEnv => (print("Unbound variable: \"" ^ var ^ "\""); raise UnboundVariable)
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
exception ToRefExtractFailed

fun val_to_num (e : Val) =
    case e of
      Num n => n
    | _ => raise ToNumExtractFailed

fun val_to_bool (e : Val) =
    case e of
      Bool b => b
    | _ => raise ToBoolExtractFailed

fun val_to_ref (e : Val) =
    case e of
      Ref b => b
    | _ => raise ToRefExtractFailed


fun empty_store _ = ref [Num ~1]

val the_store = (empty_store ())

fun initialize_store _ = (the_store := [Num ~1])


fun newref (v : Val) = let
                           val nr = List.length (!the_store)
                       in
                           the_store := (!the_store) @ [v];
                           nr
                       end

fun deref r = List.nth ((!the_store),r)

exception InvalidReference

fun setref r (v : Val) = (the_store := List.update (!the_store,r,v))
                         handle Subscript => raise InvalidReference


fun apply_proc (p : Val -> Val) (v : Val) = (p v)

exception TypeError
exception NoMatchingBegin

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
    | Begin (exp1, exp2) =>
      if exp2 = BeginEnd
      then (eval exp1 p)
      else ((eval exp1 p); (eval exp2 p))
    | BeginEnd => raise NoMatchingBegin
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

    | Sub (exp1, exp2) => Num (val_to_num (eval exp1 p) -
                               val_to_num (eval exp2 p))

    | Add (exp1, exp2) => Num (val_to_num (eval exp1 p) +
                               val_to_num (eval exp2 p))

    | Mult (exp1, exp2) => Num (val_to_num (eval exp1 p) *
                                val_to_num (eval exp2 p))

    | Div (exp1, exp2) => Num (val_to_num (eval exp1 p) div
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
    | Newref exp1  =>  let
                          val v1 = eval exp1 p
                       in
                          Ref (newref v1)
                       end
    | Deref exp1  =>  let
                          val v1 = eval exp1 p
                          val ref1 = val_to_ref v1
                       in
                          deref ref1
                      end
    | Setref (exp1, exp2)  =>
                      let
                          val ref1 = val_to_ref (eval exp1 p)
                          val val2 = eval exp2 p
                      in
                          setref ref1 val2;
                          Num 23
                      end

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

fun is_cons (Cons _) = true
  | is_cons _        = false

fun is_cell (Cell _) = true
  | is_cell _        = false

fun to_cons_list [] = Emptylist
  | to_cons_list (x::xs) = Cons (x,to_cons_list xs)

fun to_begin_list []      = BeginEnd
  | to_begin_list (x::xs) = Begin (x,to_begin_list xs)

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


and make_op keyword constructor =
(>>= (symb keyword)
      (fn _ =>
        (>>= (symb "("))
        (fn _ =>
         (>>= (ParseExpr ())
         (fn exp1 =>
          (>>= (symb ")")
           (fn _ =>
              (return (constructor exp1)))))))))

and ParseZerop  _ = make_op "zero?" Zerop
and ParseNullp  _ = make_op "null?" Nullp
and ParseCar    _ = make_op "car" Car
and ParseCdr    _ = make_op "cdr" Cdr
and ParseNewref _ = make_op "newref" Newref
and ParseDeref  _ = make_op "deref" Deref

and make_binop keyword constructor =
  (>>= (symb keyword)
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
                          (return (constructor (exp1,exp2))))))))))))))

and ParseSub      _ = make_binop "-" Sub
and ParseMult     _ = make_binop "*" Mult
and ParseAdd      _ = make_binop "+" Add
and ParseDiv      _ = make_binop "/" Div
and ParseEqualp   _ = make_binop "=" Equalp
and ParseGreaterp _ = make_binop ">" Greaterp
and ParseLessp    _ = make_binop "<" Lessp
and ParseCons     _ = make_binop "cons" Cons
and ParseSetref   _ = make_binop "setref" Setref

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

and ParseList _ =
    (>>= (symb "{")
     (fn _ =>
       (>>= (ParseExpr ())
            (fn n =>
              (>>= (manyn (>>= (symb ",") (fn _ => (ParseExpr ()))))
                   (fn ns =>
                     (>>= (symb "}")
                          (fn _ => (return (to_cons_list (n :: ns)))))))))))

and ParseBegin _ =
    (>>= (symb "begin")
     (fn _ =>
       (>>= (ParseExpr ())
            (fn n =>
              (>>= (manyn (>>= (symb ";") (fn _ => (ParseExpr ()))))
                   (fn ns =>
                     (>>= (symb "end")
                          (fn _ => (return (to_begin_list (n :: ns)))))))))))


and ParseExpr _ = (ParseIf ())
              +++ (ParseConst ())
              +++ (ParseBoolean ())
              +++ (ParseComment ())
              +++ (ParseCons ())
              +++ (ParseList ())
              +++ (ParseBegin ())
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
              +++ (ParseSetref ())
              +++ (ParseDeref ())
              +++ (ParseNewref ())
              +++ (ParseProc ())
              +++ (ParseCall ())
              +++ (ParseVar ())
in
 (fn s => parse (ParseExpr ()) s)
end


fun show (x : (Expr * string) list) = #1 (car x)

val read = (show o try_read)

fun evalo e = eval e EmptyEnv

val run = let in (initialize_store ()); (evalo o read) end

fun readfile(filename) =
    let val file = TextIO.openIn filename
        val content = TextIO.inputAll file
        val _ = TextIO.closeIn file
    in content
    end

fun runfile(filename) = (run o readfile) filename


fun cell_to_string c =
    case c of
      Nil => ""
    | Cell (a, b) => val_to_string(a) ^ ( case b of
                       Cell c =>  " " ^ cell_to_string(Cell c)
                    |  Nil => ""
                    |  c => " . " ^ val_to_string(c) )
    | _ => raise TypeError


and val_to_string(v) = case v of
                   Bool a      => Bool.toString a
                 | Num a       => Int.toString a
                 | Nil         => "()"
                 | Cell a  => "(" ^ (cell_to_string (Cell a)) ^ ")"
                 | Procedure (name, _, _) => "#<procedure " ^ name ^">"
                 | Ref a => "#<reference " ^ Int.toString a ^ ">"
                 | _           => "#<value>"
(* Read evaluate print a file*)
fun repf(filename) = print ("Result of evaluation: " ^ (val_to_string o run o readfile) filename ^ "\n")

fun parse_tree filename = (read o readfile) filename
