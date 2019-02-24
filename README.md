# Standard ML Implementations of the languages from EOPL
_Note: The language might be changed to Haskell in the future._

This project aims to implement the languages found in the textbook
[Essentials of Programming
Languages](https://mitpress.mit.edu/books/essentials-programming-languages).

## Why?
It's somewhat awkward to fit in a datatype language into Scheme, which
lacks static typing and pattern matching.  Why not use Standard ML,
with uses the powerful Hindley-Milner type system to do the heavy
lifting?

## Implementation
The parser is implemented with parser combinators.  Currently it's
just a direct translation from my other Scheme parser combinator
library, and will need to be reworked significantly.  I'm striving for
an implementation of the languages in EOPL with the minimal amount of
code required that still is readable and is close to heart to the
source material.

## How to use
The most interesting function is probably `repf`, which accepts a
filename, parses it into the AST, runs `eval` over it and then uses
the pretty printer to display the result.  The pretty printer is at an
early stage so don't expect lists to look nice!  `runfile` reads the
filename, executes it but doesn't convert the final value into a
pretty printed version, which can be useful for debugging purposes.
`parse_tree` accepts a filename and shows the parse tree for that
file.  Due to the way the grammar of the language is specified, you
will find that adding extra parens around expressions can dramatically
change its semantics.  `parse_tree` lets you see those invisible
empty string variable names that may pop up, for instance.

## Program example (prime numbers)
```text
[ These square brackets are comments, a feature I added that was
  not in EOPL. ]
  
[ Generate a range of numbers ]
[ letrec allows a procedure to refer to itself in the definition ]
letrec range(start) =
  proc (stop)
    if
      =(start,stop)
    then
      emptylist
    else
      let step =
        if <(start,stop)
          then
            1
          else
            -1
      in
        [ Every procedure takes one argument, hence the extra parens ]
        cons(start, ((range +(start, step)) stop))
  in

[ Higher order function filter ]
letrec filter(p) =
  proc (l)
    if null?(l)
    then emptylist
    else if (p car(l)) then
      cons(car(l), ((filter p) cdr(l)))
      else ((filter p) cdr(l))
  in

[ Modular arithmetic ]
[ Multiplication, integer division and more operations are added ]
let mod =
  proc(x)
    proc(y)
      let q = /(x,y) in
        let a = *(y, q) in
          -(x, a)
  in


[ Is n divisible by b? ]
let dividesq = proc(n) proc(d) zero?(((mod n) d))
  in

[ Prime loop ]
[ Indentation doesn't matter, but I keep mine ML-like ]
let primeq = proc(n)
  if =(n, 1)
    then false
  else
    letrec primeloop(d) =
      if <(n, *(d,d))
      then true
      else if ((dividesq n) d)
           then false
           else (primeloop +(d, 1))
      in
    (primeloop 2)
    in

((filter primeq) ((range 1) 100))
```

## Usage example
```sml
- parse_tree "factorial.prog";
val it =
  Letrec
    ("fact","n",
     If
       (Zerop (Var "n"),Const 1,
        Mult (Var "n",Call (Var "fact",Sub (Var "n",Const 1)))),
     Call (Var "fact",Const 5)) : Expr
- runfile "factorial.prog";
val it = Num 120 : Val
- repf "prime.prog";
Result of evaluation: (2 . (3 . (5 . (7 . (11 . (13 . (17 . (19 . (23 . (29 . (31 . (37 . (41 . (43 . (47 . (53 . (59 . (61 . (67 . (71 . (73 . (79 . (83 . (89 . (97 . ())))))))))))))))))))))))))
val it = () : unit
```
