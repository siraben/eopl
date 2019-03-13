# Haskell Implementations of the languages from EOPL

```haskell
Welcome to the LETREC interpreter. Control-d to exit.
LETREC> letrec fact(n) = if zero?(n) then 1 else *(n, (fact -(n,1))) in (fact 5)
120
```

This project aims to implement the languages found in the textbook
[Essentials of Programming
Languages](https://mitpress.mit.edu/books/essentials-programming-languages),
in Haskell.

## Why?
The textbook implements the languages using Scheme, which is indeed a
very powerful functional programming language.  What about a Haskell
version?  This repository explores that, an intellectual exercise in
implementing various languages, which will later include ideas such as
such as mutable state, exceptions, then object orientation and a
module system, as EOPL does.

## Implementation
### Parser
The parser is implemented with monadic parser combinators.  This is
written from scratch in Haskell.  Expressions are represented as
inductive data types.  Since Haskell is pure, exceptions are
implemented with an `Exceptional` monad.

### Interpreter
The interpreter is very simple.  In its current form it is an
environment-passing interpreter, taking an expression, environment and
returning a `Result Val`, where `Result` is an alias for `Exceptional
Exception`, where `Exceptional` is a type constructor of kind `* ->
*`.  This allows us to still signal errors during evaluation.

## How to use
### Haskell LETREC REPL
Run `make` to build the Haskell REPL for the language `LETREC`.  The
Standard ML reference implementations can be run with SML/NJ, by
typing `use "letrec.sml"` into the SML prompt.

### Standard ML Functions
The most interesting function is probably `repf`, which accepts a
filename, parses it into the AST, runs `eval` over it and then uses
the pretty printer to display the result.  `runfile` reads the
filename, executes it but doesn't convert the final value into a
pretty printed version, which can be useful for debugging purposes.
`parse_tree` accepts a filename and shows the parse tree for that
file.  Due to the way the grammar of the language is specified, you
will find that adding extra parens around expressions can dramatically
change its semantics.  `parse_tree` lets you see those invisible empty
string variable names that may pop up, for instance.

## Program example (prime numbers with lazy streams)
```text
[ Comments are shown with square brackets (which cannot be nested) ]

letrec
streamCar(s)  = car(s)
[ We don't have thunks so pass a dummy value ]
streamCdr(s)  = (cdr(s) 44)
take(n)       = proc(s)
                  if
                    zero?(n)
                  then
                    emptylist
                  else
                    cons((streamCar s),
                         ((take -(n,1)) (streamCdr s)))
[ Some examples of stream operations. ]
repeat(n)     = cons_stream(n, (repeat n))
addStreams(a) = proc(b) cons_stream(+(car(a),car(b)),
                                    ((addStreams (streamCdr a)) (streamCdr b)))
[ Modular arithmetic ]
mod(x) =
  proc(y)
    let q = /(x,y) in
      let a = *(y, q) in
        -(x, a)

[ Logical not ]
not(b) = if b then false else true

[ Is n not divisible by b? ]
ndividesq(d) = proc(n) (not zero?(((mod n) d)))
filterStream(f) = proc(s)
                    if
                      (f car(s))
                    then
                      cons_stream(car(s),
                                  ((filterStream f) (streamCdr s)))
                    else
                      ((filterStream f) (streamCdr s))

[ The Sieve of Eratosthenes ]
sieve(s) = cons_stream(car(s),
                       (sieve ((filterStream (ndividesq car(s)))
                                             (streamCdr s))))

[ Generate integers starting from a number ]
integersFrom(z) = cons_stream(z, (integersFrom +(z,1)))
in

[ Get the first twenty prime numbers ]
((take 20) (sieve (integersFrom 2)))
```

## Usage example
### Standard ML
```sml
- parse_tree "factorial.prog";
val it =
  Letrec
    (["fact"],["n"],
     [If
        (Zerop (Var "n"),Const 1,
         Mult (Var "n",Call (Var "fact",Sub (Var "n",Const 1))))],
     Call (Var "fact",Const 5)) : Expr
- runfile "factorial.prog";
val it = Num 120 : Val
- repf "streams.prog";
Result of evaluation: (2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71)
val it = () : unit
```
