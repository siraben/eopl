# Standard ML Implementations of the languages from EOPL
_Note: The language might be changed to Haskell in the future._

This project aims to implement the languages found in the textbook
[Essentials of Programming
Languages](https://mitpress.mit.edu/books/essentials-programming-languages).

## Why?
It's somewhat awkward to fit in a datatype language into Scheme, which
lacks static typing and pattern matching.  Why not use Standard ML,
which allows us to use the powerful Hindley-Milner type system to do
the heavy lifting?

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
[ Even though our language has eager evaluation, by using closures we can
  simulate laziness. ]
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
repeat(n)     = cons(n, proc(delay) (repeat n))
addStreams(a) = proc(b) cons(+(car(a),car(b)),
                             proc(delay)
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
                      cons(car(s),
                           proc(delay) ((filterStream f) (streamCdr s)))
                    else
                      ((filterStream f) (streamCdr s))

[ The Sieve of Eratosthenes ]
sieve(s) = cons(car(s),
                proc(delay)
                  (sieve ((filterStream (ndividesq car(s)))
                          (streamCdr s))))

[ Generate integers starting from a number ]
integersFrom(z) = cons(z, proc(delay) (integersFrom +(z,1)))
in

[ Get the first hundred prime numbers ]
((take 100) (sieve (integersFrom 2)))
```

## Usage example
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
Result of evaluation: (2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71 73 79 83 89 97 101 103 107 109 113 127 131 137 139 149 151 157 163 167 173 179 181 191 193 197 199 211 223 227 229 233 239 241 251 257 263 269 271 277 281 283 293 307 311 313 317 331 337 347 349 353 359 367 373 379 383 389 397 401 409 419 421 431 433 439 443 449 457 461 463 467 479 487 491 499 503 509 521 523 541)
val it = () : unit
```
