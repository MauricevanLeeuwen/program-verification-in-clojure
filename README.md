# A Program Verifier in Clojure

This project implements a interpreter to perform program verification on a non-existing LISP style language.
Programs written in this language are transformed into SMT2 programs that can be checked using Z3. 

## Language features

- If-then-else via `(ite condition then-expr else-expr)`
- Function requires and ensures via `(fn [] {:requires expr :ensures expr} & body)`
- While loops with invariants and decreases via `(while condition {} & body)`
- A lexical scope with mutation via `(set! variable value)`
- Asserts via `(assert expr)`
- Expressions that support many arithmetic and logic operations

## Dependencies
```
apt-get install z3

```
## Usage
The quickest way to run the program is to run the .jar file directly:
```
> java -jar dist/traffic.jar examples/seb.clj out.smt2

```
The resulting smt2 file can then be verified using z3:
```
> z3 out.smt2
```

Or instead pipe the result directly into z3:
```
> java -jar dist/traffic.jar examples/seb.clj out.smt2 | z3 -in


```
If you have a working installation of `clojure` and `lein` you can rebuild the JAR from source:
```
lein uberjar
```

## Examples
The code repository contains a number of examples to test properties of the verifier:

- `seb.clj` is an example presented in class to test the proper working of the verifier. The program contains four `(mul 1 _)` statements, changing any of these statements into `(mul -1 _)` should (and will) result in a failed assertion.
- `simple.clj` is an example program that checks proper branching of an `ite` statement.

## Implementation
- `src/smt.clj` helper functions to construct SMT commands
- `src/env.clj` for managing the lexical scope
- `src/core.clj` here `eval-expr` contains all logic for transforming `fn`, `ite`, `while`, `set!`, and expressions to SMT commands.

# Contributors
- Maurice van Leeuwen





