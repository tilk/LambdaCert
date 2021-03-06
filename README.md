# Summary

This project consists of the following parts:

 * A formalized LambdaJS semantics, 
 * A certified LambdaJS interpreter,
 * Proof of soundness and completeness of the LambdaJS interpreter with respect to the semantics,
 * A translation from EcmaScript 5.1 programs to LambdaJS,
 * Proof of correctness of the said translation (work in progress).

The work is based on the [S5 variant of LambdaJS](http://cs.brown.edu/research/plt/dl/s5/).
For various reasons, we use a [slightly modified version](https://github.com/tilk/LambdaCert/wiki/Changes-in-the-core-calculus)
of the calculus.

The [JSCert](http://jscert.org) project is used as the formal specification of EcmaScript.

The initial version of the LambdaJS interpreter was written by [Martin Lorentz](https://progval.net/).

# Usage

## Compiling

```
./get_deps.sh # Slow, you have to compile jscert (and thus Flocq and TLC)
cd LambdaS5
make
```

## Running the interpreter

You can run Javascript code directly:

```
tests/js file.js
```

To print the resulting LambdaJS code instead of executing it, use `-print`:

```
tests/js -print file.js
```

It is also possible to run LambdaJS code directly:

```
tests/js -ljs file.ljs
```

There is also a REPL toplevel:

```
tests/js -top
```

The `tests/js` file is a script. The actual interpreter can be found in
`build/eval.native`; use `-help` to see the available options.

# How it works

## File hierarchy

The Coq files are in `LambdaS5/coq/`. The code is organized as follows:

 * `LjsSyntax.v` - the syntax of LambdaJS.
 * `LjsInterpreter.v` - the interpreter of LambdaJS.
 * `LjsExtraction.v` - interpreter extraction to OCaml.
 * `LjsPrettyRules.v` - pretty-big-step semantics of LambdaJS.
 * `LjsPrettyRulesIndexed.v` - indexed version of the semantics, used for
   proofs by induction on the depth of the derivation. Generated using the
   sed script `make_indexed_rules.sed`.
 * `LjsPrettyRulesIndexedInvert.v` - Coq tactics for efficient inversion
   of the semantics judgment. Generated by `make_fast_inversion.hs`.
 * `LjsCorrectness.v`, `LjsCompleteness.v` - proofs of the equivalence
   between the interpreter and the pretty-big-step semantics.
 * `EjsSyntax.v` - definition of an intermediate language ExprJS between
   LambdaJS and EcmaScript.
 * `EjsFromJs.v`, `EjsToLjs.v` - the translation from EcmaScript to
   LambdaJS, using ExprJS as an intermediate language.
 * `LjsInitEnv.v` - the initial lexical environment and state for
   EcmaScript programs compiled to LambdaJS. Generated by the 
   interpreter.
 * `LjsRulesCorrect*.v` - the proof of correctness of the translation of
   EcmaScript code to LambdaJS.

The initial LambdaJS environment for EcmaScript programs is stored in the file
`LambdaS5/env/es5.env`. It can be exported to Coq using the option `-coq-save`.

The glue files for the interpreter are written in OCaml, they are in 
`LambdaS5/caml/`. A modified version of the original LambdaJS lexer, parser
and pretty-printer is used; they are in `LambdaS5/caml/ljs/`.

The directory `LambdaS5/tests` contains the regression tests for the interpreter;
there are tests for LambdaJS and EcmaScript features.


