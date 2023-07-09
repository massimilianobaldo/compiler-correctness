# Correctness of a Compiler

This project consits in implementing and proving the correctness of a compiler for a simple arithmetic expression langugae.

The language is defined as follow:

```
B := true | false

E := n	       |
     add E1 E2 |
     min E1 E2 |
     mul E1 E2 |
     if B then E1 else E2
```

## Structure

These are the files inside this project:

- **Syntax.agda** contains the abstract syntax tree of the language

- **Evaluation.agda** contains the function for evaluate terms of the lanugage

- **Compiler.agda** contains the implementation of the compiler and the function for execute the compiled code.

- **Correctness.agda** conatins the proof that the compiler respect the semantics, i.e evaluating a term E gives the same resutl as compile E and execute the code

There is a file calles **Tests.agda** in which there are implemented some basic test for the functions.

## Resources

- [Martin-Löf's Type Theory](https://www.cse.chalmers.se/~smith/handbook.pdf)

- [An Introduction to Programming and Proving in Agda](https://www.cse.chalmers.se/~peterd/papers/AgdaLectureNotes2018.pdf)

- [Programming in Haskell](https://www.cs.nott.ac.uk/~pszgmh/pih.html)