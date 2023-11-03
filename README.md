# Sums of squares

A Lean project that develops the basic theory of sums of squares in rings and fields.

## Contents of the library

- [Definitions and examples](SumSq/Defs.md)
- [Basic properties](SumSq/Ppties.md)

## Installation

You can clone the project using GitHub Desktop or via

```console
git clone https://github.com/matematiflo/SumsOfSquares.git
```

Then, if you already have [Lean 4](https://lean-lang.org) installed on your machine, just run the command line

```console
lake exe cache get
```

to download the Mathlib binaries.

If you need to install Lean, you can go to the [Community website](https://leanprover-community.github.io/get_started.html) and follow the instructions there, depending on your OS.

Alternately, you can also look at the [Lean Manual](https://lean-lang.org/lean4/doc/quickstart.html).

## Example file

You can run `Example.lean` either with the following command line

```console
lake env lean Example.lean
```

or by building the project

```console
lake build
```

and running the resulting binary file

```console
./build/bin/example
```
