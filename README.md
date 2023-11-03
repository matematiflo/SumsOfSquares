# Sums of squares

A Lean project that develops the basic theory of sums of squares in rings and fields.

## Contents of the library

- [Definitions and examples](SumSq/Defs.md)
- [Basic properties](SumSq/Ppties.md)

## Installation

You can clone the project [using GitHub Desktop](x-github-client://openRepo/https://github.com/matematiflo/SumsOfSquares) or via the command line

```console
git clone https://github.com/matematiflo/SumsOfSquares.git
```

If you already have [Lean 4](https://lean-lang.org) installed on your machine, make sure download the Mathlib binaries via the command line

```console
lake exe cache get
```

If you need to install Lean, you can go to the [Community website](https://leanprover-community.github.io/get_started.html) and follow the instructions there, depending on your OS.

Alternately, you can also look at the [Lean Manual](https://lean-lang.org/lean4/doc/quickstart.html).

After installing Lean, it is recommended, yo work on this project, to download the Mathlib binaries via the command line `lake exe cache get`.

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
