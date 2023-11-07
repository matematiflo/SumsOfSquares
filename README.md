# Sums of squares

A Lean package that develops the basic theory of sums of squares in rings and fields. Our ultimate goal is to define a function that sends an ordered field to its real closure.

## Libraries

- [Definitions and examples](SumSq/Defs.md)
- [Basic properties](SumSq/Ppties.md)
- Formally real fields

## Installation

You can clone the project using [GitHub Desktop](https://docs.github.com/en/desktop/installing-and-authenticating-to-github-desktop/installing-github-desktop) or via the command line

```bash
git clone https://github.com/matematiflo/SumsOfSquares.git
```

If you already have [Lean 4](https://lean-lang.org) installed on your machine, make sure to download the compiled [Mathlib](https://github.com/leanprover-community/mathlib4) libraries via the command line

```bash
lake exe cache get
```

If you need to install Lean, you can go to the [Lean Community](https://leanprover-community.github.io/get_started.html) website and follow the instructions there, depending on your OS. Alternately, you can also look at the [Lean Manual](https://lean-lang.org/lean4/doc/quickstart.html).

After installing Lean, you will be able to download the compiled Mathlib libraries via the command line `lake exe cache get`, as indicated above.

## Example file

You can run `Example.lean` either with the following command line

```bash
lake env lean Example.lean
```

or by building the project via

```bash
lake build
```

and running the resulting binary file via

```bash
./build/bin/example
```
