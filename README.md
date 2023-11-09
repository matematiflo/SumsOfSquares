# Sums of squares

A Lean package that develops the basic theory of sums of squares in rings and fields. Our ultimate goal is to define a function that sends an ordered field to its real closure.

## Libraries

- [Definitions and examples](SumSq/Defs.md)
- [Basic properties](SumSq/Ppties.md)
- [Cones](SumSq/Cones.md)
- Formally real fields

## Quickstart

You can clone the project using [GitHub Desktop](https://docs.github.com/en/desktop/installing-and-authenticating-to-github-desktop/installing-github-desktop) or via the command line

```bash
git clone https://github.com/matematiflo/SumsOfSquares.git
```

Alternately, just click on the [Code button](https://github.com/matematiflo/SumsOfSquares) of the current repository.

![Code Button](img/Code.png)

If you already have [Lean 4](https://lean-lang.org) installed on your machine, make sure to download the compiled [Mathlib](https://github.com/leanprover-community/mathlib4) libraries via the command line

```bash
lake exe cache get
```

and then build the project by running the command line

```bash
lake build
```

If you need to install Lean, you can go to the [Lean Community](https://leanprover-community.github.io/get_started.html) website and follow the instructions there, depending on your OS. Alternately, you can also look at the [Lean Manual](https://lean-lang.org/lean4/doc/quickstart.html).

After installing Lean, you will be able to run the command line `lake exe cache get` and `lake build` indicated above.

## Example file

You can run `Example.lean` either with the following command line

```bash
lake env lean Example.lean
```

Alternately, if you have already built the project (using `lake build`), you can simply execute the `example` binary file via

```bash
./build/bin/example
```

## Codespaces

If you wish to work on this project online and without installing anything, you can do do by opening a Codespace (GitHub account required). Just click on the button below and wait a few minutes.

[![Open in Codespaces](https://github.com/codespaces/badge.svg)](https://github.com/codespaces/new?skip_quickstart=true&machine=standardLinux32gb&repo=713890550&ref=main&geo=EuropeWest)

It takes a few minutes to set up!

Alternately, you can open a Codespace by clicking on the [Code button](https://github.com/matematiflo/SumsOfSquares) of the current repository.

If you commit any modified file from within your Codespace, the repo will be forked to your GitHub account and your work will be saved there.

You can access the Codespaces that you have created directly from within your GitHub account:

[https://github.com/codespaces](https://github.com/codespaces)
