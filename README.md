# Sums of squares

A Lean package that develops the basic theory of sums of squares in rings and fields. Our ultimate goal is to define a function that sends an ordered field to its real closure.

## Libraries

- [Definitions and examples](Defs.md)
- [Basic properties for lists](List.md)
- [The type of sums of squares](Basic.md)
- [Precones and cones](Cones.md)
- Formally real fields

## Quickstart

### Clone the repository

You can clone the repo using [GitHub Desktop](https://docs.github.com/en/desktop/installing-and-authenticating-to-github-desktop/installing-github-desktop) or via the command line

```bash
git clone https://github.com/matematiflo/SumsOfSquares.git
```

Alternately, just click on the Code button of the current repository.

[![Code Button](img/Code_small.png)](https://github.com/matematiflo/SumsOfSquares)

### If you have Lean 4

If you already have [Lean 4](https://lean-lang.org) installed on your machine, just download the compiled [Mathlib files](https://github.com/leanprover-community/mathlib4) via the command line

```bash
lake exe cache get
```

and then build the project by running the command line

```bash
lake build
```

### If you do not have Lean 4

If you need to install Lean, you can go to the [Lean Community portal](https://leanprover-community.github.io/get_started.html) and follow the instructions there, depending on your OS. Alternately, you can also look at the [Lean Manual](https://lean-lang.org/lean4/doc/quickstart.html) or at [this repo](https://github.com/matematiflo/LeanPackage).

After installing Lean, you will be able to run the command lines `lake exe cache get` and `lake build` indicated above.

### Troubleshooting

If either `lake exe cache get` or `lake build` are not recongnized, try

```bash
curl https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
```

and then

```bash
lake update
```

before trying `lake exe cache get` and `lake build` again.

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

If you wish to work on this project online and without installing anything, you can do so by opening a Codespace. Just follow the link below and click on `Create new codespace` (**GitHub account required**).

[![Open in Codespaces](https://github.com/codespaces/badge.svg)](https://github.com/codespaces/new/matematiflo/SumsOfSquares)
  
Alternately, you can open a Codespace by clicking on the [Code button](https://github.com/matematiflo/LeanPackage) of the current repository (possibly slower, though).

If you commit any modified file from within your Codespace, the repo will be forked to your GitHub account and your work will be saved there.

To leave a Codespace, it is recommended that you stop it before closing the browser window:

1. Click on your Codespace name at the bottom-left of the VS Code interface.
2. Choose `Stop current Codespace` from the list of options.
3. Wait until the Codespace has stopped to close your browser tab.

To access a Codespace that you have previously created, just go to

> [https://github.com/codespaces](https://github.com/codespaces)

or launch them directly from the Code button of the relevant repository (no setup required this time!).
