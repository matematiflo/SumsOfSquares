# Sums of squares - Definitions and examples

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser

```lean
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.List.BigOperators.Basic
```

We introduce sums of squares and prove some of their basic properties.

The basic setup is that of a general semiring `R`. For example, we can consider sums of squares of natural numbers (`R = ℕ`).

For some results, we specialize to rings or fields.

> **Convention.** In proofs by induction, the notation `ih` is meant to signify *induction hypothesis*.

## Definition by pattern matching

Let `R` be a type. As soon as `R` is endowed with an addition function and a square function, we can define sums of squares as a function `SumSq` going from `List R` to `R`. However, in what follows, we will restrict to the case when `R` is a semiring.

Recall that `List R` is the type defined inductively and recursively by

```lean
inductive List (R : Type u) where
  | nil : List R -- the empty list
  | cons (a : R) (l : List R) : List R -- the list constructed from a term `a : R` and an already constructed list `l : List R`.
```

In Lean, the empty list can be denoted by `[]` and the list `cons a l` can be denoted by `a :: l`.

Sums of squares are then defined by pattern matching, with respect to terms of type `List R`. This means by giving the value of the function in each of the two possible cases `[]` and `a :: l`.

We work in a fixed universe `u` (this can be ignored).

```lean
def SumSq [Semiring R] : List R → R
  | [] => 0
  | a :: l => a ^ 2 + SumSq l
```

The command `#check @SumSq` will return the type of the function `SumSq`. The complete definition can be viewed using the command `#print SumSq`.

```lean
#check @SumSq -- @SumSq : {R : Type u_1} → [inst : Semiring R] → List R → R
#print SumSq
```

If we do not fix a universe, we can define the function `SumSq` simply as

```lean
def SumSq [Semiring R] : List R → R
  | [] => 0
  | a :: l => a ^ 2 + SumSq l
```

The `#check @SumSq` command then returns

```lean
@SumSq : {R : Type} → [inst : Semiring R] → List R → R
```

Either way, the definition of the function `SumSq` is computable. In particular, simple equalities can be proved using `rfl`, as we check below.

In these examples, note that Lean is capable of recognizing that `[1, -2, 3]` is a list of integers, i.e. a term of type `List ℤ`.

```lean
#eval SumSq [1, -2, 3] -- 14
#eval SumSq ([] : List ℕ) -- 0

example : SumSq [1, -2, 3] = 14 := rfl -- the two terms are definitionally equal

#eval SumSq (0 :: [1, -2, 3]) -- 14
#eval SumSq (1 :: [1, -2, 3]) -- 15
```

If `L1` and `L2` are lists, there is a concatenated list `L1 ++ L2`, and `SumSq (L1 ++ L2)` can be computed directly.

```lean
#eval SumSq ([1, -2, 3] ++ [1, 1, -2, 3]) -- 29

example : SumSq ([1, -2, 3] ++ (0 :: [1, -2, 3])) = 28 := rfl
```

We will prove later a theorem that says the following:

```lean
∀ L1 L2 : List R, SumSq (L1 ++ L2) = SumSq L1 + SumSq L2
```

## Definition using the `sum` and `square` functions

`SumSq L` can also be computed by squaring the members of the list and summing the resulting list, i.e. as the function that sends a list `L : List R` to `(L.map (. ^ 2)).sum`.

```lean
def SumSq2 [Semiring R] (L : List R) : R := (L.map (. ^ 2)).sum
```

As for `SumSq`, this is a computable definition.

```lean
#eval SumSq2 [1, -2, 3] -- 14
```

We now prove that the two definitions agree, i.e. we define a function that sends a list `L` to a proof that `SumSq2 L = SumSq L`.

```lean
theorem squaring_and_summing [Semiring R] (L : List R) : SumSq2 L = SumSq L := by
  induction L with -- we prove the result by induction on the list L (the type `List R` is an inductive type)
  | nil => rfl -- case when L is the empty list, the two terms are definitionally equal
  | cons a l ih => -- case when L = (a :: l), the two terms reduce to equal ones after some simplifications
    dsimp [SumSq2, SumSq]
    dsimp [SumSq2] at ih
    simp [ih]
```

## Tail-recursive definition

For greater efficiency in computations, we can also give a tail-recursive definition.

As usual for tail-recursive definitions, we start by defining an auxiliary function.

```lean
def SumSqAux [Semiring R] : R → List R → R
  | SoFar, [] => SoFar
  | SoFar, (a :: l) => SumSqAux (SoFar + a ^ 2) l
```

The tail-recursive version of the `SumSq` function is then defined as follows.

```lean
def SumSqTR {R : Type} [Semiring R] : List R → R
  | L => SumSqAux 0 L
```

This is computable and behaves as expected.

```lean
#eval SumSqTR [1, -2, 3] -- 14
```

We now want to prove that the two definitions agree, i.e. that

```lean
∀ L : List R, SumSqTR L = SumSq L
```

First, we need to relate the original function `SumSq` to the auxiliary function `SumSqAux`, used to define the tail-recursove version `SumSqTR`.

The point is to show how to compute `SumSqAux S L` in the case when `S = SumSq L'`. Evidently, this is also likely to be useful in more general situations later on.

```lean
theorem SumSqAuxGen [Semiring R] (L : List R) : ∀ L' : List R, SumSqAux (SumSq L') L  = SumSq L' + SumSq L := by
  induction L with
  | nil => simp [SumSqAux, SumSq]
  | cons a l ih =>
    intro L''
    simp [SumSqAux, SumSq]
    simp [SumSqAux, add_comm _ (a ^2)]
    rw [← SumSq, ih (a :: L'')]
    simp [SumSq, add_comm (a ^ 2) _, add_assoc]
```

With the help of `SumSqAuxWithSumSqList`, we can now prove that the tail-recursive version of the sum-of-squares function indeed returns the same value as the original function.

```lean
theorem TR_def_ok [Semiring R] (L : List R) : SumSq L = SumSqTR L := by
  simp [SumSq, SumSqTR, SumSqAux]
  have aux := SumSqAuxGen L []
  simp [SumSq] at aux
  exact aux.symm
```
