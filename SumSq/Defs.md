# Sums of squares - Definitions and examples

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser.

```lean
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.List.BigOperators.Basic
import Mathlib.Data.Rat.Defs
```

> **Convention.** In proofs by induction, the notation `ih` is meant to signify *induction hypothesis*.

## Definition by pattern matching

Let `R` be a type. As soon as `R` is endowed with an addition function, a zero and a square function, we can define sums of squares as a function `SumSq` going from `List R` to `R`. However, in what follows, we will restrict to the case when `R` is a `Semiring`.

Recall that `List R` is the type defined inductively and recursively by

```lean
inductive List (R : Type u) where
  | nil : List R -- the empty list
  | cons (a : R) (l : List R) : List R -- the list constructed from a term (a : R) and an already constructed list (l : List R).
```

In Lean, the empty list can be denoted by `[]` and the list `cons a l` can be denoted by `a :: l`.

Sums of squares can thus be defined by pattern matching, with respect to terms of type `List R`. This means by giving the return value of the function in each of the two possible cases `[]` and `a :: l`.

```lean
def SumSq {R : Type} [Semiring R] : (List R → R)
  | [] => 0
  | a :: l => a ^ 2 + SumSq l
```

Alternate syntax for pattern matching:

```lean
def SumSq {R : Type} [Semiring R] (L : List R) : R :=
  match L with
  | [] => 0
  | a :: l => a ^ 2 + SumSq l
```

The command `#check @SumSq` will return the type of the function `SumSq`. The complete definition can be viewed using the command `#print SumSq`.

```lean
#check @SumSq -- @SumSq : {R : Type} → [inst : Semiring R] → List R → R
#print SumSq
```

In the declaration of the function `SumSq`, one can dispense with the (implicit) variable `{R : Type}` and simply write the following:

```lean
def SumSq [Semiring R] : List R → R
  | [] => 0
  | a :: l => a ^ 2 + SumSq l
```

The `#check @SumSq` command then returns

```lean
@SumSq : {R : Type u_1} → [inst : Semiring R] → List R → R
```

Either way, the definition of the function `SumSq` is computable. In particular, simple equalities can be proved using the `rfl` tactic, as we check below.

In these examples, note that Lean is capable of recognizing that `[1, -2, 3]` is a list of integers, i.e. a term of type `List ℤ`.

```lean
#eval SumSq [1, -2, 3]  -- 14
#eval SumSq ([] : List ℕ)  -- 0
#eval SumSq ([1, -2, 3/4] : List ℚ)  -- (89 / 16 : ℚ)

example : SumSq [1, -2, 3] = 14 := by rfl  -- the two terms are definitionally equal
```

If `L1` and `L2` are lists, there is a concatenated list `L1 ++ L2`, and `SumSq (L1 ++ L2)` can be computed directly.

```lean
#eval SumSq ([1, -2, 3] ++ [1, 1, -2, 3])  -- 29
example : SumSq ([1, -2, 3] ++ (0 :: [1, -2, 3])) = 28 := by rfl  -- the two terms are definitionally equal

#eval SumSq (0 :: [1, -2, 3])  -- 14
#eval SumSq (1 :: [1, -2, 3])  -- 15
```

We will later prove a theorem that says the following:

> `∀ L1 L2 : List R, SumSq (L1 ++ L2) = SumSq L1 + SumSq L2`

## Definition using the `sum` and `square` functions

`SumSq L` can also be computed by squaring the entries of the list and summing the resulting list:

> `[1, -2, 3] => [1 ^ 2, (-2) ^ 2, 3 ^ 2] => 1 ^ 2 + (-2) ^ 2 + 3 ^ 2`

The first function is `L => (L.map (. ^ 2))` and the second function is `L => L.sum`. They can be composed as follows.

```lean
def SumSq2 [Semiring R] (L : List R) : R := (L.map (. ^ 2)).sum
```

As for `SumSq`, this is a computable definition.

```lean
#eval SumSq2 [1, -2, 3] -- 14
```

We now *prove* that the two definitions agree. This means that we define a function that sends a list `L` to a proof that `SumSq2 L = SumSq L`.

```lean
theorem squaring_and_summing [Semiring R] (L : List R) : SumSq2 L = SumSq L := by
  induction L with -- we prove the result by induction on the list L (the type `List R` is an inductive type)
  | nil => rfl -- case when L is the empty list, the two terms are definitionally equal
  | cons a l ih => -- case when L = (a :: l), the two terms reduce to equal ones after some simplifications
    dsimp [SumSq2, SumSq] -- we simplify using the definitions of SumSq2 and SumSq
    dsimp [SumSq2] at ih  -- we simplify in the induction hypothesis, using the definition of SumSq2
    simp [ih]  -- we use the induction hypothesis
```

## Tail-recursive definition

For greater efficiency in computations, we can also give a tail-recursive definition.

As usual for tail-recursive definitions, we start by defining an auxiliary function.

```lean
def SumSqAux [Semiring R] : R → List R → R
  | SoFar, [] => SoFar
  | SoFar, (a :: l) => SumSqAux (SoFar + a ^ 2) l
```

The following property holds by definition. It will be used in the proof of the equality `SumSqTR L = SumSq L`.

```lean
theorem SumSqAuxZero [Semiring R] (L : List R) : SumSqAux 0 L = SumSqAux (SumSq []) L := by rfl
```

The tail-recursive version of the `SumSq` function is then defined as follows.

```lean
def SumSqTR [Semiring R] : List R → R
  | L => SumSqAux 0 L
```

This is computable and behaves as expected.

```lean
#eval SumSqTR [1, -2, 3] -- 14
```

We now want to prove that the two definitions agree, i.e. that

> `∀ L : List R, SumSqTR L = SumSq L`

The idea behind the proof is that, when `S = SumSq L'`, the term  `SumSqAux S L` can be computed in terms of the original function `SumSq`. This idea is formalised in the next result.

```lean
theorem SumSqAuxWithSumSq [Semiring R] (L1 : List R) : ∀ L2 : List R, SumSqAux (SumSq L2) L1  = SumSq L2 + SumSq L1 := by
  induction L1 with  -- we prove the result by induction on L1
  | nil => simp [SumSqAux, SumSq]  -- the nil case follows from the definitions of the functions involved
  | cons a l1 ih =>  -- note that the induction hypothesis is for l fixed but for arbitrary L' : List R
    intro L  -- we introduce a new variable L
    dsimp [SumSq, SumSqAux]  -- we simplify, using the definitions of SumSq and SumSqAux
    rw [add_comm _ (a ^2), ← SumSq]  -- we use the commutativity of addition, then compute backwards using the definition of SumSq
    rw [ih (a :: L)]  -- we apply the induction hypothesis with L' = (a :: L'')
    rw [SumSq, add_comm (a ^ 2) _, add_assoc]  -- we compute to finish the proof
```

With the help of `SumSqAuxWithSumSq`, we can now prove that the tail-recursive version of the sum-of-squares function indeed returns the same value as the original function.

We start with an easy lemma, which is of more general interest.

```lean
lemma SumSqAuxEmptyList [Semiring R] (L : List R) : SumSqAux (SumSq []) L= SumSqAux (SumSq L) [] := by
  simp [SumSqAuxWithSumSq]  -- both terms of the equation can be modified, using the function SumSqAuxGen to get rid of SumSqAux everywhere (on the left, the function SumSqAuxGen is applied to the lists L and [], and on the right it is applied to [] and L)
  simp [SumSq]  -- we finish the proof by computing, using the fact that SumSq [] = 0 (by definition)

theorem def_TR_ok [Semiring R] (L : List R) : SumSqTR L = SumSq L := by
  simp [SumSqTR, SumSqAuxZero, SumSqAuxEmptyList, SumSqAux]  -- the proof is by direct computation
```
