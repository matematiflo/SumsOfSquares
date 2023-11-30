/-
# Sums of squares - Solutions to the exercises

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser.
-/

import SumSq.Defs

/-!
## [SumSq.List](List.md#exercises)

### [List.1](List.md#exercise-1)

Modify the syntax of the `induction` tactic in [`SumSqPermut`](List.md#permuted-lists) to make it look more similar to that of [`SumSqAppend`](List.md#appended-lists). This means: in `SumSqPermut`, replace `induction H` by `induction H with` and make the proof syntactically correct after that (start by changing `⬝ case nil` to `| nil`).
-/

/-!
### [List.2](List.md#exercise-2)

Let `R` be a type with decidable equality. Let `a` be a term of type `R` and let `L` be a term of type `List R`. Prove that, if `a ∈ L`, then the list `a :: L.erase a` is a permutation of `L` (we have used this standard result [here](List.md#erasing-an-entry)).
-/

/-!
### [List.3](List.md#exercise-3)

Prove that the statement of [`theorem SumSqSmul2`](List.md#more-computations) is indeed equivalent to the statement of [`theorem SumSqSmul`](List.md#multiplication-by-a-scalar).
-/

/-!
## [SumSq.Basic](Basic.md#exercises)

### [Basic.1](Basic.md#exercise-1)

Let `R` be a semiring and let `S` be a term in `R`. Prove that Proposition `IsSumSq S` is equivalent to Proposition `IsSumSq' S`, where `IsSumSq'` is the predicate defined inductively as follows:

```lean
inductive IsSumSq' [Semiring R] : R → Prop :=
  | sq (x : R): IsSumSq (x ^ 2 : R)
  | add (S1 S2 : R) (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 + S2)
```
-/

/-!
### [Basic.2](Basic.md#exercise-2)

Let Let `R` be a semiring and let `S` be a term in `R`. Write a (direct) proof of the implication

> (∃ L : List R, SumSq L = S) → IsSumSq S

and ask yourself whether having an existential quantifier in the assumption makes things complicated. Try using instead Lemma `SumSqListIsSumSq` and the second implication of the equivalence `IsSumSq.Char` from [SumSq.Basic](Basic.md#using-an-inductive-predicate) to prove the result.
-/

/-!
### [Basic.3](Basic.md#exercise-3)

Let `S T` be types. Let `P : T → Prop` be a predicate on `T` and let `f : S → T` be a function from `S` to `T`. Assume that the proposition `∀ x : S, P (f x)` has a proof and that the proposition `∀ y : T, ∃ x : S, y = f x` has a proof. Show that the proposition `∀ y : T, P y` has a proof.

Examples of formalisations for this result are provided below.
-/

example {S T : Type} (P : T → Prop) (f : S → T) (hPf : (∀ x : S, P (f x))) (y : T) : (∃ x : S, y = f x) → P y := by
  intro hy
  rcases hy with ⟨x, hx⟩
  rw [hx]
  apply hPf

example {S T : Type} (P : T → Prop) (f : S → T) (hPf : (∀ x : S, P (f x))) (h : ∀ y : T, ∃ x : S, y = f x) : ∀ y : T, P y := by
  intro y
  specialize h y
  rcases h with ⟨x, hx⟩
  rw [hx]
  apply hPf
