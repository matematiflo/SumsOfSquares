# Being a sum of squares

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser.

```lean
import SumSq.Defs
import Mathlib.Algebra.GroupPower.Basic
```

Let `R`be a semiring. In the file [SumSq.Defs](Defs.md), we declared a function `SumSq : List R → R` that computes the sum of squares of the entries of a list:

> SumSq [a, b, c] = a ^ 2 + b ^ 2 + c ^ 2

In the present file, we define a predicate `IsSumSq : R → Prop` that characterizes the elements of `R` that are return values of the function `SumSq`. We then use this to declare sums of squares in `R` as a subtype of `R`.

## Using an inductive predicate

Using a predicate to define sums of squares means defining the notion of *being a sum of squares in `R`* to mean being a term `S : R` such that the proposition `IsSumSq S` has a proof.

```lean
inductive IsSumSq [Semiring R] : R → Prop where
  | zero : IsSumSq (0 : R)
  | add (x S : R) (hS : IsSumSq S) : IsSumSq (x ^ 2 + S)
```

In other words, `0 : R` is a sum of squares, and if `S : R` is a sum of squares and `x : R`, then `x ^ 2 + S` is a sum of squares. We can use this to prove that, for all list `L : List R`, the term `SumSq L : R` is a sum of squares.

```lean
lemma SumSqIsSumSq [Semiring R] (L : List R) : IsSumSq (SumSq L) := by
  induction L with
  | nil =>
    exact IsSumSq.zero
  | cons a l ih =>
    rw [SumSq]
    exact IsSumSq.add a (SumSq l) ih
```

Let us give three simple examples of proofs that a term `S : R` is a sum of squares. Namely, we prove that `0`, `1` and all squares in `R` are sums of squares.

```lean
lemma zeroIsSumSq : IsSumSq 0 := by
  exact IsSumSq.zero

lemma oneIsSumSq : IsSumSq 1 := by
  have aux : 1 = (1 ^ 2 + 0) := by rfl
  rw [aux]
  exact IsSumSq.add 1 0 IsSumSq.zero

lemma aSquareIsSumSq [Semiring R] (x : R) : IsSumSq (x ^ 2) := by
  rw [← add_zero (x ^2)]
  exact IsSumSq.add x 0 IsSumSq.zero
```

For more on this, see [Exercise 1](#exercise-1). And for more on Lemma `SumSqIsSumSq`, see [Exercise 2](#exercise-2).

## Using an existential predicate

We wish to prove that, given a term `S` in a semiring `R`, the following equivalence holds:

> IsSumSq S ↔ (∃ L : List R, SumSq L = S)

We start with the first implication: starting from `S : R` such that `IsSumSq S` has a proof, we want to construct a list `L : List R` such that `SumSq L = S`. Since `IsSumSq S`is defined inductively, we can do this by induction on the proof of the proposition `IsSumSq S`.

```lean
lemma IsSumSqToExistList [Semiring R] (S : R) (hS : IsSumSq S) : (∃ L : List R, SumSq L = S) := by
  induction hS with
  | zero => -- exact ⟨[], rfl⟩
    use []
    rfl
  | add a S' _ ih =>
    rcases ih with ⟨L', hL'⟩
    rw [← hL']
    use (a :: L')
    rfl
```

From this and Lemma `SumSqIsSumSq` proved in [the first section](##using-an-inductive-predicate), we can prove the equivalence that we wanted.

```lean
theorem IsSumSq.Char [Semiring R] (S : R) : IsSumSq S ↔ (∃ L : List R, SumSq L = S) := by
  constructor
  · apply IsSumSqToExistList
  · intro h
    rcases h with ⟨L, hL⟩
    rw [← hL]
    exact SumSqIsSumSq L
```

## As a set

To the predicate `IsSumSq : R → Prop`, there is associated the set `{S : R | IsSumSq S}`, which consists of terms `S : R` such that `IsSumSq S` has a proof. Again, since `IsSumSq S` is defined inductively, we can use induction to prove certain properties of this set. For instance:

> IsSumSq S1 ∧ IsSumSq S2 → IsSumSq (S1 + S2)

In other words, if `R`is a semiring, the set of sums of squares in `R` is closed under addition.

```lean
theorem IsSumSq.Sum [Semiring R] {S1 S2 : R} (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 + S2) := by
  induction h1 with
  | zero =>
    simp
    exact h2
  | add a S hS ih =>
    rw [add_assoc]
    exact IsSumSq.add a (S + S2) ih
```

Likewise, if the semiring `R` is commutative, the set `{S : R | IsSumSq S}` is closed under multiplication. As we shall see, the assumption that `R` is commutative is used in our proof when applying [`mul_pow`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupPower/Basic.html#mul_pow). We make this apparent via a separate lemma.

```lean
lemma IsSumSq.ProdBySumSq [CommSemiring R] (S : R) (h : IsSumSq S) (x : R) : IsSumSq (x ^2 * S) := by
  induction h with
  | zero =>
    rw [mul_zero]
    exact IsSumSq.zero
  |add a s _ ih =>
    rw [mul_add, ← mul_pow x a 2]
    exact IsSumSq.add (x * a) (x ^ 2 * s) ih
```

We can now prove that the set of sums of squares in a commutative semiring `R` is closed under multiplication:

> IsSumSq S1 ∧ IsSumSq S2 → IsSumSq (S1 * S2)

```lean
theorem IsSumSq.Prod [CommSemiring R] {S1 S2 : R} (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 * S2) := by
  induction h1 with
  | zero =>
    rw [zero_mul]
    exact IsSumSq.zero
  | add a S hS ih =>
    rw [add_mul]
    apply IsSumSq.Sum _ _
    · exact IsSumSq.ProdBySumSq S2 h2 _
    · exact ih
```

## As a subtype

TO COMPLETE

ALSO: explain the proofs and add a link pointing to the definition of a set in mathlib.

## Exercises

The solutions to these exercises are available in the file [SumSq.Solutions](Solutions.md).

### Exercise 1

Let `R` be a semiring and let `S` be a term in `R`. Prove that Proposition `IsSumSq S` is equivalent to Proposition `IsSumSq' S`, where `IsSumSq'` is the predicate defined inductively as follows:

```lean
inductive IsSumSq' [Semiring R] : R → Prop where
  | sq (x : R): IsSumSq (x ^ 2 : R)
  | add (S1 S2 : R) (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 + S2)
```

Note that this definition may be more intuitive than the one we gave in [the first section](#using-an-inductive-predicate). But it might be less convenient to work with. Indeed, when proving a statement by induction on the proof of `IsSumSq' S`, then in the first case, we would have to prove it not only for `S = 0`, but in all cases `S = x ^ 2` for some `x : R`.

### Exercise 2

Let Let `R` be a semiring and let `S` be a term in `R`. Write a proof of the implication

> (∃ L : List R, SumSq L = S) → IsSumSq S

and notice that having an existential quantifier in the assumption is not very convenient. Instead, use Lemma `SumSqIsSumSq` and the second implication of the equivalence `IsSumSq.Char` to prove the result. You can then see that the approach there is to first prove `IsSumSq (SumSq L)` and from this deduce a proof of the implication. A formalisation of this is statement is suggested in [Exercise 3](#exercise-3).

### Exercise 3

Let `S T` be types. Let `P : T → Prop` be a predicate on `T` and let `f : S → T` be a function from `S` to `T`. Assume that the proposition `∀ x : S, P (f x)` has a proof and that the proposition `∀ y : T, ∃ x : S, y = f x` has a proof. Show that the proposition `∀ y : T, P y` has a proof.

```lean
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
```
