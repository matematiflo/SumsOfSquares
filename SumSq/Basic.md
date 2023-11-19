# The type of sums of squares

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser.

```lean
import SumSq.Defs
import Mathlib.Algebra.GroupPower.Basic
```

Let `R`be a semiring. In the file [SumSq.Defs](Defs.md), we declared a function `SumSq : List R → R` that computes the sum of squares of the entries of a list:

> SumSq [a, b, c] = a ^ 2 + b ^ 2 + c ^ 2

In the present file, we declare a predicate `IsSumSq : R → Prop` that characterizes the elements of `R` that are return values of the function `SumSq`. We then discuss how to use such a predicate to declare sums of squares in `R` either as a subset or as a subtype of `R`.

## As an inductive predicate

Using a predicate on `R` (i.e. a function `IsSumSq : R → Prop`) to define sums of squares in `R` means the following: a term `S : R` will be called a sum of squares if the proposition `IsSumSq S` has a proof.

Below, the predicate `IsSumSq` is defined inductively, but it could be defined [existentially](#as-an-existential-predicate).

```lean
inductive IsSumSq {R : Type} [Semiring R] : R → Prop :=
  | zero : IsSumSq (0 : R)
  | add (x S : R) (hS : IsSumSq S) : IsSumSq (x ^ 2 + S)
```

Since `IsSumSq` is declared as an inductive type, it automatically generates a recursion principle.accesible via `IsSumSq.rec`. This means that if we want to prove a result for all sums of squares in a semiring `R'`, it suffices to prove it for `0 : R'` and to prove it for all terms of the form `x ^ 2 + S` under the assumption that the term `S` is a sum of squares in `R'`, for which the result has already been proved.

```lean
variable {R' : Type} [Semiring R']
#check @IsSumSq.rec R' _
```

By definition of `IsSumSq`, the term `0 : R` is a sum of squares, and if `S : R` is a sum of squares and `x : R`, then `x ^ 2 + S` is a sum of squares. We can use this to prove that, for all list `L : List R`, the term `SumSq L : R` is a sum of squares.

```lean
lemma SumSqListIsSumSq [Semiring R] (L : List R) : IsSumSq (SumSq L) := by
  induction L with
  | nil =>
    exact IsSumSq.zero
  | cons a l ih =>
    rw [SumSq]
    exact IsSumSq.add a (SumSq l) ih
```

Let us give three simple examples of proofs that a term `S : R` is a sum of squares. Namely, we prove that `0 : R`, `1 : R` and all squares in `R` are sums of squares.

```lean
lemma zeroIsSumSq [Semiring R] : IsSumSq (0 : R) := by
  exact IsSumSq.zero

lemma oneIsSumSq [Semiring R] : IsSumSq (1 : R) := by
  have aux : (1 : R) = (1 ^ 2 + 0) := by simp
  rw [aux]
  exact IsSumSq.add 1 0 IsSumSq.zero

lemma SquareIsSumSq [Semiring R] (x : R) : IsSumSq (x ^ 2) := by
  rw [← add_zero (x ^2)]
  exact IsSumSq.add x 0 IsSumSq.zero
```

For more on this, see [Exercise 1](#exercise-1). And for more on Lemma `SumSqListIsSumSq`, see [Exercise 2](#exercise-2).

## As an existential predicate

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

From this and Lemma `SumSqListIsSumSq` proved in [the first section](##using-an-inductive-predicate), we can prove the equivalence that we wanted.

```lean
theorem IsSumSq.Char [Semiring R] (S : R) : IsSumSq S ↔ (∃ L : List R, SumSq L = S) := by
  constructor
  · apply IsSumSqToExistList
  · intro h
    rcases h with ⟨L, hL⟩
    rw [← hL]
    exact SumSqListIsSumSq L
```

## As a set

To the predicate `IsSumSq : R → Prop`, there is associated the [set](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Set.html) `{S : R | IsSumSq S}`, which consists of terms `S : R` such that `IsSumSq S` has a proof. Since `IsSumSq S` is defined inductively, we can use induction to prove certain properties of this set, which we first write without using set-theoretic notation. For instance, to say that set of sums of squares in a semiring `R` is closed under addition, we write:

> IsSumSq S1 ∧ IsSumSq S2 → IsSumSq (S1 + S2)

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

-- If one wants to use set-theoretic notation instead of predicate notation:
-- (also check below to see what works when IsSumSq is declared to be of type Set R)

def SumSqSet (R : Type) [Semiring R] : Set R := {a : R | IsSumSq a}

-- Obs: SumSqSet could also be defined inductively

#check SumSqSet ℤ
#check (0: ℤ) ∈ SumSqSet ℤ

theorem SumSqSetContainsZero {R : Type} [Semiring R] : (0 ∈ SumSqSet R) := by
  dsimp [SumSqSet]
  change IsSumSq 0
  exact zeroIsSumSq

-- etc (rewrite the theorems above in set-theoretic notation)
```

## As a subtype

TO COMPLETE

ALSO: explain the proofs!

```lean
structure Cone' (R : Type) [Ring R] :=
  P : Set R  -- I guess here it could also be a sub-type or a predicate? Would it just change the way the axioms are written? (no ∈)
  zero : 0 ∈ P
  add : ∀ (x y : R), x ∈ P ∧ y ∈ P → x + y ∈ P
  -- etc

#check @Cone'

def test [Ring R] (P : Cone' R) : P = P := rfl

class Cone (R : Type) [Ring R] : Type :=
  P : Set R   -- I guess here it could also be a sub-type or a predicate? Would it just change the way the axioms are written? (no ∈)
  zero : 0 ∈ P
  add : ∀ (x y : R), x ∈ P ∧ y ∈ P → x + y ∈ P
  -- etc

#check @Cone

def ConeRefl [Ring R] [P : Cone R] : P = P := rfl

-- If I want to prove that the sum of squares is a cone, is it better with structure or with class?

variable (A : Type) [Ring A]

#check IsSumSq

def SumSqCone (R : Type) [Ring R] : Type := { a : R // IsSumSq a}

#check SumSqCone

#check (⟨(0 : ℤ), IsSumSq.zero⟩ : SumSqCone ℤ)

-- #check (0 : ℤ) ∈ IsSumSq -- !!! WORKS IF IsSumSq IS DECLARED AS TYPE Set R !!!  -- i.e. SumSqCone could be defined inductively like that (in Section #as-a-set)

-- #check (0 : ℤ) ∈ (SumSqCone ℤ) -- voici ce que l'on voudrait? bof... IsSumSq (0 : ℤ) seems very good... (see below)

#check IsSumSq (0 : ℤ) -- semble être le plus simple!

inductive IsSumSq' (R : Type) [Semiring R] : Set R :=
  | zero : IsSumSq' R (0 : R)
  | add (x S : R) (hS : IsSumSq' R S) : IsSumSq' R (x ^ 2 + S)

def SumSqCone' (R : Type) [Ring R] : Type := Subtype (IsSumSq' R)  -- turn this into an exercise...

#check (0 : ℤ) ∈ IsSumSq' ℤ  -- does not read very naturally (not like (0 : ℤ) ∈ (SumSqCone' ℤ))
```

## Exercises

The solutions to these exercises are available in the file [SumSq.Solutions](Solutions.md).

### Exercise 1

Let `R` be a semiring and let `S` be a term in `R`. Prove that Proposition `IsSumSq S` is equivalent to Proposition `IsSumSq' S`, where `IsSumSq'` is the predicate defined inductively as follows:

```lean
inductive IsSumSq' [Semiring R] : R → Prop :=
  | sq (x : R): IsSumSq (x ^ 2 : R)
  | add (S1 S2 : R) (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 + S2)
```

Note that this definition may be more intuitive than the one we gave in [the first section](#using-an-inductive-predicate). But it might be less convenient to work with. Indeed, when proving a statement by induction on the proof of `IsSumSq' S`, then in the first case, we would have to prove it not only for `S = 0`, but in all cases `S = x ^ 2` for some `x : R`.

### Exercise 2

Let Let `R` be a semiring and let `S` be a term in `R`. Write a (direct) proof of the implication

> (∃ L : List R, SumSq L = S) → IsSumSq S

and ask yourself whether having an existential quantifier in the assumption makes things complicated. Try using instead Lemma `SumSqListIsSumSq` and the second implication of the equivalence `IsSumSq.Char` to prove the result. You can then see that the approach there is to first prove `IsSumSq (SumSq L)` and from this deduce a proof of the implication. A formalisation of this is statement is suggested in [Exercise 3](#exercise-3).

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
