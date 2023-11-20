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

## Using an inductive predicate

Using a predicate on `R` (i.e. a function `IsSumSq : R → Prop`) to characterize sums of squares in `R` means the following: a term `S : R` will be called a sum of squares if the proposition `IsSumSq S` has a proof.

Below, the predicate `IsSumSq` is defined inductively, but later we will show that we can also define it [existentially](#using-an-existential-predicate).

```lean
inductive IsSumSq {R : Type} [Semiring R] : R → Prop :=
  | zero : IsSumSq (0 : R)
  | add (x S : R) (hS : IsSumSq S) : IsSumSq (x ^ 2 + S)
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

Let us give three more examples of simple proofs that a term `S : R` is a sum of squares. Namely, we prove that `0 : R`, `1 : R` and all squares in `R` are sums of squares.

For more on this, see [Exercise 1](#exercise-1). And for more on Lemma `SumSqListIsSumSq`, see [Exercise 2](#exercise-2).

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

Based on its declaration, the type `IsSumSq` behaves like a `Prop`-valued function on `R`. The only subtlety is that the variable `R : Type` is implicit, and the fact that `R` is a semiring is implemented using a class instance (which we could name `hR : Semiring R` if we wanted to).

For instance, `IsSumSq ℤ 0` is the formalized version of the statement `0 is a sum of squares in ℤ`.

```lean
#check @IsSumSq  -- @IsSumSq : {R : Type} → [hR : Semiring R] → R → Prop
#check IsSumSq (0 : ℤ)  -- IsSumSq 0 : Prop
```

Implementing class instance parameters is useful to *automatically* give meaning to expressions `(0 : R)` and `x ^ 2 + S` (since `R` is a semiring), via a process called [*typeclass resolution*](https://lean-lang.org/theorem_proving_in_lean4/type_classes.html).

And we can use this to present the above checks differently. Note that we have to do it with a type that has already been declared and instantiated as a semiring, for instance `ℤ`.

```lean
#check @IsSumSq ℤ _  -- IsSumSq : ℤ → Prop
#check @IsSumSq ℤ _ 0  -- IsSumSq 0 : Prop
```

Since `IsSumSq` is declared as an inductive type, it automatically generates an induction principle.accesible via `IsSumSq.rec`. This means that if we want to prove a result for all sums of squares in a semiring `R'`, it suffices to prove it for `0 : R'` and to prove it for all terms of the form `x ^ 2 + S` under the assumption that the term `S` is a sum of squares in `R'`, for which the result has already been proved.

To see how it works, we can either use a concrete example of a semiring, like `ℤ`, or declare  a variable to play that role (note that we do not call it `R`, in order to avoid conflicts in future declarations).

```lean
variable {R' : Type} [hR' : Semiring R']

#check @IsSumSq.rec R' _
```

The induction principle for `IsSumSq` is reproduced below. There, the `Prop`-valued function `motive` is to be thought of as a property of sums of squares in `R` that one wants to prove.

```lean
@IsSumSq.rec R' hR' : ∀ {motive : (a : R') → IsSumSq a → Prop},
  motive 0 (_ : IsSumSq 0) →
    (∀ (x S : R') (hS : IsSumSq S), motive S hS → motive (x ^ 2 + S) (_ : IsSumSq (x ^ 2 + S))) →
      ∀ {a : R'} (t : IsSumSq a), motive a t
```

Let us now use induction to prove certain properties of sums of squares in a semiring `R`. For instance, to say that set of sums of squares in a semiring `R` is closed under addition, we write:

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

Likewise, if the semiring `R` is commutative,  a product of sums of squares is a sum of squares. As we shall see, the assumption that `R` is commutative is used in our proof when applying [`mul_pow`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupPower/Basic.html#mul_pow). We make this apparent via a separate lemma.

```lean
lemma IsSumSq.ProdBySumSq [CommSemiring R] {S : R} (h : IsSumSq S) {x : R} : IsSumSq (x ^2 * S) := by
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
    · exact IsSumSq.ProdBySumSq h2
    · exact ih
```

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

From this and Lemma `SumSqListIsSumSq` proved in [the first section](#using-an-inductive-predicate), we can prove the equivalence that we wanted.

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

Recall that, given a type `R`, a term of type [Set R](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Set.html) is by definition a predicate `R → Prop`. For instance, to the predicate `IsSumSq : R → Prop`, there is associated the set `{S : R | IsSumSq S}`, which consists of terms `S : R` such that `IsSumSq S` has a proof.

The upshot of using the type `Set R` is that it gives access to type-theoretic notation, most prominently the symbol `∈`. Note that it is convenient, in the definition of the function `SumSqSet : R → Set R`, to make the variable `R` explicit.

```lean
def SumSqSet (R : Type) [Semiring R] : Set R := {a : R | IsSumSq a}

#check SumSqSet ℤ  -- SumSqSet ℤ : Set ℤ
#check 0 ∈ SumSqSet ℤ  -- 0 ∈ SumSqSet ℤ : Prop

example [Semiring R] : 0 ∈ SumSqSet R := by  -- the goal is 0 ∈ SumSqSet R
  dsimp [SumSqSet]  -- simplifies the goal to 0 ∈ {a | IsSumSq a}, using the definition of SumSqSet
  change IsSumSq 0  -- changes the goal to IsSumSq 0, which is definitionally equal to 0 ∈ {a | IsSumSq a}
  exact IsSumSq.zero  -- this closes the goal because IsSumSq.zero is the proof that 0 is a sumof squares in R, by definition
```

We can now rewrite the theorems above in set-theoretic notation. All of them have already been proved, so we close the goal with an `exact` tactic everty time.

```lean
theorem SumSqSet.Sum [Semiring R] {S1 S2 : R} (h1 : S1 ∈ SumSqSet R) (h2 : S2 ∈ SumSqSet R) : (S1 + S2) ∈ SumSqSet R  := by
  exact IsSumSq.Sum h1 h2

lemma SumSqSet.ProdBySumSq [CommSemiring R] {S : R} (h : S ∈ SumSqSet R) {x : R} : (x ^2 * S) ∈ SumSqSet R := by
  exact IsSumSq.ProdBySumSq h

theorem SumSqSet.Prod [CommSemiring R] {S1 S2 : R} (h1 : S1 ∈ SumSqSet R) (h2 : S2 ∈ SumSqSet R) :(S1 * S2) ∈ SumSqSet R := by
  exact IsSumSq.Prod h1 h2

-- TO COMPLETE! ADD COMMENTS TO PROOFS ABOVE!! AND ADD EXERCISES!

-- NEXT IS A COMMENT ON WHAT CHANGES IF THE VARIABLE `R` IS MADE EXPLICIT. Maybe turn this into an exercise instead?

inductive IsSumSqExpl (R : Type) [Semiring R] : R → Prop :=
  | zero : IsSumSqExpl R (0 : R)
  | add (x S : R) (hS : IsSumSqExpl R S) : IsSumSqExpl R (x ^ 2 + S)

-- #check (0 : ℤ) ∈ IsSumSq ℤ  -- failed to synthesize instance Membership ℤ Prop

-- #check (0 : ℤ) ∈ IsSumSq -- WORKS IF IsSumSq IS DECLARED AS TYPE Set R (even with the type `R` implicit)

-- #check (0 : ℤ) ∈ IsSumSq'' ℤ  -- does not read very naturally anyway  (not like (0 : ℤ) ∈ (SumSqSet ℤ)) EXERCISE AGAIN?
```

## As a subtype

TO COMPLETE (mimic the set-theoretic approach, explaining why it is more complicated to formalise the proofs with subtypes...)

ALSO: explain the proofs everywhere!

```lean
def SumSqType (R : Type) [Semiring R] : Type := {a : R // IsSumSq a}

#check SumSqType

#check (⟨(0 : ℤ), IsSumSq.zero⟩ : SumSqType ℤ)

-- see below for one advantage of making the typ `R` explicit in the definition of `IsSumSq'`

def SumSqType' (R : Type) [Ring R] : Type := Subtype (IsSumSqExpl R)  -- turn this into an exercise...?

#check SumSqType'
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
-- TO COMPLETE (see also Sols.lean)

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
