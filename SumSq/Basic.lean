/-
# The type of sums of squares

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser.
-/

import SumSq.Defs
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.GroupTheory.Submonoid.Basic

-- ADD COMMENTS TO PROOFS AND REBUILD GITHUB PAGES... Maybe prove submonoid?

/-!
Let `R`be a semiring. In the file [SumSq.Defs](Defs.md), we declared a function `SumSq : List R → R` that computes the sum of squares of the entries of a list:

> SumSq [a, b, c] = a ^ 2 + b ^ 2 + c ^ 2

In the present file, we declare a predicate `IsSumSq : R → Prop` that characterizes the elements of `R` that are return values of the function `SumSq`. We then discuss how to use such a predicate to declare sums of squares in `R` either as a subset or as a subtype of `R`.

## Using an inductive predicate

Using a predicate on `R` (i.e. a function `IsSumSq : R → Prop`) to characterize sums of squares in `R` means the following: a term `S : R` will be called a sum of squares if the proposition `IsSumSq S` has a proof.

Below, the predicate `IsSumSq` is defined inductively, but later we will show that we can also define it [existentially](#using-an-existential-predicate).
-/

inductive IsSumSq {R : Type} [Semiring R] : R → Prop :=
  | zero : IsSumSq (0 : R)
  | add (x S : R) (hS : IsSumSq S) : IsSumSq (x ^ 2 + S)

/-!
By definition of `IsSumSq`, the term `0 : R` is a sum of squares, and if `S : R` is a sum of squares and `x : R`, then `x ^ 2 + S` is a sum of squares. We can use this to prove that, for all list `L : List R`, the term `SumSq L : R` is a sum of squares.
-/

lemma SumSqListIsSumSq {R : Type} [Semiring R] (L : List R) : IsSumSq (SumSq L) := by
  induction L with
  | nil =>
    exact IsSumSq.zero
  | cons a l ih =>
    rw [SumSq]
    exact IsSumSq.add a (SumSq l) ih

/-!
Let us give three more examples of simple proofs that a term `S : R` is a sum of squares. Namely, we prove that `0 : R`, `1 : R` and all squares in `R` are sums of squares.

For more on this, see [Exercise 1](#exercise-1). And for more on Lemma `SumSqListIsSumSq`, see [Exercise 2](#exercise-2).
-/

lemma zeroIsSumSq {R : Type} [Semiring R] : IsSumSq (0 : R) := by
  exact IsSumSq.zero

lemma oneIsSumSq {R : Type} [Semiring R] : IsSumSq (1 : R) := by
  have aux : (1 : R) = (1 ^ 2 + 0) := by simp
  rw [aux]
  exact IsSumSq.add 1 0 IsSumSq.zero

lemma SquareIsSumSq {R : Type} [Semiring R] (x : R) : IsSumSq (x ^ 2) := by
  rw [← add_zero (x ^2)]
  exact IsSumSq.add x 0 IsSumSq.zero

/-!
Based on its declaration, the type `IsSumSq` behaves like a `Prop`-valued function on `R`. The only two subtleties are:

- the fact that the variable `R : Type` is implicit (between brackets of the form `{}`).
- the fact that the assumption that `R` is a semiring is implemented using a class instance (between brackets of the form `[]`).

For example, `IsSumSq ℤ 0` is the formalized version of the statement `0 is a sum of squares in ℤ`.
-/

#check @IsSumSq  -- @IsSumSq : {R : Type} → [hR : Semiring R] → R → Prop
#check IsSumSq (0 : ℤ)  -- IsSumSq 0 : Prop

/-!
Implementing class instance parameters is useful to *automatically* give meaning to expressions `(0 : R)` and `x ^ 2 + S` (since `R` is a semiring), via a process called [*typeclass resolution*](https://lean-lang.org/theorem_proving_in_lean4/type_classes.html). Note that we could give that instantiation a name if we wanted to, by declaring `[hR : Semiring R]` instead of just `[Semiring R]`.

The fact that `IsSumSq` behaves like a function with an implicit parameter and a class instance parameter can be used to present the above checks differently.
-/

#check @IsSumSq ℤ _  -- IsSumSq : ℤ → Prop
#check @IsSumSq ℤ _ 0  -- IsSumSq 0 : Prop

/-!
Since `IsSumSq` is declared as an inductive type, it automatically generates an induction principle accesible via `IsSumSq.rec`. This means that if we want to prove a result for all sums of squares in a semiring `R'`, it suffices to prove it for `0 : R'` and to prove it for all terms of the form `x ^ 2 + S` under the assumption that the term `S` is a sum of squares in `R'`, for which the result has already been proved.

To see how it works, we can either use a concrete example of a type with semiring instance, like `ℤ`, or declare  a variable which plays that role (note that we do not call it `R`, in order to avoid conflicts in future declarations).
-/

variable {R' : Type} [hR' : Semiring R']
#check @IsSumSq.rec R' _

/-!
Since it is a bit long, the induction principle for `IsSumSq` is reproduced below. There, the `Prop`-valued function `motive` is to be thought of as a property of sums of squares in `R` that one wants to prove.

```lean
@IsSumSq.rec R' hR' : ∀ {motive : (a : R') → IsSumSq a → Prop},
  motive 0 (_ : IsSumSq 0) →
    (∀ (x S : R') (hS : IsSumSq S), motive S hS → motive (x ^ 2 + S) (_ : IsSumSq (x ^ 2 + S))) →
      ∀ {a : R'} (t : IsSumSq a), motive a t
```

Let us now see how to use induction on the type `IsSumSq` to prove certain properties of sums of squares in a semiring `R`. For example, to say that the sum of two sums of squares is itself a sum of squares, we write:

> IsSumSq S1 ∧ IsSumSq S2 → IsSumSq (S1 + S2)

-/

theorem IsSumSq.Sum {R : Type} [Semiring R] {S1 S2 : R} (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 + S2) := by
  induction h1 with
  | zero =>
    simp
    exact h2
  | add a S hS ih =>
    rw [add_assoc]
    exact IsSumSq.add a (S + S2) ih

/-!
Likewise, if the semiring `R` is commutative, a product of sums of squares is a sum of squares. As we shall see, the assumption that `R` is commutative is used in our proof when applying [`mul_pow`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupPower/Basic.html#mul_pow). We make this apparent via a separate lemma.
-/

lemma IsSumSq.ProdBySumSq {R : Type} [CommSemiring R] {S : R} (h : IsSumSq S) {x : R} : IsSumSq (x ^2 * S) := by
  induction h with
  | zero =>
    rw [mul_zero]
    exact IsSumSq.zero
  |add a s _ ih =>
    rw [mul_add, ← mul_pow x a 2]
    exact IsSumSq.add (x * a) (x ^ 2 * s) ih

/-!
We can now prove that, indeed, a product of sums of squares is a sum of squares:

> IsSumSq S1 ∧ IsSumSq S2 → IsSumSq (S1 * S2)
-/

theorem IsSumSq.Prod {R : Type} [CommSemiring R] {S1 S2 : R} (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 * S2) := by
  induction h1 with
  | zero =>
    rw [zero_mul]
    exact IsSumSq.zero
  | add a S hS ih =>
    rw [add_mul]
    apply IsSumSq.Sum _ _
    · exact IsSumSq.ProdBySumSq h2
    · exact ih

/-!
## Using an existential predicate

We now show that we could also define `IsSumSq S` by asking that it be a return value of the function `SumSq` defined in [SumSq.Defs](Defs.md). More precicely, we prove that, given a term `S` in a semiring `R`, the following equivalence holds:

> IsSumSq S ↔ (∃ L : List R, SumSq L = S)

We start with the first implication: starting from `S : R` such that `IsSumSq S` has a proof, we want to construct a list `L : List R` such that `SumSq L = S`. Since `IsSumSq S`is defined inductively, we can do this by induction on the proof of the proposition `IsSumSq S`.
-/

lemma IsSumSqToExistList {R : Type} [Semiring R] (S : R) (hS : IsSumSq S) : (∃ L : List R, SumSq L = S) := by
  induction hS with
  | zero => -- exact ⟨[], rfl⟩
    use []
    rfl
  | add a S' _ ih =>
    rcases ih with ⟨L', hL'⟩
    rw [← hL']
    use (a :: L')
    rfl

/-!
From this and Lemma `SumSqListIsSumSq` proved in [the first section](#using-an-inductive-predicate), we can prove the equivalence that we wanted.
-/

theorem IsSumSq.Char (R : Type) [Semiring R] (S : R) : IsSumSq S ↔ (∃ L : List R, SumSq L = S) := by
  constructor
  · apply IsSumSqToExistList
  · intro h
    rcases h with ⟨L, hL⟩
    rw [← hL]
    exact SumSqListIsSumSq L

/-!
## As a set

Recall that, given a type `R`, a term of type [`Set R`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Set.html) is by definition a predicate `R → Prop`. But it comes with a series of extra functions, such as [`Set.Mem`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Set.html#Set.Mem) to define membership in a set. And Lean provides a way to define sets from predicates, with a syntax that is familiar to mathematicians.

For example, to the predicate `IsSumSq : R → Prop`, there is associated the set `{S : R | IsSumSq S}`, which we can think of as *consisting of terms `S : R` such that `IsSumSq S` has a proof*. More concretely, `(0 : R) ∈ {S : R | IsSumSq S}` is definitionally equal to the proposition `IsSumSq 0` (see example below).

The upshot of using the type `Set R` is that it gives access to type-theoretic notation (the symbols `∈`, `∩`, `∪` *etc*). Note that it is convenient, in the definition of the function `SumSqSet : R → Set R`, to now make the variable `R` explicit.
-/

def SumSqSet (R : Type) [Semiring R] : Set R := {S : R | IsSumSq S}

#check @SumSqSet  -- SumSqSet : (R : Type) → [inst : Semiring R] → Set R
#check @SumSqSet ℤ  -- @SumSqSet ℤ : [inst : Semiring ℤ] → Set ℤ
#check @SumSqSet ℤ _  -- SumSqSet ℤ : Set ℤ

#check SumSqSet ℤ  -- SumSqSet ℤ : Set ℤ
#check 0 ∈ SumSqSet ℤ  -- 0 ∈ SumSqSet ℤ : Prop

/-
Alternately, the set of sums of squares can be obtained from the predicate `IsSumSq` using the function [`setOf`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Set.html#setOf).
-/

def SumSqSet' (R : Type) [Semiring R] : Set R := setOf IsSumSq

#check @SumSqSet' -- SumSqSet' : (R : Type) → [inst : Semiring R] → Set R
#check @SumSqSet' ℤ  -- @SumSqSet' ℤ : [inst : Semiring ℤ] → Set ℤ
#check @SumSqSet' ℤ _  -- SumSqSet' ℤ : Set ℤ

#check SumSqSet' ℤ  -- SumSqSet' ℤ : Set ℤ
#check 0 ∈ SumSqSet' ℤ  -- 0 ∈ SumSqSet' ℤ : Prop

/-!
We could have used the set-theoretic notation earlier if we had declared `IsSumSq` in the following way, replacing `R → Prop` with `Set R`:

```lean
inductive IsSumSq {R : Type} [Semiring R] : Set R :=
  | zero : IsSumSq (0 : R)
  | add (x S : R) (hS : IsSumSq S) : IsSumSq (x ^ 2 + S)
```

However, it is not clear that this is a better option. Indeed, if we do that, then `(0 : R) ∈ IsSumSq` type-checks, but it does not read very naturally compared to `(0 : R) ∈ SumSq R`. By definition, the latter means `(0 : R) ∈ {S : R | IsSumSq S}`, and this means that `IsSumSq (0 : R)` has a proof.

Here is a proof that `(0 : R) ∈ SumSq R`. As we can see, it uses the fact that this is definitionally equal to the proposition `IsSumSq (0 : R)`.
-/

example {R : Type} [Semiring R] : 0 ∈ SumSqSet R := by  -- the goal is 0 ∈ SumSqSet R (note that Lean identifies the term 0 as being of type R)
  dsimp [SumSqSet]  -- simplifies the goal to 0 ∈ {a | IsSumSq a}, using the definition of SumSqSet
  change IsSumSq 0  -- changes the goal to IsSumSq 0, which is definitionally equal to 0 ∈ {a | IsSumSq a}
  exact IsSumSq.zero  -- this closes the goal because IsSumSq.zero is the proof that 0 is a sum of squares in R

/-!
We can now rewrite the theorems above in set-theoretic notation. All of them have already been proved, so we close the goal with an `exact` tactic every time.
-/

theorem SumSqSet.Sum {R : Type} [Semiring R] {S1 S2 : R} (h1 : S1 ∈ SumSqSet R) (h2 : S2 ∈ SumSqSet R) : (S1 + S2) ∈ SumSqSet R  := by
  exact IsSumSq.Sum h1 h2

lemma SumSqSet.ProdBySumSq {R : Type} [CommSemiring R] {S : R} (h : S ∈ SumSqSet R) {x : R} : (x ^2 * S) ∈ SumSqSet R := by
  exact IsSumSq.ProdBySumSq h

theorem SumSqSet.Prod {R : Type} [CommSemiring R] {S1 S2 : R} (h1 : S1 ∈ SumSqSet R) (h2 : S2 ∈ SumSqSet R) :(S1 * S2) ∈ SumSqSet R := by
  exact IsSumSq.Prod h1 h2

/-!
SUBMONOID CLOSURE? We prove that the set of sums of squares of R is an additive submonoid of R by proving that it is the additive submonoid generated by the squares... infer instance to say it is a moinoid?
-/

def Squares (R : Type) [Semiring R] : Set R := {a | ∃ (b : R), a = b ^ 2}

theorem SumSqSetIsSubmonoid (R : Type) [Semiring R] : SumSqSet R = AddSubmonoid.closure (Squares R) := sorry


/-!
To conclude this subsection, we point out that we could have made the variable `R` explicit in the declaration `IsSumSq`. It makes the notation a little bit heavier, but it can be useful when declaring subtypes (see [below](#as-a-subtype)).
-/

inductive IsSumSqExpl (R : Type) [Semiring R] : R → Prop :=
  | zero : IsSumSqExpl R (0 : R)
  | add (x S : R) (hS : IsSumSqExpl R S) : IsSumSqExpl R (x ^ 2 + S)

/-!
## As a subtype

Similarly to the way the set `SumSqSet R` is defined (using the syntax `{S : R | IsSumSq S}`), Lean provides a way to define sums of squares as a [subtype](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Subtype) of `R`, using the predicate `IsSumSq : R → Prop` and a syntax similar to the one seen [earlier](#as-a-set) for `SumSqSet R` (namely `{S : R | IsSumSq R}`).

The first difference is that the return type is now `Type`, as opposed to `Set R`. Note that we are still making the variable `R` explicit here.
-/

def SumSqType (R : Type) [Semiring R] : Type := {S : R // IsSumSq S}

#check @SumSqType

/-!
By definition of the subtype associated to the predicate `IsSumSq`, a term `S : SumSqType R` is a pair `⟨S.val, S.property⟩` consisting of a term `S.val : R` and a term `S.property : IsSumSq S` (meaning a proof of the proposition `IsSumSq S`). In particular, to declare such a term `S`, we need to specify both `S.val` and `S.property`.
-/

#check (⟨0, IsSumSq.zero⟩ : SumSqType ℤ)
  -- { val := 0, property := (_ : IsSumSq 0) } : { S // IsSumSq S }

/-!
It seems reasonable to imagine that, when it comes to formalising proofs about sums of squares in `R`, it will be less natural for mathematicians to work with the subtype `IsSumSqType R` than with the set `IsSumSqSet R`. For example, when working with subtypes, to say that *the sum of two sums of squares is a sum of squares*, is equivalent to *declaring a function* `SumSqType.Add {R : Type} [Semiring R] : SumSqType R → SumSqType R → SumSqType R`, with `SumSq.Add S1 S2` defined as `⟨S1.val + S2.val, IsSumSq.Sum S1.property S2.property⟩`.

As we can see, this formalises the desired result, but in a way that is not (yet?) the usual one in mathematics. Instead, it is directly inspired by the methods of functional programming. Exploring those methods further, we can perform other constructions that are common in functional programming and object-oriented programming, such as *instantiating a class* on the type `SumSqType`. For example the class [`Add`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Add), which will equip the type `SumSqType R` with a function `SumSqType R → SumSqType R → SumSqType R`.
-/

def Addition {R : Type} [Semiring R] (S1 S2 : SumSqType R) : SumSqType R := ⟨S1.val + S2.val, IsSumSq.Sum S1.property S2.property⟩

instance {R : Type} [Semiring R] : Add (SumSqType R) := ⟨Addition⟩

/-!
As a consequence, we now have access to the methods of the class `Add`. For example, we can use the notation `+` without declaring it as such for the function `Addition`.
-/

def Double {R : Type} [Semiring R] (S : SumSqType R) : SumSqType R := S + S

example {R : Type} [Semiring R] (S : SumSqType R) : Double S = Addition S S := rfl

/-!
Note that the instantiation can also be done directly, without defining the function `Addition`. And we may give it a name if we want, and/or use a slightly different syntax (`add` is the unique attribute of the class [`Add`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Add)).
-/

instance {R : Type} [Semiring R] : Add (SumSqType R) := ⟨fun S1 S2 => ⟨S1.val + S2.val, IsSumSq.Sum S1.property S2.property⟩⟩

instance SumSqTypeAddition (R : Type) [Semiring R] : Add (SumSqType R) where add S1 S2 := ⟨S1.val + S2.val, IsSumSq.Sum S1.property S2.property⟩

/-!
Another advantage of defining sums of squares as a subtype is that we can make the type `SumSqType R` an instance of the `Repr` class, making it possible to use `#eval` on terms of type `SumSqType ℤ` or `SumSqType ℚ` (all terms of type `SumSqType R` where `R` is a *concrete* type).
-/

#check SumSqType ℤ

instance {R : Type} [Semiring R] [Repr R] : Repr (SumSqType R) where
  reprPrec :=
    fun S _ =>
      repr S.val ++ " is a sum of squares because the property IsSumSq " ++ repr S.val ++ " has been proven."

def aTermOfSumSqTypeInZ : SumSqType ℤ := ⟨0, IsSumSq.zero⟩

#check aTermOfSumSqTypeInZ.1  -- ↑aTermOfSumSqTypeInZ : ℤ
#check aTermOfSumSqTypeInZ.2  -- aTermOfSumSqTypeInZ.property : IsSumSq ↑aTermOfSumSqTypeInZ

#eval aTermOfSumSqTypeInZ.1  -- 0
#eval aTermOfSumSqTypeInZ  -- 0 is a sum of squares because the property IsSumSq 0 has been proven.

/-!
Similarly, we can put a `Decidable` instance on the proposition `IsSumSq (0 : R)`.
-/

instance {R : Type} [Semiring R] : Decidable (IsSumSq (0 : R)) :=
  Decidable.isTrue (IsSumSq.zero)

#check IsSumSq (0 : ℤ)  -- IsSumSq 0 : Prop
#eval IsSumSq (0 : ℤ)  -- true

#eval decide (IsSumSq (0 : ℤ))  -- true

#check IsSumSq (0 : R')  -- IsSumSq 0 : Prop
#eval IsSumSq (0 : R')  -- (kernel) declaration has free variables '_eval'

/-!
We conclude this subsection by showing one advantage of making the type `R` explicit in the definition of `IsSumSqExpl`. Namely that it gives us access to the function [`Subtype`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Subtype), which creates the subtype of sums of squares from the predicate `IsSumSq R : R → Prop`.

This was not necessary earlier, due to the use of the syntax `{S : R // IsSumSq S}`, which is capable of inferring what is needed in order to construct the required type.
-/

def SumSqType' (R : Type) [Semiring R] : Type := Subtype (IsSumSqExpl R)

#check @SumSqType'  -- SumSqType' : (R : Type) → [inst : Semiring R] → Type

#check (⟨0, IsSumSqExpl.zero⟩ : SumSqType' ℤ)
  -- { val := 0, property := (_ : IsSumSqExpl ℤ 0) } : Subtype (IsSumSqExpl ℤ)

/-!
## Exercises

### Exercise 1

Let `R` be a semiring and let `S` be a term in `R`. Prove that Proposition `IsSumSq S` is equivalent to Proposition `IsSumSq' S`, where `IsSumSq'` is the predicate defined inductively as follows:

```lean
inductive IsSumSq' {R : Type} [Semiring R] : R → Prop :=
  | sq (x : R): IsSumSq (x ^ 2 : R)
  | add (S1 S2 : R) (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 + S2)
```

Note that this definition may be more intuitive than the one we gave in [the first section](#using-an-inductive-predicate). But it might be less convenient to work with. Indeed, when proving a statement by induction on the proof of `IsSumSq' S`, then in the first case, we would have to prove it not only for `S = 0`, but in all cases `S = x ^ 2` for some `x : R`.

### Exercise 2

Let `R` be a semiring and let `S` be a term in `R`. Write a (direct) proof of the implication

> (∃ L : List R, SumSq L = S) → IsSumSq S

and ask yourself whether having an existential quantifier in the assumption makes things complicated. Try using Lemma `SumSqListIsSumSq` and the second implication of the equivalence `IsSumSq.Char` to prove the result. You can then see that the approach there is to first prove `IsSumSq (SumSq L)` and from this deduce a proof of the implication. A formalisation of this last statement is suggested in [Exercise 3](#exercise-3).

### Exercise 3

Let `S T` be types. Let `P : T → Prop` be a predicate on `T` and let `f : S → T` be a function from `S` to `T`. Assume that the proposition `∀ x : S, P (f x)` has a proof and that the proposition `∀ y : T, ∃ x : S, y = f x` has a proof. Show that the proposition `∀ y : T, P y` has a proof.
-/
