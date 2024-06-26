# The type of sums of squares

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser.

```lean
import SumSq.Defs
```

Let `R`be a semiring. In the file [SumSq.Defs](Defs.md), we declared a function `SumSq : List R → R` that computes the sum of squares of the entries of a list:

> SumSq [a, b, c] = a ^ 2 + b ^ 2 + c ^ 2

In the present file, we declare a predicate `IsSumSq : R → Prop` that characterizes the elements of `R` that are return values of the function `SumSq`. We then discuss how to use such a predicate to declare sums of squares in `R` either as a subset or as a subtype of `R`.

## Using an inductive predicate / type

Using a predicate on `R` (i.e. a function `IsSumSq : R → Prop`) to characterize sums of squares in `R` means the following: a term `S : R` will be called a sum of squares if the proposition `IsSumSq S` has a proof.

Below, the predicate `IsSumSq` is defined inductively, but later we will show that we can also define it [existentially](#using-an-existential-predicate).

```lean
inductive IsSumSq {R : Type} [Semiring R] : R → Prop
  | zero : IsSumSq (0 : R)
  | add (x S : R) (hS : IsSumSq S) : IsSumSq (x ^ 2 + S)
```

By definition of `IsSumSq`, the term `0 : R` is a sum of squares, and if `S : R` is a sum of squares and `x : R`, then `x ^ 2 + S` is a sum of squares. We can use this to prove that, for all list `L : List R`, the term `SumSq L : R` is a sum of squares.

```lean
lemma SumSqListIsSumSq {R : Type} [Semiring R] (L : List R) : IsSumSq (SumSq L) := by
  induction L with  -- by induction on the list L
  | nil =>  -- the case of the empty list []
    rw [SumSq]  -- rewrite using SumSq [] = 0
    exact IsSumSq.zero  -- IsSumSq 0 is a proof that 0 is a sum of squares
  | cons a l ih =>  -- the case of a list L = (a :: l) where SumSq l is assumed to be a sum of squares
    rw [SumSq]  -- rewrite using SumSq (a :: l) = a ^2 + SumSq l
    exact IsSumSq.add a (SumSq l) ih  -- conclude using the induction hypothesis and the property that, if S is a sum of squares, then x ^2 + S is a sum of squares
```

Let us give three more examples of simple proofs that a term `S : R` is a sum of squares. Namely, we prove that `0 : R`, `1 : R` and all squares in `R` are sums of squares.

For more on this, see [Exercise 1](#exercise-1). And for more on Lemma `SumSqListIsSumSq`, see [Exercise 2](#exercise-2).

```lean
lemma zeroIsSumSq {R : Type} [Semiring R] : IsSumSq (0 : R) := by
  exact IsSumSq.zero  -- 0 is a sum of squares in R by definition of the type IsSumSq

lemma SquareIsSumSq {R : Type} [Semiring R] (x : R) : IsSumSq (x ^ 2) := by
  rw [← add_zero (x ^2)]  -- rewrite using x ^ 2 = x ^ 2 + 0
  exact IsSumSq.add x 0 IsSumSq.zero  -- x ^ 2 + 0 is a sum of squares in R by definition of the type IsSumSq (and because we have already proven that 0 is a sum squares)

lemma oneIsSumSq {R : Type} [Semiring R] : IsSumSq (1 : R) := by
  rw [← one_pow 2]  -- rewrite using 1 = 1 ^ 2
  exact SquareIsSumSq 1  -- conclude using SquareIsSumSq
```

Based on its declaration, the type `IsSumSq` behaves like a `Prop`-valued function on `R`. The only two subtleties are:

- the fact that the variable `R : Type` is implicit (between brackets of the form `{}`).
- the fact that the assumption that `R` is a semiring is implemented using a class instance (between brackets of the form `[]`).

For example, `IsSumSq ℤ 0` is the formalized version of the statement `0 is a sum of squares in ℤ`.

```lean
#check @IsSumSq  -- @IsSumSq : {R : Type} → [hR : Semiring R] → R → Prop
#check IsSumSq (0 : ℤ)  -- IsSumSq 0 : Prop
```

Implementing class instance parameters is useful to *automatically* give meaning to expressions `(0 : R)` and `x ^ 2 + S` (since `R` is a semiring), via a process called [*typeclass resolution*](https://lean-lang.org/theorem_proving_in_lean4/type_classes.html). Note that we could give that instantiation a name if we wanted to, by declaring `[hR : Semiring R]` instead of just `[Semiring R]`.

The fact that `IsSumSq` behaves like a function with an implicit parameter and a class instance parameter can be used to present the above checks differently.

```lean
#check @IsSumSq ℤ _  -- IsSumSq : ℤ → Prop
#check @IsSumSq ℤ _ 0  -- IsSumSq 0 : Prop
```

Since `IsSumSq` is declared as an inductive type, it automatically generates an induction principle accesible via `IsSumSq_rec`. This means that if we want to prove a result for all sums of squares in a semiring `R'`, it suffices to prove it for `0 : R'` and to prove it for all terms of the form `x ^ 2 + S` under the assumption that the term `S` is a sum of squares in `R'`, for which the result has already been proved.

To see how it works, we can either use a concrete example of a type with semiring instance, like `ℤ`, or declare  a variable which plays that role (note that we do not call it `R`, in order to avoid conflicts in future declarations).

```lean
variable {R' : Type} [hR' : Semiring R']
#check @IsSumSq.rec R' _
```

Since it is a bit long, the induction principle for `IsSumSq` is reproduced below. There, the `Prop`-valued function `motive` is to be thought of as a property of sums of squares in `R` that one wants to prove.

```lean
@IsSumSq_rec R' hR' : ∀ {motive : (a : R') → IsSumSq a → Prop},
  motive 0 (_ : IsSumSq 0) →
    (∀ (x S : R') (hS : IsSumSq S), motive S hS → motive (x ^ 2 + S) (_ : IsSumSq (x ^ 2 + S))) →
      ∀ {a : R'} (t : IsSumSq a), motive a t
```

Let us now see how to use induction on the type `IsSumSq` to prove certain properties of sums of squares in a semiring `R`. For example, to say that the sum of two sums of squares is itself a sum of squares, we write:

> IsSumSq S1 ∧ IsSumSq S2 → IsSumSq (S1 + S2)

```lean
theorem IsSumSq_Sum {R : Type} [Semiring R] {S1 S2 : R} (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 + S2) := by
  induction h1 with  -- we prove that S1 + S2 is a sum of squares in R by induction on h1 (which is a proof that S1 is a sum of squares)
  | zero =>  -- the base step is S1 = 0, so S1 + S2 = S2
    simp only [zero_add]  -- we simplify 0 + S2 to S2
    exact h2  -- we conclude using h2
  | add a S hS ih =>  -- the inductive step is the case S1 = a ^ 2 + S, where S is a sum of squares and the induction hypothesis is that (S + S2) is a sum of squares: the goal is to prove that (a ^ 2 + S) + S2 is a sum of squares
    rw [add_assoc]  -- rewrite using (a ^ 2 + S) + S2 = a ^ 2 + (S + S2)
    exact IsSumSq.add a (S + S2) ih  -- since a ^ 2 is a square and (S + S2) is a sum of squares by the induction hypothesis, we conclude using IsSumSq.add
```

Likewise, if the semiring `R` is commutative, a product of sums of squares is a sum of squares. As we shall see, the assumption that `R` is commutative is used in our proof when applying [`mul_pow`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupPower/Basic.html#mul_pow). We make this apparent via a separate lemma.

```lean
lemma IsSumSq_ProdSqBySumSq {R : Type} [CommSemiring R] {S : R} (h : IsSumSq S) {x : R} : IsSumSq (x ^2 * S) := by
  induction h with  -- we prove that x ^ 2 * S is a sum of squares by induction on h (which is a proof that S is a sum of squares)
  | zero =>  -- the base step is S = 0 so x ^ 2 * S = x ^ 2 * 0
    rw [mul_zero]  -- we simplify x ^ 2 * 0 to 0
    exact IsSumSq.zero  -- we conclude using the fact that 0 is a sum of squares
  |add a s _ ih =>  -- the inducive step is the case S = a ^ 2 + s, where s is a sum of squares and the induction hypothesis is that (x ^ 2 * s) is a sum of squares: the goal is to prove that x ^ 2 * (a ^ 2 + s) is a sum of squares
    rw [mul_add, ← mul_pow x a 2]  -- rewrite using x ^ 2 * (a ^ 2 + s) = (x * a) ^ 2 + x ^ 2 * s
    exact IsSumSq.add (x * a) (x ^ 2 * s) ih  -- since (x * a) ^ 2 is a square and (x ^ 2 *  s) is a sum of squares by the induction hypothesis, we conclude using IsSumSq.add
```

We can now prove that, indeed, a product of sums of squares is a sum of squares:

> IsSumSq S1 ∧ IsSumSq S2 → IsSumSq (S1 * S2)

```lean
theorem IsSumSq_Prod {R : Type} [CommSemiring R] {S1 S2 : R} (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 * S2) := by
  induction h1 with  -- we prove that S1 * S2 is a sum of squares by induction on h (which is a proof that S1 is a sum of squares)
  | zero =>  -- -- the base step is S1 = 0 so S1 * S2 = 0 * S2
    rw [zero_mul]  -- we simplify 0 * S2 to 0
    exact IsSumSq.zero  -- we conclude using the fact that 0 is a sum of squares
  | add a S hS ih =>  -- the inducive step is the case S1 = a ^ 2 + S, where S is a sum of squares and the induction hypothesis is that (S * S2) is a sum of squares: the goal is to prove that (a ^ 2 + S) * S2 is a sum of squares
    rw [add_mul]  -- rewrite using (a ^ 2 + S) * S2 = a ^ 2 * S2 + S * S2
    apply IsSumSq_Sum _ _  -- since a sum of sums of squares is a sum of squares, in order to prove that (a ^ 2 * S2) + (S * S2) is a sum of squares, it suffices to prove that (a ^ 2 * S2) and (S * S2) are both sums of squares
    · exact IsSumSq_ProdSqBySumSq h2  -- the fact that (a ^ 2 * S2) is a sum of squares when S2 is a sum of squares was proved in IsSumSq_ProdSqBySumSq
    · exact ih  -- the fact that (S * S2) is a sum of squares is the induction hypothesis
```

## Using an existential predicate

We now show that we could also define `IsSumSq S` by asking that it be a return value of the function `SumSq` defined in [SumSq.Defs](Defs.md). More precicely, we prove that, given a term `S` in a semiring `R`, the following equivalence holds:

> IsSumSq S ↔ (∃ L : List R, SumSq L = S)

We begin with the first implication: starting from `S : R` such that `IsSumSq S` has a proof, we want to construct a list `L : List R` such that `SumSq L = S`. Since `IsSumSq S`is defined inductively, we can do this by induction on the proof of the proposition `IsSumSq S`.

```lean
lemma IsSumSqToExistList {R : Type} [Semiring R] (S : R) (hS : IsSumSq S) : (∃ L : List R, SumSq L = S) := by
  induction hS with  -- we prove the result by induction on hS (which is a proof that S is a sum of squares)
  | zero =>  -- the base case is when S = 0
    exact ⟨[], by rw [SumSq]⟩  -- we can use L = [] to prove that ∃ L, SumSq L = 0
    -- use []  -- instead of exact ⟨[], rfl⟩, we can write use [] followed by rfl
    -- rfl
  | add a s _ ih =>  -- the inductive step is when S = a ^2 + s, where s is a sum of squares and the induction hypothesis is that there exists a list L such that SumSq L = s
    rcases ih with ⟨l, hl⟩  -- we extract from ih a list l such that SumSq l = s
    rw [← hl]  -- we rewrite the goal using SumSq l = s
    use (a :: l)  -- We claim that we can use the list L = (a :: l) to show that there exists a list L such thatt SumSq L = a ^ 2 + SumSq l
    rw [SumSq]  -- indeed the result is true by definition of the function SumSq
```

From this and Lemma `SumSqListIsSumSq` proved in [the first section](#using-an-inductive-predicate), we can prove the equivalence that we wanted. Note that, given a sum of squares `S` in `R`, there may exist more than one list such that `SumSq L = S`.

```lean
theorem IsSumSq_Char (R : Type) [Semiring R] (S : R) : IsSumSq S ↔ (∃ L : List R, SumSq L = S) := by
  constructor  -- this tactic splits the equivalence ↔ into two implications
  · apply IsSumSqToExistList  -- the first implication is proven using the lemma IsSumSqToExistList
    -- intro hS  -- instead of the apply tactic, we can use intro followed by exact
    -- exact IsSumSqToExistList S hS
  · intro h  -- to prove the second implication , let h be a proof of the fact that there exists a list L such that SumSq L = S
    rcases h with ⟨L, hL⟩  -- we extract from h a list L such that SumSq L = S
    rw [← hL]  -- we rewrite the goal using SumSq L = S
    exact SumSqListIsSumSq L  -- we close the goal by applying a lemma that we already proved, which says that SumSq L is of type IsSumSq
```

## As a set

Recall that, given a type `R`, a term of type [`Set R`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Set.html) is by definition a predicate `R → Prop`. But it comes with a series of extra functions, such as [`Set.Mem`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Set.html#Set.Mem) to define membership in a set. And Lean provides a way to define sets from predicates, with a syntax that is familiar to mathematicians.

For example, to the predicate `IsSumSq : R → Prop`, there is associated the set `{S : R | IsSumSq S}`, which we can think of as *consisting of terms* `S : R` *such that* `IsSumSq S` *has a proof*. More concretely, `(0 : R) ∈ {S : R | IsSumSq S}` is definitionally equal to the proposition `IsSumSq 0` (see example below).

The upshot of using the type `Set R` is that it gives access to type-theoretic notation (the symbols `∈`, `∩`, `∪` *etc*). Note that it is now convenient, in the definition of the function `SumSqSet : R → Set R`, to make the parameter `R` explicit.

```lean
def SumSqSet (R : Type) [Semiring R] : Set R := {S : R | IsSumSq S}

#check @SumSqSet  -- SumSqSet : (R : Type) → [inst : Semiring R] → Set R
#check @SumSqSet ℤ  -- @SumSqSet ℤ : [inst : Semiring ℤ] → Set ℤ
#check @SumSqSet ℤ _  -- SumSqSet ℤ : Set ℤ

#check SumSqSet ℤ  -- SumSqSet ℤ : Set ℤ
#check 0 ∈ SumSqSet ℤ  -- 0 ∈ SumSqSet ℤ : Prop
```

Alternately, the set of sums of squares can be obtained from the predicate `IsSumSq` using the function [`setOf`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Set.html#setOf).

```lean
def SumSqSet' (R : Type) [Semiring R] : Set R := setOf IsSumSq

#check @SumSqSet' -- SumSqSet' : (R : Type) → [inst : Semiring R] → Set R
#check @SumSqSet' ℤ  -- @SumSqSet' ℤ : [inst : Semiring ℤ] → Set ℤ
#check @SumSqSet' ℤ _  -- SumSqSet' ℤ : Set ℤ

#check SumSqSet' ℤ  -- SumSqSet' ℤ : Set ℤ
#check 0 ∈ SumSqSet' ℤ  -- 0 ∈ SumSqSet' ℤ : Prop
```

We could have used the set-theoretic notation earlier if we had declared `IsSumSq` in the following way, replacing `R → Prop` with `Set R`:

```lean
inductive IsSumSq {R : Type} [Semiring R] : Set R :=
  | zero : IsSumSq (0 : R)
  | add (x S : R) (hS : IsSumSq S) : IsSumSq (x ^ 2 + S)
```

However, it is not clear that this is a better option. Indeed, if we do that, then `(0 : R) ∈ IsSumSq` type-checks, but it does not read very naturally compared to `(0 : R) ∈ SumSq R`. By definition, the latter means `(0 : R) ∈ {S : R | IsSumSq S}`, and this means that `IsSumSq (0 : R)` has a proof.

Here is a proof that `(0 : R) ∈ SumSq R`. As we can see, it uses the fact that this is definitionally equal to the proposition `IsSumSq (0 : R)`.

```lean
example {R : Type} [Semiring R] : 0 ∈ SumSqSet R := by  -- the goal is 0 ∈ SumSqSet R (note that Lean identifies the term 0 as being of type R)
  dsimp [SumSqSet]  -- simplifies the goal to 0 ∈ {a | IsSumSq a}, using the definition of SumSqSet
  change IsSumSq 0  -- changes the goal to IsSumSq 0, which is definitionally equal to 0 ∈ {a | IsSumSq a}
  exact IsSumSq.zero  -- this closes the goal because IsSumSq.zero is the proof that 0 is a sum of squares in R
```

We can now rewrite the theorems above in set-theoretic notation. All of them have already been proved, so we close the goal with an `exact` tactic every time.

```lean
theorem SumSqSet.Sum {R : Type} [Semiring R] {S1 S2 : R} (h1 : S1 ∈ SumSqSet R) (h2 : S2 ∈ SumSqSet R) : (S1 + S2) ∈ SumSqSet R  := by
  exact IsSumSq_Sum h1 h2

lemma SumSqSet.ProdSqBySumSq {R : Type} [CommSemiring R] {S : R} (h : S ∈ SumSqSet R) {x : R} : (x ^2 * S) ∈ SumSqSet R := by
  exact IsSumSq_ProdSqBySumSq h

theorem SumSqSet.Prod {R : Type} [CommSemiring R] {S1 S2 : R} (h1 : S1 ∈ SumSqSet R) (h2 : S2 ∈ SumSqSet R) :(S1 * S2) ∈ SumSqSet R := by
  exact IsSumSq_Prod h1 h2
```

To conclude this subsection, we point out that we could have made the variable `R` explicit in the declaration `IsSumSq`. It makes the notation a little bit heavier, but it can be useful when declaring subtypes (see [below](#as-a-subtype)).

```lean
inductive IsSumSqExpl (R : Type) [Semiring R] : R → Prop :=
  | zero : IsSumSqExpl R (0 : R)
  | add (x S : R) (hS : IsSumSqExpl R S) : IsSumSqExpl R (x ^ 2 + S)
```

## As a subtype

Similarly to the way the set `SumSqSet R` is defined (using the syntax `{S : R | IsSumSq S}`), Lean provides a way to define sums of squares as a [subtype](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Subtype) of `R`, using the predicate `IsSumSq : R → Prop` and a syntax similar to the one seen [earlier](#as-a-set) for `SumSqSet R` (namely `{S : R | IsSumSq S}`).

The first difference is that the return type is now `Type`, as opposed to `Set R`. Note that we are still making the variable `R` explicit here.

```lean
def SumSqType (R : Type) [Semiring R] : Type := {S : R // IsSumSq S}

#check @SumSqType  -- SumSqType : (R : Type) → [inst : Semiring R] → Type
```

By definition of the subtype associated to the predicate `IsSumSq`, a term `S : SumSqType R` is a pair `⟨S.val, S.property⟩` consisting of a term `S.val : R` and a term `S.property : IsSumSq S` (meaning a proof of the proposition `IsSumSq S`). In particular, to declare such a term `S`, we need to specify both `S.val` and `S.property`.

```lean
#check (⟨0, IsSumSq.zero⟩ : SumSqType ℤ)
  -- { val := 0, property := (_ : IsSumSq 0) } : { S // IsSumSq S }
```

It seems reasonable to imagine that, when it comes to formalising proofs about sums of squares in `R`, it will be less natural for mathematicians to work with the subtype `IsSumSqType R` than with the set `IsSumSqSet R`. For example, when working with subtypes, to say that *the sum of two sums of squares is a sum of squares*, is equivalent to *declaring a function* `SumSqType.Add {R : Type} [Semiring R] : SumSqType R → SumSqType R → SumSqType R`, with `SumSq.Add S1 S2` defined as `⟨S1.val + S2.val, IsSumSq_Sum S1.property S2.property⟩`.

As we can see, this formalises the desired result, but in a way that is not (yet?) the usual one in mathematics. Instead, it is directly inspired by the methods of functional programming. Exploring those methods further, we can perform other constructions that are common in functional programming and object-oriented programming, such as *instantiating a class* on the type `SumSqType`. For example the class [`Add`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Add), which will equip the type `SumSqType R` with a function `SumSqType R → SumSqType R → SumSqType R`.

```lean
def Addition {R : Type} [Semiring R] (S1 S2 : SumSqType R) : SumSqType R := ⟨S1.val + S2.val, IsSumSq_Sum S1.property S2.property⟩

instance {R : Type} [Semiring R] : Add (SumSqType R) := ⟨Addition⟩
```

As a consequence, we now have access to the methods of the class `Add`. For example, we can use the notation `+` without declaring it as such for the function `Addition`.

```lean
def Double {R : Type} [Semiring R] (S : SumSqType R) : SumSqType R := S + S

example {R : Type} [Semiring R] (S : SumSqType R) : Double S = Addition S S := by rfl
```

Note that the instantiation can also be done directly, without defining the function `Addition` first. And we may give it a name if we want, and/or use a slightly different syntax (`add` is the unique attribute of the class [`Add`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Add)).

```lean
instance {R : Type} [Semiring R] : Add (SumSqType R) := ⟨fun S1 S2 => ⟨S1.val + S2.val, IsSumSq_Sum S1.property S2.property⟩⟩

instance SumSqTypeAddition {R : Type} [Semiring R] : Add (SumSqType R) where add S1 S2 := ⟨S1.val + S2.val, IsSumSq_Sum S1.property S2.property⟩
```

Another advantage of defining sums of squares as a subtype is that we can make the type `SumSqType R` an instance of the `Repr` class, making it possible to use `#eval` on terms of type `SumSqType ℤ` or `SumSqType ℚ` (all terms of type `SumSqType R` where `R` is a *concrete* type).

```lean
#check SumSqType ℤ

instance {R : Type} [Semiring R] [Repr R] : Repr (SumSqType R) where
  reprPrec :=
    fun S _ =>
      repr S.val ++ " is a sum of squares because the property IsSumSq " ++ repr S.val ++ " has been proven."

def zero_is_SOS : SumSqType ℤ := ⟨0, IsSumSq.zero⟩

#check zero_is_SOS.1  -- ↑zero_is_SOS : ℤ
#check zero_is_SOS.2  -- zero_is_SOS.property : IsSumSq ↑zero_is_SOS

#eval zero_is_SOS.1  -- 0
#eval zero_is_SOS  -- 0 is a sum of squares because the property IsSumSq 0 has been proven.
```

Similarly, we can register a `Decidable` instance on the proposition `IsSumSq (0 : R)`.

```lean
instance {R : Type} [Semiring R] : Decidable (IsSumSq (0 : R)) :=
  Decidable.isTrue (IsSumSq.zero)

#check IsSumSq (0 : ℤ)  -- IsSumSq 0 : Prop
#eval IsSumSq (0 : ℤ)  -- true

#eval decide (IsSumSq (0 : ℤ))  -- true

#check IsSumSq (0 : R')  -- IsSumSq 0 : Prop
-- #eval IsSumSq (0 : R')  -- (kernel) declaration has free variables '_eval'
```

We conclude this subsection by showing one advantage of making the type `R` explicit in the definition of `IsSumSqExpl`. Namely that it gives us access to the function [`Subtype`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Subtype), which creates the subtype of sums of squares from the predicate `IsSumSq R : R → Prop`.

This was not necessary earlier, due to the use of the syntax `{S : R // IsSumSq S}`, which is capable of inferring what is needed in order to construct the required type.

```lean
def SumSqType' (R : Type) [Semiring R] : Type := Subtype (IsSumSqExpl R)

#check @SumSqType'  -- SumSqType' : (R : Type) → [inst : Semiring R] → Type

#check (⟨0, IsSumSqExpl.zero⟩ : SumSqType' ℤ)
  -- { val := 0, property := (_ : IsSumSqExpl ℤ 0) } : Subtype (IsSumSqExpl ℤ)
```

## As a structure

One can also define the type of sums of squares in a semiring `R` directly, using the `structure` keyword, which creates a type. A structure is similar to an inductive type with only one constructor, but the way in which the resulting terms can be used is a bit different: a term in a structure can be projected to its various "components" (we will clarify this in the example below).

Note that the notion of [subtype]((https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Subtype) that we used [earlier](#as-a-subtype) is indeed a special kind of structure. The difference is that, for a subtype, Lean inserts a so-called [*coercion*](https://leanprover-community.github.io/mathlib4_docs/Init/Coe.html#Coercion). Namely, a term `S` of type `{x : R // IsSumSq x}` will coerce to `R` (the resulting term is then denoted by `↑S`).

This coercion is an optional design choice. It is inserted explicitly in the library at [subtypeCoe](https://leanprover-community.github.io/mathlib4_docs/Init/Coe.html#subtypeCoe). By definition (in this case), the term `↑S` is the projection of `S` to `R`, which can also be accessed using `S.val` or `S.1` (while `S.property` or `S.2` will access a proof of the proposition `IsSumSq S.val`).

Getting back to our context, given a semiring `R`, we define the type `SumsOfSquares R` to be the type whose terms consists of:

- a term `val` in `R` (a *value*) and
- a certain *property* (called `ppty`) and satisfied by this term `val`.

More precisely, the term `ppty` is of type `IsSumSq val`, i.e. it is a proof that `val : R` is a sum of squares in `R`.

Below, we essentially define by hand the same type `SumSqType R` introduced [above](#as-a-subtype) as a subtype of `R`.

```lean
structure SumsOfSquares (R : Type) [Semiring R] where
mk :: (val : R) (ppty : IsSumSq val)
```

This could be written with a `:=` instead of a `where`. Also, the `mk :: ` part is optional (`mk` stands for `make`). Indeed, the following syntax also works fine:

```lean
structure SumsOfSquares (R : Type) [Semiring R]
(val : R) (ppty : IsSumSq val)
```
As a result, we have a type `SumsOfSquares ℕ` or `SumsOfSquares ℤ`.

```lean
#check SumsOfSquares
#check SumsOfSquares ℤ
```

We also have new functions, created automatically, namely the constructor `SumsOfSquares.mk` (which is there even if `mk :: ` is not used in the declaration of the structure, but would be called `SumsOfSquares.cons` if `cons` had been used in place of `mk`.)

```lean
#check SumsOfSquares.mk
```

To give examples of terms of type `SumsOfSquares R`, we use the function `SumSq` introduced in the [Defs](Defs.md) file. By Theorem `IsSumSq_Char` (proved [here](#-using-an-existential-predicate)), this function indeed characterizes sums of squares in `R`, in the sense that we have an equivalence:

> IsSumSq S ↔ (∃ L : List R, SumSq L = S)

so the sums of squares in `R` are exactly the values of the function `SumSq`. This observation leads to the declaration of a function `SumSqList: List R → SumsOfSquares R`.

```lean
def SumSqList {R : Type} [Semiring R] (L : List R) : SumsOfSquares R := SumsOfSquares.mk (SumSq L) (SumSqListIsSumSq L)  -- ⟨SumSq L, SumSqListIsSumSq L⟩ also works

#check SumSqList [1, -2, 3]  -- SumSqList [1, -2, 3] : SumsOfSquares ℤ
```

We can then project a term `S : SumsOfSquares R` to `R` and `IsSumSq S.val`.

```lean
#check SumsOfSquares.val  -- SumsOfSquares.val {R : Type} [inst✝ : Semiring R] (self : SumsOfSquares R) : R
#check SumsOfSquares.ppty  -- SumsOfSquares.ppty {R : Type} [inst✝ : Semiring R] (self : SumsOfSquares R) : IsSumSq self.val

#check (SumSqList [1, -2, 3]).val   -- (SumSqList [1, -2, 3]).val : ℤ
#check (SumSqList [1, -2, 3]).ppty  -- (SumSqList [1, -2, 3]).ppty : IsSumSq (SumSqList [1, -2, 3]).val
```

As in the first implementation of the type of sums of squares given [above](#-as-a-subtype), we can put a `Repr` instance on the type `SumsOfSquares R`.

```lean
instance {R : Type} [Semiring R] [Repr R] : Repr (SumsOfSquares R) where
  reprPrec :=
    fun S _ =>
      repr S.val ++ " is a sum of squares because the property IsSumSq " ++ repr S.val ++ " has been proven."

-- Below, we use a Type-valued predicate (as opposed to Prop-valued)

inductive IsSumSq' {R : Type} [Semiring R] : R → Type
  | zero : IsSumSq' (0 : R)
  | add (x S : R) (hS : IsSumSq' S) : IsSumSq' (x ^ 2 + S)

structure SumsOfSquares' (R : Type) [Semiring R] where
(val : R) (ppty : IsSumSq' val)

instance {R : Type} [Semiring R] [Repr R] : Repr (SumsOfSquares' R) where
  reprPrec :=
    fun S _ =>
      repr S.val ++ " is a sum of squares because the property IsSumSq " ++ repr S.val ++ " has been proven."

def SumSqListIsSumSq' {R : Type} [Semiring R] : (L : List R) → IsSumSq' (SumSq L) := by
  intro L  -- let L be a list whose members are terms of type signature R
  induction L with  -- by induction on the list L
  | nil =>  -- the case of the empty list []
    rw [SumSq]  -- rewrite using SumSq [] = 0
    exact IsSumSq'.zero  -- IsSumSq' 0 is a proof that 0 is a sum of squares
  | cons a l ih =>  -- the case of a list L = (a :: l) where SumSq l is assumed to be a sum of squares
    rw [SumSq]  -- rewrite using SumSq (a :: l) = a ^2 + SumSq l
    exact IsSumSq'.add a (SumSq l) ih  -- conclude using the induction hypothesis and the property that, if S is a sum of squares, then x ^2 + S is a sum of squares

def SumSqList' {R : Type} [Semiring R] (L : List R) : SumsOfSquares' R :=
  ⟨SumSq L, SumSqListIsSumSq' L⟩  -- SumsOfSquares'.mk (SumSq L) (SumSqListIsSumSq' L)

instance {R : Type} [Semiring R] [Repr R] {L : List R} : Repr (IsSumSq' (SumSqList' L).val) where
 reprPrec :=
    fun _ _ =>
    "A proof of the fact that " ++ repr (SumSqList' L).val ++ " is a sum of squares is provided by applying the function SumSqListIsSumSq to the list " ++ repr L ++ ", because SumSq " ++ repr L ++ " = " ++ repr (SumSqList L).val  -- to re-examine

#check SumSqList' [1, -2, 3]
#eval SumSqList' [1, -2, 3]
#check (SumSqList' [1, -2, 3]).val
#eval (SumSqList' [1, -2, 3]).val
#check (SumSqList' [1, -2, 3]).ppty
#eval (SumSqList' [1, -2, 3]).ppty
```

We can then define terms of type `SumsOfSquares ℤ` as we did before. But note that no coercion has been inserted here (we would have to do it ourselves).

```lean
def zero_is_SOS' : SumsOfSquares ℤ := ⟨0, IsSumSq.zero⟩

#check zero_is_SOS'.1  -- zero_is_SOS'.val : ℤ
#check zero_is_SOS'.2  -- zero_is_SOS'.property : IsSumSq zero_is_SOS'.val

#eval zero_is_SOS'.1  -- 0
#eval zero_is_SOS'  -- 0 is a sum of squares because the property IsSumSq 0 has been proven.
```

We can also apply `#eval` to values of the functions `SumSqList`. But the last one gives us an error message.

```lean
#check SumSqList [1, -2, 3]
#eval SumSqList [1, -2, 3]  -- 14 is a sum of squares because the property IsSumSq 14 has been proven.
#check (SumSqList [1, -2, 3]).val  -- (SumSqList [1, -2, 3]).val : ℤ
#eval (SumSqList [1, -2, 3]).val  -- 14
#check (SumSqList [1, -2, 3]).ppty
-- #eval (SumSqList [1, -2, 3]).ppty  -- invalid universe level, 0 is not greater than 0

#reduce (SumSqList [1, -2, 3])
#reduce (SumSqList [1, -2, 3]).val
#reduce (SumSqList [1, -2, 3]).ppty
-- try to put a `Repr` instance on the type `IsSumSq (SumSq L)`?
```

Of course, this would have worked just as well with the type `SumSqType R` in place of `SumsOfSquares R`.

```lean
def SumSqListType {R : Type} [Semiring R] (L : List R) : SumSqType R := ⟨SumSq L, SumSqListIsSumSq L⟩

#check SumSqListType [1, -2, 3]
#eval SumSqListType [1, -2, 3]
#eval (SumSqListType [1, -2, 3]).val
```

Finally, we note that, if we use an inductive type with just one constructor (as opposed to a structure), the resulting data type can be used in a similar manner, but the way the terms are accessed and used is a bit different. In particular, they cannot be projected to their various components (unless one defines the projections "by hand").

```lean
inductive SumsOfSquares'' (R : Type) [Semiring R]
| mk (val : R) (ppty : IsSumSq val)

#check SumsOfSquares''
#check SumsOfSquares''.mk
#check SumsOfSquares'' ℤ

def SumSqList'' {R : Type} [Semiring R] (L : List R) : SumsOfSquares'' R := SumsOfSquares''.mk (SumSq L) (SumSqListIsSumSq L)

#check SumSqList'' [1, -2, 3]
```

The above works fine but the following command do not work (we would have to define the projections by hand):

```lean
#check (SumSqList'' [1, -2, 3]).val
#check (SumSqList'' [1, -2, 3]).ppty
```

We can still put a `Repr` instance on the type `SumsOfSquares' R`. But note that the syntax used to access the various pieces of data contained in a term `S` is different (using pattern matching instead of projecting).

```lean
instance {R : Type} [Semiring R] [Repr R] : Repr (SumsOfSquares' R) where
  reprPrec :=
    fun (SumsOfSquares'.mk val _) _ =>
      repr val ++ " is a sum of squares because the property IsSumSq " ++ repr val ++ " has been proven."

#eval SumSqList' [1, -2, 3]
```

## Exercises

### Exercise 1

Let `R` be a semiring and let `S` be a term in `R`. Prove that Proposition `IsSumSq S` is equivalent to Proposition `IsSumSq' S`, where `IsSumSq'` is the predicate defined inductively as follows:

```lean
inductive IsSumSq' {R : Type} [Semiring R] : R → Prop :=
  | sq (x : R) : IsSumSq (x ^ 2 : R)
  | add (S1 S2 : R) (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 + S2)
```

Note that this definition may be more intuitive than the one we gave in [the first section](#using-an-inductive-predicate). But it might be less convenient to work with. Indeed, when proving a statement by induction on the proof of `IsSumSq' S`, then in the first case, we would have to prove it not only for `S = 0`, but in all cases `S = x ^ 2` for some `x : R`.

### Exercise 2

Let `R` be a semiring and let `S` be a term in `R`. Write a (direct) proof of the implication

> (∃ L : List R, SumSq L = S) → IsSumSq S

and ask yourself whether having an existential quantifier in the assumption makes things complicated. Try using Lemma `SumSqListIsSumSq` and the second implication of the equivalence `IsSumSq_Char` to prove the result. You can then see that the approach there is to first prove `IsSumSq (SumSq L)` and from this deduce a proof of the implication. A formalisation of this last statement is suggested in [Exercise 3](#exercise-3).

### Exercise 3

Let `S T` be types. Let `P : T → Prop` be a predicate on `T` and let `f : S → T` be a function from `S` to `T`. Assume that the proposition `∀ x : S, P (f x)` has a proof and that the proposition `∀ y : T, ∃ x : S, y = f x` has a proof. Show that the proposition `∀ y : T, P y` has a proof.
