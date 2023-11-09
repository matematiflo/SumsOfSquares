# Sums of squares - Definitions and examples

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser.

```lean
import SumSq.Defs
import Mathlib.Algebra.GroupPower.Basic
```

We defines precones, etc. and show that sums of squares form a precone (check again)).

ANOTHER FILE:

semireal ring if -1 is not a sum of squares

real ring if sum of squares = 0 implies all terms are 0

for fields, the two are equivalent

the characteristic of a (semi?)real ring is 0

NEXT FILE:

in **rings**: def of precones, cones, examples, support of a cone , prime cone (compare all of this to positive cone in mathlib, see Leiden pdf again)

NEXT:

real ideals (in rings...)

## Being a sum of squares (inductive)

Let us write an inductive definition of what it means to be a sum of squares.

```lean
inductive ind_sum_of_squares [Semiring R] : R → Prop :=
    | zero : ind_sum_of_squares (0 : R)
    | add (a S : R) (hS : ind_sum_of_squares S) : ind_sum_of_squares (a ^ 2 + S)

lemma ind_zero_is_sum_of_squares : ind_sum_of_squares 0
  := by
    exact ind_sum_of_squares.zero
    done

lemma ind_one_is_sum_of_squares : ind_sum_of_squares 1
  := by
    have aux : 1 = (1 ^ 2 + 0) := by rfl
    rw [aux]
    exact ind_sum_of_squares.add 1 0 ind_sum_of_squares.zero
    done

lemma ind_squares_are_sums_of_squares  {R : Type} [Semiring R] (x : R) : ind_sum_of_squares (x ^ 2)
  := by
    rw [← add_zero (x ^2)]
    exact ind_sum_of_squares.add x 0 ind_sum_of_squares.zero
    done

theorem ind_sum_of_squares_from_sum {R : Type} [Semiring R] {S1 S2 : R} (h1 : ind_sum_of_squares S1) (h2 : ind_sum_of_squares S2) : ind_sum_of_squares (S1 + S2)
  := by
    induction h1 with
      | zero =>
        simp
        exact h2
      | add a S hS ih =>
        rw [add_assoc]
        exact ind_sum_of_squares.add a (S + S2) ih
    done

lemma ind_mul_by_sq_sum_of_squares {R : Type} [CommSemiring R] {S : R} (h : ind_sum_of_squares S) (x : R) : ind_sum_of_squares (x ^2 * S)
  := by
    induction h with
    | zero =>
    rw [mul_zero]
    exact ind_sum_of_squares.zero
    |add a s _ ih =>
    rw [mul_add, ← mul_pow x a 2]
    exact ind_sum_of_squares.add (x * a) (x ^ 2 * s) ih
    done

theorem ind_sum_of_squares_from_mul {R : Type} [CommSemiring R] {S1 S2 : R} (h1 : ind_sum_of_squares S1) (h2 : ind_sum_of_squares S2) : ind_sum_of_squares (S1 * S2)
  := by
    induction h1 with
    | zero =>
      rw [zero_mul]
      exact ind_sum_of_squares.zero
    | add a S hS ih =>
      rw [add_mul]
      apply ind_sum_of_squares_from_sum _ _
      · exact ind_mul_by_sq_sum_of_squares h2 _
      · exact ih
    done
```

## Being a sum of squares (existential)

If `R` is a semiring, we can define what it means for a term `x` of type `R` to be a sum of squares.

The definition means that `x : R` is a sum of squares if we can prove that there exists a list `L : List R` such that the sum of squares of members of that list is equal to `x`.

```lean
def is_sum_of_squares {R : Type} [Semiring R] (x : R) : Prop := ∃ L : List R, SumSq L = x
```

The inductive definition is very convenient in order to write proofs of certain basic facts (by induction!). For instance, we have proven in this way that the sum `S1 + S2` and the product `S1 * S2` of two sums of squares `S1` and `S2` are again sums of squares.

Now we want to check that the [inductive definition](#being-a-sum-of-squares-inductive) coincides with the [existential definition](#being-a-sum-of-squares-existential).

```lean
lemma exist_to_ind {R : Type} [Semiring R] (S : R) (H : is_sum_of_squares S) : ind_sum_of_squares S
  := by
    rcases H with ⟨L, hL⟩
    induction L generalizing S with
    | nil =>
      simp [SumSq] at hL
      rw [← hL]
      exact ind_sum_of_squares.zero
    | cons a L ih =>
      rw [← hL]
      simp [SumSq]
      specialize ih (SumSq L) (Eq.refl (SumSq L))
      exact ind_sum_of_squares.add a (SumSq L) ih
    done

lemma ind_to_exist {R : Type} [Semiring R] (S : R) (H : ind_sum_of_squares S) : is_sum_of_squares S
  := by
    simp [is_sum_of_squares]
    induction H with
    | zero =>
      use []
      rfl
    | add a S' _ ih =>
      rcases ih with ⟨L', hL'⟩
      rw [← hL']
      use (a :: L')
      rfl
    done

theorem equiv_defs {R : Type} [Semiring R] (S : R) : is_sum_of_squares S ↔ ind_sum_of_squares S
  := by
    constructor
    · apply exist_to_ind
    · apply ind_to_exist
    done
```
