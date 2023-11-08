/-
# Sums of squares - Definitions and examples

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.List.BigOperators.Basic
import Mathlib.Data.Rat.Defs

-- Some things should be added to `simp`, it will make the proofs shorter

namespace MathlibSumSq2

universe u
variable {R : Type u}

-- Given a type `R` with an addition map, a zero and powers by a natural number, we define a sum-of-squares function on `List R`.
@[simp]
def SumSq [Add R] [Zero R] [Pow R ℕ] : List R → R
  | [] => 0
  | a :: l => a ^ 2 + SumSq l

-- Tail-recursive version of `List.SumSq`.
def SumSqAux [Add R] [Pow R ℕ] : R → List R → R
  | SoFar, [] => SoFar
  | SoFar, (a :: l) => SumSqAux (SoFar + a ^ 2) l

@[simp]
def SumSqTR [Add R] [Zero R] [Pow R ℕ] : List R → R
  | L => SumSqAux 0 L

-- The following property holds by definition. It will be used in the proof of the equality `SumSqTR L = SumSq L`.
@[simp]
theorem SumSqAuxZero [Add R] [Zero R] [Pow R ℕ] (L : List R) : SumSqAux 0 L = SumSqAux (SumSq []) L := by rfl

/-
We now want to prove that the tail-recursuve definition agree with the original one: `∀ L : List R, SumSqTR L = SumSq L`. The key is that, when `S = SumSq L2`, the term  `SumSqAux S L1` can be computed in terms of `SumSq L1` and `SumSq L2`.
-/
theorem SumSqAuxWithSumSq [AddCommMonoid R] [Pow R ℕ] (L1 : List R) : ∀ L2 : List R, SumSqAux (SumSq L2) L1  = SumSq L2 + SumSq L1 := by
  induction L1 with
  | nil => simp [SumSqAux]
  | cons a l1 ih => intro L; simp [SumSqAux]; rw [add_comm _ (a ^2), ← SumSq,ih (a :: L), SumSq, add_comm (a ^ 2) _, add_assoc]

-- We can now prove that `SumSqTR L = SumSq L`.
lemma SumSqAuxEmptyList [AddCommMonoid R] [Pow R ℕ] (L : List R) : SumSqAux (SumSq []) L= SumSqAux (SumSq L) [] := by rw [SumSqAuxWithSumSq]; simp [SumSqAux]

theorem def_TR_ok [AddCommMonoid R] [Pow R ℕ] (L : List R) : SumSqTR L = SumSq L := by simp [SumSqAuxEmptyList, SumSqAux]

-- A sum-of-squares function on `List R` can also be defined as the composition of the function `L => (L.map (. ^ 2))` with `L => L.sum`. We show that the two definitions agree.
theorem squaring_and_summing [AddCommMonoid R] [Pow R ℕ] (L : List R) : SumSq L = (L.map (. ^ 2)).sum := by
  induction L with
  | nil => rfl
  | cons a l ih => simp [ih]

end MathlibSumSq2

#lint
