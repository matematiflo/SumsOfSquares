/-
# Sums of squares - Definitions and examples

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.List.BigOperators.Basic
import Mathlib.Data.Rat.Defs

-- Given a semiring `R`, we define a sum-of-squares function on `List R`.
def SumSq {R : Type} [Semiring R] : List R → R
  | [] => 0
  | a :: l => a ^ 2 + SumSq l

-- Tail-recursive version of `List.SumSq`.
def SumSqAux [Semiring R] : R → List R → R
  | SoFar, [] => SoFar
  | SoFar, (a :: l) => SumSqAux (SoFar + a ^ 2) l
def SumSqTR [Semiring R] : List R → R
  | L => SumSqAux 0 L

-- The following property holds by definition. It will be used in the proof of the equality `SumSqTR L = SumSq L`.
theorem SumSqAuxZero [Semiring R] (L : List R) : SumSqAux 0 L = SumSqAux (SumSq []) L := by rfl

/-
We now want to prove that the tail-recursuve definition agree with the original one: `∀ L : List R, SumSqTR L = SumSq L`.

The key is that, when `S = SumSq L2`, the term  `SumSqAux S L1` can be computed in terms of `SumSq L1` and `SumSq L2`.
-/
theorem SumSqAuxWithSumSq [Semiring R] (L1 : List R) : ∀ L2 : List R, SumSqAux (SumSq L2) L1  = SumSq L2 + SumSq L1 := by
  induction L1 with
  | nil => simp [SumSqAux, SumSq]
  | cons a l1 ih => intro L; rw [SumSq, SumSqAux, add_comm _ (a ^2), ← SumSq,ih (a :: L), SumSq, add_comm (a ^ 2) _, add_assoc]

-- We can now prove that `SumSqTR L = SumSq L`.
lemma SumSqAuxEmptyList [Semiring R] (L : List R) : SumSqAux (SumSq []) L= SumSqAux (SumSq L) [] := by simp [SumSqAuxWithSumSq]; simp [SumSq]
theorem def_TR_ok [Semiring R] (L : List R) : SumSqTR L = SumSq L := by
  simp [SumSqTR, SumSqAuxZero, SumSqAuxEmptyList, SumSqAux]

-- A sum-of-squares function on `List R` can also be defined as the composition of the function `L => (L.map (. ^ 2))` with `L => L.sum`. We show that the two definitions agree.
theorem squaring_and_summing2 [Semiring R] (L : List R) : SumSq L = (L.map (. ^ 2)).sum := by
  induction L with
  | nil => rfl
  | cons a l ih => simp [SumSq,ih]
