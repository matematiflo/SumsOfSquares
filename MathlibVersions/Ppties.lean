/-
# Sums of squares - Basic properties

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser
-/

import MathlibVersions.Defs
import Mathlib.Data.List.Perm

namespace MathlibSumSq

universe u
variable {R : Type u}

theorem SumSqAppend [Semiring R] (L1 L2 : List R) : SumSq (L1 ++ L2) = SumSq L1 + SumSq L2 := by
  induction L1 with
  | nil =>  simp [SumSq]
  | cons a L ih => simp [SumSq]; rw[ih, add_assoc]

-- A sum of squares is invariant under permutations: `L1 ~ L2 → SumSq L1 = SumSq L2`.
theorem SumSq_permut {R : Type} [AddCommMonoid R] [Pow R ℕ] {L1 L2 : List R} (H : L1 ~ L2) : SumSq L1 = SumSq L2 := by
  induction H with
  | nil => rfl
  | cons x _ Sum12 => simp [SumSq, Sum12]
  | swap x y l => simp [SumSq]; rw [← add_assoc, ← add_assoc, add_comm (y ^ 2) (x ^ 2)]
  | trans L1 L2 Sum1 Sum2 => rw [Sum1, Sum2]

-- `a ∈ L → SumSq L = a ^ 2 + SumSq (L.erase a)`
theorem SumSq_erase {R : Type} [AddCommMonoid R] [Pow R ℕ] [DecidableEq R] (L : List R) (a : R) (h : a ∈ L) : SumSq L = a ^ 2 + SumSq (L.erase a) := by
  simp [SumSq_permut (L.perm_cons_erase h), SumSq]

end MathlibSumSq
