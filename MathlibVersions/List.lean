/-
# Sums of squares - Definitions and examples

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser.
-/

-- WORK IN PROGRESS (REVOIR SI LES TRUCS IMPORTÉS SONT LES BONS)

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.List.BigOperators.Basic

def SumSq {R : Type} [Add R] [Zero R] [Pow R ℕ] : (List R → R)
  | [] => 0
  | a :: l => a ^ 2 + SumSq l

theorem SumSqAppend [AddMonoid R] [Pow R ℕ] (L1 L2 : List R) : SumSq (L1 ++ L2) = SumSq L1 + SumSq L2 := by
  induction L1 with
  | nil => simp [SumSq]
  | cons a L ih =>
    simp [SumSq]
    rw [ih, add_assoc]

theorem SumSqAppend' [AddMonoid R] [Pow R ℕ] (L1 L2 : List R) : SumSq (L1.append L2) = SumSq L1 + SumSq L2 := by
  induction L1 with
  | nil => simp [SumSq]
  | cons a L ih =>
    simp [SumSq]
    dsimp at ih
    simp [ih]
    rw [add_assoc]

theorem SumAppend [AddMonoid R] (L1 L2 : List R) : (L1 ++ L2).sum = L1.sum + L2.sum := by
  induction L1 with
  | nil => simp
  | cons a L ih =>
    simp [ih]
    rw [add_assoc]

theorem SumAppend' [AddMonoid R] (L1 L2 : List R) : (L1.append L2).sum = L1.sum + L2.sum := by
  induction L1 with
  | nil => simp
  | cons a L ih =>
    simp [ih]
    rw [add_assoc]
