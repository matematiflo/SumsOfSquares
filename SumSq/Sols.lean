/-
# Sums of squares - Solutions to the exercises

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser.
-/

import SumSq.Defs

/-!
## SumSq.Props

### Props.1

### Props.2

## [SumSq.Basic](Basic.md)

### Basic.1

### Basic.2

### [Basic.3](Basic.md#exercise-3)
-/

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
