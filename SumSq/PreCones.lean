/-
# PreCones

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser.
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Set

/-- A precone `P` in a ring `R` is a term `P : Set R` satisfying the properties listed below, in the structure `Set.isPreCone`. Note that the axiom `-1 ∉ P` does not make sense in a semiring.-/
structure Set.isPreCone {R : Type} [Ring R] (P : Set R) : Prop :=
add   : ∀ {x y : R}, x ∈ P ∧ y ∈ P → x + y ∈ P
mul   : ∀ {x y : R}, x ∈ P ∧ y ∈ P → x * y ∈ P
sq    : ∀ {x : R}, x ^ 2 ∈ P
minus : (-1 : R) ∉ P

/-- We define the type of precones in a ring as a structure. -/
structure PreConeIn (R : Type) [Ring R] : Type :=
/-- Precones in R are dependent pairs consisting of a term `P : Set R` and a proof of the property `P.isPreCone`. -/
carrier  : Set R
ppty     : carrier.isPreCone

instance (R : Type) [Ring R] : Membership R (PreConeIn R) where
mem x P := x ∈ P.carrier

theorem zero_in_precone {R : Type} [Ring R] {P : Set R} (hP : P.isPreCone) : 0 ∈ P := by
have aux : (0 : R) ^ 2 ∈ P := isPreCone.sq hP
simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at aux
exact aux

theorem one_in_precone {R : Type} [Ring R] {P : Set R} (hP : P.isPreCone) : 1 ∈ P := by
have aux : (1 : R) ^ 2 ∈ P := isPreCone.sq hP
simp only [one_pow] at aux
exact aux

/- Next, we put an ordering on the type of precones in a ring. -/
instance (R : Type) [Ring R] : LE (PreConeIn R) where
le P Q := P.carrier ⊆ Q.carrier

/-- Given `P : Set R` and `a : R`, we construct inductively a set `addElem P a`. When `P` is a precone, the set `addElem P a` contains `P` and `a`. -/
inductive addElem {R : Type} [Ring R] (P : Set R) (a : R) : Set R :=
| intro (x y z : R) (hx : x ∈ P) (hy : y ∈ P) (hz : z = x + a * y) : addElem P a z

/-- The notation for the set `addElem P a`. -/
notation:max P"["a"]" => addElem P a

theorem addElemSet {R : Type} [Ring R] (P : Set R) (a : R) : P[a] = {z : R | ∃ x ∈ P, ∃ y ∈ P, z = x + a * y} := by
ext u
apply Iff.intro
· intro hu
  rcases hu with ⟨x, y, u, hx, hy, hu⟩
  apply Exists.intro x
  apply And.intro
  · exact hx
  · apply Exists.intro y
    exact And.intro hy hu
· intro hu
  rcases hu with ⟨x, hx, y, hy, hu⟩
  exact addElem.intro x y u hx hy hu

theorem addElem.inclusion {R : Type} [Ring R] (P : Set R) (a : R) (hP : P.isPreCone) : P ⊆ P[a] := by
intro x hx
have aux : x = x + a * 0 := by rw [mul_zero, add_zero]
exact addElem.intro x 0 x hx (zero_in_precone hP) aux

lemma addElemToPreCone.add {R : Type} [Ring R] (P : Set R) (a : R) (hP : P.isPreCone) : ∀ {x y : R}, x ∈ P[a] ∧ y ∈ P[a] → x + y ∈ P[a] := by
intro x y ⟨hx, hy⟩
rcases hx with ⟨u, v, x, hu, hv, hx⟩
rcases hy with ⟨p, q, y, hp, hq, hy⟩
rw [hx, hy]
apply addElem.intro (u + p) (v + q) ((u + a * v) + (p + a * q))
· exact isPreCone.add hP ⟨hu, hp⟩
· exact isPreCone.add hP ⟨hv, hq⟩
· rw [add_assoc, ← add_assoc _ p _, add_assoc u _ _, add_comm _ p, mul_add, add_assoc p _ _] -- this identity holds in a non-necessarily commutative ring; in a commutative ring, the `ring` tactic closes the goal

lemma addElemToPreCone.mul {R : Type} [CommRing R] (P : Set R) (a : R) (hP : P.isPreCone) : ∀ {x y : R}, x ∈ P[a] ∧ y ∈ P[a] → x * y ∈ P[a] := by
intro x y ⟨hx, hy⟩
rcases hx with ⟨u, v, x, hu, hv, hx⟩
rcases hy with ⟨p, q, y, hp, hq, hy⟩
rw [hx, hy]
have aux : (u + a * v) * (p + a * q) = (u * p + a ^ 2 * (v * q)) +  a * (u * q + v * p) := by ring_nf
apply addElem.intro (u * p + a ^ 2 * (v * q)) ((u * q + v * p)) ((u + a * v) * (p + a * q))  --(u * p + a ^ 2 * (v * q) +  a * (u * q + v * p)) rfl
· apply isPreCone.add hP
  apply And.intro
  · exact isPreCone.mul hP ⟨hu, hp⟩
  · apply isPreCone.mul hP
    apply And.intro
    · exact isPreCone.sq hP
    · exact isPreCone.mul hP ⟨hv, hq⟩
· apply isPreCone.add hP
  apply And.intro
  · exact isPreCone.mul hP ⟨hu, hq⟩
  · exact isPreCone.mul hP ⟨hv, hp⟩
· exact aux

lemma addElemToPreCone.sq  {R : Type} [Ring R] (P : Set R) (a : R) (hP : P.isPreCone) : ∀ {x : R}, x ^ 2 ∈ P[a] := by
intro x
apply addElem.inclusion P a hP
exact isPreCone.sq hP

lemma addElemToPreCone.minus {R : Type} [Field R] (P : Set R) (a : R) (hP : P.isPreCone) (ha : -a ∉ P) : -1 ∉ P[a] := by
intro h
rcases h with ⟨x, y, z, hx, hy, hz⟩
have hy' : y ≠ 0 := by
  intro h
  apply isPreCone.minus hP
  rw [h, mul_zero, add_zero] at hz
  rw [←hz] at hx
  exact hx
apply ha
have aux1 : -a = x * y * (1 / y) ^ 2 + y * (1 / y) ^ 2 := by
  field_simp
  have aux2 : -(a * y) = 1 + x := by
    have aux3 : (-1) * (-1) = (-1) * (x + a * y) := by
      exact congrArg (fun t => (-1) * t) hz
    simp only [mul_neg, mul_one, neg_neg, neg_mul, one_mul, neg_add_rev] at aux3
    rw [aux3]
    ring
  have aux3 : -(a * y) * y = (1 + x) * y := by
    exact congrArg (fun t => t * y) aux2
  ring_nf at aux3
  rw [aux3]
  ring_nf
rw [aux1]
apply isPreCone.add hP
apply And.intro
· apply isPreCone.mul hP
  apply And.intro
  · exact isPreCone.mul hP ⟨hx, hy⟩
  · exact isPreCone.sq hP
· apply isPreCone.mul hP
  apply And.intro
  · exact hy
  · exact isPreCone.sq hP

theorem addElemToPreCone {R : Type} [Field R] (P : Set R) (a : R) (ha : -a ∉ P) : P.isPreCone → P[a].isPreCone := by
intro hP
apply isPreCone.mk
· case add   := addElemToPreCone.add P a hP
· case mul   := addElemToPreCone.mul P a hP
· case sq    := addElemToPreCone.sq P a hP
· case minus := addElemToPreCone.minus P a hP ha
