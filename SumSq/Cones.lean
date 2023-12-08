/-
# Precones and cones

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser.
-/

import SumSq.Defs
import SumSq.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
We defines precones, etc. and show that **in a real field (ring?)** sums of squares form a precone. CAREFUL with pre-existing notions of cone,l positive cone, etc in Mathlib

in a ring: precone, **cone**, support of a precone, support of a precone is an additive subgroup, support of a cone is an ideal, prime cones

**example: positive elements in an ordered field/ring, sums of squares in a formally real field/ring?**

**(compare all of this to positive cone in mathlib, see Leiden pdf again)**

in a field: all cones are prime

in a ring: order on precones, maximal precones are prime cones

in a field: all cones are maximal precones

in a field: **cones in F ↔ orderings on F**  -- That's until later...

in a ring: prime cones with support P in R ↔ orderings of Frac(R/P)  -- also later
-/

open Set

class Set.IsPreCone {R : Type} [Ring R] (P : Set R) : Prop where
  add : ∀ (x y : R), x ∈ P ∧ y ∈ P → x + y ∈ P
  mul : ∀ (x y : R), x ∈ P ∧ y ∈ P → x * y ∈ P
  sq : ∀ (x : R), x ^ 2 ∈ P
  minus : (-1 : R) ∉ P

-- note that the axiom -1 ∉ P does not make sense in a semiring

theorem zero_in_precone {R : Type} [Ring R]  {P : Set R} [IsPreCone P] : 0 ∈ P := by
  have aux : (0 : R) ^ 2 ∈ P := IsPreCone.sq (0 : R)
  simp at aux
  exact aux

theorem one_in_precone {R : Type} [Ring R] {P : Set R} [IsPreCone P] : 1 ∈ P := by
  have aux : (1 : R) ^ 2 ∈ P := IsPreCone.sq (1 : R)
  simp at aux
  exact aux

def supp {R : Type} [Ring R] (P : Set R) [IsPreCone P] : Set R := {x : R | x ∈ P ∧ (-x) ∈ P}

lemma zero_in_supp {R : Type} [Ring R] {P : Set R} [IsPreCone P] : 0 ∈ supp P := by
  constructor
  · exact zero_in_precone
  · simp; exact zero_in_precone

lemma PreConeInField {R : Type} [Field R] (P : Set R) [IsPreCone P] (x : R) : x ∈ P ∧ -x ∈ P → x = 0 := by
  intro ⟨h1, h2⟩
  by_contra hx
  suffices new : -1 ∈ P
  · exact IsPreCone.minus new
  · have aux1 : x * (-x) ∈ P := by
      apply IsPreCone.mul _ _
      exact ⟨h1, h2⟩
    ring_nf at aux1
    have aux2 : (1 / x) ^ 2 ∈ P := by
      apply IsPreCone.sq
    ring_nf at aux2
    have aux3 : -x ^ 2 * x⁻¹ ^ 2 ∈ P := by
      apply IsPreCone.mul _ _
      exact ⟨aux1, aux2⟩
    field_simp at aux3
    exact aux3

theorem SuppPreConeInField {R : Type} [Field R] (P : Set R) [IsPreCone P] : supp P = {0} := by
  ext x; simp
  constructor
  · intro h
    exact PreConeInField P x h
  · intro h
    rw [h]
    exact zero_in_supp

def PreConeAddElem {R : Type} [Ring R] (P : Set R) (a : R) : Set R :=
{z : R | ∃ x ∈ P, ∃ y ∈ P, z = x + a * y}

notation:max P"["a"]" => PreConeAddElem P a

lemma PreConeInPreConeAddElem {R : Type} [Ring R] (P : Set R) [IsPreCone P] (a : R) : P ≤ P[a] := by
  intro x hx
  use x; constructor; swap
  use 0; constructor; exact zero_in_precone
  simp
  exact hx

theorem PreConeAddElemIsPreCone {R : Type} [Ring R] (P : Set R) [IsPreCone P] (a : R) (ha : -a ∉ P) : IsPreCone P[a] := by
  constructor
  · intro x y h
    rcases h with ⟨hx, hy⟩
    rcases hx with ⟨u, hu, v, hv, hx⟩
    rcases hy with ⟨p, hp, q, hq, hy⟩
    have aux : u + a * v + (p + a * q) = (u + p) + a * (v + q) := by
      rw [add_assoc, ← add_assoc _ p _, add_assoc u _ _, add_comm _ p, mul_add, add_assoc p _ _]
    rw [hx, hy, aux]
    have hup : u + p ∈ P := by
      apply IsPreCone.add
      exact ⟨hu, hp⟩
    have hvq : v + q ∈ P := by
      apply IsPreCone.add
      exact ⟨hv, hq⟩
    use u + p
    constructor
    swap
    use v + q
    assumption
  · intro x y h
    rcases h with ⟨hx, hy⟩
    rcases hx with ⟨u, hu, v, hv, hx⟩
    rcases hy with ⟨p, hp, q, hq, hy⟩
    rw [hx, hy]
    have aux : (u + a * v) * (p + a * q) = (u * p + a ^ 2 * (v * q)) +  a * (u * q + v * p) := sorry
    rw [aux]
    use u * p + a ^ 2 * (v * q); constructor; swap
    use u * q + v * p; constructor; swap
    · rw [← aux]
    · apply IsPreCone.add
      constructor
      · apply IsPreCone.mul; exact ⟨hu, hq⟩
      · apply IsPreCone.mul; exact ⟨hv, hp⟩
    · apply IsPreCone.add
      constructor
      · apply IsPreCone.mul; exact ⟨hu, hp⟩
      · apply IsPreCone.mul
        constructor
        · exact IsPreCone.sq a
        · apply IsPreCone.mul; exact ⟨hv, hq⟩
  · intro x
    have aux : x ^ 2 ∈ P := IsPreCone.sq x
    apply PreConeInPreConeAddElem
    exact aux
  · by_contra aux
    apply ha
    rcases aux with ⟨x, hx, y, hy, h⟩
    sorry

class Set.IsConeTemp {R : Type} [Ring R] (P : Set R) : Prop where
  pre : IsPreCone P
  tot : ∀ x : R, x ∈ P ∨ -x ∈ P

-- need to register a IsPreCone intance on IsCone manually? does it even make sense?

class Set.IsCone {R : Type} [Ring R] (P : Set R) : Prop where
  zero : 0 ∈ P
  -- add : ∀ (x y : R), x ∈ P ∧ y ∈ P → x + y ∈ P
  -- mul : ∀ (x y : R), x ∈ P ∧ y ∈ P → x * y ∈ P
  -- sq : ∀ (x : R), x ^ 2 ∈ P
  -- minus : -1 ∉ P
  -- etc

-- this has the desired behaviour (in particular, `IsCone (SumSqSet ℤ)` is recognized as a term of type Prop)


#check @IsCone
#check IsCone (SumSqSet ℤ)
#check (SumSqSet ℤ).IsCone


-- we put a cone instance on the set of sums of squares in a (semi)ring R; now everything we prove about cones will be true for the set of sums of squares? (which would not be true if we declared a theorem instead of an instance?) -- NEED AN EXAMPLE OF THIS See below :-)
-- Note: the same procedure but with structure instead of class generates a non-class instance error report in lint

instance SumSqCone {R : Type} [Ring R] : IsCone (SumSqSet R) := ⟨zeroIsSumSq⟩
-- by {constructor; exact zeroIsSumSq}

-- the term defined in SumSqCone is a proof of the fact that SumSqSet R is a cone in R

#check SumSqCone

-- Can also do the following for the proof of the above:
-- by {constructor; exact IsSumSq.zero}
-- the point is that the constructor tactic works well and should be helpful when there are more properties to prove, or a difficult one

-- now we define the type of cones in a (semir)ring R

def Cone (R : Type) [Ring R] : Type := {P : Set R // IsCone P}

#check @Cone

-- we define a membership instance for cones (we could have done this for the type of sum of squares! Then the set of sum of squares becomes less useful? we do use it in the example below, though...)

instance (R : Type) [Ring R] : Membership R (Cone R) where
  mem x P := x ∈ P.val

-- we illustrate how a property true for all cones can be deduced for the cone of sums of squares by instantion (would be better with a more intersting property...)

lemma zeroInCone {R : Type} [Ring R] (P : Cone R) : 0 ∈ P := P.property.zero

example : 0 ∈ SumSqSet ℤ := by
  -- let aux : Cone ℤ := ⟨SumSqSet ℤ, inferInstance⟩
  -- exact zeroInCone aux
  exact zeroInCone ⟨SumSqSet ℤ, inferInstance⟩

-- Note that ⟨SumSqSet ℤ, inferInstance⟩ ceases to work (with inferInstance) if we replace SumSqSet ℤ by IsSumSq or IsSumSqExpl ℤ, or setOf IsSumSq (ℤ). This is probably due to the way we have done things, but it is still interesting.

-- A variant of the lemma above (with P instantiated as a cone, as opposed to being of type Cone R)

lemma zeroInCone' {R : Type} [Ring R] (P : Set R) [IsCone P] : 0 ∈ P := IsCone.zero

-- then the example still  works, but in a different, maybe better way?

example : 0 ∈ SumSqSet ℤ := by
  apply zeroInCone'
  -- exact zeroInCone' (SumSqSet ℤ) -- is a variant of the apply tactic
  -- Note: exact zeroInCone' ⟨SumSqSet ℤ, inferInstance⟩ does not work

-- this suggests that declaring Cone as a type is not absolutely necessary (however, it is convenient; for example in order to register a membership instance, which is in fact used in the statement of the variant lemma... showing that it is useful to define the type of cones and that also that when we instantiate IsCone P in a declaration, then the membership instance registred on P is recognized automatically).

-- we could also have incorporated P in the def of the class IsCone. This time, it produces a type of Sort 1 (because Set R is of Sort 1).

class Cone' (R : Type) [Ring R] :=
  P : Set R
  zero : 0 ∈ P
  -- add : ∀ (x y : R), x ∈ P ∧ y ∈ P → x + y ∈ P
  -- etc

#check @Cone'
#check Cone'.P
#check Cone'.zero

-- in this case, the instance Cone' R is registered differently, the issue being that there is no reference to sums of squares in the statement... (only in the proof itself)

instance SumSqCone' (R : Type) [Ring R] : Cone' R := ⟨IsSumSq, IsSumSq.zero⟩

-- and the term produced in this way is of type Cone' R, which is of type Type

#check SumSqCone'

#lint

-- NEXT TASK: ordering on the "set" of cones, lattice structure?

/-!
**ANOTHER FILE: Formally real**

semireal ring if -1 is not a sum of squares *see Zulip discussion about semirings again*

real ring if sum of squares = 0 implies all terms are 0

for fields, the two are equivalent


the characteristic of a (semi?)real ring is 0

**Artin-Schreier theory**

example of a formally real field: ordered field

-> study the converse

**Real-closed fields**

characterisation

existence and uniqueness of the real closure of an ordered field

**NEXT: ideals (towards real Nullstellensatz)**

real ideals (in rings...)

**NEXT: real spectrum**

definition (as set of prime cones), topology, structure sheaf

example: `Spr R[T]`

map to the Zariski spectrum
-/



-- Other things we can prove: S is a sum of squares iff it lies in the submonoid generated by the squares... (in particular, the squares are sums of squares...) and this is equivalent to the existence of a list such that S is the sum of the squares of the entries of the list. **GOES INTO FILE ABOUT CONES?**
