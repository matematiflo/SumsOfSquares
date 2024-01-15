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

-- Declaring `IsPreCone` as `Set.IsPreCone` enables one to use the syntax `P.IsPreCone` for `Set.IsPreCone P` if `P` is a set (i.e. a  predicate on some type `R`).

structure Set.IsPreCone {R : Type} [Ring R] (P : Set R) : Prop where
  add : ∀ (x y : R), x ∈ P ∧ y ∈ P → x + y ∈ P
  mul : ∀ (x y : R), x ∈ P ∧ y ∈ P → x * y ∈ P
  sq : ∀ (x : R), x ^ 2 ∈ P
  minus : (-1 : R) ∉ P

-- note that the axiom -1 ∉ P does not make sense in a semiring

#check {x : ℤ | x = 0}.IsPreCone

-- The command `open Set` enables one to use just use `IsPreCone` in order to call the function Set.IsPreCone

open Set

#check IsPreCone
#check IsPreCone.sq

-- Comparing the above with the file were `Set.IsPreCone` is define as a class, we see that the function `Set.IsPreCone` is of the same type in both cases. **But** the function `IsPreCone.sq` is **not**. When using a class, it takes `P.IsPreCone` as a class instance (overloaded function), while when using structure, it takes it as a parameter. This has consequences in the way some proofs are written, even basic ones such as `zero_in_precone`. And there we see that the definition using `structure` is better, because we can just project our precone to the term `aux := IsPreCone.sq hP (0 : R)` *without having to specify the type of the latter*.

-- On the other hand, the proof that a certain set is a precone can be written in the same way, using the `constructor` tactic, regardless of whether we use the a class or a structure.

-- parameters: we have variable parameters, implicit parameters and instance parameters

example : {S : ℤ | IsSumSq S}.IsPreCone := by {
  constructor
  pick_goal 3
  · intro x
    simp
    sorry
  · sorry
  · sorry
  · sorry
}

theorem zero_in_precone {R : Type} [Ring R] {P : Set R} (hP : IsPreCone P) : 0 ∈ P := by
  have aux := IsPreCone.sq hP (0 : R)
  simp at aux
  exact aux

theorem one_in_precone {R : Type} [Ring R] {P : Set R} (hP : P.IsPreCone) : 1 ∈ P := by
  have aux : (1 : R) ^ 2 ∈ P := IsPreCone.sq hP (1 : R)
  simp at aux
  exact aux

-- def supp {R : Type} [Ring R] (P : Set R) : Set R := {x : R | x ∈ P ∧ (-x) ∈ P}

-- The `supp` function above is not constrained enough (we are not restricting ourselves to support of *precones*). There should be a `supp` class and we should instantiate the type of precones (which we have not defined... how should we do it?) by saying what the support *of a precone* is.


def PreConeIn (R : Type) [Ring R] : Type := {P : Set R // P.IsPreCone}

instance {R : Type} [Ring R] : Membership R (PreConeIn R) where
  mem x P := x ∈ P.val

class support (α : Type) (β : Type) : Type where
  supp (a : α) : Set β

#check support.supp

instance {R : Type} [Ring R] : support (PreConeIn R) R where
  supp P := {x : R | x ∈ P ∧ (-x) ∈ P}

def supp {α : Type} {β : Type} [support α β] (a : α) : Set β := support.supp a

-- instance (R : Type) [Ring R] : Membership R (support (PreConeIn R) R)where
--   mem x S := x ∈ supp S

#check @supp

lemma zero_in_supp {R : Type} [Ring R] (P : PreConeIn R) : (0 : R) ∈ supp P := by
  constructor
  · exact zero_in_precone P.prop
  · simp; exact zero_in_precone P.prop

lemma PreConeInField {R : Type} [Field R] {P : PreConeIn R} {x : R} : x ∈ P ∧ -x ∈ P → x = 0 := by {
  intro ⟨h1, h2⟩
  by_contra hx
  suffices aux : -1 ∈ P
  · apply IsPreCone.minus P.prop aux
  · have aux1 : x * (-x) ∈ P := by {apply IsPreCone.mul P.prop _ _ ⟨h1, h2⟩}
    ring_nf at aux1
    have aux2 : (1 / x) ^ 2 ∈ P := by {apply IsPreCone.sq P.prop}
    ring_nf at aux2
    have aux3 : -x ^ 2 * x⁻¹ ^ 2 ∈ P := by {apply IsPreCone.mul P.prop _ _ ⟨aux1, aux2⟩}
    field_simp at aux3
    exact aux3
}

theorem SuppPreConeInField {R : Type} [Field R] (P : PreConeIn R) : supp P = {(0 : R)} := by {
  ext x; simp
  constructor
  · intro h
    apply PreConeInField h
  · intro h
    rw [h]
    apply zero_in_supp P
}

def PreConeAddElem {R : Type} [Ring R] (P : Set R) (a : R) : Set R :=
{z : R | ∃ x ∈ P, ∃ y ∈ P, z = x + a * y}

notation:max P"["a"]" => PreConeAddElem P a

lemma PreConeInPreConeAddElem {R : Type} [Ring R] (P : Set R) (hP : P.IsPreCone) (a : R) : P ≤ P[a] := by
  intro x hx
  use x; constructor; swap
  use 0; constructor; exact zero_in_precone hP
  simp
  exact hx

theorem PreConeAddElemIsPreCone {R : Type} [Field R] (P : PreConeIn R) (a : R) (ha : -a ∉ P) : IsPreCone P[a] := by
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
    rcases aux with ⟨x, hx, y, hy, h⟩
    by_cases hy' : y = 0
    · suffices aux : (-1 ∈ P) from IsPreCone.minus aux
      simp [hy'] at h
      rw [← h] at hx
      exact hx
    · apply ha
      push_neg at hy'
      have aux : -a = (1 + x) * y * (1 / y) ^ 2 :=
      by
        field_simp
        have aux1 : -1 = x + a * y → -y = x * y + a * y ^ 2 := by
          intro h
          rw [neg_eq_neg_one_mul, h]
          ring
        have aux2 : -y = x * y + a * y ^ 2 → (1 + x) * y = -(a * y ^ 2) := by
          intro aux'
          ring_nf at aux'
          ring_nf
          rw [neg_eq_neg_one_mul, neg_mul, mul_comm, ← mul_neg] at aux'
          simp at aux'
          sorry
        have aux3 : -y = x * y + a * y ^ 2 := aux1 h
        have aux4 := aux2 aux3
        rw [aux4]
      rw [aux]
      apply IsPreCone.mul
      constructor
      · apply IsPreCone.mul
        constructor
        · apply IsPreCone.add
          exact ⟨one_in_precone, hx⟩
        · exact hy
      · apply IsPreCone.sq

structure Set.IsConeTemp {R : Type} [Ring R] (P : Set R) : Prop where
  pre : P.IsPreCone
  tot : ∀ x : R, x ∈ P ∨ -x ∈ P

-- need to register a IsPreCone intance on IsCone manually? is it possible? does it even make sense?

structure Set.IsCone {R : Type} [Ring R] (P : Set R) : Prop where
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

instance SumSqCone {R : Type} [Ring R] : (SumSqSet R).IsCone := ⟨zeroIsSumSq⟩
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
  exact zeroInCone ⟨SumSqSet ℤ, SumSqCone⟩

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
