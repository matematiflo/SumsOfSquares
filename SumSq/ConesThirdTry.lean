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

structure PreConeIn (R : Type) [Ring R] : Type where
  carrier : Set R
  add : ∀ (x y : R), x ∈ carrier ∧ y ∈ carrier → x + y ∈ carrier
  mul : ∀ (x y : R), x ∈ carrier ∧ y ∈ carrier → x * y ∈ carrier
  sq : ∀ (x : R), x ^ 2 ∈ carrier
  minus : (-1 : R) ∉ carrier

-- note that the axiom -1 ∉ cone does not make sense in a semiring

instance {R : Type} [Ring R] : Membership R (PreConeIn R) where
  mem x P := x ∈ P.carrier

-- The command `open Set` enables one to use just use `IsPreCone` in order to call the function Set.IsPreCone

--open Set

#check PreConeIn
#check PreConeIn.sq

-- Comparing the above with the file were `Set.IsPreCone` is define as a class, we see that the function `Set.IsPreCone` is of the same type in both cases. **But** the function `IsPreCone.sq` is **not**. When using a class, it takes `P.IsPreCone` as a class instance (overloaded function), while when using structure, it takes it as a parameter. This has consequences in the way some proofs are written, even basic ones such as `zero_in_precone`. And there we see that the definition using `structure` is better, because we can just project our precone to the term `aux := IsPreCone.sq hP (0 : R)` *without having to specify the type of the latter*.
-- Subsequent note: in the end, it is not so clear that structure is better than class. So ok, the only relevant question when trying to choose between structure and class is: do we intend to instantiate the notion at hand?

-- On the other hand, the proof that a certain set is a precone can be written in the same way, using the `constructor` tactic, regardless of whether we use the a class or a structure.

-- parameters: we have variable parameters, implicit parameters and instance parameters

theorem zero_in_precone {R : Type} [Ring R] (P : PreConeIn R) : 0 ∈ P := by
  --have aux : 0 ^ 2 ∈ P := PreConeIn.sq P 0  -- P.sq 0 also works
  have aux := PreConeIn.sq P 0  -- also works, but then aux gets added to the local context as `0 ^ 2 ∈ P.carrier`, not `0 ^ 2 ∈ P`
  simp at aux
  exact aux

theorem one_in_precone {R : Type} [Ring R] (P : PreConeIn R) : 1 ∈ P := by
  have aux : 1 ^ 2 ∈ P := P.sq 1
  simp at aux
  exact aux

class support (α : Type) (β : Type) : Type where
  supp (a : α) : Set β

#check support.supp

instance {R : Type} [Ring R] : support (PreConeIn R) R where
  supp P := {x : R | x ∈ P ∧ (-x) ∈ P}

def supp {α : Type} {β : Type} [support α β] (a : α) : Set β := support.supp a

#check @supp

lemma zero_in_supp {R : Type} [Ring R] {P : PreConeIn R} : (0 : R) ∈ supp P := by -- `0 ∈ (supp P : Set R)` also works, but `0 ∈ supp P` does  not (`0` here is believed to be `(0 : ℕ)`)
  constructor
  · exact zero_in_precone P
  · simp; exact zero_in_precone P

lemma PreConeInField {R : Type} [Field R] {P : PreConeIn R} {x : R} : x ∈ P ∧ -x ∈ P → x = 0 := by {
  intro ⟨h1, h2⟩
  by_contra hx
  suffices aux : -1 ∈ P
  · apply PreConeIn.minus P aux
  · have aux1 : x * (-x) ∈ P := by {apply PreConeIn.mul P _ _ ⟨h1, h2⟩}
    ring_nf at aux1
    have aux2 : (1 / x) ^ 2 ∈ P := by {apply PreConeIn.sq P}
    ring_nf at aux2
    have aux3 : -x ^ 2 * x⁻¹ ^ 2 ∈ P := by {apply PreConeIn.mul P _ _ ⟨aux1, aux2⟩}
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
    exact zero_in_supp
}

def PreConeAddElem {R : Type} [Ring R] (P : Set R) (a : R) : Set R :=
{z : R | ∃ x ∈ P, ∃ y ∈ P, z = x + a * y}

-- need an LE instance on PreCone?

instance {R : Type} [Ring R] : LE (PreConeIn R) where
  le P1 P2 := P1.carrier ≤ P2.carrier

lemma PreConeInPreConeAddElem {R : Type} [Ring R] (P : PreConeIn R) (a : R) : P.carrier ≤ PreConeAddElem P.carrier a := by
  intro z hz
  use z; constructor; exact hz
  use 0; constructor; exact zero_in_precone P
  simp

-- the following result now needs to be proven completely differently... prove lemmas and define an instance? no, define a function whose return type is `PreConeIn R`, obviously!

def PreCone {R : Type} [Field R] (P : PreConeIn R) (a : R) (ha : -a ∉ P) : PreConeIn R := ⟨{z : R | ∃ x ∈ P, ∃ y ∈ P, z = x + a * y}, sorry, sorry, sorry, sorry⟩

notation:max P"["a"]" => PreCone P a  -- precone spanned by `P` and `a`...




def PreConeAddElemIsPreCone {R : Type} [Field R] (P : PreConeIn R) (a : R) (ha : -a ∉ P) : PreConeIn R := by
  constructor
  pick_goal 5
  · exact {z : R | ∃ x ∈ P, ∃ y ∈ P, z = x + a * y}
  · intro x y h
    rcases h with ⟨hx, hy⟩
    rcases hx with ⟨u, hu, v, hv, hx⟩
    rcases hy with ⟨p, hp, q, hq, hy⟩
    have aux : u + a * v + (p + a * q) = (u + p) + a * (v + q) := by
      rw [add_assoc, ← add_assoc _ p _, add_assoc u _ _, add_comm _ p, mul_add, add_assoc p _ _]
    rw [hx, hy, aux]
    have hup : u + p ∈ P := by
      apply PreConeIn.add
      exact ⟨hu, hp⟩
    have hvq : v + q ∈ P := by
      apply PreConeIn.add
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
    · apply PreConeIn.add
      constructor
      · apply PreConeIn.mul; exact ⟨hu, hq⟩
      · apply PreConeIn.mul; exact ⟨hv, hp⟩
    · apply PreConeIn.add
      constructor
      · apply PreConeIn.mul; exact ⟨hu, hp⟩
      · apply PreConeIn.mul
        constructor
        · exact PreConeIn.sq P a
        · apply PreConeIn.mul; exact ⟨hv, hq⟩
  · intro x
    have aux : x ^ 2 ∈ P := PreConeIn.sq P x
    apply PreConeInPreConeAddElem
    exact aux
  · by_contra aux
    rcases aux with ⟨x, hx, y, hy, h⟩
    by_cases hy' : y = 0
    · suffices aux : (-1 ∈ P) from PreConeIn.minus P aux
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
      apply PreConeIn.mul
      constructor
      · apply PreConeIn.mul
        constructor
        · apply PreConeIn.add
          exact ⟨one_in_precone P, hx⟩
        · exact hy
      · apply PreConeIn.sq

structure ConeIn (R : Type) [Ring R] : Type where
  carrier : PreConeIn R
  tot : ∀ x : R, x ∈ carrier ∨ -x ∈ carrier

#check ConeIn

-- is this the same? better in terms of inheritance?

structure ConeIn' (R : Type) [Ring R] extends PreConeIn R : Type where
  tot : ∀ x : R, x ∈ carrier ∨ -x ∈ carrier


-- we put a precone instance on the set of sums of squares in a (semi)ring R; now everything we prove about cones will be true for the set of sums of squares? (which would not be true if we declared a theorem instead of an instance?) -- NEED AN EXAMPLE OF THIS See below :-)
-- Note: the following instantatiation procedure, with structure instead of class, generates a non-class instance error report in lint

-- instance SumSqPreCone (R : Type) [Ring R] : PreConeIn R := ⟨SumSqSet R, sorry, sorry, sorry, sorry⟩

-- Therefore, this should be a def (only classes should be instantiated!)

def SumSqPreCone (R : Type) [Ring R] : PreConeIn R := ⟨SumSqSet R, sorry, sorry, sorry, sorry⟩

#check SumSqPreCone
#check SumSqPreCone ℤ
#check (SumSqPreCone ℤ).carrier

def test := (SumSqPreCone ℤ).carrier
example : test = SumSqSet ℤ := by rfl

-- is this useful? was it better when we were stating a theorem saying that `SumSqSet R` is a precone?









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
  exact zero_in_precone SumSqPreCone

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

#check SumSqCone' ℤ

def SumSqCone'' (R : Type) [Ring R] : Cone' R := ⟨IsSumSq, IsSumSq.zero⟩

#check SumSqCone'' ℤ

def test := ℕ

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
