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

class PreCone (R : Type) [Ring R] : Type where
  carrier : Set R
  add : ∀ (x y : R), x ∈ carrier ∧ y ∈ carrier → x + y ∈ carrier
  mul : ∀ (x y : R), x ∈ carrier ∧ y ∈ carrier → x * y ∈ carrier
  sq : ∀ (x : R), x ^ 2 ∈ carrier
  minus : (-1 : R) ∉ carrier

-- note that the axiom -1 ∉ P does not make sense in a semiring

#check PreCone
#check PreCone.sq

-- Comparing the above with the file were `Set.IsPreCone` is define as a structure, we see that the function `Set.IsPreCone` is of the same typ in both cases. **But** the function `IsPreCone.sq` is **not**. When using a class, it takes `P.IsPreCone` as an instance parameter (overloaded function), while when using structure, it takes it as a variable parameter. This has consequences in the way some proofs are written, even basic ones such as `zero_in_precone`. And there we see that the definition using structure is better, because we can just project our precone to the term `aux := IsPreCone.sq hP (0 : R)` *without having to specify the type of the latter*.

-- On the other hand, the proof that a certain set is a precone can be written in the same way, using the `constructor` tactic, regardless of whether we use the a class or a structure.

-- parameters: we have variable parameters, implicit parameters and instance parameters

instance {R : Type} [Ring R] : Membership R (PreCone R) where
  mem x P := x ∈ P.carrier

theorem zero_in_precone {R : Type} [Ring R] (P : PreCone R) : 0 ∈ P := by
  have aux : 0 ^ 2 ∈ P := PreCone.sq 0
  simp at aux
  exact aux

theorem one_in_precone {R : Type} [Ring R] (P :  PreCone R) : 1 ∈ P := by
  have aux : 1 ^ 2 ∈ P := PreCone.sq 1
  simp at aux
  exact aux

-- In the following class declaration, we have to use Type (l + 1) because we want `param to be a term of type `Type l`, which is itself a term of type `Type (l + 1)`.

class support (α : Type l) : Type (l + 1) where
  param : Type l
  supp (a : α) : Set param

#check support
#check support.param
#check support.supp

instance (R : Type) [Ring R] : support (PreCone R) where
  param := R
  supp P := {x : R | x ∈ P ∧ (-x) ∈ P}

def supp {α : Type} [support α] (a : α) : Set (support.param α) := support.supp a

#check @supp

variable (C : PreCone ℤ)

#check supp C

#check support.supp C

--needs a Repr instance?
#check support.param (PreCone ℤ)
#reduce support.param (PreCone ℤ)
#reduce support.supp C

lemma zero_in_supp {R : Type} [Ring R] (P : PreCone R) : 0 ∈ supp P := by
  constructor
  · exact zero_in_precone P
  · simp; exact zero_in_precone P

-- Note that if we do not want to use the `support` class, we can just define a function `supp` as follows. The point was to have definitions that enable `0 ∈ supp P` to be interpreted automatically as `(0 : R) ∈ supp P`, or equivalently `0 ∈ (supp P : Set R)`, not `(0 : ℕ) ∈ supp P`.

/-
def supp' {R : Type} [Ring R] (P : PreCone R) : Set R := {x : R | x ∈ P ∧ (-x) ∈ P}

#check (supp' C : Set ℤ)
#check supp' C

lemma zero_in_supp' {R : Type} [Ring R] (P : PreCone R) : 0 ∈ supp' P := by
  constructor
  · exact zero_in_precone P
  · simp; exact zero_in_precone P
-/

lemma PreConeInField {R : Type} [Field R] {P : PreCone R} {x : R} : x ∈ P ∧ -x ∈ P → x = 0 := by
  intro ⟨h1, h2⟩
  by_contra hx
  suffices new : -1 ∈ P
  · exact PreCone.minus new
  · have aux1 : x * (-x) ∈ P := by
      apply PreCone.mul
      exact ⟨h1, h2⟩
    ring_nf at aux1
    have aux2 : (1 / x) ^ 2 ∈ P := by
      apply PreCone.sq
    ring_nf at aux2
    have aux3 : -x ^ 2 * x⁻¹ ^ 2 ∈ P := by
      apply PreCone.mul
      exact ⟨aux1, aux2⟩
    field_simp at aux3
    exact aux3

theorem SuppPreConeInField {R : Type} [Field R] (P : PreCone R) : supp P = {0} := by
  ext x; simp
  constructor
  · intro h
    exact PreConeInField h
  · intro h
    rw [h]
    exact zero_in_supp P

def AddElem {R : Type} [Ring R] (P : Set R) (a : R) : Set R :=
{z : R | ∃ x ∈ P, ∃ y ∈ P, z = x + a * y}

def PreConeAddElem {R : Type} [Ring R] (P : PreCone R) (a : R) : Set R :=
AddElem P.carrier a

notation:max P"["a"]" => AddElem P a  -- introduced too soon? actually, this is just an `AddElem`, sort of...

notation: max P"["a"]" => PreConeAddElem P a  -- introduced too soon? actually, this is just an `AddElem`, sort of...

-- already need an LE instance on PreCone R? would be better in order to state the following result (look for it in the ConesThirdTry file or something...)

variable (P' : PreCone ℚ)

#check P'.carrier[(0:ℚ)]
#check P'[(0 : ℚ)]
#check P'[0]  -- if we want to avoid this problem, we need a well-written adjunction class...

lemma PreConeInPreConeAddElem {R : Type} [Ring R] (P : PreCone R) (a : R) : P.carrier ≤ P.carrier[a] := by {
  intro x hx
  use x; constructor; exact hx
  use 0; constructor; exact zero_in_precone P; simp
}

instance PreConeAddElemIsPreCone {R : Type} [Field R] (P : PreCone R) (a : R) (ha : -a ∉ P) : PreCone R := by {
  constructor
  pick_goal 5
  · exact P.carrier[a]
  · intro x y h
    rcases h with ⟨hx, hy⟩
    rcases hx with ⟨u, hu, v, hv, hx⟩
    rcases hy with ⟨p, hp, q, hq, hy⟩
    have aux : u + a * v + (p + a * q) = (u + p) + a * (v + q) := by
      rw [add_assoc, ← add_assoc _ p _, add_assoc u _ _, add_comm _ p, mul_add, add_assoc p _ _]
    rw [hx, hy, aux]
    have hup : u + p ∈ P := by
      apply PreCone.add
      exact ⟨hu, hp⟩
    have hvq : v + q ∈ P := by
      apply PreCone.add
      exact ⟨hv, hq⟩
    use u + p
    constructor
    swap
    use v + q
    constructor
    assumption
    · rfl -- there is something ugly here: fix it
    · apply PreCone.add; exact ⟨hu, hp⟩
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
    · apply PreCone.add
      constructor
      · apply PreCone.mul; exact ⟨hu, hq⟩
      · apply PreCone.mul; exact ⟨hv, hp⟩
    · apply PreCone.add
      constructor
      · apply PreCone.mul; exact ⟨hu, hp⟩
      · apply PreCone.mul
        constructor
        · exact PreCone.sq a
        · apply PreCone.mul; exact ⟨hv, hq⟩
  · intro x
    have aux : x ^ 2 ∈ P := PreCone.sq x
    apply PreConeInPreConeAddElem
    exact aux
  · by_contra aux
    rcases aux with ⟨x, hx, y, hy, h⟩
    by_cases hy' : y = 0
    · suffices aux : (-1 ∈ P) from PreCone.minus aux
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
      apply PreCone.mul
      constructor
      · apply PreCone.mul
        constructor
        · apply PreCone.add
          exact ⟨one_in_precone P, hx⟩
        · exact hy
      · apply PreCone.sq
  }

class Cone (R : Type) [Ring R] extends PreCone R : Type where
  tot : ∀ x : R, x ∈ carrier ∨ -x ∈ carrier

#check @Cone
#check Cone ℤ
#check Cone.tot

#check Cone.toPreCone

instance {R : Type} [Ring R] : Membership R (Cone R) where
  mem x P := x ∈ P.carrier

-- we put a cone instance on the set of sums of squares in a (semi)ring R; now everything we prove about cones will be true for the set of sums of squares? (which would not be true if we declared a theorem instead of an instance?) -- NEED AN EXAMPLE OF THIS See below :-)
-- Note: the same procedure but with structure instead of class generates a non-class instance error report in lint

instance SqPreCone (R : Type) [Ring R] : PreCone R := ⟨SumSqSet R, sorry, sorry, sorry, sorry⟩

instance SqCone (R : Type) [Ring R] : Cone R := ⟨sorry⟩

#check SqCone

-- we define a membership instance for cones (we could have done this for the type of sum of squares! Then the set of sum of squares becomes less useful? we do use it in the example below, though...)

-- we illustrate how a property true for all cones can be deduced for the cone of sums of squares by instantiation (would be better with a more interesting property...). We say instantiation because we have put an `IsCone` instance on `SumSqSet R` (see above).

lemma zeroInCone {R : Type} [Ring R] (P : Cone R) : 0 ∈ P := zero_in_precone P.toPreCone

-- the following shows that `0 ∈ SumSqSet ℤ` becauses `SumSqSet ℤ` has been given a cone structure and `0` is an element of all cones.

example : 0 ∈ SumSqSet ℤ := by {exact zeroInCone (SqCone ℤ)}

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


-- is the following better than with a structure? Well, it depends: are we going to instantiate this? what would it permit?

-- More precisely, is it correct to think that classes should be used mostly to overload polymorphic functions?  And then instantiating a class means declaring objects to which said functions will be applied? WOuld make sense! The point is to be able to apply the function to the term without having to provide a proof that we can apply it... THIS MAKES A LOT OF SENSE!!!!!!!!!!!!!!!!!!!!!!! Do we have an example in the present context? I mean, besides the class constructors themselves.

class precone (R : Type) [Ring R] : Type where
  P : Set R
  add : ∀ (x y : R), x ∈ P ∧ y ∈ P → x + y ∈ P
  mul : ∀ (x y : R), x ∈ P ∧ y ∈ P → x * y ∈ P
  sq : ∀ (x : R), x ^ 2 ∈ P
  minus : (-1 : R) ∉ P

#check precone
#check precone.sq

instance {R : Type} [Ring R] : Membership R (precone R) where
  mem x C := x ∈ C.P

theorem zero_in_precone' {R : Type} [Ring R] (C : precone R) : 0 ∈ C := by {
  have aux : (0 : R) ^ 2 ∈ C := precone.sq (0 : R)
  simp at aux
  exact aux
}

instance SumSqPreCone (R : Type) [Ring R] : precone R :=
  ⟨SumSqSet R, sorry, sorry, sorry, sorry⟩

#check SumSqPreCone
#check (SumSqPreCone ℤ).P

def test := (SumSqPreCone ℤ).P
example : test = SumSqSet ℤ := by rfl

-- note that using def instead of instance in the declaration of SumSqPreCone also works (and does not generate a linter report). What does that change? CHECK GRAHAM HUTTON'S COURSE FOR INSTANTIATION/OVERLOADING?

class cone (R : Type) [Ring R] extends precone R where
  tot : ∀ x : R, x ∈ P ∨ -x ∈ P

#check cone
