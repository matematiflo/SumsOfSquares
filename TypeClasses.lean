import Mathlib.Algebra.Group.Defs

def test (G : Type) [pG : Group G] : (∀ g : G, 1 * g = g) := by intro g; exact one_mul g

def test' (G : Type) (pG : Group G) : (∀ g : G, 1 * g = g) := by intro g; exact one_mul g

def test'' (G : Type) {pG : Group G} : (∀ g : G, 1 * g = g) := by intro g; exact one_mul g

variable {H : Type} [pH : Group H]

#check test H
#check @test H _

#check test' H
#check @test' H _
#check @test' H pH

#check test'' H
#check @test'' H _
#check @test'' H pH

variable {H' : Type} {pH' : Group H'}

#check test H'
#check @test H' _

#check test' H'
#check test' H' _
#check @test' H' pH'

#check test'' H'
#check @test'' H' _
#check @test'' H' pH'

-- CCL: if we use type classes as parameter types in functions, an instance of that type class is treated as an implicit parameter

#check propext

example (P : Prop) (p q : P) : p = q := rfl

def action.{l} : {M : Type l} → [Add M] → Nat → (M → M) :=
  fun n ↦ match n with
  | 0     => id
  | n + 1 => fun x ↦ action n x + x
