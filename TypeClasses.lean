import Mathlib.Algebra.Group.Defs

def test (G : Type) [pG : Group G] : (∀ g : G, 1 * g = g) := by intro g; exact one_mul g

def test' (G : Type) (pG : Group G) : (∀ g : G, 1 * g = g) := by intro g; exact one_mul g

variable {H : Type} [pH : Group H]

#check test H
#check @test H _

#check test' H
#check @test' H _
#check @test' H pH

variable {H' : Type} {pH' : Group H'}

#check test H'
#check @test H' _
#check test' H'
#check test' H' _
#check @test' H' pH'
