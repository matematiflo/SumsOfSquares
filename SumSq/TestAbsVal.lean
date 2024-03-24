import Mathlib.Data.Vector

def square (n : Nat) : Nat := n ^ 2

def abs (n : Int) : Int :=
if n ≥ 0 then n else (-n)

#check (n : Nat) → Vector Nat n

def v1 : Vector Nat 2 := ⟨[1,2], rfl⟩

def v2 : Vector Nat 2 := ⟨[1,2], rfl⟩

#eval Vector.length v1

#check Vector.get v1 1
#eval Vector.get v1 1

theorem VecEq {X : Type} (v v' : Vector X k) : v = v' ↔ ∀ i : Fin k, Vector.get v i = Vector.get v' i := by
  {
    constructor
    · intro h
      intro i
      let f := fun (w : Vector X k) => Vector.get w i
      exact congrArg f h
    · intro h

      sorry
  }


theorem test_zero_add (n : ℕ) : 0 + n = n := by {
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
}

theorem zero_add' : ∀ (n : Nat), Nat.add 0 n = n :=
 fun n => by {simp}

#print zero_add'

theorem le_zero (n : Nat) : n ≤ 0 → n = 0 := by {
  intro h
  cases h
  rfl
}

#print le_zero

#check @Nat.le

theorem le_zero' (n : Nat) : n ≤ 0 → n = 0 :=
  fun h => match n, h with
  | _, Nat.le.refl => rfl
  -- | Nat.zero, Nat.le.refl => rfl  -- works perfectly, but produces a slightly different code.


#print le_zero'

theorem le_zero'' : (n : Nat) → n ≤ 0 → n = 0 :=
  fun n h => match n, h with
  | _, Nat.le.refl => rfl
  -- | Nat.zero, Nat.le.refl => rfl  -- works perfectly, but produces a slightly different code.

#print le_zero''

def n0 : ℕ := 2 + 3
def n1 : ℕ := 3 + 2

#check n0
#check n1

example : n0 = n1 := rfl

def Example1 := (1 = 0)

#check Example1
×
inductive Example2 : Prop where
| one_eq_zero (p : 1 = 0)

#check Example2.one_eq_zero

theorem test : Example1 ↔ Example2 := by {
  constructor
  intro x; exact Example2.one_eq_zero x
  intro x
  cases x with
  | one_eq_zero p => exact p
}
