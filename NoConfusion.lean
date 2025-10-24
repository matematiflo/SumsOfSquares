#check Nat.rec

#check Nat.recAux

#check @Decidable.recOn

#check @Decidable.casesOn

#check @Decidable.rec

inductive myType : Type
  | Monday
  | Tuesday
  | Wednesday
  deriving Repr, DecidableEq

#check myType

#check myType.rec

#eval myType.Monday

namespace myType

#check DecidableEq myType


#print Decidable


#print DecidableEq

#check Monday = Tuesday
#eval Monday = Tuesday

#check false

#print Ord

#check @compare myType

end myType

-- --------------------------------------------------

inductive myNat : Type
  | zero : myNat
  | succ : myNat → myNat
  --deriving Repr--, DecidableEq

namespace myNat

#eval zero = succ zero
#eval zero
#eval succ (succ zero)
#eval succ (succ zero) = succ zero

def succ_ne_zero (a : myNat) : succ a ≠ zero := by
  intro p
  cases p

def ne_imp_succ_ne {a b : myNat} : (a ≠ b) → succ a ≠ succ b := by
  intro p
  intro q
  cases q
  apply p
  rfl

def dec_a_b_imp_dec_succ_a_succ_b {a b : myNat} : Decidable (a = b) → Decidable (succ a = succ b)
| isTrue (h : a = b) => isTrue <| by congr
| isFalse (h : a ≠ b) => isFalse (ne_imp_succ_ne h)

example (n : Nat) : n < n + 1 := by simp only [Nat.lt_succ_self]

def this (a : myNat) : sizeOf a < 1 + sizeOf a := by
  rw [Nat.add_comm]
  apply Nat.lt_succ_self

instance instDecidableEq (a b : myNat) : Decidable (a = b) :=
by
match a, b with
  | zero, zero => exact isTrue rfl
  | zero, succ b' => exact isFalse (succ_ne_zero b').symm
  | succ a', zero => exact isFalse (succ_ne_zero a')
  | succ a, succ b => exact dec_a_b_imp_dec_succ_a_succ_b (instDecidableEq a b)
termination_by sizeOf a
decreasing_by
  simp_wf
  exact this a

#check decide

#eval @Decidable.decide (zero = succ zero) _ -- (instDecidableEq zero (succ zero))

#eval Decidable.decide (zero = succ zero)
#eval zero = succ zero

def succ_inj (a b : myNat) : (succ a = succ b) → a = b := by
  simp only [succ.injEq, imp_self]
  -- intro p
  -- cases p
  -- rfl

#print succ_inj

#print succ.injEq

def succ_inj' (a b : myNat) : (succ a = succ b) → a = b :=
  fun p => match p with | _ => sorry

end myNat
