import Mathlib.Tactic.Ring

def AddElem {R : Type} (P : Set R) (a : R) : Set R := P ∪ {a}

variable (S : Set ℚ)
#check AddElem S (0 : ℚ)  -- AddElem S 0 : Set ℚ
#check AddElem S 0  -- AddElem S 0 : Set ℚ

notation:max P"("a")" => AddElem P a
#check S((0 : ℚ))  -- S(0) : Set ℚ
#check S(0)  -- S(0) : Set ℚ

notation:max (priority := high) P"["a"]" => AddElem P a
#check S[(0 : ℚ)]  -- S[0] : Set ℚ
#check S[0]  -- S[0] : Set ℚ

notation:max P" ["a"] " => AddElem P a
#check S[(0 : ℚ)]  -- S[0] : Set ℚ
#check S [0]  -- S[0] : Set ℚ
