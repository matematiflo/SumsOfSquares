set_option pp.proofs true

inductive Vec (α : Type) : Nat → Type
| nil  : Vec α 0
| cons : ∀ {n : Nat}, Vec α n → α → Vec α (n + 1)

#check Vec.nil
#check Vec.cons

def append : ∀ (α : Type) (m n p : Nat) (eq_pf : m + n = p), Vec α m → Vec α n → Vec α p :=
  fun α m n p eq_pf xs ys ↦
    match n with
    | 0     => cast (congrArg (Vec α) eq_pf) xs
    | n + 1 => match ys with
              | Vec.cons ys' y => cast (congrArg (Vec α) eq_pf) (Vec.cons ((append α m n (m + n) rfl xs ys')) y)

#check cast

def append_nil : ∀ {α : Type} {n : Nat} (ys : Vec α n), append α n 0 n rfl ys Vec.nil = ys :=
  fun {α} {n} ys ↦ rfl

def nil_append : ∀ {α : Type} {m : Nat} (xs : Vec α m), append α 0 m m (Nat.zero_add m) Vec.nil xs = xs :=
  fun {α} {m} xs ↦ match m with
  | 0     => match xs with | Vec.nil => rfl
  | n + 1 => match xs with
    | Vec.cons xs' x =>
      by
      dsimp [append]
        -- to conclude, it suffices to use some commutativity property between `cons` and "the rest", then use the congruence property for the function `Vec.cons` and conclude using an induction hypothesis...
        -- the "commutativity property" we are after is something like `append xs (ys.cons y) = (append xs ys).cons y`
      have : cast (append.proof_5 α 0 (n + 1) n (Nat.zero_add (n + 1))) ((append α 0 n (0 + n) (append.proof_6 0 n) Vec.nil xs').cons x) =  (cast _ (append α 0 n (0 + n) _ Vec.nil xs')).cons x := sorry
      sorry
