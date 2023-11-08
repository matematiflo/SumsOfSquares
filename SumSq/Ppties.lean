/-
# Sums of squares - Basic properties

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser
-/

import SumSq.Defs
import Mathlib.Data.List.Perm
import Mathlib.Tactic.FieldSimp

/-!
**CHECK OLD FILES AGAIN!!!**
-/

/-!
## Appended lists

We recall that `L1 ++ L2` (which is notation for `List.append L1 L2`) is defined as follows, by pattern matching on `L1` (see Init.Data.List.Basic for details).

```lean
def List.append : (L1 L2 : List R) → List R
  | [], L2 => L2
  | a::l1, L2 => a :: List.append l1 L2
```

We now prove that the sum of squares of the list `L1 ++ L2` is equal to the sum of squares of `L1` plus the sum of squares of `L2`.

> `SumSq (L1 ++ L2) = SumSq L1 + SumSq L2`

-/

theorem SumSqAppend [Semiring R] (L1 L2 : List R) : SumSq (L1 ++ L2) = SumSq L1 + SumSq L2 := by
  induction L1 with -- we prove the result by induction on the list L1
  | nil => -- case when L1 is the empty list
    simp [SumSq] -- [] ++ L2 = L2 so everything follows by definition of SumSq
  | cons a L ih => -- case when L1 = (a :: L)
    simp [SumSq] -- (a :: L) ++ L2 = a :: (L ++ L2) and SumSq (a :: (L ++ L2)) = a ^ 2  + SumSq (L ++ L2)
    simp [ih] -- ih : SumSq (L ++ L2) = SumSq L + SumSq L2
    simp [add_assoc] -- the two terms are now equal up to associativity of addition

/-!
## Permuted lists

Recall that the relation `L1 ~ L2` (which is notation for `List.Perm L1 L2`) is defined inductively using pairwise swaps.

```lean
inductive Perm : List R → List R → Prop
  | nil : Perm [] []
  | cons (a : R) {l₁ l₂ : List R} : Perm l₁ l₂ → Perm (a :: l₁) (a :: l₂)
  | swap (a₁ a₂ : R) (l : List R) : Perm (a₂ :: a₁ :: l) (a₁ :: a₂ :: l)
  | trans {L₁ L₂ L₃ : List R} : Perm L₁ L₂ → Perm L₂ L₃ → Perm L₁ L₃
```

We can now prove that a sum of squares is invariant under permutations:

> `L1 ~ L2 → SumSq L1 = SumSq L2`

Note that, since `List.Perm` uses implicit variables for the constructors `cons` and `trans`, we choose to write the proof by indution with a slighty different syntax (using `case`), to make the Lean infoview rendering more readable.
-/

theorem SumSq_permut {R : Type} [Semiring R] {L1 L2 : List R} (H : L1 ~ L2) : SumSq L1 = SumSq L2 := by
  induction H -- we prove the result by induction on ~ (recall that `List.Perm` is an inductive type: L2 is a permutation of L1 if and only if one of four cases occurs)
  · case nil => -- case when L1 L2 are both empty
    rfl -- equality holds by definition
  · case cons x l1 l2 Hl Sum12 => -- case when L1 = (x :: l1) and L2 = (x :: l2) with l1 ~ l2
    simp [SumSq] -- by definition, SumSq (x :: lj) = x ^ 2  + SumSq lj for j = 1, 2
    rw [Sum12] -- by induction, SumSq l1 = SumSq l2
  · case swap a b L => -- case when L1 = (b :: (a :: L)) and L2 = (a :: (b :: L))
    simp [SumSq] -- by definition, SumSq (b :: (a :: L)) = b ^ 2  + (a ^ 2  + SumSq L)
    rw [← add_assoc, ← add_assoc, add_comm (b ^ 2) (a ^ 2)] -- the two expressions are equal in R
  · case trans L1 L L2 H1 H2 Sum1 Sum2 => -- case when L1 ~ L and L ~ L2
    rw [Sum1, Sum2] -- by induction SumSq L1 = SumSq L and SumSq L = SumSq L2

/-!
## Erasing a member

The function `List.erase` can erase a member of a list. It is defined as follows.

```lean
def List.erase {R : Type} [BEq α] : List R → R → List R
  | [], _ => []
  | a::l, b => match a == b with
    | true  => l
    | false => a :: List.erase l b
```

Note that this declaration uses Boolean equality. It could be written using decidable equality, in the following way.

```lean
def List.erase' {R : Type} [DecidableEq R] : List R → R → List R
  | [], _ => []
  | a::l, b => if a = b then l else List.erase' l b
```

Whichever definition of `erase` we choose, we need to assume that the type `R` has decidable equality in order to be able to use it (and the same goes for the function `List.perm_cons_erase`, also used below).

We now prove that, if a term `a : R` is a member of a list `L : List R`, then we can compute `SumSq L` from `a` and `SumSq (L.erase a)`. More precisely:

> `a ∈ L → SumSq L = a ^ 2 + SumSq (L.erase a)`

-/

theorem SumSq_erase {R : Type} [Semiring R] [DecidableEq R] (L : List R) (a : R) (h : a ∈ L) : SumSq L = a ^ 2 + SumSq (L.erase a) := by
  change SumSq L = SumSq (a :: (L.erase a)) -- we can replace the goal with a *definitionally equal* one
  have H : L ~ (a :: (L.erase a)) := L.perm_cons_erase h -- this is the Mathlib proof that, if a ∈ L, then L ~ (a :: (L.erase a))
  rw [SumSq_permut H] -- since we have a proof that L ~ (a :: (L.erase a)), we can use the SumSq_permut function that we defined earlier to conclude that the two sums of squares are equal

/-!
## More computations

The next result formalizes a property that one would like to denote by `(c • L).sum = c * L.sum`, meaning that the sum of the list ontained by multiplying each member of `L` by `c` is equal to `c` times the sum of `L`.

**--> DEFINE THE LIST `c • L` SOMEWHERE AND PROVE `mul_sum` USING THIS NOTATION!!!**

*This needs to be done in the following way: if `R` has a `mul`, then `List R` has an `smul`.
-/

theorem mul_sum {R : Type} [Semiring R] (L : List R) (c : R) : List.sum (List.map (c * .) L) = c * List.sum L
  := by
    induction L with -- the proof is by induction on `L`
    | nil => simp -- the case of the empty list reduces to `0 = 0`
    | cons _ _ ih => simp [mul_add, ih] -- the case `L = (a :: l) follows from `c * (a + l.sum) = c * a + c * l.sum` and the induction hypothesis
    done

/-!
Combining `squaring_and_summing` and `mul_sum`, we can prove the following property, which says that `SumSq (c • L) = c ^ 2 * SumSq L`.

CHECK FILE AGAIN

This will be proven again in the section on [Multiplicative properties](#multiplicative-properties). There, we will present a proof by induction, more similar to the proof of `mul_sum` above.

CHECK FILE AGAIN

Note that for this result we assume that `R` is a *commutative* semiring (so that we can use [`mul_pow`]()).
-/

theorem mul_sum_sq {R : Type} [CommSemiring R] (L : List R) (c : R) :
SumSq (L.map (c * .)) = c ^ 2 * SumSq L
  := by
    simp [← squaring_and_summing, ← mul_sum] -- we reduce the statement to an equality between two sums of lists
    have aux : ((fun x => x ^ 2) ∘ fun x => c * x) = ((fun x => c ^ 2 * x) ∘ fun x => x ^ 2)
      := by simp [Function.funext_iff, mul_pow] -- we prove an auxiliary result that implies that the two lists are in fact equal
    --rw [SumSq2, SumSq2, ← mul_sum]
    dsimp [SumSq2]
    rw [← mul_sum]
    simp [aux] -- by incorporating `aux`, the result is proved: the sums of two equal lists are equal
    done

/-!
## Multiplicative properties

The first result says that if you multiply every member of a list `L : List R` by a constant `c : R`, then the sum of squares of the new list is equal to `c ^ 2 * SumSq L`.

In order to be able to apply lemmas such as `mul_pow` in the proof, we assume here that the semiring `R` is commutative.

We take a look at a few examples first.
-/

#eval SumSq [2 * 1, 2 * ( -2), 2 * 3] -- 56
#eval 4 * SumSq [1, -2, 3] -- 56

example : SumSq [2 * 1, 2 * ( -2), 2 * 3] = 4 * SumSq [1, -2, 3] := rfl

example (a x y : ℚ) : SumSq [a * x, a * y] = a ^ 2 * SumSq [x, y]
  := by simp [SumSq, mul_pow, mul_add]

/-!
REPROOF OF `mul_sum_sq` (by induction)
-/

theorem mul_sum_sq2 {R : Type} [CommSemiring R]
  (L : List R) (c : R) : SumSq (L.map (c * .)) = c ^ 2 * SumSq L
    := by
      induction L with -- again an induction on L
      | nil => simp [SumSq] -- the case of the empty list is trivial
      | cons a _ ih => simp [SumSq, ih, mul_add, mul_pow] -- the case of a list of the form (a :: l) follows from simplifications and the use of the induction hypothesis
      done

theorem SumSq_of_list_div {F : Type} [Semifield F]
  (L : List F) (c : F) : SumSq (L.map (. / c)) = (1 / c ^ 2) * SumSq L
    := by -- this will be an application of SumSq_of_list_mul, using the fact that . / c = . * c⁻¹
      have aux : (fun x => x / c) = (fun x => c⁻¹ * x)
        := by field_simp
      -- simp [aux, mul_sum_sq]
      simp [aux, mul_sum_sq2]
      done
