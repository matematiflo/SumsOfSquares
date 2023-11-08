# Sums of squares - Basic properties

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser

```haskell
import SumSq.Defs
import Mathlib.Data.List.Perm
```

**CHECK OLD FILES AGAIN!!!**

## Appended lists

The sum of squares of the list `L1 ++ L2` is equal to the sum of squares of `L1` plus the sum of squares of `L2`.

> `SumSq (L1 ++ L2) = SumSq L1 + SumSq L2`

We recall that `L1 ++ L2` (which is notation for `List.append L1 L2`) is defined as follows by pattern matching on `L1`.

```haskell
def List.append : (L1 L2 : List R) → List R
  | [], L2 => L2
  | a::l1, L2 => a :: List.append l1 L2
```

See Init.Data.List.Basic for details.

```haskell
theorem SumSqAppend [Semiring R] (L1 L2 : List R) : SumSq (L1 ++ L2) = SumSq L1 + SumSq L2 := by
  induction L1 with -- we prove the result by induction on the list L1
  | nil => -- case when L1 is the empty list
    simp [SumSq] -- [] ++ L2 = L2 so everything follows by definition of SumSq
  | cons a L ih => -- case when L1 = (a :: L)
    simp [SumSq] -- (a :: L) ++ L2 = a :: (L ++ L2) and SumSq (a :: (L ++ L2)) = a ^ 2  + SumSq (L ++ L2)
    simp [ih] -- ih : SumSq (L ++ L2) = SumSq L + SumSq L2
    simp [add_assoc] -- the two terms are now equal up to associativity of addition
```

## Permuted lists

Recall that the relation `L1 ~ L2` (which is notation for `List.Perm L1 L2`) is defined inductively using pairwise swaps.

```haskell
inductive Perm : List R → List R → Prop
  | nil : Perm [] []
  | cons (a : R) {l₁ l₂ : List R} : Perm l₁ l₂ → Perm (a :: l₁) (a :: l₂)
  | swap (a₁ a₂ : R) (l : List R) : Perm (a₂ :: a₁ :: l) (a₁ :: a₂ :: l)
  | trans {L₁ L₂ L₃ : List R} : Perm L₁ L₂ → Perm L₂ L₃ → Perm L₁ L₃
```

We can now prove that a sum of squares is invariant under permutations:

> `L1 ~ L2 → SumSq L1 = SumSq L2`

Note that, since `List.Perm` uses implicit variables for the constructors `cons` and `trans`, we choose to write the proof by indution with a slighty different syntax (using `case`), to make the Lean infoview rendering more readable.

```haskell
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
```

## Erasing a member

The function `List.erase` can erase a member of a list. It is defined as follows.

```haskell
def List.erase {R : Type} [BEq α] : List R → R → List R
  | [], _ => []
  | a::l, b => match a == b with
    | true  => l
    | false => a :: List.erase l b
```

Note that this declaration uses Boolean equality. It could be written using decidable equality, in the following way.

```haskell
def List.erase' {R : Type} [DecidableEq R] : List R → R → List R
  | [], _ => []
  | a::l, b => if a = b then l else List.erase' l b
```

Whichever definition of `erase` we choose, we need to assume that the type `R` has decidable equality in order to be able to use it (and the same goes for the function `List.perm_cons_erase`, also used below).

We now prove that, if a term `a : R` is a member of a list `L : List R`, then we can compute `SumSq L` from `a` and `SumSq (L.erase a)`. More precisely:

> `a ∈ L → SumSq L = a ^ 2 + SumSq (L.erase a)`

```haskell
theorem SumSq_erase {R : Type} [Semiring R] [DecidableEq R] (L : List R) (a : R) (h : a ∈ L) : SumSq L = a ^ 2 + SumSq (L.erase a) := by
  change SumSq L = SumSq (a :: (L.erase a)) -- we can replace the goal with a *definitionally equal* one
  have H : L ~ (a :: (L.erase a)) := L.perm_cons_erase h -- this is the Mathlib proof that, if a ∈ L, then L ~ (a :: (L.erase a))
  rw [SumSq_permut H] -- since we have a proof that L ~ (a :: (L.erase a)), we can use the SumSq_permut function that we defined earlier to conclude that the two sums of squares are equal
```
