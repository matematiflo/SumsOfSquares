# Sums of squares - Basic properties

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser

```lean
import «FormallyRealFields».SumsOfSquares.SumSq
import Mathlib.Data.List.Perm
```

## Concatenated lists

The sum of squares of the list `L1 ++ L2` is equal to the sum of squares of `L1` plus the sum of squares of `L2`.

> `SumSq (L1 ++ L2) = SumSq L1 + SumSq L2`

```lean
theorem SumSq_concat {R : Type} [Semiring R]
  (L1 L2 : List R) : SumSq (L1 ++ L2) = SumSq L1 + SumSq L2
    := by
      induction L1 with -- we prove the result by induction on the list L1
      | nil => -- case when L1 is the empty list
        simp [SumSq] -- [] ++ L2 = L2 so everything follows by definition of SumSq
      | cons a L ih => -- case when L1 = (a :: L)
        simp [SumSq] -- (a :: L) ++ L2 = a :: (L ++ L2) and SumSq (a :: (L ++ L2)) = a ^ 2  + SumSq (L ++ L2)
        rw [ih] -- ih : SumSq (L ++ L2) = SumSq L + SumSq L2
        rw [add_assoc] -- the two terms are now equal up to associativity of addition
      done
```

## Permuted lists

A sum of squares is invariant under permutations:

> `L1 ~ L2 → SumSq L1 = SumSq L2`.

```lean
theorem SumSq_permut {R : Type} [Semiring R] {L1 L2 : List R}
  (H : L1 ~ L2) : SumSq L1 = SumSq L2
    := by
      induction H -- we prove the result by induction on ~ (recall that the permutation type is an inductive type: L2 is a permutation of L1 if and only if one of four cases occurs)
      · case nil => -- case when L1 L2 are both empty
        rfl -- equality holds by definition
      · case cons x l1 l2 Hl Sum12 => -- case when L1 = (x :: l1) and L2 = (x :: l2) with l1 ~ l2
        simp [SumSq] -- by definition, SumSq (x :: lj) = x ^ 2  + SumSq lj for j = 1, 2
        rw [Sum12] -- by induction, SumSq l1 = SumSq l2
      · case swap x y L => -- case when L1 = (y :: (x :: L)) and L2 = (x :: (y :: L))
        simp [SumSq] -- by definition, SumSq (y :: (x :: L)) = y ^ 2  + (x ^ 2  + SumSq L)
        rw [← add_assoc, ← add_assoc, add_comm (y ^ 2) (x ^ 2)] -- the two expressions are equal in R
      · case trans l1 L l2 H1 H2 Sum1 Sum2 => -- case when L1 ~ L and L ~ L2
        rw [Sum1, Sum2] -- by induction SumSq L1 = SumSq L and SumSq L = SumSq L2
      done
```

## Erasing a member

If a term `a : R` is a member of a list `L : List R`, then we can compute `SumSq L` from `a` and `SumSq (L.erase a)` in the following way.

In order to be able to use the function `List.erase`, we assume that the semiring `R` has decidable equality. Recall that `L.erase a` can be used as notation for `List.erase L a`.

```lean
theorem SumSq_erase {R : Type} [Semiring R] [DecidableEq R]
  (L : List R) (a : R) (h : a ∈ L) : SumSq L = a ^ 2 + SumSq (L.erase a)
    := by
      change SumSq L = SumSq (a :: (L.erase a)) -- we can replace the goal with a *definitionally equal* one
      have H : L ~ (a :: (L.erase a)) := L.perm_cons_erase h -- this is the Mathlib proof that L ~ (a :: (L.erase a))
      rw [SumSq_permut H] -- since we ha ve a proof that L ~ (a :: (L.erase a)), we can use the SumSq_permut function that we defined earlier to conclude that the two sums of squares are equal
      done
```
