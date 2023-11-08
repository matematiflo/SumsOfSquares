# Sums of squares - Basic properties

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser

```haskell
import SumSq.Defs
import Mathlib.Data.List.Perm
import Mathlib.Tactic.FieldSimp
```

## Appended lists

Recall from [#List.append](https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html#List.append) that `L1 ++ L2` (which is notation for `List.append L1 L2`) is defined as follows, by pattern matching on `L1` (see Init.Data.List.Basic for details).

```haskell
def List.append : (L1 L2 : List R) → List R
  | [], L2 => L2
  | a::l1, L2 => a :: List.append l1 L2
```

We now prove that the sum of squares of the list `L1 ++ L2` is equal to the sum of squares of `L1` plus the sum of squares of `L2`.

> `SumSq (L1 ++ L2) = SumSq L1 + SumSq L2`

```haskell
theorem SumSqAppend [Semiring R] (L1 L2 : List R) : SumSq (L1 ++ L2) = SumSq L1 + SumSq L2 := by
  induction L1 with -- we prove the result by induction on the list L1
  | nil => -- case when L1 is the empty list
    simp [SumSq] -- since [] ++ L2 = L2 by definition of ++, the result follows by definition of SumSq
  | cons a l1 ih => -- case when L1 = (a :: L)
    simp [SumSq] -- by [`List.cons_append](https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html#List.cons_append) (a :: L) ++ L2 = a :: (L ++ L2), so SumSq (a :: (L ++ L2)) = a ^ 2  + SumSq (L ++ L2)
    rw [ih] -- recall that ih : SumSq (L ++ L2) = SumSq L + SumSq L2
    rw [add_assoc] -- the two terms are now equal up to associativity of addition
```

## Permuted lists

Recall from [#List.Perm](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Perm.html#List.Perm) that the relation `L1 ~ L2` (which is notation for `List.Perm L1 L2`) is defined inductively using pairwise swaps.

```haskell
inductive Perm : List R → List R → Prop
  | nil : Perm [] []
  | cons (a : R) {l₁ l₂ : List R} : Perm l₁ l₂ → Perm (a :: l₁) (a :: l₂)
  | swap (a₁ a₂ : R) (l : List R) : Perm (a₂ :: a₁ :: l) (a₁ :: a₂ :: l)
  | trans {L₁ L₂ L₃ : List R} : Perm L₁ L₂ → Perm L₂ L₃ → Perm L₁ L₃
```

 So we wee that `List.Perm` is an inductive type: `L2` is a permutation of `L1` if and only if one of four cases occurs.

We can now prove that a sum of squares is invariant under permutations:

> `L1 ~ L2 → SumSq L1 = SumSq L2`

Note that, since `List.Perm` uses implicit variables for the constructors `cons` and `trans`, we choose to write the proof by indution with a slighty different syntax (using `case`), to make the Lean infoview rendering more readable (for more on this, see Exercise 1 [below](#exercises)).

```haskell
theorem SumSqPermut {R : Type} [Semiring R] {L1 L2 : List R} (H : L1 ~ L2) : SumSq L1 = SumSq L2 := by
  induction H -- we prove the result by induction on `H`, which is a term of type `L1 ~ L2` (and the latter is indeed an inductive type)
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

## Erasing an entry

The function `List.erase` can erase an entry of a list. It is defined as follows in [#List.erase](https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html#List.erase).

```haskell
def List.erase {R : Type} [BEq R] : List R → R → List R
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

Whichever definition of `erase` we choose, we need to assume that the type `R` has decidable equality in order to be able to use it (and the same goes for the function [`#List.perm_cons_erase`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Perm.html#List.perm_cons_erase), also used below).

We now prove that, if a term `a : R` is an entry of a list `L : List R`, then we can compute `SumSq L` from `a` and `SumSq (L.erase a)`. More precisely:

> `a ∈ L → SumSq L = a ^ 2 + SumSq (L.erase a)`

The type `a ∈ L` is defined in [#List.Mem](https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html#List.Mem). It is an inductive type: a term `a : R` belongs to a list `L : List R` if and only if `L = (a :: l)` or `L = (b :: l)` with `b ∈ l`.

```haskell
theorem SumSqErase {R : Type} [Semiring R] [DecidableEq R] (L : List R) (a : R) (h : a ∈ L) : SumSq L = a ^ 2 + SumSq (L.erase a) := by
  change SumSq L = SumSq (a :: (L.erase a)) -- we can replace the goal with a *definitionally equal* one
  have H : L ~ (a :: (L.erase a)) := L.perm_cons_erase h -- this is the Mathlib proof that, if a ∈ L, then L ~ (a :: (L.erase a)), see also the exercises section below
  rw [SumSqPermut H] -- since we have a proof that L ~ (a :: (L.erase a)), we can use the SumSq_permut function that we defined earlier to conclude that the two sums of squares are equal
```

## Multiplication by a scalar

Let `L` be a list with entries in a semiring `R`. If `c` is a term of type `R`, we can multiply each entry of `L` by `c` to define a new list, that we shall denote `c • L`. For instance, if `L = [x, y, z]`, we should have:

> `c • [x, y, z] = [c * x, c * y, c * z]`

Let us define this formally and take a look at a few examples. As we shall see, one has to be precise in the notation, in order for Lean to interpret the command correctly.

```haskell
def ListSmul [Semiring R] (c : R) : List R → List R
  | [] => []
  | a :: l => (c * a) :: ListSmul c l

infixl:50 " • " => ListSmul

theorem ListSmulMap [Semiring R] (c : R) (L : List R) : (c • L) = L.map (c * .) := by
  induction L with
  | nil => simp [ListSmul]  -- the case of the empty list is trivial
  | cons a l ih =>  simp [ListSmul, ih]  -- the case of a list of the form (a :: l) reduces immediately to the induction hypothesis

#eval ListSmul 2 [1, -2, 3]  --[2, -4, 6]
#eval ((2 : ℤ) • [1, -2, 3])

example : ListSmul 2 [1, -2, 3] = [2, -4, 6] := by rfl

#eval SumSq (ListSmul 2 [1, -2, 3])  -- 56
#eval SumSq ((2 : ℤ) • [1, -2, 3])  -- 56

example : SumSq (ListSmul 2 [1, -2, 3]) = 4 * SumSq [1, -2, 3] := by rfl

#eval SumSq [2, -4, 6]
#eval 4 * SumSq [1, -2, 3]  -- 56

example (a x y : ℚ) : (ListSmul a [x, y]) = [a * x, a * y] := by rfl
example (a x y : ℚ) : SumSq (ListSmul a [x, y]) = a ^ 2 * SumSq [x, y] := by simp [SumSq, mul_pow, mul_add]
```

The result we expect is then the following:

> `SumSq (c • L) = c ^ 2 * SumSq L`

We will see below that this result holds when `R` is a *commutative* semiring.

Indeed, in order to be able to apply lemmas such as [`#mul_pow`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupPower/Basic.html#mul_pow) in the proof, we need to assume that the semiring `R` is commutative.

Before proving the result that is relevant result, we prove an easier one, of possibly greater general interest, with `SumSq` replaced by `List.sum`.

```haskell
theorem SumSmul {R : Type} [Semiring R] (c : R) (L : List R) : List.sum (c • L) = c • (List.sum L) := by
  induction L with
  | nil => simp [ListSmul]
  | cons a l ih => simp [ListSmul, mul_add, ih]

theorem SumSqSmul {R : Type} [CommSemiring R] (c : R) (L : List R) : SumSq (c • L) = c ^ 2 * SumSq L := by
    induction L with -- we prove the result by induction on L
    | nil => simp [SumSq] -- the case of the empty list is trivial
    | cons a _ ih => simp [SumSq, mul_add, ih, mul_pow] -- the case of a list of the form (a :: l) follows from simplifications and the use of the induction hypothesis
```

If we assume that the semiring `R` is in fact a semifield, then we can also consider the list from `L` obtained by dividing each entry by a term `c` such that `c ≠ 0'.

```haskell
theorem SumSqDiv {F : Type} [Semifield F]
  (L : List F) (c : F) : SumSq (L.map (. / c)) = (1 / c ^ 2) * SumSq L := by
    -- this will be an application of mul_sum_sq2, using the fact that . / c = . * c⁻¹
    have aux : (fun x => x / c) = (fun x => c⁻¹ * x) := by field_simp
    simp [aux, ← ListSmulMap, SumSqSmul]
```

Note that no assumption `(hc : c ≠ 0)` has been used because Lean gives a value to division by `c` in `F` even if `c = 0` and that the equality remains true in this case.

```haskell
example [Semifield F] (x : F) : x / 0 = 0 := by field_simp
```

## More computations

Before moving on to the exercises, we give another proof of `theorem SumSqSmul`, seen in the section on [Multiplication by a scalar](#multiplication-by-a-scalar).

It is a direct, more computational proof, harder to follow than the original proof (by induction).

```haskell
lemma SumSmul2 [Semiring R]  (c : R) (L : List R) : (L.map (c * .)).sum = c * L.sum := by
  induction L with
  | nil => simp
  | cons a l ih => simp [mul_add, ih]

theorem SumSqSmul2 {R : Type} [CommSemiring R] (L : List R) (c : R) : ((L.map (c * .)).map (. ^2)).sum = c ^ 2 * (L.map (. ^ 2)).sum := by
    simp [mul_add, mul_pow, ← SumSmul2]  -- we simplify the statement
    have aux : ((fun x => x ^ 2) ∘ fun x => c * x) = ((fun x => c ^ 2 * x) ∘ fun x => x ^ 2)
      := by simp [Function.funext_iff, mul_pow]  -- we prove an auxiliary result in order to incorporate it in the goal
    rw [aux]
```

## Exercises

1. Modify the syntax of the `induction` tactic in [`SumSqPermut`](#permuted-lists) to make it look more similar to that of [`SumSqAppend`](#appended-lists). This means: in `SumSqPermut`, replace `induction H` by `induction H with` and make the proof syntactically correct after that (start by changing `⬝ case nil` to `| nil`).

2. Let `R` be a type with decidable equality. Let `a` be a term of type `R` and let `L` be a term of type `List R`. Prove that, if `a ∈ L`, then the list `a :: L.erase a` is a permutation of `L` (we have used this standard result [here](#erasing-an-entry)).

3. Prove that the statement of [`theorem SumSqSmul2`](#more-computations) is indeed equivalent to the statement of [`theorem SumSqSmul`](#multiplication-by-a-scalar).
