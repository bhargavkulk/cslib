/-
Copyright (c) 2026 Bhargav Kulkarni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhargav Kulkarni
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# Insertion Sort on a list

In this file we introduce `insert` and `insertionSort` algorithms that returns a time monad
over the list `TimeM (List α)`. The time complexity of `insertionSort` is the number of comparisons.

--
## Main results

- `insertionSort_correct`: `insertionSort` permutes the list into a sorted one.
- `insertionSort_time`:  The number of comparisons of `insertionSort` is at most `n^2`.

-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type} [LinearOrder α]

/-- Inserts an element into a list, counting comparisons as time cost.
Returns a `TimeM (List α)` where the time represents the number of comparisons performed. -/
def insert : α → List α → TimeM (List α)
| x, [] => return [x]
| x, y :: ys => do
  let c ← ✓ (x ≤ y : Bool)
  if c then
    return (x :: y :: ys)
  else
    let rest ← insert x ys
    return (y :: rest)

/-- Sorts a list using the insertion sort algorithm, counting comparisons as time cost.
Returns a `TimeM (List α)` where the time represents the total number of comparisons. -/
def insertionSort (xs : List α) : TimeM (List α) := do
  match xs with
  | [] => return []
  | x :: xs' => do
    let sortedTail ← insertionSort xs'
    insert x sortedTail

section Correctness

open List

@[grind →]
theorem mem_either_insert (xs : List α) (a b : α) (hz : a ∈ ⟪insert b xs⟫) : a = b ∨ a ∈ xs := by
  fun_induction insert with
  | case1 _ => simp only [Pure.pure, pure, mem_cons, not_mem_nil, or_false] at hz; exact Or.inl hz
  | case2 x y ys ih =>
    simp_all only [Bind.bind, Pure.pure]
    simp at hz
    grind

/-- A list is sorted if it satisfies the `Pairwise (· ≤ ·)` predicate. -/
abbrev IsSorted (l : List α) : Prop := List.Pairwise (· ≤ ·) l

theorem sorted_insert {x : α} {xs : List α} (hxs : IsSorted xs) :
  IsSorted ⟪insert x xs⟫ := by
  fun_induction insert x xs with
  | case1 _ => simp
  | case2 x y ys ih =>
    simp only [Bind.bind, Pure.pure]
    grind [pairwise_cons]

theorem insertionSort_sorted (xs : List α) : IsSorted ⟪insertionSort xs⟫ := by
  fun_induction insertionSort xs with
  | case1 => simp
  | case2 x xs ih =>
    simp only [Bind.bind]
    grind [sorted_insert]

lemma insert_perm x (xs : List α) : ⟪insert x xs⟫ ~ x :: xs := by
  fun_induction insert with
  | case1 x => simp
  | case2 x y ys ih =>
    simp only [Bind.bind, Pure.pure]
    grind

theorem insertionSort_perm (xs : List α) : ⟪insertionSort xs⟫ ~ xs := by
  fun_induction insertionSort xs with
  | case1 => simp
  | case2 x xs ih =>
    simp only [Bind.bind, ret_bind]
    refine (insert_perm x (insertionSort xs).ret).trans ?_
    grind [List.Perm.cons]

/-- Insertion Sort is functionally correct. -/
theorem insertionSort_correct (xs : List α) :
    IsSorted ⟪insertionSort xs⟫ ∧ ⟪insertionSort xs⟫ ~ xs :=
  ⟨insertionSort_sorted xs, insertionSort_perm xs⟩

end Correctness

section TimeComplexity

/-- Time complexity of `insert`. -/
theorem insert_time (x : α) (xs : List α) :
    (insert x xs).time ≤ xs.length := by
  fun_induction insert with
  | case1 _ => simp
  | case2 x y ys ih =>
    simp [Bind.bind, Pure.pure]
    grind

theorem insert_length (x : α) (xs : List α) :
    (insert x xs).ret.length = xs.length + 1 := by
  fun_induction insert with
  | case1 _ => simp
  | case2 x y ys ih =>
    simp [Bind.bind, Pure.pure]
    grind

theorem insertionSort_length (xs : List α) :
    (insertionSort xs).ret.length = xs.length := by
  fun_induction insertionSort xs with
  | case1 => simp
  | case2 x xs ih =>
    simp [Bind.bind]
    grind [insert_length]

/-- Time complexity of `insertionSort`. -/
theorem insertionSort_time (xs : List α) :
    (insertionSort xs).time ≤ xs.length * xs.length:= by
  fun_induction insertionSort with
  | case1 => simp
  | case2 x xs ih =>
    simp [Bind.bind]
    grind [insert_time, insertionSort_length]

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
