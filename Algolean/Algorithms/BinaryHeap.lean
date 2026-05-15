/-
Copyright (c) 2026 Ethan Ermovick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Ermovick
-/
module

public import Algolean.Models.ReadWriteVec

@[expose] public section

/-!
# Binary Heap

Heap implementation (not theorems) were inspired by [Batteries].

## References
1. [Batteries](https://github.com/leanprover-community/batteries)
-/

namespace Algolean

namespace Algorithms

def parentIdx (i : Fin sz) (hpos : i.1 > 0) : { j : Fin sz // j < i } :=
  ⟨⟨(i.1-1) / 2, by lia⟩, by grind⟩

def maxHeapPropertyPartial (le : α → α → Bool) (a : Vector α sz) (p : Fin sz → Prop) : Prop :=
  ∀ (i : Fin sz) (hpos : i.1 > 0), p i → le a[i] a[(parentIdx i hpos).1]

@[simp]
def maxHeapProperty (le : α → α → Bool) (a : Vector α sz) : Prop :=
  maxHeapPropertyPartial le a fun _ => True

/-- Push element at `i` up to restore the max-heap property, logging all reads and writes. -/
def heapifyUp (le : α → α → Bool) (a : Vector α sz) (i : Fin sz) :
    Prog (Vec α) (Vector α sz) := do
  if hpos : i.1 > 0 then
    let ⟨parent, _⟩ := parentIdx i hpos
    let parentVal ← Vec.read a parent
    let currentVal ← Vec.read a i
    if le parentVal currentVal then
      let a ← Vec.write a parent currentVal
      let a ← Vec.write a i parentVal
      heapifyUp le a parent
    else
      return a
  else
    return a

def heap_insert (le : α → α → Bool) (a : Vector α sz) (x : α) :
    Prog (Vec α) (Vector α (sz+1)) := do
  -- TODO: How to count the push?
  let a ← heapifyUp le (a.push x) ⟨a.size, Nat.lt_succ_self _⟩
  return a

/-- Push element at `i` down to restore the max-heap property, logging all reads and writes. -/
def heapifyDown (le : α → α → Bool) (a : Vector α sz) (i : Fin sz) :
    Prog (Vec α) (Vector α sz) := do
  let leftIdx := 2 * i.1 + 1
  if hleft : leftIdx < sz then
    let left : α ← Vec.read a ⟨leftIdx, hleft⟩
    let rightIdx := leftIdx + 1
    have hleftBound : i.1 < leftIdx := by lia
    let boundedIndex := { j : Fin sz // i.1 < j.1 }
    let maxChild : α × boundedIndex ← if hright : rightIdx < sz then do
        let right : α ← Vec.read a ⟨rightIdx, hright⟩
        let maxChildPair := if le left right
              then (right, (⟨Fin.mk rightIdx hright, by lia⟩ : boundedIndex))
              else (left, (⟨Fin.mk leftIdx hleft, hleftBound⟩ : boundedIndex))
        pure maxChildPair
      else
        pure (left, (⟨Fin.mk leftIdx hleft, hleftBound⟩ : boundedIndex))
    let curr : α ← Vec.read a i
    if le curr maxChild.1 then
      let a ← Vec.write a i maxChild.1
      let a ← Vec.write a maxChild.2.1 curr
      heapifyDown le a maxChild.2.1
    else
      return a
  else
    return a
termination_by sz - i.1
decreasing_by lia

def heap_remove_max (le : α → α → Bool) (a : Vector α sz) (hpos : sz > 0) :
    Prog (Vec α) (Vector α (sz-1)) := do
  if hlen : sz > 1 then
    let last : α ← Vec.read a ⟨sz-1, by lia⟩
    let a := a.pop
    let idxZero : Fin (sz-1) := ⟨0, by lia⟩
    let a : Vector α (sz-1) ← Vec.write a idxZero last
    heapifyDown le a idxZero
  else
    return (⟨#[], by grind⟩ : Vector α (sz-1))

section Correctness

open Cslib Prog

/-- If `a` satisfies the max-heap property everywhere except possibly at `i`,
    and the children of `i` are bounded by its parent whenever `i` has a parent,
    then `heapifyUp` restores the full max-heap property. -/
lemma heapifyUp_restores_heap
    (le : α → α → Bool) [Std.Total (le · ·)] [IsTrans _ (le · ·)]
    (a : Vector α sz) (i : Fin sz)
    (hinv : maxHeapPropertyPartial le a (· ≠ i))
    (hbelow : ∀ (hpos : i.1 > 0) (k : Fin sz) (hkpos : k.1 > 0),
      (parentIdx k hkpos).1 = i → le a[k] a[(parentIdx i hpos).1]) :
    maxHeapProperty le ((heapifyUp le a i).eval vecRWModel) := by
  unfold heapifyUp
  split_ifs with hpos
  · simp only [FreeM.bind_eq_bind, FreeM.lift_def, FreeM.liftBind_bind, FreeM.pure_bind,
      eval_liftBind, vecRWModel_evalQuery]
    split_ifs with hle
    · -- swap case: recurse on parent
      let p := (parentIdx i hpos).1
      let b := (a.set p a[i]).set i a[p]
      have hpi : p.1 < i.1 := Fin.lt_def.mp (parentIdx i hpos).2
      change maxHeapProperty le ((heapifyUp le b p).eval vecRWModel)
      apply heapifyUp_restores_heap
      · intro k hkpos hkne
        by_cases hki : k = i
        · simp_all [b, p, Fin.ext_iff, parentIdx]
        · by_cases hkparenti : (parentIdx k hkpos).1 = i
          · have hiltk := Fin.lt_def.mp (hkparenti ▸ (parentIdx k hkpos).2)
            simpa [b, p, Vector.getElem_set, Fin.ext_iff, hkparenti, hiltk.ne,
              (Nat.lt_trans hpi hiltk).ne] using hbelow hpos k hkpos hkparenti
          · have hk_inv := hinv k hkpos hki
            by_cases hkparentp : (parentIdx k hkpos).1 = p
            · have := IsTrans.trans (r := (le · ·)) a[k] a[p] a[i]
                (by simpa [p, hkparentp] using hk_inv) hle
              simp_all [b, p, Fin.ext_iff, Nat.ne_of_lt hpi, Ne.symm]
            · simp_all [b, p, Fin.ext_iff, Fin.val_ne_of_ne hkparenti,
                Fin.val_ne_of_ne hkparentp, Ne.symm]
      · intro hppos k hkpos hkparentp
        have := hinv p hppos (Fin.lt_def.mpr hpi).ne
        by_cases hki : k = i <;>
        · try (have := IsTrans.trans (r := (le · ·)) a[k] a[p] a[(parentIdx p hppos).1]
                (by simpa [p, hkparentp] using hinv k hkpos hki) ‹_›)
          grind
    · intro k hkpos _
      if hki : k = i then
        exact (Std.Total.total (r := (le · ·)) a[k] a[(parentIdx k hkpos).1]).elim id
          fun h => absurd (by simpa [hki, parentIdx] using h) hle
      else exact hinv k hkpos hki
  · exact fun k hkpos _ => hinv k hkpos fun hki => absurd (hki ▸ hkpos) hpos
termination_by i.1
decreasing_by exact Fin.lt_def.mp (parentIdx i hpos).2

theorem insert_is_heap
    (le : α → α → Bool) [Std.Total (le · ·)] [IsTrans _ (le · ·)]
    (a : Vector α sz) (hheap : maxHeapProperty le a)
    (x : α) :
    let newHeap := (heap_insert le a x).eval vecRWModel
    maxHeapProperty le newHeap := by
  simp only [heap_insert, FreeM.pure_eq_pure, FreeM.bind_eq_bind, eval_bind, eval_pure]
  exact heapifyUp_restores_heap le (a.push x) ⟨sz, Nat.lt_succ_self _⟩
    (fun i hpos hne => by
      have hi := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.2) fun h => hne (Fin.ext h)
      have hp := Nat.lt_trans (Fin.lt_def.mp (parentIdx i hpos).2) hi
      simp only [Fin.getElem_fin, Vector.getElem_push_lt hi, Vector.getElem_push_lt hp]
      exact hheap ⟨i.1, hi⟩ hpos trivial)
    (by grind)

lemma heapifyUp_is_permutation (le : α → α → Bool) (a : Vector α sz) (i : Fin sz) :
    List.Perm ((heapifyUp le a i).eval vecRWModel).toList a.toList := by
  unfold heapifyUp
  split_ifs with hpos
  · simp only [FreeM.bind_eq_bind, FreeM.lift_def, FreeM.liftBind_bind,
               FreeM.pure_bind, eval_liftBind, vecRWModel_evalQuery]
    split_ifs with hle
    · let p := (parentIdx i hpos).1
      let b := (a.set p a[i]).set i a[p]
      change List.Perm ((heapifyUp le b p).eval vecRWModel).toList a.toList
      exact (heapifyUp_is_permutation le b p).trans
        (show List.Perm b.toList a.toList from (Vector.swap_perm p.2 i.2).toList)
    · exact List.Perm.refl _
  · exact List.Perm.refl _
termination_by i.1
decreasing_by exact Fin.lt_def.mp (parentIdx i hpos).2

theorem heap_insert_is_permutation (le : α → α → Bool) (a : Vector α sz) (x : α) :
    let newHeap := (heap_insert le a x).eval vecRWModel
    List.Perm newHeap.toList (a.toList ++ [x]) := by
  simpa [Vector.toList_push, heap_insert] using
    heapifyUp_is_permutation le (a.push x) ⟨sz, Nat.lt_succ_self _⟩

end Correctness

end Algorithms

end Algolean
