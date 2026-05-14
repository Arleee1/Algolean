/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, François G. Dorais, Ethan Ermovick
-/
module

public import Algolean.Models.ReadWriteVec

@[expose] public section

/-!
# Binary Heap


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

/-- Find the index of the larger child of node `i`, logging reads of both children. -/
def maxChildIdx (le : α → α → Bool) (a : Vector α sz) (i : Fin sz) :
    Prog (Vec α) (Option { j : Fin sz // i < j }) := do
  let left := 2 * i.1 + 1
  let right := left + 1
  let child (k : Nat) (hk : k < sz) (hlt : i.1 < k) : Option { j : Fin sz // i < j } :=
    some ⟨⟨k, hk⟩, Fin.lt_def.2 hlt⟩
  if hleft : left < sz then
    if hright : right < sz then
      let al ← Vec.read a ⟨left, hleft⟩
      let ar ← Vec.read a ⟨right, hright⟩
      if le al ar then
        return child right hright (by lia)
      else
        return child left hleft (by lia)
    else
      return child left hleft (by lia)
  else return none

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

section Correctness

open Cslib Prog

/-- `j` is `i` or an ancestor of `i` in the heap tree -/
inductive AncestorOrSelf : Fin sz → Fin sz → Prop where
  | refl (i : Fin sz) : AncestorOrSelf i i
  | step (i : Fin sz) (hpos : i.1 > 0) :
      AncestorOrSelf j (parentIdx i hpos).1 → AncestorOrSelf j i

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
  · simp only [FreeM.bind_eq_bind, FreeM.lift_def, FreeM.liftBind_bind,
      FreeM.pure_bind, eval_liftBind, vecRWModel_evalQuery]
    split_ifs with hle
    · -- swap: a[parent] ← a[i], a[i] ← a[parent], recurse on parent
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
              (Nat.lt_trans hpi hiltk).ne]
              using hbelow hpos k hkpos hkparenti
          · have hki_ne := (Fin.val_ne_of_ne hki)
            have hkne_ne := (Fin.val_ne_of_ne hkne)
            by_cases hkparentp : (parentIdx k hkpos).1 = p
            · have hk_le_p : le a[k] a[p] := by simpa [p, hkparentp] using hinv k hkpos hki
              simpa [b, p, hkparentp, hki_ne, hkne_ne, (Nat.ne_of_lt hpi), Ne.symm]
                using IsTrans.trans (r := (le · ·)) a[k] a[p] a[i] hk_le_p hle
            · simpa [b, p, hki_ne, hkne_ne, (Fin.val_ne_of_ne hkparenti),
                (Fin.val_ne_of_ne hkparentp), Ne.symm] using hinv k hkpos hki
      · intro hppos k hkpos hkparentp
        have hp_old := hinv p hppos (Fin.lt_def.mpr hpi).ne
        by_cases hki : k = i
        · grind
        · have hk_le_p : le a[k] a[p] := by simpa [p, hkparentp] using hinv k hkpos hki
          have := IsTrans.trans (r := (le · ·)) a[k] a[p] a[(parentIdx p hppos).1] hk_le_p hp_old
          grind
    · -- no swap: le a[i] a[parent] follows from totality
      intro k hkpos _
      by_cases hki : k = i
      · rcases Std.Total.total (r := (le · ·))
          (a[k]) (a[(parentIdx k hkpos).1]) with h | h
        · exact h
        · exact absurd (by simpa [hki, parentIdx] using h) hle
      · exact hinv k hkpos hki
  · exact fun k hkpos _ => hinv k hkpos fun hki => absurd (hki ▸ hkpos) hpos
termination_by i.1
decreasing_by exact Fin.lt_def.mp (parentIdx i hpos).2

theorem insert_is_heap
    (le : α → α → Bool) [Std.Total (le · ·)] [IsTrans _ (le · ·)]
    (a : Vector α sz) (hheap : maxHeapProperty le a)
    (x : α) :
    let newHeap := (heap_insert le a x).eval vecRWModel
    maxHeapProperty le newHeap := by
  simp only [heap_insert, FreeM.pure_eq_pure, Cslib.FreeM.bind_eq_bind,
     Prog.eval_bind, Prog.eval_pure]
  exact heapifyUp_restores_heap le (a.push x) ⟨sz, Nat.lt_succ_self _⟩
    (by
      intro i hpos hne
      have hi_lt : i.1 < sz := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.2) fun h => hne (Fin.ext h)
      have hpar_lt : (parentIdx i hpos).1.1 < sz :=
        Nat.lt_trans (Fin.lt_def.mp (parentIdx i hpos).2) hi_lt
      simp only [Fin.getElem_fin, Vector.getElem_push_lt hi_lt, Vector.getElem_push_lt hpar_lt]
      exact hheap ⟨i.1, hi_lt⟩ hpos trivial)
    (by grind)

end Correctness

end Algorithms

end Algolean
