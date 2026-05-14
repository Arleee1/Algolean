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
  by_cases hpos : i.1 > 0
  · simp only [dif_pos hpos, FreeM.bind_eq_bind, FreeM.lift_def, FreeM.liftBind_bind,
               FreeM.pure_bind, eval_liftBind, vecRWModel_evalQuery]
    split_ifs with hle
    · -- swap: a[parent] ← a[i], a[i] ← a[parent], recurse on parent
      let p := (parentIdx i hpos).1
      let b := (a.set p a[i]).set i a[p]
      have hpi : p.1 < i.1 := by simpa [p] using (parentIdx i hpos).2
      change maxHeapProperty le ((heapifyUp le b p).eval vecRWModel)
      apply heapifyUp_restores_heap
      · intro k hkpos hkne
        by_cases hki : k = i
        · have hp_ne_i : p.1 ≠ i.1 := Nat.ne_of_lt hpi
          simpa [b, p, Vector.getElem_set, Fin.ext_iff, parentIdx, hki, hp_ne_i,
            hp_ne_i.symm,
            Nat.ne_of_gt (show i.1 > (i.1-1)/2 from
              by simpa [parentIdx] using (parentIdx i hpos).2)]
            using hle
        · by_cases hkparenti : (parentIdx k hkpos).1 = i
          · have hiltk : i.1 < k.1 := by simpa [hkparenti] using (parentIdx k hkpos).2
            have hk_ne_i : i.1 ≠ k.1 := by lia
            have hk_ne_p : p.1 ≠ k.1 := by lia
            simpa [b, p, Vector.getElem_set, Fin.ext_iff, hkparenti, hk_ne_i, hk_ne_p]
              using hbelow hpos k hkpos hkparenti
          · by_cases hkparentp : (parentIdx k hkpos).1 = p
            · have hk_le_p : le a[k] a[p] := by simpa [p, hkparentp] using hinv k hkpos hki
              have hk_ne_i : i.1 ≠ k.1 := fun h => hki (Fin.ext h.symm)
              have hk_ne_p : p.1 ≠ k.1 := fun h => hkne (Fin.ext h.symm)
              simpa [b, p, Vector.getElem_set, Fin.ext_iff, hkparentp,
                hk_ne_i, hk_ne_p, (Nat.ne_of_lt hpi).symm]
                using IsTrans.trans (r := (le · ·))
                  a[k] a[p] a[i] hk_le_p hle
            · have hk_ne_i : i.1 ≠ k.1 := fun h => hki (Fin.ext h.symm)
              have hk_ne_p : p.1 ≠ k.1 := fun h => hkne (Fin.ext h.symm)
              have hpar_ne_i : i.1 ≠ (parentIdx k hkpos).1.1 :=
                fun h => hkparenti (Fin.ext h.symm)
              have hpar_ne_p : p.1 ≠ (parentIdx k hkpos).1.1 :=
                fun h => hkparentp (Fin.ext h.symm)
              simpa [b, p, Vector.getElem_set, Fin.ext_iff,
                hk_ne_i, hk_ne_p, hpar_ne_i, hpar_ne_p] using hinv k hkpos hki
      · intro hppos k hkpos hkparentp
        have hgp_lt_p := (parentIdx p hppos).2
        have hp_ne_i : p ≠ i := Fin.ext_iff.not.mpr (by lia)
        have hgp_ne_i : (parentIdx p hppos).1 ≠ i := Fin.ext_iff.not.mpr (by lia)
        have hgp_ne_p : (parentIdx p hppos).1 ≠ p := Fin.ext_iff.not.mpr (by lia)
        have hp_old := hinv p hppos hp_ne_i
        by_cases hki : k = i
        · simpa [b, p, hki, Vector.getElem_set, Fin.ext_iff,
            Fin.val_ne_of_ne hp_ne_i.symm,
            Fin.val_ne_of_ne hgp_ne_i.symm,
            Fin.val_ne_of_ne hgp_ne_p.symm] using hp_old
        · have hk_ne_p : k ≠ p := by
            intro hkp; have := (parentIdx k hkpos).2; simp [hkparentp] at this; lia
          have hk_le_p : le a[k] a[p] := by simpa [p, hkparentp] using hinv k hkpos hki
          have hk_ne_i_val : i.1 ≠ k.1 := fun h => hki (Fin.ext h.symm)
          have hk_ne_p_val : p.1 ≠ k.1 := fun h => hk_ne_p (Fin.ext h.symm)
          simpa [b, p, Vector.getElem_set, Fin.ext_iff,
            hk_ne_i_val, hk_ne_p_val,
            Fin.val_ne_of_ne hgp_ne_i.symm,
            Fin.val_ne_of_ne hgp_ne_p.symm]
            using IsTrans.trans (r := (le · ·))
              a[k] a[p] a[(parentIdx p hppos).1] hk_le_p hp_old
    · -- no swap: le a[i] a[parent] follows from totality
      intro k hkpos _
      by_cases hki : k = i
      · rcases Std.Total.total (r := (le · ·))
          (a[k]) (a[(parentIdx k hkpos).1]) with h | h
        · exact h
        · exact absurd (by simpa [hki, parentIdx] using h) hle
      · exact hinv k hkpos hki
  · simp only [dif_neg hpos]
    exact fun k hkpos _ => hinv k hkpos fun hki => absurd (hki ▸ hkpos) hpos
termination_by i.1
decreasing_by exact Fin.lt_def.mp (parentIdx i hpos).2

theorem insert_is_heap
    (le : α → α → Bool) [Std.Total (le · ·)] [IsTrans _ (le · ·)]
    (a : Vector α sz) (hheap : maxHeapProperty le a)
    (x : α) :
    let newHeap := (heap_insert le a x).eval vecRWModel
    maxHeapProperty le newHeap := by
  dsimp [heap_insert]; rw [Prog.eval_bind]; simp only [Prog.eval_pure]
  apply heapifyUp_restores_heap
  · intro k hkpos hkne
    have hkne' : k.1 ≠ sz := fun h => hkne (Fin.ext (by simp [h]))
    have hklt : k.1 < sz := by lia
    have hparentlt : (k.1 - 1) / 2 < sz := by lia
    simpa [parentIdx, Vector.getElem_push_lt, hklt, hparentlt]
      using hheap ⟨k.1, hklt⟩ (by lia : (⟨k.1, hklt⟩ : Fin sz).1 > 0) trivial
  · intro hlastpos k hkpos hkparent
    exact absurd (show sz < k.1 by simpa [hkparent] using (parentIdx k hkpos).2) (by lia)

end Correctness

end Algorithms

end Algolean
