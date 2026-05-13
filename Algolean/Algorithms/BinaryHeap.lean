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
      -- invariant case analysis: k=i uses totality, parent(k)=parent uses transitivity, else hinv
      let p := (parentIdx i hpos).1
      let b := (a.set p a[i]).set i a[p]
      have hpi : p.1 < i.1 := by simpa [p] using (parentIdx i hpos).2
      change maxHeapProperty le ((heapifyUp le b p).eval vecRWModel)
      apply heapifyUp_restores_heap
      · intro k hkpos hkne
        by_cases hki : k = i
        · have hp_ne_i_val : p.1 ≠ i.1 := by
            exact Nat.ne_of_lt hpi
          have hi_ne_parent_nat : i.1 ≠ (i.1 - 1) / 2 := by
            exact Nat.ne_of_gt <| by
              simpa [parentIdx] using (parentIdx i hpos).2
          simpa [b, p, Vector.getElem_set, Fin.ext_iff, parentIdx, hki, hp_ne_i_val,
            Ne.symm hp_ne_i_val, hi_ne_parent_nat] using hle
        · by_cases hkparenti : (parentIdx k hkpos).1 = i
          · have hk_ne_p : k ≠ p := by
              intro hk_eq_p
              have hlt : i.1 < p.1 := by
                simpa [hkparenti, hk_eq_p, p] using (parentIdx k hkpos).2
              have hplti : p.1 < i.1 := by
                simpa [p] using (parentIdx i hpos).2
              omega
            have hi_ne_k_val : i.1 ≠ k.1 := fun h => hki (Fin.ext h.symm)
            have hp_ne_k_val : p.1 ≠ k.1 := fun h => hk_ne_p (Fin.ext h.symm)
            have hle_child := hbelow hpos k hkpos hkparenti
            simpa [b, p, Vector.getElem_set, Fin.ext_iff, hi_ne_k_val, hp_ne_k_val,
              hkparenti] using hle_child
          · by_cases hkparentp : (parentIdx k hkpos).1 = p
            · have hk_old := hinv k hkpos hki
              have hk_le_p : le a[k] a[p] = true := by
                simpa [p, hkparentp] using hk_old
              have hk_ne_p : k ≠ p := hkne
              have hi_ne_k_val : i.1 ≠ k.1 := fun h => hki (Fin.ext h.symm)
              have hp_ne_k_val : p.1 ≠ k.1 := fun h => hk_ne_p (Fin.ext h.symm)
              have hi_ne_p_val : i.1 ≠ p.1 := by
                have hplti : p.1 < i.1 := by
                  simpa [p] using (parentIdx i hpos).2
                omega
              have hk_le_i := IsTrans.trans (r := fun x y => le x y = true)
                a[k] a[p] a[i] hk_le_p hle
              simpa [b, p, Vector.getElem_set, Fin.ext_iff, hi_ne_k_val, hp_ne_k_val,
                hi_ne_p_val, hkparentp] using hk_le_i
            · have hk_old := hinv k hkpos hki
              have hk_ne_p : k ≠ p := hkne
              have hi_ne_k_val : i.1 ≠ k.1 := fun h => hki (Fin.ext h.symm)
              have hp_ne_k_val : p.1 ≠ k.1 := fun h => hk_ne_p (Fin.ext h.symm)
              have hi_ne_parent_val : i.1 ≠ (parentIdx k hkpos).1.1 := fun h =>
                hkparenti (Fin.ext h.symm)
              have hp_ne_parent_val : p.1 ≠ (parentIdx k hkpos).1.1 := fun h =>
                hkparentp (Fin.ext h.symm)
              simpa [b, p, Vector.getElem_set, Fin.ext_iff, hi_ne_k_val, hp_ne_k_val,
                hi_ne_parent_val, hp_ne_parent_val] using hk_old
      · intro hppos k hkpos hkparentp
        have hp_ne_i : p ≠ i := by
          intro hpiEq
          exact (Nat.ne_of_lt hpi) (congrArg Fin.val hpiEq)
        have hgp_ne_i : (parentIdx p hppos).1 ≠ i := by
          intro hgp
          have hval : (parentIdx p hppos).1.1 = i.1 := congrArg Fin.val hgp
          have hlt : i.1 < i.1 := by
            simpa [hval] using Nat.lt_trans (parentIdx p hppos).2 hpi
          exact Nat.lt_irrefl _ hlt
        have hgp_ne_p : (parentIdx p hppos).1 ≠ p := by
          intro hgp
          have hval : (parentIdx p hppos).1.1 = p.1 := congrArg Fin.val hgp
          have hneq : (parentIdx p hppos).1.1 ≠ p.1 := Nat.ne_of_lt (parentIdx p hppos).2
          exact hneq hval
        have hp_old := hinv p hppos hp_ne_i
        by_cases hki : k = i
        · have hi_ne_p_val : i.1 ≠ p.1 := fun h => hp_ne_i (Fin.ext h.symm)
          have hi_ne_gp_val : i.1 ≠ (parentIdx p hppos).1.1 := fun h =>
            hgp_ne_i (Fin.ext h.symm)
          have hp_ne_gp_val : p.1 ≠ (parentIdx p hppos).1.1 := fun h =>
            hgp_ne_p (Fin.ext h.symm)
          simpa [b, p, hki, hi_ne_p_val, hi_ne_gp_val, hp_ne_gp_val] using hp_old
        · have hk_ne_p : k ≠ p := by
            intro hkp
            have hplt : p.1 < k.1 := by
              simpa [hkparentp] using (parentIdx k hkpos).2
            have := congrArg Fin.val hkp
            omega
          have hk_old := hinv k hkpos hki
          have hk_le_p : le a[k] a[p] = true := by
            simpa [p, hkparentp] using hk_old
          have hk_le_gp := IsTrans.trans (r := fun x y => le x y = true)
            a[k] a[p] a[(parentIdx p hppos).1] hk_le_p hp_old
          have hi_ne_k_val : i.1 ≠ k.1 := fun h => hki (Fin.ext h.symm)
          have hp_ne_k_val : p.1 ≠ k.1 := fun h => hk_ne_p (Fin.ext h.symm)
          have hi_ne_gp_val : i.1 ≠ (parentIdx p hppos).1.1 := fun h =>
            hgp_ne_i (Fin.ext h.symm)
          have hp_ne_gp_val : p.1 ≠ (parentIdx p hppos).1.1 := fun h =>
            hgp_ne_p (Fin.ext h.symm)
          simpa [b, p, hi_ne_k_val, hp_ne_k_val, hi_ne_gp_val, hp_ne_gp_val]
            using hk_le_gp
    · -- no swap: array unchanged; le a[i] a[parent] follows from totality since ¬le a[parent] a[i]
      simp only [maxHeapProperty, maxHeapPropertyPartial]
      intro k hkpos _
      by_cases hki : k = i
      · rcases Std.Total.total (r := fun x y => le x y = true)
          (a[k]) (a[(parentIdx k hkpos).1]) with h | h
        · exact h
        · exfalso
          apply hle
          simpa [hki, parentIdx] using h
      · exact hinv k hkpos hki
  · simp only [dif_neg hpos, maxHeapProperty, maxHeapPropertyPartial]
    intro k hkpos _
    apply hinv k hkpos
    intro hki; subst hki; exact absurd hkpos hpos

theorem insert_is_heap
    (le : α → α → Bool) [Std.Total (le · ·)] [IsTrans _ (le · ·)]
    (a : Vector α sz) (hheap : maxHeapProperty le a)
    (x : α) :
    let newHeap := (heap_insert le a x).eval vecRWModel
    maxHeapProperty le newHeap := by
  dsimp [heap_insert]
  rw [Prog.eval_bind]
  simp only [Prog.eval_pure]
  apply heapifyUp_restores_heap
  · intro k hkpos hkne
    have hkne' : k.1 ≠ sz := fun h => hkne (Fin.ext h)
    have hklt : k.1 < sz := by omega
    let hkold : Fin sz := ⟨k.1, hklt⟩
    have hkoldpos : hkold.1 > 0 := by
      simpa [hkold] using hkpos
    have hheap' := hheap hkold hkoldpos trivial
    have hparentlt' : (k.1 - 1) / 2 < sz := by
      simpa [parentIdx] using Nat.lt_trans (parentIdx k hkpos).2 hklt
    simpa [hkold, parentIdx, Vector.getElem_push_lt, hklt, hparentlt'] using hheap'
  · intro hlastpos k hkpos hkparent
    exfalso
    have hlast_lt_k : sz < k.1 := by
      simpa [hkparent] using (parentIdx k hkpos).2
    omega

end Correctness

end Algorithms

end Algolean
