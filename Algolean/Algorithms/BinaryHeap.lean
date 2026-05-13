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

-- /-- heapifyUp does not modify elements outside the ancestor chain of i -/
-- lemma heapifyUp_non_ancestor (le : α → α → Bool) (a : Vector α sz) (i j : Fin sz)
--     (h : ¬ AncestorOrSelf j i) :
--     ((heapifyUp le a i).eval vecRWModel)[j] = a[j] := by
--   unfold heapifyUp
--   by_cases hpos : i.1 > 0
--   · have hji  : j ≠ i    := fun heq => h (heq ▸ .refl i)
--     have hjanc : ¬ AncestorOrSelf j (parentIdx i hpos).1 := fun ha => h (.step i hpos ha)
--     have hjpar : j ≠ (parentIdx i hpos).1 := fun heq => hjanc (heq ▸ .refl _)
--     simp only [dif_pos hpos, FreeM.bind_eq_bind, FreeM.lift_def, FreeM.liftBind_bind,
--                FreeM.pure_bind, eval_liftBind, vecRWModel_evalQuery]
--     split_ifs with hle
--     · simp only [eval_liftBind, vecRWModel_evalQuery]
--       rw [heapifyUp_non_ancestor le _ (parentIdx i hpos).1 j hjanc]
--       simp [Vector.getElem_set_ne, Ne.symm (Fin.val_ne_of_ne hji),
--             Ne.symm (Fin.val_ne_of_ne hjpar)]
--     · simp
--   · simp [dif_neg hpos]
-- termination_by i.1
-- decreasing_by exact Fin.lt_def.mp (parentIdx i hpos).2

/-- If `a` satisfies the max-heap property everywhere except possibly at `i`,
    then `heapifyUp` restores the full max-heap property. -/
lemma heapifyUp_restores_heap
    (le : α → α → Bool) [Std.Total (le · ·)] [IsTrans _ (le · ·)]
    (a : Vector α sz) (i : Fin sz)
    (hinv : maxHeapPropertyPartial le a (· ≠ i)) :
    maxHeapProperty le ((heapifyUp le a i).eval vecRWModel) := by
  unfold heapifyUp
  by_cases hpos : i.1 > 0
  · simp only [dif_pos hpos, FreeM.bind_eq_bind, FreeM.lift_def, FreeM.liftBind_bind,
               FreeM.pure_bind, eval_liftBind, vecRWModel_evalQuery]
    split_ifs with hle
    · -- swap: a[parent] ← a[i], a[i] ← a[i], recurse on parent
      -- invariant case analysis: k=i uses totality, parent(k)=parent uses transitivity, else hinv
      apply heapifyUp_restores_heap
      intro k hkpos hkne
      sorry
    · -- no swap: array unchanged; le a[i] a[parent] follows from totality since ¬le a[parent] a[i]
      simp only [maxHeapProperty, maxHeapPropertyPartial]
      intro k hkpos _
      by_cases hki : k = i
      · subst hki; sorry
      · exact hinv k hkpos hki
  · simp only [dif_neg hpos, maxHeapProperty, maxHeapPropertyPartial]
    intro k hkpos _
    apply hinv k hkpos
    intro hki; subst hki; exact absurd hkpos hpos
termination_by i.1
decreasing_by exact Fin.lt_def.mp (parentIdx i hpos).2

theorem insert_is_heap
    (le : α → α → Bool) [Std.Total (le · ·)] [IsTrans _ (le · ·)]
    (a : Vector α sz) (hheap : maxHeapProperty le a)
    (x : α) :
    let newHeap := (heap_insert le a x).eval vecRWModel
    maxHeapProperty le newHeap := by
  sorry

end Correctness

end Algorithms

end Algolean
