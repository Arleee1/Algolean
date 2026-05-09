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

@[simp]
def maxHeapProperty (le : α → α → Bool) (a : Vector α sz) : Prop :=
  ∀ (i : Fin sz),
    ((h: 2 * i.val + 1 < sz) → le a[2 * i.val + 1] a[i]) ∧
    ((h: 2 * i.val + 2 < sz) → le a[2 * i.val + 2] a[i])

/-- A max-heap data structure. -/
structure BinaryHeap (α) (le : α → α → Bool) where
  arr : Array α

def empty (le) : BinaryHeap α le := ⟨#[]⟩

instance (le) : Inhabited (BinaryHeap α le) := ⟨empty _⟩

instance (le) : EmptyCollection (BinaryHeap α le) := ⟨empty _⟩

def singleton (le) (x : α) : BinaryHeap α le := ⟨#[x]⟩

def size (self : BinaryHeap α le) : Nat := self.1.size

/-- `O(1)`. Get an element in the heap by index. -/
def get (self : BinaryHeap α le) (i : Fin (size self)) : Prog (Vec α) α := do
  Vec.read self.1.toVector i

/-- Find the index of the larger child of node `i`, logging reads of both children. -/
def maxChild (le : α → α → Bool) (a : Vector α sz) (i : Fin sz) :
    Prog (Vec α) (Option { j : Fin sz // i < j }) := do
  let left := 2 * i.1 + 1
  let right := left + 1
  if hleft : left < sz then
    if hright : right < sz then
      let al ← Vec.read a ⟨left, hleft⟩
      let ar ← Vec.read a ⟨right, hright⟩
      if le al ar then
        return some ⟨⟨right, hright⟩, by
          have hlt : i.1 < right := by lia
          exact Fin.lt_def.2 hlt⟩
      else
        return some ⟨⟨left, hleft⟩, by
          have hlt : i.1 < left := by lia
          exact Fin.lt_def.2 hlt⟩
    else
      return some ⟨⟨left, hleft⟩, by
        have hlt : i.1 < left := by lia
        exact Fin.lt_def.2 hlt⟩
  else return none

/-- Push element at `i` down to restore the max-heap property, logging all reads and writes. -/
def heapifyDown (le : α → α → Bool) (a : Vector α sz) (i : Fin sz) :
    Prog (Vec α) (Vector α sz) := do
  let j? ← maxChild le a i
  match j? with
  | none => return a
  | some ⟨j, _hj⟩ =>
    let ai ← Vec.read a i
    let aj ← Vec.read a j
    if le ai aj then
      let a'  ← Vec.write a  i aj
      let a'' ← Vec.write a' j ai
      heapifyDown le a'' j
    else return a
termination_by sz - i.val
decreasing_by
  have : i.val < j.val := by simpa using _hj
  lia

/-- Push element at `i` up to restore the max-heap property, logging all reads and writes. -/
def heapifyUp (le : α → α → Bool) (a : Vector α sz) (i : Fin sz) :
    Prog (Vec α) (Vector α sz) := do
  match i with
  | ⟨0, _⟩ => return a
  | ⟨i'+1, hi⟩ =>
    let j : Fin sz := ⟨i'/2, by lia⟩
    let aj ← Vec.read a j
    let ai ← Vec.read a ⟨i'+1, hi⟩
    if le aj ai then
      let a'  ← Vec.write a  ⟨i'+1, hi⟩ aj
      let a'' ← Vec.write a' j              ai
      heapifyUp le a'' j
    else return a
termination_by i.val
decreasing_by lia

def insert (self : BinaryHeap α le) (x : α) : Prog (Vec α) (BinaryHeap α le) := do
  let a ← heapifyUp le (self.1.toVector.push x) ⟨self.1.size, Nat.lt_succ_self _⟩
  return ⟨a.toArray⟩

def mkHeap (le : α → α → Bool) (a : Array α) : Prog (Vec α) (BinaryHeap α le) := do
  let v ← loop a.toVector (a.size / 2) (Nat.div_le_self ..)
  return ⟨v.toArray⟩
where
  loop : (v : Vector α a.size) → (i : Nat) → i ≤ a.size → Prog (Vec α) (Vector α a.size)
    | v, 0,   _  => return v
    | v, i+1, h  => do
      let v' ← heapifyDown le v ⟨i, Nat.lt_of_succ_le h⟩
      loop v' i (Nat.le_trans (Nat.le_succ _) h)

/-- `O(1)`. Get the maximum element in a `BinaryHeap`. -/
def max (self : BinaryHeap α lt) : Prog (Vec α) (Option α) := do
  if h0 : self.1.size = 0 then
    return none
  else
    let v ← Vec.read self.1.toVector ⟨0, Nat.zero_lt_of_ne_zero h0⟩
    return some v

def popMax (self : BinaryHeap α le) : Prog (Vec α) (BinaryHeap α le) := do
  if h0 : self.1.size = 0 then
    return self
  else
    have hs  : self.1.size - 1 < self.1.size := Nat.pred_lt h0
    have h0' : 0 < self.1.size               := Nat.zero_lt_of_ne_zero h0
    -- Swap root with last element via the query model, then pop structurally.
    let last ← Vec.read  self.1.toVector ⟨self.1.size - 1, hs⟩
    let v : Vector α self.1.size ← Vec.write self.1.toVector ⟨0, h0'⟩ last
    let v'   := v.pop
    if h : 0 < self.1.size - 1 then
      let a ← heapifyDown le v' ⟨0, h⟩
      return ⟨a.toArray⟩
    else
      return ⟨v'.toArray⟩

def replaceMax (self : BinaryHeap α le) (x : α) : Prog (Vec α) (Option α × BinaryHeap α le) := do
  if h0 : self.1.size = 0 then
    return (none, ⟨self.1.push x⟩)
  else
    have h0' : 0 < self.1.size := Nat.zero_lt_of_ne_zero h0
    let m  ← Vec.read  self.1.toVector ⟨0, h0'⟩
    let v  ← Vec.write self.1.toVector ⟨0, h0'⟩ x
    let a  ← heapifyDown le v ⟨0, h0'⟩
    return (some m, ⟨a.toArray⟩)

end Algorithms

end Algolean
