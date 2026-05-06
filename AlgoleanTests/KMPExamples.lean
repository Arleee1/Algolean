/-
Copyright (c) 2026 Ethan Ermovick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Ermovick
-/

module

public import Algolean.Algorithms.KMPPatternSearch

@[expose] public section

/-!
# Examples

This file contains some examples of KMP, including examples for `buildLPS` and `kmpPatternSearch`.
-/
namespace AlgoleanTests

open Algolean Algorithms

section LPSExamples

lemma empty_LPS [BEq α] :
    let pat : List α := []
    let lps := (buildLPS pat).eval Comparison.natCost
    lps =               [] := by
  rfl

lemma singleton_LPS [BEq α] (x : α) :
    let pat := [x]
    let lps := (buildLPS pat).eval Comparison.natCost
    lps =      [0] := by
  rfl

lemma repeated_LPS [BEq α] [LawfulBEq α] (x : α) (n : Nat) :
    let pat := List.replicate n x
    let lps := (buildLPS pat).eval Comparison.natCost
    lps = List.range n := by
  obtain ⟨hlen, hlps⟩ := buildLPS_eval (List.replicate n x)
  refine List.ext_getElem (by simpa using hlen) fun i hi hi' => ?_
  have hrep : LongestPrefixSuffixOf (List.replicate n x) (i + 1) i := by
    refine ⟨⟨by lia, ?_⟩, fun l hl => Nat.le_of_lt_succ hl.1⟩
    intro j hj
    rw [List.getElem?_eq_getElem (by lia), List.getElem?_eq_getElem (by lia)]
    simp
  simpa using Nat.le_antisymm
    (hrep.2 _ (hlps i (by simpa using hi')).1)
    ((hlps i (by simpa using hi')).2 _ hrep.1)

lemma nonoverlapping_LPS :
    let pat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    let lps := (buildLPS pat).eval Comparison.natCost
    lps =      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rfl

lemma alternating_LPS :
    let pat := [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
    let lps := (buildLPS pat).eval Comparison.natCost
    lps =      [0, 0, 1, 2, 3, 4, 5, 6, 7, 8] := by
  rfl

lemma random_LPS1 :
    let pat := [1, 0, 1, 0, 1, 0, 1, 1, 1, 1]
    let lps := (buildLPS pat).eval Comparison.natCost
    lps =      [0, 0, 1, 2, 3, 4, 5, 1, 1, 1] := by
  rfl

lemma random_LPS2 :
    let pat := [1, 0, 1, 1, 1, 0, 0, 0, 0, 1]
    let lps := (buildLPS pat).eval Comparison.natCost
    lps =      [0, 0, 1, 1, 1, 2, 0, 0, 0, 1] := by
  rfl

lemma random_LPS3 :
    let pat := [0, 0, 1, 0, 0, 1, 0, 1, 1, 1]
    let lps := (buildLPS pat).eval Comparison.natCost
    lps =      [0, 1, 0, 1, 2, 3, 4, 0, 0, 0] := by
  rfl

end LPSExamples

end AlgoleanTests
