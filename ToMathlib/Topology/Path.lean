/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Path
public import ToMathlib.Topology.Order.IntermediateValue

/-!
# First exit of a path from an open set

A path starting inside an open set and ending outside it first leaves through the frontier.
The interval theorem is `ContinuousOn.exists_first_mem_frontier`; the path results use
Mathlib's real-parameter extension `Path.extend`.
-/

public section

open Set

/-- A path from inside an open set to outside it first leaves through its frontier. -/
theorem Path.extend_exists_first_mem_frontier {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : Path x y) {A : Set X} (hA : IsOpen A) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ t ∈ Ioc (0 : ℝ) 1, γ.extend t ∈ frontier A ∧ MapsTo γ.extend (Ico 0 t) A :=
  γ.continuous_extend.continuousOn.exists_first_mem_frontier zero_le_one hA
    (by simpa using hx) (by simpa using hy)

/-- First time a path starting in an open set leaves that set. -/
theorem Path.extend_exists_first_notMem {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : Path x y) {A : Set X} (hA : IsOpen A)
    (hx : γ.extend 0 ∈ A) (hy : γ.extend 1 ∉ A) :
    ∃ t, t ∈ Icc (0 : ℝ) 1 ∧ γ.extend t ∉ A ∧ 0 < t ∧
      ∀ s, 0 ≤ s → s < t → γ.extend s ∈ A := by
  obtain ⟨t, ht, hfront, hprefix⟩ := γ.extend_exists_first_mem_frontier hA
    (by simpa using hx) (by simpa using hy)
  exact ⟨t, ⟨ht.1.le, ht.2⟩, (hA.frontier_eq ▸ hfront).2, ht.1,
    fun s hs hst ↦ hprefix ⟨hs, hst⟩⟩

end
