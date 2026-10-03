/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue

/-!
# First exit from an open set

A continuous function on a real interval that starts in an open set and ends outside it
has a first exit. At that time its value belongs to the frontier of the set.
-/

public section

open Set

/-- A continuous function starting inside an open set and ending outside it first leaves
through its frontier. Only continuity on the closed interval is required. -/
theorem ContinuousOn.exists_first_mem_frontier {X : Type*} [TopologicalSpace X]
    {f : ℝ → X} {a b : ℝ} (hf : ContinuousOn f (Icc a b)) (hab : a ≤ b)
    {A : Set X} (hA : IsOpen A) (ha : f a ∈ A) (hb : f b ∉ A) :
    ∃ t ∈ Ioc a b, f t ∈ frontier A ∧ MapsTo f (Ico a t) A := by
  let S : Set ℝ := Icc a b ∩ f ⁻¹' Aᶜ
  have hSc : IsClosed S := hf.preimage_isClosed_of_isClosed isClosed_Icc hA.isClosed_compl
  have hSne : S.Nonempty := ⟨b, ⟨hab, le_rfl⟩, hb⟩
  have hSbdd : BddBelow S := ⟨a, fun t ht ↦ ht.1.1⟩
  have htS : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  have hat : a < sInf S := lt_of_le_of_ne htS.1.1 fun h ↦ htS.2 (h ▸ ha)
  have hprefix : MapsTo f (Ico a (sInf S)) A := by
    intro s hs
    by_contra h
    exact notMem_of_lt_csInf hs.2 hSbdd ⟨⟨hs.1, hs.2.le.trans htS.1.2⟩, h⟩
  refine ⟨sInf S, ⟨hat, htS.1.2⟩, ?_, hprefix⟩
  rw [hA.frontier_eq]
  refine ⟨?_, htS.2⟩
  apply ((hf _ htS.1).mono (fun s hs ↦ ⟨hs.1, hs.2.le.trans htS.1.2⟩)).mem_closure
    (s := Ico a (sInf S)) _ hprefix
  rw [closure_Ico hat.ne]
  exact ⟨hat.le, le_rfl⟩

end
