/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Closure
public import Mathlib.Topology.Connected.Basic

/-!
# Frontiers and complementary components

## Main results

* `IsOpen.notMem_of_mem_frontier`: A frontier point of an open set does not belong to the set.
* `IsOpen.connectedComponentIn_compl_frontier`: An open preconnected set is a component
  of the complement of its frontier.
* `IsClosed.isPreconnected_compl_of_isPreconnected_sdiff`: A connected exterior neighborhood
  of a closed set suffices to prove that its entire complement is preconnected.

## References

* `Mathlib.Topology.Closure`: formal background used by this module.
* `Mathlib.Topology.Connected.Basic`: formal background used by this module.
-/

public section

/-- A frontier point of an open set does not belong to the set. -/
theorem IsOpen.notMem_of_mem_frontier {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsOpen s) {x : X} (hx : x ∈ frontier s) : x ∉ s := by
  rw [hs.frontier_eq] at hx
  exact hx.2

/-- A nonempty open preconnected set is a connected component of the complement of
its frontier. This does not assert how many other components there are. -/
theorem IsOpen.connectedComponentIn_compl_frontier {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) (hc : IsPreconnected U) {x : X} (hx : x ∈ U) :
    connectedComponentIn (frontier U)ᶜ x = U := by
  have hsub : U ⊆ (frontier U)ᶜ := fun y hy hfr ↦ (hU.notMem_of_mem_frontier hfr) hy
  apply Set.Subset.antisymm
  · apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hU
      ⟨x, mem_connectedComponentIn (hsub hx), hx⟩
    rintro y ⟨hy, hyc⟩
    by_contra hn
    exact (connectedComponentIn_subset _ _ hyc) (by rw [hU.frontier_eq]; exact ⟨hy, hn⟩)
  · exact hc.subset_connectedComponentIn hx hsub

/-- A disjoint open cover of a closed set's complement cannot place an entire exterior
neighborhood on one side while both sides are nonempty in a preconnected ambient space. -/
private theorem not_disjoint_compl_open_cover_of_sdiff_subset
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {K O u v : Set X}
    (hK : IsClosed K) (hO : IsOpen O) (hKO : K ⊆ O) (hu : IsOpen u) (hv : IsOpen v)
    (hcover : Kᶜ ⊆ u ∪ v) (hune : (Kᶜ ∩ u).Nonempty) (hvne : (Kᶜ ∩ v).Nonempty)
    (hside : O \ K ⊆ Kᶜ ∩ u) : ¬ Disjoint (Kᶜ ∩ u) (Kᶜ ∩ v) := by
  intro hd
  obtain ⟨x, hx⟩ := hvne
  have hall : (Set.univ : Set X) ⊆ (O ∪ (Kᶜ ∩ u)) ∪ (Kᶜ ∩ v) := by
    intro y _
    by_cases hy : y ∈ K
    · exact Or.inl (Or.inl (hKO hy))
    · rcases hcover hy with h | h
      · exact Or.inl (Or.inr ⟨hy, h⟩)
      · exact Or.inr ⟨hy, h⟩
  have hnleft : (Set.univ ∩ (O ∪ (Kᶜ ∩ u))).Nonempty := by
    obtain ⟨y, hy⟩ := hune
    exact ⟨y, Set.mem_univ _, Or.inr hy⟩
  obtain ⟨y, _, hy, hyv⟩ := isPreconnected_univ _ _
    (hO.union (hK.isOpen_compl.inter hu)) (hK.isOpen_compl.inter hv)
    hall hnleft ⟨x, Set.mem_univ _, hx⟩
  apply hd.le_bot (show y ∈ (Kᶜ ∩ u) ∩ (Kᶜ ∩ v) from ⟨?_, hyv⟩)
  rcases hy with hy | hy
  · exact hside ⟨hy, hyv.1⟩
  · exact hy

/-- In a preconnected space, a closed set has preconnected complement if some open
neighborhood of it has preconnected complement relative to that neighborhood. -/
theorem IsClosed.isPreconnected_compl_of_isPreconnected_sdiff
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {K O : Set X}
    (hK : IsClosed K) (hO : IsOpen O) (hKO : K ⊆ O) (hc : IsPreconnected (O \ K)) :
    IsPreconnected Kᶜ := by
  intro u v hu hv hcover hnu hnv
  by_contra hn
  have hd : Disjoint (Kᶜ ∩ u) (Kᶜ ∩ v) := by
    rw [Set.disjoint_left]
    intro x hxu hxv
    exact hn ⟨x, hxu.1, hxu.2, hxv.2⟩
  have hwu : O \ K ⊆ (Kᶜ ∩ u) ∪ (Kᶜ ∩ v) := by
    intro x hx
    rcases hcover hx.2 with h | h
    · exact Or.inl ⟨hx.2, h⟩
    · exact Or.inr ⟨hx.2, h⟩
  have hside : O \ K ⊆ Kᶜ ∩ u ∨ O \ K ⊆ Kᶜ ∩ v := by
    by_cases h : ((O \ K) ∩ (Kᶜ ∩ u)).Nonempty
    · exact Or.inl (hc.subset_left_of_subset_union (hK.isOpen_compl.inter hu)
        (hK.isOpen_compl.inter hv) hd hwu h)
    · right
      intro x hx
      exact (hwu hx).resolve_left (fun hxu ↦ h ⟨x, hx, hxu⟩)
  rcases hside with h | h
  · exact not_disjoint_compl_open_cover_of_sdiff_subset hK hO hKO hu hv hcover hnu hnv h hd
  · exact not_disjoint_compl_open_cover_of_sdiff_subset hK hO hKO hv hu
      (by simpa only [Set.union_comm] using hcover) hnv hnu h hd.symm

end
