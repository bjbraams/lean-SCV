/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Compact exhaustions of open subsets of proper normed groups

## Main results

* `IsOpen.exists_compact_exhaustion`: An open subset of a proper normed group is exhausted by an
  increasing sequence of compact subsets, each compact subset lying in one of them.
-/

public section

open Metric Set

/-- An exhaustion of an open set by compact subsets of the form `closedBall 0 k ∩ {infDist ≥
1/(k+1)}`. Every compact subset of the open set lies in one of them, and they increase. -/
theorem IsOpen.exists_compact_exhaustion {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {U : Set E} (hU : IsOpen U) :
    ∃ L : ℕ → Set E, (∀ k, IsCompact (L k)) ∧ (∀ k, L k ⊆ U) ∧ (∀ k, L k ⊆ L (k + 1)) ∧
      ∀ K, IsCompact K → K ⊆ U → ∃ k, K ⊆ L k := by
  rcases eq_empty_or_nonempty Uᶜ with hc | hc
  · have hU' : U = univ := compl_empty_iff.mp hc
    refine ⟨fun k => closedBall 0 k, fun k => isCompact_closedBall 0 k,
      fun k => by simp only [hU', subset_univ],
      fun k => closedBall_subset_closedBall (by exact_mod_cast Nat.le_succ k), fun K hK _ => ?_⟩
    obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨k, hk⟩ := exists_nat_ge B
    exact ⟨k, hB.trans (closedBall_subset_closedBall hk)⟩
  refine ⟨fun k => closedBall 0 k ∩ {z | 1 / ((k : ℝ) + 1) ≤ infDist z Uᶜ}, fun k => ?_, fun k z
    hz => ?_,
    fun k z hz => ⟨closedBall_subset_closedBall (by exact_mod_cast Nat.le_succ k) hz.1, ?_⟩,
    fun K hK hKU => ?_⟩
  · exact isCompact_of_isClosed_isBounded (isClosed_closedBall.inter
      (isClosed_le continuous_const (continuous_infDist_pt _))) (isBounded_closedBall.subset
        inter_subset_left)
  · have hpos : 0 < infDist z Uᶜ := lt_of_lt_of_le (by positivity) hz.2
    by_contra hzU
    rw [infDist_zero_of_mem hzU] at hpos
    exact lt_irrefl _ hpos
  · have h1 : (1 : ℝ) / ((k : ℝ) + 1 + 1) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    show (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) ≤ infDist z Uᶜ
    push_cast
    exact le_trans h1 hz.2
  · obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall 0
    -- positive distance from the complement
    have hd : ∃ δ > 0, ∀ z ∈ K, δ ≤ infDist z Uᶜ := by
      rcases K.eq_empty_or_nonempty with hKe | hKne
      · exact ⟨1, one_pos, fun z hz => by simp [hKe] at hz⟩
      obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne (continuous_infDist_pt Uᶜ).continuousOn
      refine ⟨infDist z₀ Uᶜ, ?_, fun z hz => hmin hz⟩
      exact (infDist_pos_iff_notMem_closure hc).mp (by
        rw [hU.isClosed_compl.closure_eq]
        exact notMem_compl_iff.mpr (hKU hz₀))
    obtain ⟨δ, hδ, hδK⟩ := hd
    obtain ⟨k₁, hk₁⟩ := exists_nat_ge B
    obtain ⟨k₂, hk₂⟩ := exists_nat_ge (1 / δ)
    refine ⟨max k₁ k₂, fun z hz => ⟨closedBall_subset_closedBall ?_ (hB hz), ?_⟩⟩
    · exact hk₁.trans (by exact_mod_cast le_max_left k₁ k₂)
    · have hk₂' : (1 : ℝ) / δ ≤ (max k₁ k₂ : ℕ) + 1 := by
        have : (k₂ : ℝ) ≤ (max k₁ k₂ : ℕ) := by exact_mod_cast le_max_right k₁ k₂
        linarith
      have : (1 : ℝ) / ((max k₁ k₂ : ℕ) + 1) ≤ δ := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hδ] at hk₂'
        linarith
      exact this.trans (hδK z hz)

end
