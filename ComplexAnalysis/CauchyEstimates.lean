/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Derivative and Taylor-coefficient bounds

Uniform derivative bounds near compact subsets of planar domains and geometric
majorants for Taylor coefficients on disks.

## Main results

* `AnalyticOnNhd.exists_cthickening_deriv_bound`: The derivative of a holomorphic function is
  uniformly bounded on a sufficiently small closed thickening of any compact subset of its open
  domain.
* `Complex.exists_taylor_geometric_bound`: Taylor coefficients on a disk admit a geometric
  majorant whose ratio is summable at every prescribed nonnegative radius strictly smaller than
  the disk radius.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology NNReal ENNReal

/-- The derivative of a holomorphic function is uniformly bounded on a sufficiently small closed
thickening of any compact subset of its open domain. -/
theorem AnalyticOnNhd.exists_cthickening_deriv_bound
    {Ω K : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (hΩopen : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ K ⊆ Ω ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Metric.cthickening δ K, ‖deriv f w‖ ≤ C := by
  obtain ⟨δ₁, hδ₁, hδ₁compact⟩ := hK.exists_isCompact_cthickening
  obtain ⟨δ₂, hδ₂, hδ₂Ω⟩ := hK.exists_cthickening_subset_open hΩopen hKΩ
  let δ := min δ₁ δ₂
  have hcompact : IsCompact (Metric.cthickening δ K) :=
    hδ₁compact.of_isClosed_subset Metric.isClosed_cthickening
      (Metric.cthickening_mono (min_le_left _ _) K)
  have hsub : Metric.cthickening δ K ⊆ Ω :=
    (Metric.cthickening_mono (min_le_right _ _) K).trans hδ₂Ω
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image (hf.deriv.continuousOn.mono hsub).norm
  exact ⟨δ, lt_min hδ₁ hδ₂, hsub, max C 0, le_max_right _ _,
    fun w hw ↦ (hC (Set.mem_image_of_mem _ hw)).trans (le_max_left _ _)⟩

/-- Taylor coefficients on a disk admit a geometric majorant whose ratio is summable
at every prescribed nonnegative radius strictly smaller than the disk radius. -/
theorem Complex.exists_taylor_geometric_bound {A : ℂ} {R r : ℝ}
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball A R))
    (hr : 0 ≤ r) (hrR : r < R) :
    ∃ C q : ℝ, 0 ≤ C ∧ 0 ≤ q ∧ q * r < 1 ∧
      ∀ n, ‖iteratedDeriv n f A / n.factorial‖ ≤ C * q ^ n := by
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  have hs : 0 < s := hr.trans_lt hrs
  let s' : ℝ≥0 := ⟨s, hs.le⟩
  have hfull := DifferentiableOn.hasFPowerSeriesOnBall (R := s')
    (hf.differentiableOn.mono (Metric.closedBall_subset_ball hsR)) (show 0 < s' from hs)
  have hlocal := (hf A (by simpa using hr.trans_lt hrR)).hasFPowerSeriesAt
  rw [hfull.hasFPowerSeriesAt.eq_formalMultilinearSeries hlocal] at hfull
  obtain ⟨ρ, hrρ, hρs⟩ := exists_between hrs
  have hρ : 0 < ρ := hr.trans_lt hrρ
  let ρ' : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hρrad : (ρ' : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ iteratedDeriv n f A / n.factorial)).radius :=
    (show (ρ' : ℝ≥0∞) < s' by exact_mod_cast hρs).trans_le hfull.r_le
  obtain ⟨C, hC, hbound⟩ := FormalMultilinearSeries.norm_le_div_pow_of_pos_of_lt_radius
    (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ iteratedDeriv n f A / n.factorial))
    (show 0 < ρ' from hρ) hρrad
  refine ⟨C, ρ⁻¹, hC.le, inv_nonneg.mpr hρ.le, ?_, ?_⟩
  · simpa [div_eq_mul_inv, mul_comm] using (div_lt_one hρ).mpr hrρ
  · intro n
    have hn := hbound n
    rw [FormalMultilinearSeries.ofScalars_norm] at hn
    change ‖iteratedDeriv n f A / n.factorial‖ ≤ C / ρ ^ n at hn
    simpa only [div_eq_mul_inv, inv_pow] using hn

end
