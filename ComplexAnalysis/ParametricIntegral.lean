/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import ToMathlib.Analysis.Integral.CompactSupport

/-!
# Differentiation of compact integrals in one complex parameter

Fixed integrable weights and arbitrary compact integration sets are allowed.

## Main results

* `hasDerivAt_integral_of_continuousOn_compact`: Differentiation under an integral over a
  compact set when the integrand and its pointwise complex derivative are jointly continuous.
  Compactness supplies domination.
* `hasDerivAt_integral_smul_of_continuousOn_compact`: A fixed integrable scalar weight can be
  included in compact-domain differentiation. Only the kernel and its derivative must be jointly
  continuous; the weight may be singular on the boundary of the integration domain.
* `hasDerivAt_integral_mul_of_continuousOn_compact`: A fixed integrable scalar weight can be
  included in compact-domain differentiation. Only the kernel and its derivative must be jointly
  continuous; the weight may be singular on the boundary of the integration domain.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Differentiation under an integral over a compact set when the integrand and its pointwise
complex derivative are jointly continuous. Compactness supplies domination. -/
theorem hasDerivAt_integral_of_continuousOn_compact
    [TopologicalSpace α] [BorelSpace α] [T2Space α]
    {μ : Measure α} [IsLocallyFiniteMeasure μ] {K : Set α} (hK : IsCompact K)
    {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    {F F' : ℂ → α → E}
    (hF : ContinuousOn (fun p : ℂ × α ↦ F p.1 p.2) (U ×ˢ K))
    (hF' : ContinuousOn (fun p : ℂ × α ↦ F' p.1 p.2) (U ×ˢ K))
    (hd : ∀ z ∈ U, ∀ a ∈ K, HasDerivAt (fun w ↦ F w a) (F' z a) z) :
    HasDerivAt (fun z ↦ ∫ a in K, F z a ∂μ) (∫ a in K, F' x a ∂μ) x := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hc : IsCompact (Metric.closedBall x r ×ˢ K) := (isCompact_closedBall _ _).prod hK
  have hcont := hF'.mono (Set.prod_mono hball Subset.rfl)
  obtain ⟨M, hM⟩ := hc.bddAbove_image hcont.norm
  have hslice {z : ℂ} (hz : z ∈ U) : ContinuousOn (F z) K :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun a ha ↦ ⟨hz, ha⟩)
  have hslice' {z : ℂ} (hz : z ∈ U) : ContinuousOn (F' z) K :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn (fun a ha ↦ ⟨hz, ha⟩)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ.restrict K) (F := F) (F' := F') (bound := fun _ ↦ M)
    (Metric.closedBall_mem_nhds x hr) ?_ ((hslice hx).integrableOn_compact hK)
    ((hslice' hx).integrableOn_compact hK).aestronglyMeasurable ?_
    (integrableOn_const hK.measure_ne_top) ?_).2
  · filter_upwards [hU.eventually_mem hx] with z hz
    exact ((hslice hz).integrableOn_compact hK).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro z hz
    exact hM (mem_image_of_mem (fun p : ℂ × α ↦ ‖F' p.1 p.2‖)
      (show (z, a) ∈ Metric.closedBall x r ×ˢ K from ⟨hz, ha⟩))
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro z hz
    exact hd z (hball hz) a ha

omit [CompleteSpace E] in
/-- A fixed integrable scalar weight can be included in compact-domain differentiation. Only the
kernel and its derivative must be jointly continuous; the weight may be singular on the boundary
of the integration domain. -/
theorem hasDerivAt_integral_smul_of_continuousOn_compact
    [TopologicalSpace α] [BorelSpace α] [T2Space α]
    {μ : Measure α} {K : Set α} (hK : IsCompact K)
    {g : α → ℂ} (hg : IntegrableOn g K μ)
    {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    {F F' : ℂ → α → E}
    (hF : ContinuousOn (fun p : ℂ × α ↦ F p.1 p.2) (U ×ˢ K))
    (hF' : ContinuousOn (fun p : ℂ × α ↦ F' p.1 p.2) (U ×ˢ K))
    (hd : ∀ z ∈ U, ∀ a ∈ K, HasDerivAt (fun w ↦ F w a) (F' z a) z) :
    HasDerivAt (fun z ↦ ∫ a in K, g a • F z a ∂μ)
      (∫ a in K, g a • F' x a ∂μ) x := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hc : IsCompact (Metric.closedBall x r ×ˢ K) := (isCompact_closedBall _ _).prod hK
  obtain ⟨M, hM⟩ := hc.bddAbove_image
    (hF'.mono (Set.prod_mono hball Subset.rfl)).norm
  have hslice {z : ℂ} (hz : z ∈ U) : ContinuousOn (F z) K :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun a ha ↦ ⟨hz, ha⟩)
  have hslice' {z : ℂ} (hz : z ∈ U) : ContinuousOn (F' z) K :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn (fun a ha ↦ ⟨hz, ha⟩)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ.restrict K) (F := fun z a ↦ g a • F z a)
    (F' := fun z a ↦ g a • F' z a) (bound := fun a ↦ ‖g a‖ * M)
    (Metric.closedBall_mem_nhds x hr) ?_ (hg.smul_continuousOn_of_isCompact (hslice hx) hK)
    (hg.smul_continuousOn_of_isCompact (hslice' hx) hK).aestronglyMeasurable ?_
    (hg.norm.mul_const M) ?_).2
  · filter_upwards [hU.eventually_mem hx] with z hz
    exact (hg.smul_continuousOn_of_isCompact (hslice hz) hK).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro z hz
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (hM (mem_image_of_mem (fun p : ℂ × α ↦ ‖F' p.1 p.2‖)
        (show (z, a) ∈ Metric.closedBall x r ×ˢ K from ⟨hz, ha⟩))) (norm_nonneg _)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro z hz
    exact (hd z (hball hz) a ha).const_smul (g a)

/-- A fixed integrable scalar weight can be included in compact-domain differentiation. Only the
kernel and its derivative must be jointly continuous; the weight may be singular on the boundary
of the integration domain. -/
theorem hasDerivAt_integral_mul_of_continuousOn_compact
    [TopologicalSpace α] [BorelSpace α] [T2Space α]
    {μ : Measure α} {K : Set α} (hK : IsCompact K)
    {g : α → ℂ} (hg : IntegrableOn g K μ)
    {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    {F F' : ℂ → α → ℂ}
    (hF : ContinuousOn (fun p : ℂ × α ↦ F p.1 p.2) (U ×ˢ K))
    (hF' : ContinuousOn (fun p : ℂ × α ↦ F' p.1 p.2) (U ×ˢ K))
    (hd : ∀ z ∈ U, ∀ a ∈ K, HasDerivAt (fun w ↦ F w a) (F' z a) z) :
    HasDerivAt (fun z ↦ ∫ a in K, g a * F z a ∂μ)
      (∫ a in K, g a * F' x a ∂μ) x := by
  simpa only [smul_eq_mul] using
    hasDerivAt_integral_smul_of_continuousOn_compact hK hg hU hx hF hF' hd

end
