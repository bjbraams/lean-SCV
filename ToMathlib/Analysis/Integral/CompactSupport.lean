/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integration helpers for compactly supported and weighted functions

An integrable scalar weight can be multiplied by a continuous normed-space-valued function on a
compact set without losing integrability. A second result gives integrability on a half-line for
continuous functions that vanish beyond a finite radius.

## Main results

* `MeasureTheory.IntegrableOn.smul_continuousOn_of_isCompact`: An integrable scalar weight times
  a continuous normed-space-valued function on a compact set is integrable. Compactness gives
  both boundedness and a separable image, so no countability assumption on either ambient space
  is required.
* `MeasureTheory.integrableOn_Ioi_of_continuous_of_eq_zero`: A continuous function on the
  half-line vanishing beyond a radius is integrable there.

## References

* `Mathlib.Analysis.Calculus.ParametricIntegral`: formal background used by this module.
* `Mathlib.MeasureTheory.Integral.IntegralEqImproper`: formal background used by this module.
-/

public noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

variable {𝕜 α E : Type*} [NormedField 𝕜] [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- An integrable scalar weight times a continuous normed-space-valued function on a compact set is
integrable. Compactness gives both boundedness and a separable image, so no countability
assumption on either ambient space is required. -/
theorem MeasureTheory.IntegrableOn.smul_continuousOn_of_isCompact
    [TopologicalSpace α] [BorelSpace α] [T2Space α]
    {μ : Measure α} {K : Set α} {g : α → 𝕜} {H : α → E}
    (hg : IntegrableOn g K μ) (hH : ContinuousOn H K) (hK : IsCompact K) :
    IntegrableOn (fun t ↦ g t • H t) K μ := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image hH.norm
  apply (hg.norm.mul_const M).mono'
    (hg.aestronglyMeasurable.smul (hH.aestronglyMeasurable_of_isCompact hK hK.measurableSet))
  filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
  change ‖g t • H t‖ ≤ ‖g t‖ * M
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hM ⟨t, ht, rfl⟩) (norm_nonneg _)

end

public section

open MeasureTheory Set

namespace MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [NormedSpace ℂ F] in
/-- A continuous function on the half-line vanishing beyond a radius is integrable there. -/
theorem integrableOn_Ioi_of_continuous_of_eq_zero {g : ℝ → F} (hg : Continuous g) {R : ℝ}
    (hz : ∀ r, R < r → g r = 0) : IntegrableOn g (Ioi 0) := by
  have h1 : IntegrableOn g (Icc 0 R) := hg.continuousOn.integrableOn_Icc
  have h2 : IntegrableOn g (Ioi R) :=
    ((integrable_zero _ _ _).integrableOn).congr_fun (fun r hr ↦ (hz r hr).symm) measurableSet_Ioi
  refine (h1.union h2).mono_set fun r hr ↦ ?_
  rcases le_or_gt r R with h | h
  · exact Or.inl ⟨le_of_lt hr, h⟩
  · exact Or.inr h

end MeasureTheory

end
