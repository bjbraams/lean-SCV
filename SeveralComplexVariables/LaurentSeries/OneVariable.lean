/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.LaurentSeries.Basic
public import SeveralComplexVariables.RemovableSingularity.Cauchy

/-!
# Holomorphic parameter dependence of one-variable Laurent coefficients

A circle Laurent coefficient of a function depending holomorphically on several complex
parameters is analytic in those parameters under the stated continuity and domain hypotheses.
This supplies the parameter-dependence step for several-variable Laurent expansions, using the
planar coefficient definition from `ComplexAnalysis.LaurentSeries.Basic`.

## Main results

* `SeveralComplexVariables.analyticOnNhd_circleLaurentCoeff`: A fixed-circle Laurent coefficient
  is analytic in any finite-dimensional complex parameter on which the integrand depends
  holomorphically.

## References

* V. Scheidemann, *Introduction to Complex Analysis in Several Variables*,
  Birkhäuser, 2005 (background on holomorphic functions of several variables).
-/

public noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A fixed-circle Laurent coefficient is analytic in any finite-dimensional complex parameter on
which the integrand depends holomorphically. -/
theorem analyticOnNhd_circleLaurentCoeff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {V : Set E} (hV : IsOpen V)
    {U : Set (E × ℂ)} {f : E × ℂ → F} (hf : AnalyticOnNhd ℂ f U)
    {r : ℝ} (hr : 0 < r) (hsub : ∀ z ∈ V, ∀ w ∈ sphere (0 : ℂ) r, (z, w) ∈ U)
    (k : ℤ) : AnalyticOnNhd ℂ (fun z => circleLaurentCoeff (fun w => f (z, w)) r k) V := by
  let W := U ∩ {p : E × ℂ | p.2 ≠ 0}
  have hH : AnalyticOnNhd ℂ (fun p : E × ℂ => p.2 ^ (-k - 1) • f p) W := by
    intro p hp
    exact (analyticAt_snd.zpow (n := -k - 1) hp.2).smul (hf p hp.1)
  apply (analyticOnNhd_circleIntegral_kernel hV hH hr.le ?_).const_smul
  intro z hz w hw
  refine ⟨hsub z hz w hw, ?_⟩
  exact norm_pos_iff.mp (by rw [mem_sphere_zero_iff_norm.mp hw]; exact hr)

end SeveralComplexVariables
