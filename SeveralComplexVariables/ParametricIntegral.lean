/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.ParametricIntegral
public import SeveralComplexVariables.Analyticity

/-!
# Analytic dependence of integrals on several complex parameters

The parameter space is an arbitrary finite-dimensional complex normed space. This file combines
Mathlib's dominated Fréchet-differentiation theorem with the SCV holomorphy–analyticity theorem.
The compact-integral derivative formulas in one complex parameter are imported from
`ComplexAnalysis.ParametricIntegral`; general integration support remains in
`ToMathlib.Analysis.Integral.CompactSupport`.

`analyticOnNhd_integral_of_dominated_of_fderiv_le` packages the local dominated derivative
criterion at every point of an open parameter domain. Its name remains in the root namespace,
consistently with Mathlib's parametric-integral API.

## Main results

* `analyticOnNhd_integral_of_dominated_of_fderiv_le`: An integral on a finite-dimensional
  complex parameter space is analytic if, locally at every parameter, its pointwise Fréchet
  derivatives have an integrable uniform bound. The hypotheses are grouped pointwise so that the
  dominating function and neighborhood may depend on the base parameter.

## References

* V. Scheidemann, *Introduction to Complex Analysis in Several Variables*,
  Birkhäuser, 2005 (background on holomorphic functions of several variables).
-/

public section

open Filter MeasureTheory Set
open scoped Topology

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An integral on a finite-dimensional complex parameter space is analytic if, locally at every
parameter, its pointwise Fréchet derivatives have an integrable uniform bound. The hypotheses
are grouped pointwise so that the dominating function and neighborhood may depend on the base
parameter. -/
theorem analyticOnNhd_integral_of_dominated_of_fderiv_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    {μ : Measure α} {U : Set P} {F : P → α → E}
    (hU : IsOpen U)
    (hdom : ∀ x ∈ U, ∃ (s : Set P) (bound : α → ℝ)
        (F' : P → α → P →L[ℂ] E),
      s ∈ nhds x ∧
      (∀ᶠ y in nhds x, AEStronglyMeasurable (F y) μ) ∧
      Integrable (F x) μ ∧ AEStronglyMeasurable (F' x) μ ∧
      (∀ᵐ a ∂μ, ∀ y ∈ s, ‖F' y a‖ ≤ bound a) ∧ Integrable bound μ ∧
      (∀ᵐ a ∂μ, ∀ y ∈ s, HasFDerivAt (F · a) (F' y a) y)) :
    AnalyticOnNhd ℂ (fun x ↦ ∫ a, F x a ∂μ) U := by
  apply DifferentiableOn.analyticOnNhd_of_finiteDimensional _ hU
  intro x hx
  obtain ⟨s, bound, F', hs, hmeas, hint, hF'meas, hbound, hboundInt, hdiff⟩ := hdom x hx
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le hs hmeas hint hF'meas
    hbound hboundInt hdiff).differentiableAt.differentiableWithinAt


end
