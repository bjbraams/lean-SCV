/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.LaurentSeries
public import SeveralComplexVariables.FunctionSpace

/-!
# Laurent approximation and coefficient projections

Finite Laurent sums approximate holomorphic functions uniformly on compact subsets.
The approximation is derived from the pending Laurent expansion. Continuous coefficient
projections on the compact-open holomorphic space are stated as a further pending target.
Only the elementary analytic consequences of Scheidemann (2005), Section 2.2, are used;
no representation theory of compact groups is introduced.
-/

public noncomputable section

open Set Filter
open scoped Topology

namespace SeveralComplexVariables

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Finite canonical Laurent sums approximate uniformly on any given compact subset.
Depends on the Laurent expansion theorem, with no finite-dimensional target restriction. -/
theorem exists_finite_laurent_approximation {U K : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsConnected U) (hR : IsReinhardt U)
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U)
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrU : (fun i => (r i : ℂ)) ∈ U)
    (hK : IsCompact K) (hKU : K ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (Fin n → ℤ), ∀ z ∈ K,
      ‖f z - ∑ m ∈ s, multivariableLaurentTerm (multivariableLaurentCoeff f r) m z‖ < ε := by
  have h := hasSumUniformlyOn_iff_tendstoUniformlyOn.mp
    (hasSumUniformlyOn_multivariableLaurent ho hc hR hf hr hrU hK hKU)
  obtain ⟨s, hs⟩ := (Metric.tendstoUniformlyOn_iff.mp h ε hε).exists
  exact ⟨s, fun z hz => by simpa [dist_eq_norm] using hs z hz⟩

/-- Continuous Laurent projections, their coefficient formulas, and their mutual
orthogonality. Proof pending: continuity of torus integration, holomorphy of the permitted
monomials, and Laurent uniqueness. Terms with forbidden negative exponents are zero.
The finite partial sums converge in the existing compact-open topology. -/
theorem exists_laurentProjections (U : TopologicalSpace.Opens (Fin n → ℂ))
    (hc : IsConnected (U : Set (Fin n → ℂ))) (hR : IsReinhardt (U : Set (Fin n → ℂ)))
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrU : (fun i => (r i : ℂ)) ∈ U) :
    ∃ P : (Fin n → ℤ) → HolomorphicMap U F →L[ℂ] HolomorphicMap U F,
      (∀ m f z, (P m f).val z =
        multivariableLaurentTerm (multivariableLaurentCoeff (openExtension U f.val) r) m z) ∧
      (∀ m k f, P m (P k f) = if m = k then P m f else 0) ∧
      (∀ f, Tendsto (fun s : Finset (Fin n → ℤ) => ∑ m ∈ s, P m f) atTop (𝓝 f)) := by
  sorry

end SeveralComplexVariables
