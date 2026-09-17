/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.CauchyCoefficients
public import SeveralComplexVariables.Reinhardt.Hull
public import SeveralComplexVariables.LocallyUniform

/-!
# Multivariable analytic Laurent series

Coefficients are arbitrary families indexed by integer multi-indices, not algebraic
`LaurentSeries`, whose support is bounded below. Sums use finite subsets of the index type.
The main expansion theorem includes coordinate hyperplanes: coefficients with negative
exponent in a coordinate vanish when the domain meets that hyperplane. This makes the
statement compatible with Lean's totalized integer powers at zero.

The analytic expansion and uniqueness proof is pending. Its explicit consequences depend
on that proof. References: Korevaar–Wiegerinck (2017), Theorem 2.7.1 and Lemma 2.8.1.
-/

@[expose] public noncomputable section

open Complex Set MeasureTheory
open scoped Real Topology

namespace SeveralComplexVariables

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The Laurent coefficient obtained by integrating over a positive-radius coordinate torus. -/
def multivariableLaurentCoeff (f : (Fin n → ℂ) → F) (r : Fin n → ℝ)
    (m : Fin n → ℤ) : F :=
  ((2 * π * I : ℂ) ^ n)⁻¹ •
    torusIntegral (fun z => (∏ i, z i ^ (-m i - 1)) • f z) 0 r

/-- An integer-indexed Laurent term. Negative powers at zero are totalized; the expansion
theorem separately forces their coefficients to vanish whenever necessary. -/
def multivariableLaurentTerm (c : (Fin n → ℤ) → F) (m : Fin n → ℤ) (z : Fin n → ℂ) : F :=
  (∏ i, z i ^ m i) • c m

/-- **Multivariable Laurent expansion on a connected Reinhardt domain.** The expansion is
absolutely and locally uniformly convergent, its coefficients are independent of the torus,
and they are unique. Negative exponents disappear in any coordinate whose hyperplane is met.
Proof pending: iterated annular Cauchy formulas, contour independence, and geometric bounds. -/
theorem multivariableLaurent_expansion {U : Set (Fin n → ℂ)} (ho : IsOpen U)
    (hc : IsConnected U) (hR : IsReinhardt U) {f : (Fin n → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i)
    (hrU : (fun i => (r i : ℂ)) ∈ U) :
    HasSumLocallyUniformlyOn (multivariableLaurentTerm (multivariableLaurentCoeff f r)) f U ∧
    (∀ z ∈ U, Summable (fun m => ‖multivariableLaurentTerm (multivariableLaurentCoeff f r) m z‖)) ∧
    (∀ (m : Fin n → ℤ) (i : Fin n), (∃ z ∈ U, z i = 0) → m i < 0 →
      multivariableLaurentCoeff f r m = 0) ∧
    (∀ s : Fin n → ℝ, (∀ i, 0 < s i) → (fun i => (s i : ℂ)) ∈ U →
      multivariableLaurentCoeff f s = multivariableLaurentCoeff f r) ∧
    (∀ c : (Fin n → ℤ) → F,
      HasSumLocallyUniformlyOn (multivariableLaurentTerm c) f U →
      c = multivariableLaurentCoeff f r) := by
  sorry

/-- Laurent expansion converges uniformly on compact subsets of the original domain.
This depends on the pending Laurent expansion theorem. -/
theorem hasSumUniformlyOn_multivariableLaurent {U K : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsConnected U) (hR : IsReinhardt U) {f : (Fin n → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i)
    (hrU : (fun i => (r i : ℂ)) ∈ U) (hK : IsCompact K) (hKU : K ⊆ U) :
    HasSumUniformlyOn (multivariableLaurentTerm (multivariableLaurentCoeff f r)) f K :=
  hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      (((multivariableLaurent_expansion ho hc hR hf hr hrU).1).mono hKU))

/-- If a Reinhardt domain meets every coordinate hyperplane, only nonnegative exponents
occur in its Laurent expansion. This is Lemma 2.8.1 applied in each coordinate. -/
theorem multivariableLaurentCoeff_eq_zero_of_not_nonneg {U : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsConnected U) (hR : IsReinhardt U)
    (hmeet : ∀ i, ∃ z ∈ U, z i = 0) {f : (Fin n → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i)
    (hrU : (fun i => (r i : ℂ)) ∈ U) {m : Fin n → ℤ} (hm : ¬ ∀ i, 0 ≤ m i) :
    multivariableLaurentCoeff f r m = 0 := by
  push Not at hm
  obtain ⟨i, hi⟩ := hm
  exact (multivariableLaurent_expansion ho hc hR hf hr hrU).2.2.1 m i (hmeet i) hi

end SeveralComplexVariables
