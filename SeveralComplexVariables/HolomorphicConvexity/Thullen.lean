/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.HolomorphicConvexity.BoundaryDistance
public import Mathlib.Analysis.Normed.Module.Connected
public import SeveralComplexVariables.DomainOfHolomorphy
public import SeveralComplexVariables.PolydiscTaylor
public import SeveralComplexVariables.PowerSeriesConvergence.Analytic

/-!
# Thullen's lemma and the boundary distance of holomorphic hulls

Cauchy bounds on derivatives transfer to a holomorphic hull. The pending analytic step
assembles these bounds into Taylor continuation on a polydisc of variable radius controlled
by a scalar holomorphic function. Agreement is asserted near the center, not on unrelated
components of the overlap. The deductions of radius preservation, exact boundary distance,
and holomorphic convexity are proved from that single pending step.

References: Scheidemann §6.2 and §7.3; Hörmander §2.5; Korevaar–Wiegerinck §6.4.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology ENNReal

namespace SeveralComplexVariables

variable {n : ℕ}

/-- Mixed derivative bounds transfer to the holomorphic hull of the set on which they
hold. This elementary step is independent of the pending Taylor continuation theorem. -/
theorem norm_multiIndexDeriv_le_on_holomorphicHull {U K : Set (Fin n → ℂ)}
    (ho : IsOpen U) {f : (Fin n → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (m : Fin n → ℕ) {M : ℝ} (hM : ∀ z ∈ K, ‖multiIndexDeriv m f z‖ ≤ M) :
    ∀ z ∈ holomorphicHull U K, ‖multiIndexDeriv m f z‖ ≤ M :=
  norm_le_on_holomorphicHull (hf.iteratedPartialDeriv ho (multiIndexList m)) hM

/-- The scalar Taylor sum centered at an arbitrary point, using the existing normalized
multivariate Taylor coefficients. -/
def taylorSumAt (f : (Fin n → ℂ) → ℂ) (a z : Fin n → ℂ) : ℂ :=
  powerSeriesSum (holomorphicTaylorSeries f a) (z - a)

/-- **Thullen's lemma, with a holomorphic radius bound.** Taylor series centered at a
hull point converge locally uniformly on the indicated polydisc and continue the original
germ. Proof pending: uniform Cauchy estimates on compact variable-radius thickenings. -/
theorem taylor_continuation_on_holomorphicHull {U K : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {q f : (Fin n → ℂ) → ℂ} (hq : AnalyticOnNhd ℂ q U) (hf : AnalyticOnNhd ℂ f U)
    (hr : ∀ w ∈ K, ball w ‖q w‖ ⊆ U) {a : Fin n → ℂ} (ha : a ∈ holomorphicHull U K) :
    AnalyticOnNhd ℂ (taylorSumAt f a) (ball a ‖q a‖) ∧
      taylorSumAt f a =ᶠ[𝓝 a] f ∧
      HasSumLocallyUniformlyOn
        (fun (m : Fin n →₀ ℕ) z => (∏ i, (z i - a i) ^ m i) * holomorphicTaylorSeries f a m)
        (taylorSumAt f a) (ball a ‖q a‖) := by
  sorry

/-- The constant-radius form of Thullen's continuation lemma. Its proof depends on the
pending variable-radius Taylor theorem. -/
theorem exists_continuation_ball_of_mem_holomorphicHull {U K : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {r : ℝ} (hr : 0 < r)
    (hball : ∀ w ∈ K, ball w r ⊆ U) {a : Fin n → ℂ} (ha : a ∈ holomorphicHull U K)
    {f : (Fin n → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    ∃ g, AnalyticOnNhd ℂ g (ball a r) ∧ g =ᶠ[𝓝 a] f := by
  have hnorm : ‖(r : ℂ)‖ = r := Complex.norm_of_nonneg hr.le
  have h := taylor_continuation_on_holomorphicHull ho hK hKU
    (q := fun _ => (r : ℂ)) analyticOnNhd_const hf (by simpa only [hnorm] using hball) ha
  exact ⟨taylorSumAt f a, by simpa only [hnorm] using h.1, h.2.1⟩

/-- On a domain of holomorphy, a ball supporting continuation of every germ at its center
must lie in the domain. The overlap is chosen uniformly, independently of the function. -/
theorem IsDomainOfHolomorphy.ball_subset_of_continuation {U : Set (Fin n → ℂ)}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) {a : Fin n → ℂ} (ha : a ∈ U)
    {r : ℝ} (hr : 0 < r)
    (he : ∀ f : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ f U →
      ∃ g, AnalyticOnNhd ℂ g (ball a r) ∧ g =ᶠ[𝓝 a] f) : ball a r ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp ho a ha
  let W := ball a (min ε r)
  have haW : a ∈ W := mem_ball_self (lt_min hε hr)
  have hWU : W ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hεU
  have hWV : W ⊆ ball a r := ball_subset_ball (min_le_right _ _)
  apply hU (ball a r) W isOpen_ball (isConnected_ball hr) isOpen_ball ⟨a, haW⟩ hWU hWV
  intro f hf
  obtain ⟨g, hg, heq⟩ := he f hf
  exact ⟨g, hg, (hg.mono hWV).eqOn_of_preconnected_of_eventuallyEq
    (hf.mono hWU) isPreconnected_ball haW heq⟩

/-- A domain of holomorphy preserves every radius bound supplied by a holomorphic
function on a compact set. Depends on the pending Thullen lemma. -/
theorem IsDomainOfHolomorphy.holomorphic_radius_bound {U K : Set (Fin n → ℂ)}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {q : (Fin n → ℂ) → ℂ} (hq : AnalyticOnNhd ℂ q U)
    (hr : ∀ w ∈ K, ball w ‖q w‖ ⊆ U) :
    ∀ a ∈ holomorphicHull U K, ball a ‖q a‖ ⊆ U := by
  intro a ha
  by_cases hqa : ‖q a‖ = 0
  · simp [hqa]
  · apply hU.ball_subset_of_continuation ho ha.1 (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hqa))
    intro f hf
    have h := taylor_continuation_on_holomorphicHull ho hK hKU hq hf hr ha
    exact ⟨taylorSumAt f a, h.1, h.2.1⟩

/-- Domains of holomorphy preserve uniform polydisc radii on compact hulls.
Depends on the pending Thullen lemma. -/
theorem IsDomainOfHolomorphy.hullRadiusProperty {U : Set (Fin n → ℂ)}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) : HasHolomorphicHullRadiusProperty U := by
  intro K hK hKU r hr hball a ha
  exact hU.ball_subset_of_continuation ho ha.1 hr fun _ hf =>
    exists_continuation_ball_of_mem_holomorphicHull ho hK hKU hr hball ha hf

/-- The boundary distance of a compact holomorphic hull equals that of the original
compact set in a domain of holomorphy. Depends on the pending Thullen lemma. -/
theorem IsDomainOfHolomorphy.hullDistanceProperty {U : Set (Fin n → ℂ)}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) : HasHolomorphicHullDistanceProperty U :=
  (hU.hullRadiusProperty ho).distanceProperty

/-- **Cartan–Thullen, forward implication.** A domain of holomorphy is holomorphically
convex. The remaining analytic dependency is Thullen's Taylor continuation lemma. -/
theorem IsDomainOfHolomorphy.isHolomorphicallyConvex {U : Set (Fin n → ℂ)}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) : IsHolomorphicallyConvex U :=
  (hU.hullRadiusProperty ho).isHolomorphicallyConvex ho

end SeveralComplexVariables
