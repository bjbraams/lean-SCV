/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import SeveralComplexVariables.CircularContinuation
public import SeveralComplexVariables.Reinhardt.Extension
public import SeveralComplexVariables.Runge

/-!
# Examples of Runge domains

Complete Reinhardt open sets in `ℂ^ι`, for any finite index type `ι`, are Runge domains, since holomorphic functions on them are
represented by their Taylor series at the origin, converging locally uniformly. More generally,
circular connected open sets containing the origin are Runge domains, since holomorphic
functions on them are locally uniform sums of their homogeneous expansions, whose terms are
polynomials. In particular polydiscs and balls centered at the origin, and the whole space, are
Runge domains.

Runge domains are transported by holomorphic maps with polynomial inverses: if `U` is Runge, `Φ`
is holomorphic on `U` with values in `U'`, and `Ψ` is a polynomial map from `U'` into `U` with
`Φ ∘ Ψ = id` on `U'`, then `U'` is Runge; the dimensions of the two spaces may differ.
Translates and polynomial-automorphic images of Runge domains are Runge
([Jakóbczak–Jarnicki][JakobczakJarnicki2021], Proposition 4.3.2).

References: [Hörmander][Hormander1973] (1973), Section 2.7;
[Jakóbczak–Jarnicki][JakobczakJarnicki2021] (2021), Section 4.3.

## Main definitions

* `mvPolynomialMap`: The polynomial map with components `G i`, between coordinate spaces of
  possibly different dimensions.

## Main results

* `IsCompleteReinhardt.isRungeDomain`: **Complete Reinhardt open sets are Runge domains** :
  holomorphic functions are locally uniform sums of their Taylor series at the origin.
* `IsCircular.isRungeDomain`: **Circular connected open sets containing the origin are Runge
  domains** : holomorphic functions are locally uniform sums of their homogeneous expansions, whose
  terms are polynomials.
* `IsRungeDomain.transport`: **Transport of Runge domains.** If `U` is a Runge domain, `Φ` is
  holomorphic on `U` with values in `U'`, and `Ψ` is a polynomial map from `U'` into `U` with
  `Φ ∘ Ψ = id` on `U'`, then `U'` is a Runge domain. The two coordinate spaces may have
  different dimensions.
* `IsRungeDomain.of_comp_equiv`: **Reindexing.** Runge domains are invariant under reindexing of
  coordinates; this reduces the complete Reinhardt case to `Fin n`.

## References

* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public noncomputable section

open Filter Function Metric Set
open scoped Topology

namespace SeveralComplexVariables

section Transport

variable {ι σ τ R : Type*}

/-- The polynomial map from `σ → R` to `τ → R` with components `G i`. -/
@[expose] def mvPolynomialMap [CommSemiring R] (G : τ → MvPolynomial σ R) (z : σ → R) : τ → R :=
  fun i => MvPolynomial.eval z (G i)

/-- Polynomial maps are continuous. -/
theorem continuous_mvPolynomialMap [CommSemiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] (G : τ → MvPolynomial σ R) : Continuous (mvPolynomialMap G) :=
  continuous_pi fun i => (G i).continuous_eval

/-- Substitution of a polynomial map into a polynomial. -/
theorem eval_bind₁_mvPolynomialMap [CommSemiring R] (G : τ → MvPolynomial σ R)
    (P : MvPolynomial τ R) (z : σ → R) :
    MvPolynomial.eval z (MvPolynomial.bind₁ G P) = MvPolynomial.eval (mvPolynomialMap G z) P := by
  simp only [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
  rfl

/-- **Transport of Runge domains.** If `U ⊆ ℂ^σ` is a Runge domain, `Φ` is holomorphic on `U`
with values in `U' ⊆ ℂ^τ`, and `Ψ` is a polynomial map from `U'` into `U` with `Φ ∘ Ψ = id` on
`U'`, then `U'` is a Runge domain. The dimensions of the two spaces may differ; for instance `Φ`
may be a holomorphic retraction onto a lower-dimensional coordinate space. -/
theorem IsRungeDomain.transport [Fintype σ] [Fintype τ] {U : Set (σ → ℂ)} {U' : Set (τ → ℂ)}
    (hU : IsRungeDomain U) {Φ : (σ → ℂ) → (τ → ℂ)} (hΦ : AnalyticOnNhd ℂ Φ U)
    (hΦU : MapsTo Φ U U') (G : σ → MvPolynomial τ ℂ) (hGU : MapsTo (mvPolynomialMap G) U' U)
    (hinv : ∀ z ∈ U', Φ (mvPolynomialMap G z) = z) : IsRungeDomain U' := by
  intro f hf K hK hKU ε hε
  have hfΦ : AnalyticOnNhd ℂ (f ∘ Φ) U := hf.comp hΦ hΦU
  have hK' : IsCompact (mvPolynomialMap G '' K) := hK.image (continuous_mvPolynomialMap G)
  obtain ⟨P, hP⟩ := hU (f ∘ Φ) hfΦ _ hK' (image_subset_iff.mpr fun z hz => hGU (hKU hz)) ε hε
  refine ⟨MvPolynomial.bind₁ G P, fun z hz => ?_⟩
  have := hP (mvPolynomialMap G z) (mem_image_of_mem _ hz)
  rw [eval_bind₁_mvPolynomialMap]
  simpa [comp_apply, hinv z (hKU hz)] using this

/-- Runge domains are transported by polynomial automorphisms with polynomial inverses. -/
theorem IsRungeDomain.image_mvPolynomialMap [Fintype ι] {U : Set (ι → ℂ)} (hU : IsRungeDomain U)
    (F G : ι → MvPolynomial ι ℂ)
    (hFG : ∀ z, mvPolynomialMap F (mvPolynomialMap G z) = z)
    (hGF : ∀ z, mvPolynomialMap G (mvPolynomialMap F z) = z) :
    IsRungeDomain (mvPolynomialMap F '' U) := by
  refine hU.transport (Φ := mvPolynomialMap F) ?_ (mapsTo_image _ _) G ?_ fun z _ => hFG z
  · exact fun z _ => by
      apply analyticAt_pi_iff.mpr
      intro i
      exact AnalyticOnNhd.eval_mvPolynomial (F i) z (mem_univ z)
  · rintro _ ⟨z, hz, rfl⟩
    rw [hGF]
    exact hz

/-- Translates of Runge domains are Runge domains. -/
theorem IsRungeDomain.translate [Fintype ι] {U : Set (ι → ℂ)} (hU : IsRungeDomain U)
    (a : ι → ℂ) : IsRungeDomain ((fun z => z + a) '' U) := by
  have hF : (fun z : ι → ℂ => z + a) =
      mvPolynomialMap (fun i => MvPolynomial.X i + MvPolynomial.C (a i)) := by
    funext z i
    simp [mvPolynomialMap]
  rw [hF]
  refine hU.image_mvPolynomialMap _ (fun i => MvPolynomial.X i - MvPolynomial.C (a i)) ?_ ?_ <;>
    · intro z
      funext i
      simp [mvPolynomialMap]

/-- **Reindexing.** A set is a Runge domain if its preimage under a reindexing of coordinates is. -/
theorem IsRungeDomain.of_comp_equiv [Fintype σ] [Fintype τ] (e : τ ≃ σ) {U : Set (τ → ℂ)}
    (h : IsRungeDomain {w : σ → ℂ | w ∘ e ∈ U}) : IsRungeDomain U := by
  have hG : ∀ z : τ → ℂ, mvPolynomialMap (fun j => MvPolynomial.X (e.symm j)) z ∘ e = z :=
    fun z => funext fun i => by simp [mvPolynomialMap]
  exact h.transport (Φ := fun w => w ∘ e) ((analyticOnNhd_comp_equiv e).mono (subset_univ _))
    (fun _ hw => hw) (fun j => MvPolynomial.X (e.symm j)) (fun z hz => by simpa [hG z] using hz)
    fun z _ => hG z

end Transport

section Reinhardt

/-- Complete Reinhardt open sets in `ℂ^{Fin n}` are Runge domains, by the Taylor series at the
origin. -/
private theorem IsCompleteReinhardt.isRungeDomain_fin {n : ℕ} {U : Set (Fin n → ℂ)} (ho : IsOpen U)
    (hc : IsCompleteReinhardt U) : IsRungeDomain U := by
  intro f hf K hK hKU ε hε
  obtain ⟨hdom, heq⟩
    := IsCompleteReinhardt.subset_convergenceDomain_and_eqOn_powerSeriesSum ho hc hf
  have hsum := hasSumUniformlyOn_powerSeries (taylorCoefficientsAtZero f) hK (hKU.trans hdom)
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn, Metric.tendstoUniformlyOn_iff] at hsum
  obtain ⟨t, ht⟩ := (hsum ε hε).exists
  obtain ⟨P, hP⟩ := exists_mvPolynomial_eval_eq_sum t (fun m => taylorCoefficientsAtZero f m)
  refine ⟨P, fun z hz => ?_⟩
  have := ht z hz
  rw [dist_eq_norm, heq (hKU hz)] at this
  rw [hP z]
  simpa only [smul_eq_mul] using this

/-- **Complete Reinhardt open sets are Runge domains**: holomorphic functions are locally uniform
sums of their Taylor series at the origin. The coordinates are reindexed by `Fin n`. -/
theorem IsCompleteReinhardt.isRungeDomain {ι : Type*} [Fintype ι] {U : Set (ι → ℂ)}
    (ho : IsOpen U) (hc : IsCompleteReinhardt U) : IsRungeDomain U := by
  let e := Fintype.equivFin ι
  refine IsRungeDomain.of_comp_equiv e (IsCompleteReinhardt.isRungeDomain_fin ?_ ?_)
  · exact ho.preimage (continuous_pi fun _ => continuous_apply _)
  · exact fun z hz w hw => hc hz fun i => hw (e i)

/-- Polydiscs centered at the origin are Runge domains. -/
theorem isRungeDomain_polydisc {ι : Type*} [Fintype ι] (r : ι → ℝ) :
    IsRungeDomain (polydisc (0 : ι → ℂ) r) :=
  (isCompleteReinhardt_polydisc r).isRungeDomain (isOpen_polydisc 0 r)

/-- Balls centered at the origin are Runge domains. -/
theorem isRungeDomain_ball {ι : Type*} [Fintype ι] (r : ℝ) :
    IsRungeDomain (ball (0 : ι → ℂ) r) := by
  refine IsCompleteReinhardt.isRungeDomain isOpen_ball fun z hz w hw => ?_
  rw [mem_ball_zero_iff] at hz ⊢
  refine lt_of_le_of_lt ?_ hz
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg z)]
  exact fun i => (hw i).trans (norm_le_pi_norm z i)

end Reinhardt

section Circular

variable {ι : Type*} [Fintype ι]

/-- The restriction of a continuous multilinear map on `ℂ^ι` to the diagonal is a polynomial. -/
theorem exists_mvPolynomial_eval_eq_multilinear_diagonal {k : ℕ}
    (m : ContinuousMultilinearMap ℂ (fun _ : Fin k => (ι → ℂ)) ℂ) :
    ∃ P : MvPolynomial ι ℂ, ∀ z, MvPolynomial.eval z P = m (fun _ => z) := by
  classical
  refine ⟨∑ r : Fin k → ι, MvPolynomial.C (m fun j => Pi.single (r j) (1 : ℂ)) *
    ∏ j, MvPolynomial.X (r j), fun z => ?_⟩
  have hz : (fun _ : Fin k => z) = fun _ => ∑ i : ι, z i • Pi.single i (1 : ℂ) := by
    funext _ j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hz, ContinuousMultilinearMap.map_sum]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]

/-- Homogeneous terms of power series on `ℂ^ι` are polynomials. -/
theorem exists_mvPolynomial_eval_eq_homogeneousTerm
    (p : FormalMultilinearSeries ℂ (ι → ℂ) ℂ) (k : ℕ) :
    ∃ P : MvPolynomial ι ℂ, ∀ z, MvPolynomial.eval z P = homogeneousTerm p k z := by
  obtain ⟨P, hP⟩ := exists_mvPolynomial_eval_eq_multilinear_diagonal (p k)
  exact ⟨P, fun z => by rw [hP, homogeneousTerm_apply]⟩

/-- **Circular connected open sets containing the origin are Runge domains**: holomorphic
functions are locally uniform sums of their homogeneous expansions, whose terms are
polynomials. -/
theorem IsCircular.isRungeDomain {U : Set (ι → ℂ)} (ho : IsOpen U) (hc : IsPreconnected U)
    (hrot : IsCircular U) (hzero : (0 : ι → ℂ) ∈ U) : IsRungeDomain U := by
  intro f hf K hK hKU ε hε
  obtain ⟨p, hp⟩ := hf 0 hzero
  have hsum :=
    (IsCircular.hasSumLocallyUniformlyOn_homogeneousTerm_balancedHull ho hc hrot hzero hf hp).1
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hsum
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hsum.mono hKU)
  rw [Metric.tendstoUniformlyOn_iff] at hu
  obtain ⟨t, ht⟩ := (hu ε hε).exists
  choose Q hQ using exists_mvPolynomial_eval_eq_homogeneousTerm p
  refine ⟨∑ k ∈ t, Q k, fun z hz => ?_⟩
  have := ht z hz
  rw [dist_eq_norm] at this
  simpa only [map_sum, hQ] using this

end Circular


end SeveralComplexVariables
