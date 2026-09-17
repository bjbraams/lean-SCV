/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.AnalyticGerm.CoefficientPolynomial

/-!
# Weierstrass theorems in the germ ring

These interfaces express division and preparation directly in the analytic germ ring,
using ordinary polynomials over parameter germs and Mathlib's distinguished-polynomial
predicate. Polynomial degree (rather than natural degree) handles the zero remainder
and degree-zero divisors uniformly. Units are represented by the existing units group.

Existence and uniqueness of both division and preparation are proved by choosing analytic
representatives, applying the analytic Weierstrass theorems on any finite-dimensional
parameter space, and reassembling the polynomial coefficients using the bookkeeping in
`CoefficientPolynomial.lean`. Polynomial preservation under division (Lemma 1.8.1(a))
follows by comparing ordinary Euclidean division of polynomials with germ division
uniqueness. The irreducibility equivalence is pending. Finite simultaneous preparation
follows from the proved finite normalization theorem and the existing analytic
preparation theorem.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace SeveralComplexVariables.AnalyticGerm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Division by a distinguished polynomial has a unique germ quotient and polynomial
remainder of smaller degree. Choose representatives and apply analytic Weierstrass
division, then identify the germ quotient and coefficient germs by uniqueness. -/
theorem existsUnique_division [FiniteDimensional ℂ E]
    (w : Polynomial (AnalyticGerm (0 : E)))
    (hw : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _)) (f : AnalyticGerm (0 : E × ℂ)) :
    ∃! qr : AnalyticGerm (0 : E × ℂ) × Polynomial (AnalyticGerm (0 : E)),
      qr.2.degree < (w.natDegree : WithBot ℕ) ∧
      f = qr.1 * polynomialHom w + polynomialHom qr.2 := by
  set d := w.natDegree with hd_def
  obtain ⟨hwmon, hwcoeff0⟩ := (isDistinguishedAt_iff w).mp hw
  have hweq : w = ofCoefficients (fun j : Fin d => w.coeff (j : ℕ)) :=
    eq_ofCoefficients_of_monic hwmon hd_def
  choose a0 ha0 haeq using fun j : Fin d => exists_rep (w.coeff (j : ℕ))
  have ha00 : ∀ j : Fin d, a0 j 0 = 0 := by
    intro j
    have h0 := hwcoeff0 (j : ℕ) (hd_def ▸ j.isLt)
    rw [← haeq j, eval_ofAnalyticAt] at h0
    exact h0
  have hweq2 : w = ofCoefficients (fun j : Fin d => ofAnalyticAt (a0 j) (ha0 j)) := by
    rw [hweq]; congr 1; funext j; exact (haeq j).symm
  have hwhom : polynomialHom w = ofAnalyticAt (weierstrassPolynomial a0)
      (analyticAt_weierstrassPolynomial ha0) := by
    rw [hweq2]; exact polynomialHom_ofCoefficients a0 ha0
  have horder : analyticOrderAt (fun t : ℂ => weierstrassPolynomial a0 (0, t)) 0 = d := by
    have hcentral : (fun t : ℂ => weierstrassPolynomial a0 (0, t)) = fun t : ℂ => t ^ d :=
      funext (weierstrassPolynomial_central ha00)
    rw [hcentral]
    show analyticOrderAt ((id : ℂ → ℂ) ^ d) 0 = d
    rw [analyticOrderAt_pow (analyticAt_id (𝕜 := ℂ)) d, analyticOrderAt_id]; simp
  obtain ⟨f0, hf0, rfl⟩ := exists_rep f
  obtain ⟨q, a, Hdiv, huniqdiv⟩ :=
    weierstrass_division_at_findim (analyticAt_weierstrassPolynomial ha0) hf0 horder
  set r : Polynomial (AnalyticGerm (0 : E)) :=
    remainderOfCoefficients (fun j => ofAnalyticAt (a j) (Hdiv.coefficient_analytic j)) with hr_def
  have hrdeg : r.degree < (d : WithBot ℕ) := degree_remainderOfCoefficients_lt _
  have hrhom : polynomialHom r = ofAnalyticAt (weierstrassRemainder a)
      (analyticAt_weierstrassRemainder Hdiv.coefficient_analytic) :=
    polynomialHom_remainderOfCoefficients a Hdiv.coefficient_analytic
  refine ⟨(ofAnalyticAt q Hdiv.quotient_analytic, r), ⟨hrdeg, ?_⟩, ?_⟩
  · have hgerm : ofAnalyticAt f0 hf0 = ofAnalyticAt q Hdiv.quotient_analytic *
        ofAnalyticAt (weierstrassPolynomial a0) (analyticAt_weierstrassPolynomial ha0) +
        ofAnalyticAt (weierstrassRemainder a)
          (analyticAt_weierstrassRemainder Hdiv.coefficient_analytic) := by
      rw [← ofAnalyticAt_mul, ← ofAnalyticAt_add]
      exact ofAnalyticAt_eq_iff.mpr Hdiv.eq
    simp only
    rw [hgerm, hwhom, hrhom]
  · rintro ⟨q', r'⟩ ⟨hr'deg, hfeq⟩
    simp only at hr'deg hfeq ⊢
    have hr'eq : r' = remainderOfCoefficients (fun j : Fin d => r'.coeff (j : ℕ)) :=
      eq_remainderOfCoefficients_of_degree_lt hr'deg
    choose a' ha' haeq' using fun j : Fin d => exists_rep (r'.coeff (j : ℕ))
    have hr'eq2 : r' = remainderOfCoefficients (fun j : Fin d => ofAnalyticAt (a' j) (ha' j)) := by
      rw [hr'eq]; congr 1; funext j; exact (haeq' j).symm
    have hr'hom : polynomialHom r' = ofAnalyticAt (weierstrassRemainder a')
        (analyticAt_weierstrassRemainder ha') := by
      rw [hr'eq2]; exact polynomialHom_remainderOfCoefficients a' ha'
    obtain ⟨q0', hq0', hq0'eq⟩ := exists_rep q'
    have Hdiv' : IsWeierstrassDivisionAt (weierstrassPolynomial a0) f0 q0' a' := by
      refine ⟨hq0', ha', ?_⟩
      have hgerm : ofAnalyticAt f0 hf0 = ofAnalyticAt q0' hq0' *
          ofAnalyticAt (weierstrassPolynomial a0) (analyticAt_weierstrassPolynomial ha0) +
          ofAnalyticAt (weierstrassRemainder a') (analyticAt_weierstrassRemainder ha') := by
        rw [hq0'eq, ← hwhom, ← hr'hom]; exact hfeq
      exact (ofAnalyticAt_eq_iff (hg := (hq0'.mul (analyticAt_weierstrassPolynomial ha0)).add
        (analyticAt_weierstrassRemainder ha'))).mp hgerm
    obtain ⟨hqeqq0', haeqa'⟩ := huniqdiv q0' a' Hdiv'
    have hqeq : ofAnalyticAt q Hdiv.quotient_analytic = q' := by
      rw [(ofAnalyticAt_eq_iff (hg := hq0')).mpr hqeqq0', hq0'eq]
    have hreq : r = r' := by
      rw [hr_def, hr'eq2]
      congr 1
      funext j
      exact ofAnalyticAt_eq_iff.mpr (haeqa' j)
    rw [Prod.mk.injEq]
    exact ⟨hqeq.symm, hreq.symm⟩

/-- Preparation has a unique unit and distinguished polynomial of the prescribed order.
Order zero gives polynomial one. Pending proof: convert the analytic preparation
and uniqueness theorems into polynomial and unit equalities in the germ ring. -/
theorem existsUnique_preparation [FiniteDimensional ℂ E]
    (f : AnalyticGerm (0 : E × ℂ)) {d : ℕ} (hd : orderInLastVariable f = d) :
    ∃! up : (AnalyticGerm (0 : E × ℂ))ˣ × Polynomial (AnalyticGerm (0 : E)),
      up.2.IsDistinguishedAt (IsLocalRing.maximalIdeal _) ∧ up.2.natDegree = d ∧
      f = ↑up.1 * polynomialHom up.2 := by
  obtain ⟨f0, hf0, rfl⟩ := exists_rep f
  rw [orderInLastVariable_ofAnalyticAt] at hd
  obtain ⟨u, a, H, huniq⟩ := weierstrass_preparation_at_findim hf0 hd
  obtain ⟨hunit, hfact⟩ := H.germ_factorization hf0
  set w : Polynomial (AnalyticGerm (0 : E)) :=
    ofCoefficients (fun j => ofAnalyticAt (a j) (H.coefficient_analytic j)) with hw_def
  have hwdist : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _) :=
    isDistinguishedAt_ofCoefficients _ (fun j => by
      rw [eval_ofAnalyticAt]; exact H.coefficient_zero j)
  have hwdeg : w.natDegree = d := natDegree_ofCoefficients _
  have hwhom : polynomialHom w = ofAnalyticAt (weierstrassPolynomial a)
      (analyticAt_weierstrassPolynomial H.coefficient_analytic) :=
    polynomialHom_ofCoefficients a H.coefficient_analytic
  refine ⟨(hunit.unit, w), ⟨hwdist, hwdeg, ?_⟩, ?_⟩
  · rw [hunit.unit_spec, hwhom]; exact hfact
  · rintro ⟨u', w'⟩ ⟨hw'dist, hw'deg, hfeq⟩
    simp only at hw'dist hw'deg hfeq ⊢
    obtain ⟨hw'mon, hw'coeff0⟩ := (isDistinguishedAt_iff w').mp hw'dist
    have hw'eq : w' = ofCoefficients (fun j : Fin d => w'.coeff (j : ℕ)) :=
      eq_ofCoefficients_of_monic hw'mon hw'deg
    choose a' ha' haeq using fun j : Fin d => exists_rep (w'.coeff (j : ℕ))
    obtain ⟨v0, hv0, hveq⟩ := exists_rep (↑u' : AnalyticGerm (0 : E × ℂ))
    have hv0ne : v0 0 ≠ 0 := by
      have hu' := (isUnit_iff (↑u' : AnalyticGerm (0 : E × ℂ))).mp u'.isUnit
      rwa [← hveq, eval_ofAnalyticAt] at hu'
    have ha'0 : ∀ j : Fin d, a' j 0 = 0 := by
      intro j
      have hlt : (j : ℕ) < w'.natDegree := by rw [hw'deg]; exact j.isLt
      have h0 := hw'coeff0 (j : ℕ) hlt
      rw [← haeq j, eval_ofAnalyticAt] at h0
      exact h0
    have hw'eq2 : w' = ofCoefficients (fun j : Fin d => ofAnalyticAt (a' j) (ha' j)) := by
      rw [hw'eq]; congr 1; funext j; exact (haeq j).symm
    have Hprep' : IsWeierstrassPreparationAt f0 v0 a' := by
      refine ⟨hv0, hv0ne, ha', ha'0, ?_⟩
      have hgerm : ofAnalyticAt f0 hf0 = ofAnalyticAt (v0 * weierstrassPolynomial a')
          (hv0.mul (analyticAt_weierstrassPolynomial ha')) := by
        rw [hfeq, ← hveq, hw'eq2, polynomialHom_ofCoefficients, ← ofAnalyticAt_mul]
      exact ofAnalyticAt_eq_iff.mp hgerm
    obtain ⟨hueqv0, haeqa'⟩ := huniq v0 a' Hprep'
    have hueq : hunit.unit = u' := Units.ext (by
      rw [hunit.unit_spec, (ofAnalyticAt_eq_iff (hg := hv0)).mpr hueqv0, hveq])
    have hweq : w = w' := by
      rw [hw_def, hw'eq2]
      congr 1
      funext j
      exact ofAnalyticAt_eq_iff.mpr (haeqa' j)
    rw [Prod.mk.injEq]
    exact ⟨hueq.symm, hweq.symm⟩

/-- Division by a distinguished polynomial preserves polynomial germs (Lemma 1.8.1(a)).
The Euclidean remainder of ordinary polynomial division by the monic divisor gives a
second decomposition; germ division uniqueness identifies it with the hypothesised one. -/
theorem exists_polynomial_quotient [FiniteDimensional ℂ E]
    (p w : Polynomial (AnalyticGerm (0 : E)))
    (hw : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _))
    (g : AnalyticGerm (0 : E × ℂ)) (h : polynomialHom p = g * polynomialHom w) :
    ∃ q : Polynomial (AnalyticGerm (0 : E)), polynomialHom q = g := by
  have hwne : w ≠ 0 := hw.monic.ne_zero
  have hrdeg : (p %ₘ w).degree < (w.natDegree : WithBot ℕ) := by
    rw [← Polynomial.degree_eq_natDegree hwne]
    exact Polynomial.degree_modByMonic_lt p hw.monic
  have hpeq : polynomialHom p = polynomialHom (p /ₘ w) * polynomialHom w +
      polynomialHom (p %ₘ w) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div p w]
    rw [map_add, map_mul]
    ring
  have hveq : polynomialHom p = g * polynomialHom w +
      polynomialHom (0 : Polynomial (AnalyticGerm (0 : E))) := by simp [h]
  have hzerodeg : (0 : Polynomial (AnalyticGerm (0 : E))).degree < (w.natDegree : WithBot ℕ) := by
    rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe w.natDegree
  have hp1 : (p %ₘ w).degree < (w.natDegree : WithBot ℕ) ∧
      polynomialHom p = polynomialHom (p /ₘ w) * polynomialHom w + polynomialHom (p %ₘ w) :=
    ⟨hrdeg, hpeq⟩
  have hp2 : (0 : Polynomial (AnalyticGerm (0 : E))).degree < (w.natDegree : WithBot ℕ) ∧
      polynomialHom p = g * polynomialHom w +
        polynomialHom (0 : Polynomial (AnalyticGerm (0 : E))) :=
    ⟨hzerodeg, hveq⟩
  obtain ⟨y, _, huniq⟩ := existsUnique_division w hw (polynomialHom p)
  have h1 := huniq (polynomialHom (p /ₘ w), p %ₘ w) hp1
  have h2 := huniq (g, 0) hp2
  exact ⟨p /ₘ w, (Prod.mk.injEq ..).mp (h1.trans h2.symm) |>.1⟩

/-- If the numerator in a distinguished division is polynomial, so is the quotient.
This applies with a nonzero remainder as well as to exact divisibility. -/
theorem exists_polynomial_division_quotient [FiniteDimensional ℂ E]
    (p w r : Polynomial (AnalyticGerm (0 : E)))
    (hw : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _))
    (q : AnalyticGerm (0 : E × ℂ))
    (h : polynomialHom p = q * polynomialHom w + polynomialHom r) :
    ∃ s : Polynomial (AnalyticGerm (0 : E)), polynomialHom s = q := by
  apply exists_polynomial_quotient (p - r) w hw q
  rw [map_sub, h, add_sub_cancel_right]

/-- A distinguished polynomial is irreducible exactly when its analytic germ is.
Pending proof: preparation of germ factors and normalization of polynomial factors.
Degree zero is allowed: both sides are then false. -/
theorem irreducible_polynomialHom_iff [FiniteDimensional ℂ E]
    (w : Polynomial (AnalyticGerm (0 : E)))
    (hw : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _)) :
    Irreducible (polynomialHom w) ↔ Irreducible w := by
  sorry

end AnalyticGerm

/-- One coordinate system permits preparation of all members of a finite family.
This depends on the existing preparation theorem and hence on pending analytic division.
Empty parameter types, empty families, and unit germs are all included. -/
theorem exists_weierstrass_preparation_finite {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : κ → (ι → ℂ) × ℂ → ℂ} (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (hne : ∀ i, ¬ f i =ᶠ[𝓝 0] 0) :
    ∃ (L : ((ι → ℂ) × ℂ) ≃L[ℂ] ((ι → ℂ) × ℂ)) (d : κ → ℕ), ∀ i,
      ∃ (u : (ι → ℂ) × ℂ → ℂ) (a : Fin (d i) → (ι → ℂ) → ℂ),
        IsWeierstrassPreparationAt (fun z => f i (L z)) u a := by
  obtain ⟨L, d, hd⟩ := exists_regular_coordinate_change_finite hf hne
  refine ⟨L, d, fun i => ?_⟩
  have ha : AnalyticAt ℂ (fun z => f i (L z)) 0 :=
    (hf i).comp_of_eq (L.toContinuousLinearMap.analyticAt 0) L.map_zero
  obtain ⟨u, a, h, _⟩ := weierstrass_preparation_at ha (hd i)
  exact ⟨u, a, h⟩

end SeveralComplexVariables
