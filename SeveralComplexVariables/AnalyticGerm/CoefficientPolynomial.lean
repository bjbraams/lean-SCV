/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.AnalyticGerm.Polynomial

/-!
# Polynomials built from coefficient germs

`ofCoefficients` and `remainderOfCoefficients` build a polynomial in `X` from a finite family of
coefficient germs indexed below a fixed degree `d`, with and without the extra monic `X ^ d`
term respectively. Evaluated in the last coordinate by `polynomialHom`, these match the analytic
`weierstrassPolynomial` and `weierstrassRemainder` built from representatives of the same
coefficients. Every monic polynomial of degree `d`, and every polynomial of degree below `d`, is
recovered from its own coefficients in one of these two shapes.

This coefficient-level bookkeeping underlies Weierstrass division and preparation in the
analytic germ ring, proved in `SeveralComplexVariables.AnalyticGerm.Weierstrass`.

## Main definitions

* `ofCoefficients`: The monic polynomial in `X` of degree `d` with prescribed coefficient germs
  below `d`.
* `remainderOfCoefficients`: The polynomial in `X` of degree below `d` with prescribed coefficient
  germs.

## Main results

* `isDistinguishedAt_ofCoefficients`: The distinguished-shape polynomial is distinguished exactly
  when its coefficients vanish at the parameter origin.
* `eq_ofCoefficients_of_monic`: Any monic polynomial of degree `d` is the distinguished-shape
  polynomial built from its own coefficients.
* `polynomialHom_ofCoefficients`: Evaluating the distinguished-shape polynomial in the last
  coordinate gives the Weierstrass polynomial built from analytic representatives of the coefficient
  germs.
* `eq_remainderOfCoefficients_of_degree_lt`: Any polynomial of degree below `d` is the
  remainder-shape polynomial built from its own coefficients.
-/

public noncomputable section

namespace SeveralComplexVariables.AnalyticGerm

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The monic polynomial in `X` of degree `d` with prescribed coefficient germs below `d`. -/
@[expose] def ofCoefficients {d : ℕ} (b : Fin d → AnalyticGerm ℂ (0 : E)) :
    Polynomial (AnalyticGerm ℂ (0 : E)) :=
  Polynomial.X ^ d + ∑ j : Fin d, Polynomial.C (b j) * Polynomial.X ^ (j : ℕ)

/-- The lower-degree part of `ofCoefficients` has degree strictly below `d`. -/
theorem degree_sum_lt {d : ℕ} (b : Fin d → AnalyticGerm ℂ (0 : E)) :
    (∑ j : Fin d, Polynomial.C (b j) * Polynomial.X ^ (j : ℕ)).degree < (d : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe d)).2 fun j _ => ?_)
  exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.mpr j.isLt)

/-- The distinguished-shape polynomial built from coefficient germs is monic. -/
theorem monic_ofCoefficients {d : ℕ} (b : Fin d → AnalyticGerm ℂ (0 : E)) :
    (ofCoefficients b).Monic :=
  (Polynomial.monic_X_pow d).add_of_left (by rw [Polynomial.degree_X_pow]; exact degree_sum_lt b)

/-- The distinguished-shape polynomial built from coefficient germs has degree `d`. -/
theorem natDegree_ofCoefficients {d : ℕ} (b : Fin d → AnalyticGerm ℂ (0 : E)) :
    (ofCoefficients b).natDegree = d := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  have hlt : (∑ j : Fin d, Polynomial.C (b j) * Polynomial.X ^ (j : ℕ)).degree <
      (Polynomial.X ^ d : Polynomial (AnalyticGerm ℂ (0 : E))).degree := by
    rw [Polynomial.degree_X_pow]; exact degree_sum_lt b
  rw [ofCoefficients, Polynomial.degree_add_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]

/-- Coefficients of `ofCoefficients` below `d` recover the prescribed germs. -/
theorem coeff_ofCoefficients_of_lt {d : ℕ} (b : Fin d → AnalyticGerm ℂ (0 : E)) {i : ℕ}
    (hi : i < d) : (ofCoefficients b).coeff i = b ⟨i, hi⟩ := by
  rw [ofCoefficients, Polynomial.coeff_add, Polynomial.finsetSum_coeff]
  have h1 : (Polynomial.X ^ d : Polynomial (AnalyticGerm ℂ (0 : E))).coeff i = 0 := by
    rw [Polynomial.coeff_X_pow]; simp [hi.ne]
  rw [h1, zero_add, Finset.sum_eq_single (⟨i, hi⟩ : Fin d)]
  · simp
  · intro j _ hji
    have hij : i ≠ (j : ℕ) := fun h => hji (Fin.ext h.symm)
    simp [hij]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- The distinguished-shape polynomial is distinguished exactly when its coefficients vanish at the
parameter origin. -/
theorem isDistinguishedAt_ofCoefficients {d : ℕ} (b : Fin d → AnalyticGerm ℂ (0 : E))
    (hb : ∀ j, eval 0 (b j) = 0) :
    (ofCoefficients b).IsDistinguishedAt (IsLocalRing.maximalIdeal _) := by
  rw [isDistinguishedAt_iff]
  refine ⟨monic_ofCoefficients b, fun i hi => ?_⟩
  rw [natDegree_ofCoefficients] at hi
  rw [coeff_ofCoefficients_of_lt b hi]
  exact hb _

/-- Any monic polynomial of degree `d` is the distinguished-shape polynomial built from its own
coefficients. -/
theorem eq_ofCoefficients_of_monic {w : Polynomial (AnalyticGerm ℂ (0 : E))} {d : ℕ}
    (hm : w.Monic) (hd : w.natDegree = d) :
    w = ofCoefficients (fun j : Fin d => w.coeff (j : ℕ)) := by
  subst hd
  rw [ofCoefficients]
  conv_lhs => rw [w.as_sum_range' (w.natDegree + 1) (Nat.lt_succ_self _)]
  rw [Finset.sum_range_succ, Polynomial.coeff_natDegree, hm]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_1, one_mul]
  rw [add_comm]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (w.coeff i) * Polynomial.X ^ i)
    w.natDegree).symm

/-- Evaluating the distinguished-shape polynomial in the last coordinate gives the Weierstrass
polynomial built from analytic representatives of the coefficient germs. -/
theorem polynomialHom_ofCoefficients {d : ℕ} (a : Fin d → E → ℂ)
    (ha : ∀ j, AnalyticAt ℂ (a j) 0) :
    polynomialHom (ofCoefficients (fun j => ofAnalyticAt (a j) (ha j))) =
      ofAnalyticAt (weierstrassPolynomial a) (analyticAt_weierstrassPolynomial ha) := by
  have hfst : AnalyticAt ℂ (Prod.fst : E × ℂ → E) 0 := analyticAt_fst
  have hsnd : AnalyticAt ℂ (Prod.snd : E × ℂ → ℂ) 0 := analyticAt_snd
  have hlc : (lastCoordinate : AnalyticGerm ℂ (0 : E × ℂ)) = ofAnalyticAt Prod.snd hsnd := rfl
  rw [ofCoefficients]
  simp only [map_add, map_sum, map_mul, map_pow, polynomialHom_C, polynomialHom_X, hlc]
  have hstep : ∀ j : Fin d, parameterHom (ofAnalyticAt (a j) (ha j)) *
      ofAnalyticAt Prod.snd hsnd ^ (j : ℕ) =
      ofAnalyticAt (a j ∘ Prod.fst * Prod.snd ^ (j : ℕ))
        (((ha j).comp_of_eq hfst rfl).mul (hsnd.pow (j : ℕ))) := by
    intro j
    have hpar := pullback_ofAnalyticAt Prod.fst (analyticAt_fst (p := (0 : E × ℂ))) (a j) (ha j)
    show pullback Prod.fst (analyticAt_fst (p := (0 : E × ℂ))) (ofAnalyticAt (a j) (ha j)) *
      ofAnalyticAt Prod.snd hsnd ^ (j : ℕ) = _
    rw [hpar, ← ofAnalyticAt_pow, ofAnalyticAt_mul]
  rw [Finset.sum_congr rfl (fun j _ => hstep j),
    ← ofAnalyticAt_sum Finset.univ (fun j => a j ∘ Prod.fst * Prod.snd ^ (j : ℕ))
      (fun j => ((ha j).comp_of_eq hfst rfl).mul (hsnd.pow (j : ℕ)))
      (Finset.analyticAt_sum _ fun j _ => ((ha j).comp_of_eq hfst rfl).mul (hsnd.pow (j : ℕ))),
    ← ofAnalyticAt_pow, ← ofAnalyticAt_add]
  congr 1
  funext z
  simp [weierstrassPolynomial, weierstrassRemainder, Function.comp]

/-- A distinguished polynomial's image is regular of order equal to its degree: the Weierstrass
polynomial built from representatives of its coefficients has central slice `t ↦ t ^ d`, whose
order at the origin is exactly `d`. -/
theorem orderInLastVariable_polynomialHom_of_isDistinguishedAt
    {w : Polynomial (AnalyticGerm ℂ (0 : E))}
    (hw : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _)) :
    orderInLastVariable (polynomialHom w) = w.natDegree := by
  obtain ⟨hwmon, hwcoeff0⟩ := (isDistinguishedAt_iff w).mp hw
  set d := w.natDegree with hd_def
  have hweq : w = ofCoefficients (fun j : Fin d => w.coeff (j : ℕ)) :=
    eq_ofCoefficients_of_monic hwmon hd_def
  choose a0 ha0 haeq using fun j : Fin d => exists_rep (w.coeff (j : ℕ))
  have ha00 : ∀ j : Fin d, a0 j 0 = 0 := by
    intro j
    have h0 := hwcoeff0 (j : ℕ) j.isLt
    rw [← haeq j, eval_ofAnalyticAt] at h0
    exact h0
  have hweq2 : w = ofCoefficients (fun j : Fin d => ofAnalyticAt (a0 j) (ha0 j)) := by
    rw [hweq]; congr 1; funext j; exact (haeq j).symm
  have hwhom : polynomialHom w = ofAnalyticAt (weierstrassPolynomial a0)
      (analyticAt_weierstrassPolynomial ha0) := by
    rw [hweq2]; exact polynomialHom_ofCoefficients a0 ha0
  rw [hwhom, orderInLastVariable_ofAnalyticAt]
  have hcentral : (fun t : ℂ => weierstrassPolynomial a0 (0, t)) = fun t : ℂ => t ^ d :=
    funext (weierstrassPolynomial_central ha00)
  rw [hcentral]
  show analyticOrderAt ((id : ℂ → ℂ) ^ d) 0 = d
  rw [analyticOrderAt_pow (analyticAt_id (𝕜 := ℂ)) d, analyticOrderAt_id]
  simp

/-- The polynomial in `X` of degree below `d` with prescribed coefficient germs. -/
@[expose] def remainderOfCoefficients {d : ℕ} (b : Fin d → AnalyticGerm ℂ (0 : E)) :
    Polynomial (AnalyticGerm ℂ (0 : E)) :=
  ∑ j : Fin d, Polynomial.C (b j) * Polynomial.X ^ (j : ℕ)

/-- The remainder-shape polynomial has degree strictly below `d`. -/
theorem degree_remainderOfCoefficients_lt {d : ℕ} (b : Fin d → AnalyticGerm ℂ (0 : E)) :
    (remainderOfCoefficients b).degree < (d : WithBot ℕ) := degree_sum_lt b

/-- Any polynomial of degree below `d` is the remainder-shape polynomial built from its own
coefficients. -/
theorem eq_remainderOfCoefficients_of_degree_lt {r : Polynomial (AnalyticGerm ℂ (0 : E))} {d : ℕ}
    (hr : r.degree < (d : WithBot ℕ)) :
    r = remainderOfCoefficients (fun j : Fin d => r.coeff (j : ℕ)) := by
  rcases eq_or_ne r 0 with h0 | h0
  · simp [remainderOfCoefficients, h0]
  · have hnd : r.natDegree < d := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hr
    rw [remainderOfCoefficients]
    conv_lhs => rw [r.as_sum_range' d hnd]
    simp only [← Polynomial.C_mul_X_pow_eq_monomial]
    exact (Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (r.coeff i) * Polynomial.X ^ i)
      d).symm

/-- Evaluating the remainder-shape polynomial in the last coordinate gives the Weierstrass remainder
built from analytic representatives of the coefficient germs. -/
theorem polynomialHom_remainderOfCoefficients {d : ℕ} (a : Fin d → E → ℂ)
    (ha : ∀ j, AnalyticAt ℂ (a j) 0) :
    polynomialHom (remainderOfCoefficients (fun j => ofAnalyticAt (a j) (ha j))) =
      ofAnalyticAt (weierstrassRemainder a) (analyticAt_weierstrassRemainder ha) := by
  have hfst : AnalyticAt ℂ (Prod.fst : E × ℂ → E) 0 := analyticAt_fst
  have hsnd : AnalyticAt ℂ (Prod.snd : E × ℂ → ℂ) 0 := analyticAt_snd
  have hlc : (lastCoordinate : AnalyticGerm ℂ (0 : E × ℂ)) = ofAnalyticAt Prod.snd hsnd := rfl
  rw [remainderOfCoefficients]
  simp only [map_sum, map_mul, map_pow, polynomialHom_C, polynomialHom_X, hlc]
  have hstep : ∀ j : Fin d, parameterHom (ofAnalyticAt (a j) (ha j)) *
      ofAnalyticAt Prod.snd hsnd ^ (j : ℕ) =
      ofAnalyticAt (a j ∘ Prod.fst * Prod.snd ^ (j : ℕ))
        (((ha j).comp_of_eq hfst rfl).mul (hsnd.pow (j : ℕ))) := by
    intro j
    have hpar := pullback_ofAnalyticAt Prod.fst (analyticAt_fst (p := (0 : E × ℂ))) (a j) (ha j)
    show pullback Prod.fst (analyticAt_fst (p := (0 : E × ℂ))) (ofAnalyticAt (a j) (ha j)) *
      ofAnalyticAt Prod.snd hsnd ^ (j : ℕ) = _
    rw [hpar, ← ofAnalyticAt_pow, ofAnalyticAt_mul]
  rw [Finset.sum_congr rfl (fun j _ => hstep j),
    ← ofAnalyticAt_sum Finset.univ (fun j => a j ∘ Prod.fst * Prod.snd ^ (j : ℕ))
      (fun j => ((ha j).comp_of_eq hfst rfl).mul (hsnd.pow (j : ℕ)))
      (Finset.analyticAt_sum _ fun j _ => ((ha j).comp_of_eq hfst rfl).mul (hsnd.pow (j : ℕ)))]
  congr 1
  funext z
  simp [weierstrassRemainder, Function.comp]

/-- `remainderOfCoefficients` is additive in the coefficient tuple. -/
theorem remainderOfCoefficients_add {d : ℕ} (a b : Fin d → AnalyticGerm ℂ (0 : E)) :
    remainderOfCoefficients (a + b) = remainderOfCoefficients a + remainderOfCoefficients b := by
  simp only [remainderOfCoefficients, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/-- `remainderOfCoefficients` scales by a constant-polynomial factor under a common germ multiplier
on the coefficient tuple. -/
theorem remainderOfCoefficients_smul {d : ℕ} (c : AnalyticGerm ℂ (0 : E))
    (a : Fin d → AnalyticGerm ℂ (0 : E)) :
    remainderOfCoefficients (c • a) = Polynomial.C c * remainderOfCoefficients a := by
  simp only [remainderOfCoefficients, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum,
    mul_assoc]

/-- `remainderOfCoefficients` commutes with finite sums of coefficient tuples. -/
theorem remainderOfCoefficients_sum {d : ℕ} {ι : Type*} (s : Finset ι)
    (v : ι → Fin d → AnalyticGerm ℂ (0 : E)) :
    remainderOfCoefficients (∑ i ∈ s, v i) = ∑ i ∈ s, remainderOfCoefficients (v i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [remainderOfCoefficients]
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi,
      remainderOfCoefficients_add, ih]

end SeveralComplexVariables.AnalyticGerm
