/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.LeviConvexity
public import SeveralComplexVariables.Pseudoconvexity
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Levi's necessary condition

A domain of holomorphy in `Fin n → ℂ` with `C²` boundary is Levi pseudoconvex. This is
E. E. Levi's theorem (Range, Theorem 2.11; Fritzsche–Grauert, Theorem 4.7, first half).

The proof avoids holomorphic coordinate changes. If the Levi form of a defining function `ρ`
were negative in a complex tangent direction `w` at a boundary point `p`, the Levi polynomial
provides a quadratic analytic disc `ζ ↦ p + ζ • w + ζ ^ 2 • c + ε • ν` tangent to the boundary
from inside, on which `ρ` behaves like `-ε + ‖ζ‖ ^ 2 L` with `L < 0`. Its boundary circle is
therefore much deeper inside the domain than its center. The boundary distance is comparable
to `|ρ|` near `p`, the center lies in the holomorphic hull of the boundary circle by the
maximum modulus principle, and Thullen's radius bound for domains of holomorphy then forces
the center to be as deep as the circle, a contradiction for small radii.

References: Range (1986), Chapter II, Theorems 2.9 and 2.11; Hörmander (1973), Theorem 2.6.?;
Fritzsche–Grauert (2002), Chapter II, Theorem 4.7.
-/

@[expose] public noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {U : Set E} {p : E} {ρ : E → ℝ} {V : Set E}

/-- Near a boundary point, a defining function is comparable to the distance to the
complement: `c₂ * |ρ z| ≤ infDist z Uᶜ ≤ C₁ * |ρ z|` for `z ∈ U` near `p`. -/
theorem IsLocalDefiningFunction.exists_infDist_bounds (hU : IsOpen U) (hp : p ∈ frontier U)
    (h : IsLocalDefiningFunction U p ρ V) :
    ∃ C₁ c₂ δ : ℝ, 0 < C₁ ∧ 0 < c₂ ∧ 0 < δ ∧ ∀ z ∈ ball p δ, z ∈ U →
      c₂ * |ρ z| ≤ infDist z Uᶜ ∧ infDist z Uᶜ ≤ C₁ * |ρ z| := by
  set ℓ := fderiv ℝ ρ p with hℓ
  have hUc : Uᶜ.Nonempty := ⟨p, notMem_of_mem_frontier hU hp⟩
  -- an inward direction
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, ℓ c₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h.fderiv_ne (ContinuousLinearMap.ext hcon)
  set ν : E := (1 / ℓ c₀) • c₀ with hν
  have hℓν : ℓ ν = 1 := by
    rw [hν, map_smul, smul_eq_mul, one_div, inv_mul_cancel₀ hc₀]
  have hν0 : 0 < ‖ν‖ := by
    rw [norm_pos_iff]
    intro hzero
    rw [hzero, map_zero] at hℓν
    exact zero_ne_one hℓν
  -- continuity of the derivative near `p`
  have hDcont : ContinuousOn (fderiv ℝ ρ) V :=
    h.contDiffOn.continuousOn_fderiv_of_isOpen h.isOpen (by norm_num)
  have hdiff : ∀ z ∈ V, DifferentiableAt ℝ ρ z := fun z hz =>
    (h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hz)).differentiableAt (by norm_num)
  set Lip := ‖ℓ‖ + 1 with hLip
  have hLip0 : 0 < Lip := by positivity
  have hev : ∀ᶠ y in 𝓝 p, y ∈ V ∧ ‖fderiv ℝ ρ y‖ ≤ Lip ∧ (1 / 2 : ℝ) ≤ fderiv ℝ ρ y ν := by
    have h1 : ∀ᶠ y in 𝓝 p, y ∈ V := h.isOpen.mem_nhds h.mem
    have hcontp : ContinuousAt (fderiv ℝ ρ) p := hDcont.continuousAt (h.isOpen.mem_nhds h.mem)
    have h2 : ∀ᶠ y in 𝓝 p, ‖fderiv ℝ ρ y‖ ≤ Lip := by
      have := (continuous_norm.continuousAt.comp hcontp).eventually
        (eventually_le_nhds (show ‖fderiv ℝ ρ p‖ < Lip by rw [hLip]; linarith))
      exact this
    have h3 : ∀ᶠ y in 𝓝 p, (1 / 2 : ℝ) ≤ fderiv ℝ ρ y ν := by
      have hc : ContinuousAt (fun y => fderiv ℝ ρ y ν) p :=
        (ContinuousLinearMap.apply ℝ ℝ ν).continuous.continuousAt.comp hcontp
      exact hc.eventually (eventually_ge_nhds (show (1 / 2 : ℝ) < fderiv ℝ ρ p ν by
        rw [← hℓ, hℓν]; norm_num))
    exact h1.and (h2.and h3) |>.mono fun y hy => ⟨hy.1, hy.2.1, hy.2.2⟩
  obtain ⟨δ₀, hδ₀, hball₀⟩ := Metric.mem_nhds_iff.mp hev
  -- `ρ` is small near `p`
  have hρcont : ContinuousAt ρ p := (hdiff p h.mem).continuousAt
  have hsmall : ∀ᶠ z in 𝓝 p, |ρ z| < min (Lip * δ₀ / 2) (δ₀ / (4 * ‖ν‖)) := by
    have hcabs : ContinuousAt (fun z => |ρ z|) p := hρcont.abs
    exact hcabs.eventually (eventually_lt_nhds (show |ρ p| < min (Lip * δ₀ / 2) (δ₀ / (4 * ‖ν‖)) by
      rw [h.eq_zero, abs_zero]; exact lt_min (by positivity) (by positivity)))
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.mem_nhds_iff.mp hsmall
  refine ⟨2 * ‖ν‖, 1 / Lip, min (δ₀ / 2) δ₁, by positivity, by positivity, by positivity, ?_⟩
  intro z hz hzU
  have hzδ₀ : z ∈ ball p (δ₀ / 2) := ball_subset_ball (min_le_left _ _) hz
  have hzV : z ∈ V := (hball₀ (ball_subset_ball (half_le_self hδ₀.le) hzδ₀)).1
  have hρz : ρ z < 0 := h.neg_of_mem hzV hzU
  have hρabs : |ρ z| = -ρ z := abs_of_neg hρz
  have hρsmall : |ρ z| < min (Lip * δ₀ / 2) (δ₀ / (4 * ‖ν‖)) :=
    hball₁ (ball_subset_ball (min_le_right _ _) hz)
  constructor
  · -- lower bound
    rw [le_infDist hUc]
    intro y hy
    by_cases hyV : y ∈ ball p δ₀
    · have hρy : 0 ≤ ρ y := by
        by_contra hneg
        push Not at hneg
        exact hy (h.mem_of_neg (hball₀ hyV).1 hneg)
      have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (f := ρ) (s := ball p δ₀) (C := Lip)
        (fun x hx => hdiff x (hball₀ hx).1) (fun x hx => (hball₀ hx).2.1) (convex_ball p δ₀)
        (ball_subset_ball (half_le_self hδ₀.le) hzδ₀) hyV
      rw [Real.norm_eq_abs, ← dist_eq_norm, dist_comm] at hmv
      have : |ρ z| ≤ |ρ y - ρ z| := by
        rw [hρabs, abs_of_nonneg (by linarith)]
        linarith
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hLip0]
      linarith
    · have hdz : δ₀ / 2 ≤ dist z y := by
        have h1 : δ₀ ≤ dist y p := not_lt.mp (by simpa [mem_ball] using hyV)
        have h2 : dist z p < δ₀ / 2 := mem_ball.mp hzδ₀
        have := dist_triangle y z p
        rw [dist_comm y z] at this
        linarith
      have : |ρ z| / Lip ≤ δ₀ / 2 := by
        rw [div_le_iff₀ hLip0]
        have := (lt_min_iff.mp hρsmall).1
        linarith
      rw [div_mul_eq_mul_div, one_mul]
      exact this.trans hdz
  · -- upper bound: move inward along `ν`
    set T : ℝ := 2 * |ρ z| with hT
    have hT0 : 0 ≤ T := by positivity
    have hseg : ∀ t ∈ Icc (0 : ℝ) T, z + t • ν ∈ ball p δ₀ := by
      intro t ht
      have h1 : ‖t • ν‖ ≤ T * ‖ν‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      have h2 : T * ‖ν‖ < δ₀ / 2 := by
        have := (lt_min_iff.mp hρsmall).2
        rw [hT]
        rw [lt_div_iff₀ (by positivity)] at this
        nlinarith
      rw [mem_ball, dist_eq_norm]
      calc ‖z + t • ν - p‖ ≤ ‖z - p‖ + ‖t • ν‖ := by
            rw [add_sub_right_comm]; exact norm_add_le _ _
        _ < δ₀ / 2 + δ₀ / 2 := by
            have := mem_ball.mp hzδ₀
            rw [dist_eq_norm] at this
            linarith
        _ = δ₀ := by ring
    -- the function along the segment grows at rate at least `1 / 2`
    have hderiv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt (fun t : ℝ => ρ (z + t • ν))
        (fderiv ℝ ρ (z + t • ν) ν) t := by
      intro t ht
      have hl : HasDerivAt (fun t : ℝ => z + t • ν) ν t := by
        simpa using ((hasDerivAt_id t).smul_const ν).const_add z
      exact (hdiff _ (hball₀ (hseg t ht)).1).hasFDerivAt.comp_hasDerivAt t hl
    have hmono := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc 0 T)
      (f := fun t : ℝ => ρ (z + t • ν)) (C := 1 / 2)
      (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [(hderiv t (interior_subset ht)).deriv]
        exact (hball₀ (hseg t (interior_subset ht))).2.2)
      0 (left_mem_Icc.mpr hT0) T (right_mem_Icc.mpr hT0) hT0
    simp only [zero_smul, add_zero, sub_zero] at hmono
    have hρT : 0 ≤ ρ (z + T • ν) := by
      rw [hT] at hmono ⊢
      rw [hρabs] at hmono ⊢
      linarith
    have hnot : z + T • ν ∉ U := fun hmem =>
      absurd (h.neg_of_mem (hball₀ (hseg T (right_mem_Icc.mpr hT0))).1 hmem) (not_lt.mpr hρT)
    calc infDist z Uᶜ ≤ dist z (z + T • ν) := infDist_le_dist_of_mem hnot
      _ = T * ‖ν‖ := by
          rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg hT0]
      _ = 2 * ‖ν‖ * |ρ z| := by rw [hT]; ring

/-- The complex quadratic coefficient of a real bilinear form along a complex line. -/
def leviQuadratic (B : E →L[ℝ] E →L[ℝ] ℝ) (w : E) : ℂ :=
  (((B w w - B (I • w) (I • w)) / 4 : ℝ) : ℂ) - I / 2 * (B w (I • w) : ℝ)

/-- **Disc estimate along the Levi polynomial.** With `c` cancelling the complex quadratic
term and `ν` an inward direction, the defining function along the disc
`ζ ↦ p + ζ • w + ζ ^ 2 • c + (κ r ^ 2) • ν` is `-κ r ^ 2 + ‖ζ‖ ^ 2 L` up to `η r ^ 2`, for
`‖ζ‖ ≤ r` and `r` small, and the disc lies in any prescribed neighborhood of `p`. -/
theorem IsLocalDefiningFunction.exists_disc_estimate (h : IsLocalDefiningFunction U p ρ V)
    {w : E} (hw : IsComplexTangent ρ p w) {c ν : E}
    (hc : complexPart (fderiv ℝ ρ p) c = -leviQuadratic (fderiv ℝ (fderiv ℝ ρ) p) w)
    (hν : fderiv ℝ ρ p ν = -1) {κ η : ℝ} (hκ : 0 ≤ κ) (hη : 0 < η) {W : Set E} (hW : W ∈ 𝓝 p) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ ζ : ℂ, ‖ζ‖ ≤ r →
      p + ζ • w + ζ ^ 2 • c + (κ * r ^ 2) • ν ∈ W ∧
      |ρ (p + ζ • w + ζ ^ 2 • c + (κ * r ^ 2) • ν) - (-(κ * r ^ 2) + ‖ζ‖ ^ 2 * leviForm ρ p w)|
        ≤ η * r ^ 2 := by
  set ℓ := fderiv ℝ ρ p with hℓ
  set B := fderiv ℝ (fderiv ℝ ρ) p with hB
  have hρp : ContDiffAt ℝ 2 ρ p := h.contDiffOn.contDiffAt (h.isOpen.mem_nhds h.mem)
  -- symmetry of the second derivative
  have hev : ∀ᶠ y in 𝓝 p, HasFDerivAt ρ (fderiv ℝ ρ y) y := by
    filter_upwards [h.isOpen.mem_nhds h.mem] with y hy
    exact ((h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt
  have hBd : HasFDerivAt (fderiv ℝ ρ) B p :=
    ((hρp.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hsymm : ∀ v v', B v v' = B v' v := second_derivative_symmetric_of_eventually hev hBd
  -- constants
  set M₀ : ℝ := ‖w‖ + ‖c‖ + κ * ‖ν‖ with hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  set M₁ : ℝ := ‖B‖ * ‖w‖ * (‖c‖ + κ * ‖ν‖) + ‖B‖ * (‖c‖ + κ * ‖ν‖) ^ 2 / 2 with hM₁
  have hM₁0 : 0 ≤ M₁ := by positivity
  obtain ⟨δ', hδ', htaylor⟩ := exists_taylor_bound hρp (ε := η / (2 * (M₀ ^ 2 + 1))) (by positivity)
  obtain ⟨δW, hδW, hballW⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨min 1 (min (η / (2 * (M₁ + 1))) (min (δ' / (2 * (M₀ + 1))) (δW / (2 * (M₀ + 1))))),
    by positivity, fun r hr hr₀ ζ hζ => ?_⟩
  have hr1 : r ≤ 1 := hr₀.trans (min_le_left _ _)
  have hrM₁ : r * (M₁ + 1) ≤ η / 2 := by
    have := hr₀.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hrδ' : r * (M₀ + 1) < δ' := by
    have := hr₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    rw [le_div_iff₀ (by positivity)] at this
    have hpos : 0 < r * (M₀ + 1) := by positivity
    linarith
  have hrδW : r * (M₀ + 1) < δW := by
    have := hr₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    rw [le_div_iff₀ (by positivity)] at this
    have hpos : 0 < r * (M₀ + 1) := by positivity
    linarith
  -- the increment and its pieces
  set h₁ : E := ζ • w with hh₁
  set h₂ : E := ζ ^ 2 • c + (κ * r ^ 2) • ν with hh₂
  have hsplit : p + ζ • w + ζ ^ 2 • c + (κ * r ^ 2) • ν = p + (h₁ + h₂) := by
    rw [hh₁, hh₂]; abel
  have hζr2 : ‖ζ‖ ^ 2 ≤ r ^ 2 := by gcongr
  have hn₁ : ‖h₁‖ ≤ r * ‖w‖ := by
    rw [hh₁, norm_smul]
    exact mul_le_mul_of_nonneg_right hζ (norm_nonneg _)
  have hn₂ : ‖h₂‖ ≤ r ^ 2 * (‖c‖ + κ * ‖ν‖) := by
    rw [hh₂]
    calc ‖ζ ^ 2 • c + (κ * r ^ 2) • ν‖ ≤ ‖ζ ^ 2 • c‖ + ‖(κ * r ^ 2) • ν‖ := norm_add_le _ _
      _ = ‖ζ‖ ^ 2 * ‖c‖ + κ * r ^ 2 * ‖ν‖ := by
          rw [norm_smul, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ r ^ 2 * ‖c‖ + κ * r ^ 2 * ‖ν‖ := by gcongr
      _ = r ^ 2 * (‖c‖ + κ * ‖ν‖) := by ring
  have hn₂' : ‖h₂‖ ≤ r * (‖c‖ + κ * ‖ν‖) := by
    refine hn₂.trans ?_
    have : r ^ 2 ≤ r := by nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hn : ‖h₁ + h₂‖ ≤ r * M₀ := by
    calc ‖h₁ + h₂‖ ≤ ‖h₁‖ + ‖h₂‖ := norm_add_le _ _
      _ ≤ r * ‖w‖ + r * (‖c‖ + κ * ‖ν‖) := add_le_add hn₁ hn₂'
      _ = r * M₀ := by rw [hM₀]; ring
  have hnlt : ‖h₁ + h₂‖ < δ' := hn.trans_lt (by nlinarith)
  constructor
  · rw [hsplit]
    apply hballW
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hn.trans_lt (by nlinarith)
  -- the Taylor expansion
  have ht := htaylor (h₁ + h₂) hnlt
  -- linear term
  have hℓw : complexPart ℓ w = 0 := by
    have h1 : ℓ w = 0 := hw.1
    have h2 : ℓ (I • w) = 0 := hw.2
    simp [complexPart, h1, h2]
  have hlin : ℓ (h₁ + h₂) = (ζ ^ 2 * (-leviQuadratic B w)).re - κ * r ^ 2 := by
    rw [hh₁, hh₂, map_add, map_add, apply_smul_eq_re_mul_complexPart ℓ ζ w,
      apply_smul_eq_re_mul_complexPart ℓ (ζ ^ 2) c, hℓw, hc, map_smul, smul_eq_mul, hν]
    simp
    ring
  -- quadratic term
  have hquad : (1 / 2 : ℝ) * B (h₁ + h₂) (h₁ + h₂) =
      (1 / 2 : ℝ) * B h₁ h₁ + B h₁ h₂ + (1 / 2 : ℝ) * B h₂ h₂ := by
    simp only [map_add, add_apply, hsymm h₂ h₁]
    ring
  have hquad₁ : (1 / 2 : ℝ) * B h₁ h₁ = ‖ζ‖ ^ 2 * leviForm ρ p w + (ζ ^ 2 * leviQuadratic B w).re := by
    rw [hh₁, bilinear_smul_smul_eq B (hsymm w (I • w)) ζ, leviForm_eq_fderiv, leviQuadratic]
  -- cancellation of the complex quadratic terms
  have hcancel : (ζ ^ 2 * (-leviQuadratic B w)).re + (ζ ^ 2 * leviQuadratic B w).re = 0 := by
    rw [mul_neg, Complex.neg_re]; ring
  -- error bounds
  have hBn : 0 ≤ ‖B‖ := ContinuousLinearMap.opNorm_nonneg B
  have hB₁₂ : |B h₁ h₂| ≤ ‖B‖ * ‖w‖ * (‖c‖ + κ * ‖ν‖) * r ^ 3 := by
    have := B.le_opNorm₂ h₁ h₂
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    calc ‖B‖ * ‖h₁‖ * ‖h₂‖ ≤ ‖B‖ * (r * ‖w‖) * (r ^ 2 * (‖c‖ + κ * ‖ν‖)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hn₁ hBn) hn₂ (norm_nonneg _) (by positivity)
      _ = ‖B‖ * ‖w‖ * (‖c‖ + κ * ‖ν‖) * r ^ 3 := by ring
  have hB₂₂ : |(1 / 2 : ℝ) * B h₂ h₂| ≤ ‖B‖ * (‖c‖ + κ * ‖ν‖) ^ 2 / 2 * r ^ 3 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    have := B.le_opNorm₂ h₂ h₂
    rw [Real.norm_eq_abs] at this
    have h2 : ‖B‖ * ‖h₂‖ * ‖h₂‖ ≤ ‖B‖ * (r * (‖c‖ + κ * ‖ν‖)) * (r ^ 2 * (‖c‖ + κ * ‖ν‖)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hn₂' hBn) hn₂ (norm_nonneg _) (by positivity)
    calc 1 / 2 * |B h₂ h₂| ≤ 1 / 2 * (‖B‖ * (r * (‖c‖ + κ * ‖ν‖)) * (r ^ 2 * (‖c‖ + κ * ‖ν‖))) :=
          mul_le_mul_of_nonneg_left (this.trans h2) (by norm_num)
      _ = ‖B‖ * (‖c‖ + κ * ‖ν‖) ^ 2 / 2 * r ^ 3 := by ring
  have hR : |ρ (p + (h₁ + h₂)) - ρ p - ℓ (h₁ + h₂) - (1 / 2 : ℝ) * B (h₁ + h₂) (h₁ + h₂)|
      ≤ η / (2 * (M₀ ^ 2 + 1)) * (r * M₀) ^ 2 :=
    ht.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) (by positivity))
  have hRle : η / (2 * (M₀ ^ 2 + 1)) * (r * M₀) ^ 2 ≤ η / 2 * r ^ 2 := by
    rw [mul_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : M₀ ^ 2 ≤ M₀ ^ 2 + 1 := by linarith
    calc η * (r ^ 2 * M₀ ^ 2) ≤ η * (r ^ 2 * (M₀ ^ 2 + 1)) := by gcongr
      _ = η / 2 * r ^ 2 * (2 * (M₀ ^ 2 + 1)) := by ring
  -- assemble
  rw [hsplit]
  have hkey : ρ (p + (h₁ + h₂)) - (-(κ * r ^ 2) + ‖ζ‖ ^ 2 * leviForm ρ p w) =
      (ρ (p + (h₁ + h₂)) - ρ p - ℓ (h₁ + h₂) - (1 / 2 : ℝ) * B (h₁ + h₂) (h₁ + h₂)) +
        (B h₁ h₂ + (1 / 2 : ℝ) * B h₂ h₂) := by
    rw [h.eq_zero, hlin, hquad, hquad₁]
    linarith [hcancel]
  rw [hkey]
  calc |(ρ (p + (h₁ + h₂)) - ρ p - ℓ (h₁ + h₂) - (1 / 2 : ℝ) * B (h₁ + h₂) (h₁ + h₂)) +
        (B h₁ h₂ + (1 / 2 : ℝ) * B h₂ h₂)|
      ≤ |ρ (p + (h₁ + h₂)) - ρ p - ℓ (h₁ + h₂) - (1 / 2 : ℝ) * B (h₁ + h₂) (h₁ + h₂)| +
        (|B h₁ h₂| + |(1 / 2 : ℝ) * B h₂ h₂|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ η / 2 * r ^ 2 + M₁ * r ^ 3 := by
        rw [hM₁, add_mul]
        exact add_le_add (hR.trans hRle) (add_le_add hB₁₂ hB₂₂)
    _ ≤ η / 2 * r ^ 2 + η / 2 * r ^ 2 := by
        refine add_le_add le_rfl ?_
        calc M₁ * r ^ 3 = r * M₁ * r ^ 2 := by ring
          _ ≤ η / 2 * r ^ 2 := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              have : r * M₁ ≤ r * (M₁ + 1) := mul_le_mul_of_nonneg_left (by linarith) hr.le
              linarith
    _ = η * r ^ 2 := by ring

variable {n : ℕ}

/-- **Levi's theorem.** A domain of holomorphy in `Fin n → ℂ` is Levi pseudoconvex: the Levi
form of every local defining function is positive semidefinite on the complex tangent space at
every boundary point. -/
theorem IsDomainOfHolomorphy.isLeviPseudoconvex {U : Set (Fin n → ℂ)}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) : IsLeviPseudoconvex U := by
  intro p hp ρ V h w hw
  by_contra hneg
  push Not at hneg
  set L := leviForm ρ p w with hL
  set ℓ := fderiv ℝ ρ p with hℓ
  set B := fderiv ℝ (fderiv ℝ ρ) p with hB
  obtain ⟨c, hc⟩ := exists_complexPart_eq h.fderiv_ne (-leviQuadratic B w)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, ℓ c₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h.fderiv_ne (ContinuousLinearMap.ext hcon)
  set ν : Fin n → ℂ := (-1 / ℓ c₀) • c₀ with hν
  have hℓν : ℓ ν = -1 := by
    rw [hν, map_smul, smul_eq_mul, div_mul_cancel₀ _ hc₀]
  obtain ⟨C₁, c₂, δ, hC₁, hc₂, hδ, hdist⟩ := h.exists_infDist_bounds ho hp
  set κ : ℝ := c₂ * (-L) / (8 * C₁) with hκ
  have hκ0 : 0 < κ := by
    rw [hκ]
    have : 0 < -L := by linarith
    positivity
  set η : ℝ := min (κ / 2) (-L / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by linarith)
  have hηκ : η ≤ κ / 2 := min_le_left _ _
  have hηL : η ≤ -L / 2 := min_le_right _ _
  obtain ⟨r, hr, hest⟩ := h.exists_disc_estimate hw hc hℓν hκ0.le hη0
    (W := V ∩ ball p δ) (inter_mem (h.isOpen.mem_nhds h.mem) (ball_mem_nhds p hδ))
  set φ : ℂ → Fin n → ℂ := fun ζ => p + ζ • w + ζ ^ 2 • c + (κ * r ^ 2) • ν with hφ
  have hφan : AnalyticOnNhd ℂ φ (closedBall 0 r) := fun ζ _ =>
    ((analyticAt_const.add (analyticAt_id.smul analyticAt_const)).add
      ((analyticAt_id.pow 2).smul analyticAt_const)).add analyticAt_const
  have hest' : ∀ ζ : ℂ, ‖ζ‖ ≤ r → φ ζ ∈ V ∩ ball p δ ∧
      |ρ (φ ζ) - (-(κ * r ^ 2) + ‖ζ‖ ^ 2 * L)| ≤ η * r ^ 2 := hest r hr le_rfl
  -- the disc lies in `U`
  have hdiscU : ∀ ζ ∈ closedBall (0 : ℂ) r, φ ζ ∈ U := by
    intro ζ hζ
    have hζ' : ‖ζ‖ ≤ r := mem_closedBall_zero_iff.mp hζ
    obtain ⟨hmem, hρ⟩ := hest' ζ hζ'
    apply h.mem_of_neg hmem.1
    have h1 := (abs_le.mp hρ).2
    have h2 : ‖ζ‖ ^ 2 * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg.le
    have h3 : η * r ^ 2 ≤ κ / 2 * r ^ 2 := mul_le_mul_of_nonneg_right hηκ (by positivity)
    have h4 : 0 < κ / 2 * r ^ 2 := by positivity
    linarith
  -- the boundary circle is deep inside
  set m : ℝ := c₂ * (-L) / 2 * r ^ 2 with hm
  have hm0 : 0 < m := by
    have : 0 < -L := by linarith
    positivity
  have hcircle : ∀ ζ ∈ sphere (0 : ℂ) r, m ≤ infDist (φ ζ) Uᶜ := by
    intro ζ hζ
    have hζ' : ‖ζ‖ = r := mem_sphere_zero_iff_norm.mp hζ
    obtain ⟨hmem, hρ⟩ := hest' ζ hζ'.le
    have hin := hdiscU ζ (sphere_subset_closedBall hζ)
    have hlow := (hdist (φ ζ) hmem.2 hin).1
    have h1 := (abs_le.mp hρ).2
    rw [hζ'] at h1
    have hρneg : ρ (φ ζ) ≤ L / 2 * r ^ 2 := by
      have h3 : η * r ^ 2 ≤ -L / 2 * r ^ 2 := mul_le_mul_of_nonneg_right hηL (by positivity)
      have h4 : 0 ≤ κ * r ^ 2 := by positivity
      linarith
    have habs : -L / 2 * r ^ 2 ≤ |ρ (φ ζ)| := by
      rw [abs_of_nonpos (by nlinarith [pow_pos hr 2])]
      linarith
    calc m = c₂ * (-L / 2 * r ^ 2) := by rw [hm]; ring
      _ ≤ c₂ * |ρ (φ ζ)| := mul_le_mul_of_nonneg_left habs hc₂.le
      _ ≤ infDist (φ ζ) Uᶜ := hlow
  -- the center is shallow
  have hcenter : infDist (φ 0) Uᶜ ≤ C₁ * (2 * κ * r ^ 2) := by
    obtain ⟨hmem, hρ⟩ := hest' 0 (by simp [hr.le])
    have hin := hdiscU 0 (mem_closedBall_self hr.le)
    have hup := (hdist (φ 0) hmem.2 hin).2
    have habs : |ρ (φ 0)| ≤ 2 * κ * r ^ 2 := by
      have h0 : ‖(0 : ℂ)‖ ^ 2 * L = 0 := by simp
      rw [h0, add_zero, sub_neg_eq_add] at hρ
      have h3 : η * r ^ 2 ≤ κ / 2 * r ^ 2 := mul_le_mul_of_nonneg_right hηκ (by positivity)
      have hκr : 0 ≤ κ * r ^ 2 := by positivity
      have := abs_le.mp hρ
      rw [abs_le]
      constructor <;> linarith
    exact hup.trans (mul_le_mul_of_nonneg_left habs hC₁.le)
  -- Thullen's radius bound
  have hhull := mem_holomorphicHull_of_analytic_disc hr hφan hdiscU (mem_closedBall_self hr.le)
  have hK : IsCompact (φ '' sphere 0 r) :=
    (isCompact_sphere (0 : ℂ) r).image_of_continuousOn
      (hφan.continuousOn.mono sphere_subset_closedBall)
  have hKU : φ '' sphere 0 r ⊆ U := by
    rintro _ ⟨ζ, hζ, rfl⟩
    exact hdiscU ζ (sphere_subset_closedBall hζ)
  have hrad := hU.holomorphic_radius_bound ho hK hKU (q := fun _ => (m : ℂ)) analyticOnNhd_const
    (fun z hz => by
      obtain ⟨ζ, hζ, rfl⟩ := hz
      have : ‖(m : ℂ)‖ = m := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
      rw [this]
      exact (ball_subset_ball (hcircle ζ hζ)).trans
        (by simpa using ball_infDist_subset_compl (x := φ ζ) (s := Uᶜ)))
    (φ 0) hhull
  have hm' : ‖(m : ℂ)‖ = m := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
  rw [hm'] at hrad
  have hUc : Uᶜ.Nonempty := ⟨p, notMem_of_mem_frontier ho hp⟩
  have hmle : m ≤ infDist (φ 0) Uᶜ := by
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy, hdy⟩ := (infDist_lt_iff hUc).mp hlt
    exact hy (hrad (by rwa [mem_ball, dist_comm]))
  have hfinal : m ≤ C₁ * (2 * κ * r ^ 2) := hmle.trans hcenter
  rw [hm, hκ] at hfinal
  have hC₁' : C₁ * (2 * (c₂ * (-L) / (8 * C₁)) * r ^ 2) = c₂ * (-L) / 4 * r ^ 2 := by
    field_simp
    ring
  rw [hC₁'] at hfinal
  have : 0 < c₂ * (-L) / 4 * r ^ 2 := by
    have : 0 < -L := by linarith
    positivity
  linarith

end SeveralComplexVariables
