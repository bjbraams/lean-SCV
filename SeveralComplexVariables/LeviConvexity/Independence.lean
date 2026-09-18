/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.LeviConvexity
public import SeveralComplexVariables.Subharmonic.SmoothCriterion
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Independence of the defining function

Two local `C²` defining functions of the same open set at the same boundary point have
positively proportional derivatives, and their second derivatives are proportional by the
same factor on tangent vectors. Consequently the complex tangent space and the sign of the
Levi form on it do not depend on the choice of defining function, and the Levi condition can
be verified on a single defining function.

The proofs avoid the implicit function theorem and the positive-factor lemma of Range
(Lemma 2.5). First derivatives are compared through one-sided difference quotients along
lines entering the set; second derivatives through second-order expansions along parabolic
curves `t ↦ p + t v + β t² ν`, whose sign is controlled by the defining property.

References: Range (1986), Chapter II, Lemma 2.5 and the discussion after (2.19);
Fritzsche–Grauert (2002), Chapter II, Lemma 4.1.
-/

@[expose] public noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section LinearAlgebra

/-- A nonzero functional whose closed negative half-space contains the open negative half-space
of another nonzero functional is a positive multiple of it. -/
theorem exists_pos_smul_eq_of_neg_imp_nonpos {ℓ₁ ℓ₂ : E →L[ℝ] ℝ} (h₁ : ℓ₁ ≠ 0) (h₂ : ℓ₂ ≠ 0)
    (h : ∀ v, ℓ₂ v < 0 → ℓ₁ v ≤ 0) : ∃ c : ℝ, 0 < c ∧ ℓ₁ = c • ℓ₂ := by
  obtain ⟨u, hu⟩ : ∃ u, ℓ₂ u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h₂ (ContinuousLinearMap.ext hcon)
  set u₀ : E := (1 / ℓ₂ u) • u with hu₀
  have hℓu₀ : ℓ₂ u₀ = 1 := by rw [hu₀, map_smul, smul_eq_mul, one_div, inv_mul_cancel₀ hu]
  set c := ℓ₁ u₀ with hc
  -- the kernel of `ℓ₂` is contained in the kernel of `ℓ₁`
  have hker : ∀ v, ℓ₂ v = 0 → ℓ₁ v = 0 := by
    intro v hv
    have hle : ∀ ε : ℝ, 0 < ε → ℓ₁ v ≤ ε * c := by
      intro ε hε
      have := h (v - ε • u₀) (by rw [map_sub, map_smul, hv, hℓu₀, smul_eq_mul]; linarith)
      rw [map_sub, map_smul, smul_eq_mul] at this
      linarith
    have hge : ∀ ε : ℝ, 0 < ε → -(ε * c) ≤ ℓ₁ v := by
      intro ε hε
      have := h (-v - ε • u₀) (by rw [map_sub, map_neg, map_smul, hv, hℓu₀, smul_eq_mul]; linarith)
      rw [map_sub, map_neg, map_smul, smul_eq_mul] at this
      linarith
    have h1 : ℓ₁ v ≤ 0 := le_of_forall_pos_le_add fun ε hε => by
      have := hle (ε / (|c| + 1)) (by positivity)
      have hcb : ε / (|c| + 1) * c ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [le_abs_self c, abs_nonneg c]
      linarith
    have h2 : 0 ≤ ℓ₁ v := by
      by_contra hneg
      push Not at hneg
      have := hge (-ℓ₁ v / (2 * (|c| + 1))) (div_pos (by linarith) (by positivity))
      have hcb : -ℓ₁ v / (2 * (|c| + 1)) * c ≤ -ℓ₁ v / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [le_abs_self c, abs_nonneg c]
      linarith
    exact le_antisymm h1 h2
  have heq : ℓ₁ = c • ℓ₂ := by
    ext v
    have hv : ℓ₂ (v - ℓ₂ v • u₀) = 0 := by rw [map_sub, map_smul, hℓu₀, smul_eq_mul, mul_one, sub_self]
    have := hker _ hv
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
    rw [this, smul_apply, smul_eq_mul, hc, mul_comm]
  have hc0 : 0 ≤ c := by
    have := h (-u₀) (by rw [map_neg, hℓu₀]; norm_num)
    rw [map_neg] at this
    linarith
  refine ⟨c, lt_of_le_of_ne hc0 fun hzero => h₁ ?_, heq⟩
  rw [heq, ← hzero, zero_smul]

end LinearAlgebra

section Comparison

variable {U : Set E} {p : E} {ρ ρ₁ ρ₂ : E → ℝ} {V V₁ V₂ : Set E}

/-- Second-order expansion of a `C²` function along the parabolic curve
`t ↦ p + t • v + (β * t ^ 2) • ν`. -/
theorem exists_parabola_bound (hρ : ContDiffAt ℝ 2 ρ p) (v ν : E) (β : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      |ρ (p + t • v + (β * t ^ 2) • ν) - ρ p - (t * fderiv ℝ ρ p v + β * t ^ 2 * fderiv ℝ ρ p ν +
        t ^ 2 / 2 * fderiv ℝ (fderiv ℝ ρ) p v v)| ≤ η * t ^ 2 := by
  set B := fderiv ℝ (fderiv ℝ ρ) p with hB
  set M₀ : ℝ := ‖v‖ + |β| * ‖ν‖ with hM₀
  set M₁ : ℝ := |β| * ‖B‖ * ‖v‖ * ‖ν‖ + β ^ 2 * ‖B‖ * ‖ν‖ ^ 2 / 2 with hM₁
  have hM₀0 : 0 ≤ M₀ := by positivity
  have hM₁0 : 0 ≤ M₁ := by positivity
  obtain ⟨δ', hδ', htaylor⟩ := exists_taylor_bound hρ (ε := η / (2 * (M₀ ^ 2 + 1))) (by positivity)
  refine ⟨min 1 (min (η / (2 * (M₁ + 1))) (δ' / (2 * (M₀ + 1)))), by positivity, fun t ht htδ => ?_⟩
  have ht1 : t ≤ 1 := (htδ.trans_le (min_le_left _ _)).le
  have htM₁ : t * (M₁ + 1) ≤ η / 2 := by
    have := (htδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have htδ' : t * (M₀ + 1) < δ' := by
    have := (htδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
    rw [le_div_iff₀ (by positivity)] at this
    have hpos : 0 < t * (M₀ + 1) := by positivity
    linarith
  set k : E := t • v + (β * t ^ 2) • ν with hk
  have hkn : ‖k‖ ≤ t * M₀ := by
    calc ‖k‖ ≤ ‖t • v‖ + ‖(β * t ^ 2) • ν‖ := norm_add_le _ _
      _ = t * ‖v‖ + |β| * t ^ 2 * ‖ν‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht, abs_mul,
            abs_of_pos (by positivity : (0:ℝ) < t ^ 2)]
      _ ≤ t * ‖v‖ + |β| * t * ‖ν‖ := by
          have : t ^ 2 ≤ t := by nlinarith
          gcongr
      _ = t * M₀ := by rw [hM₀]; ring
  have hklt : ‖k‖ < δ' := hkn.trans_lt (by nlinarith)
  have htay : |ρ (p + k) - ρ p - fderiv ℝ ρ p k - (1 / 2 : ℝ) * B k k| ≤
      η / (2 * (M₀ ^ 2 + 1)) * ‖k‖ ^ 2 := htaylor k hklt
  have hsplit : p + t • v + (β * t ^ 2) • ν = p + k := by rw [hk]; abel
  have hlin : fderiv ℝ ρ p k = t * fderiv ℝ ρ p v + β * t ^ 2 * fderiv ℝ ρ p ν := by
    rw [hk, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hquad : (1 / 2 : ℝ) * B k k - t ^ 2 / 2 * B v v =
      (1 / 2 : ℝ) * (β * t ^ 3 * (B v ν + B ν v) + β ^ 2 * t ^ 4 * B ν ν) := by
    rw [hk]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  have hBn : 0 ≤ ‖B‖ := ContinuousLinearMap.opNorm_nonneg B
  have hquad_bd : |(1 / 2 : ℝ) * B k k - t ^ 2 / 2 * B v v| ≤ M₁ * t ^ 3 := by
    rw [hquad, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    have h1 : |B v ν| ≤ ‖B‖ * ‖v‖ * ‖ν‖ := by
      have := B.le_opNorm₂ v ν; rwa [Real.norm_eq_abs] at this
    have h2 : |B ν v| ≤ ‖B‖ * ‖ν‖ * ‖v‖ := by
      have := B.le_opNorm₂ ν v; rwa [Real.norm_eq_abs] at this
    have h3 : |B ν ν| ≤ ‖B‖ * ‖ν‖ * ‖ν‖ := by
      have := B.le_opNorm₂ ν ν; rwa [Real.norm_eq_abs] at this
    have ht3 : 0 ≤ t ^ 3 := by positivity
    have ht4 : t ^ 4 ≤ t ^ 3 := by
      calc t ^ 4 = t ^ 3 * t := by ring
        _ ≤ t ^ 3 * 1 := by gcongr
        _ = t ^ 3 := mul_one _
    calc 1 / 2 * |β * t ^ 3 * (B v ν + B ν v) + β ^ 2 * t ^ 4 * B ν ν|
        ≤ 1 / 2 * (|β| * t ^ 3 * (|B v ν| + |B ν v|) + β ^ 2 * t ^ 4 * |B ν ν|) := by
          gcongr
          calc |β * t ^ 3 * (B v ν + B ν v) + β ^ 2 * t ^ 4 * B ν ν|
              ≤ |β * t ^ 3 * (B v ν + B ν v)| + |β ^ 2 * t ^ 4 * B ν ν| := abs_add_le _ _
            _ = |β| * t ^ 3 * |B v ν + B ν v| + β ^ 2 * t ^ 4 * |B ν ν| := by
                rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg ht3, abs_pow,
                  abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 4)]
                simp [sq_abs]
            _ ≤ |β| * t ^ 3 * (|B v ν| + |B ν v|) + β ^ 2 * t ^ 4 * |B ν ν| := by
                gcongr
                exact abs_add_le _ _
      _ ≤ 1 / 2 * (|β| * t ^ 3 * (‖B‖ * ‖v‖ * ‖ν‖ + ‖B‖ * ‖ν‖ * ‖v‖) +
            β ^ 2 * t ^ 3 * (‖B‖ * ‖ν‖ * ‖ν‖)) := by
          gcongr
      _ = M₁ * t ^ 3 := by rw [hM₁]; ring
  have hR : |ρ (p + k) - ρ p - fderiv ℝ ρ p k - (1 / 2 : ℝ) * B k k| ≤ η / 2 * t ^ 2 := by
    refine le_trans htay ?_
    calc η / (2 * (M₀ ^ 2 + 1)) * ‖k‖ ^ 2 ≤ η / (2 * (M₀ ^ 2 + 1)) * (t * M₀) ^ 2 := by
          gcongr
      _ ≤ η / 2 * t ^ 2 := by
          rw [mul_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          have : M₀ ^ 2 ≤ M₀ ^ 2 + 1 := by linarith
          calc η * (t ^ 2 * M₀ ^ 2) ≤ η * (t ^ 2 * (M₀ ^ 2 + 1)) := by gcongr
            _ = η / 2 * t ^ 2 * (2 * (M₀ ^ 2 + 1)) := by ring
  rw [hsplit]
  have hkey : ρ (p + k) - ρ p - (t * fderiv ℝ ρ p v + β * t ^ 2 * fderiv ℝ ρ p ν +
      t ^ 2 / 2 * B v v) = (ρ (p + k) - ρ p - fderiv ℝ ρ p k - (1 / 2 : ℝ) * B k k) +
        ((1 / 2 : ℝ) * B k k - t ^ 2 / 2 * B v v) := by
    rw [hlin]; ring
  rw [hkey]
  calc |(ρ (p + k) - ρ p - fderiv ℝ ρ p k - (1 / 2 : ℝ) * B k k) +
        ((1 / 2 : ℝ) * B k k - t ^ 2 / 2 * B v v)|
      ≤ |ρ (p + k) - ρ p - fderiv ℝ ρ p k - (1 / 2 : ℝ) * B k k| +
        |(1 / 2 : ℝ) * B k k - t ^ 2 / 2 * B v v| := abs_add_le _ _
    _ ≤ η / 2 * t ^ 2 + M₁ * t ^ 3 := add_le_add hR hquad_bd
    _ ≤ η / 2 * t ^ 2 + η / 2 * t ^ 2 := by
        refine add_le_add le_rfl ?_
        calc M₁ * t ^ 3 = t * M₁ * t ^ 2 := by ring
          _ ≤ η / 2 * t ^ 2 := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              have : t * M₁ ≤ t * (M₁ + 1) := mul_le_mul_of_nonneg_left (by linarith) ht.le
              linarith
    _ = η * t ^ 2 := by ring

/-- A defining function is negative along a line entering the set, and the derivative of any
other defining function in that direction is nonpositive. -/
theorem IsLocalDefiningFunction.fderiv_nonpos_of_fderiv_neg (h₁ : IsLocalDefiningFunction U p ρ₁ V₁)
    (h₂ : IsLocalDefiningFunction U p ρ₂ V₂) {v : E} (hv : fderiv ℝ ρ₂ p v < 0) :
    fderiv ℝ ρ₁ p v ≤ 0 := by
  have hd : ∀ (ρ : E → ℝ) (V : Set E), IsLocalDefiningFunction U p ρ V →
      HasDerivAt (fun t : ℝ => ρ (p + t • v)) (fderiv ℝ ρ p v) 0 := by
    intro ρ V h
    have hρ : DifferentiableAt ℝ ρ (p + (0 : ℝ) • v) := by
      simpa using (h.contDiffOn.contDiffAt (h.isOpen.mem_nhds h.mem)).differentiableAt (by norm_num)
    have hl : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
    have := hρ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    convert this using 2 <;> simp
  have h1 := (hasDerivAt_iff_tendsto_slope_zero.mp (hd ρ₁ V₁ h₁)).mono_left (nhdsGT_le_nhdsNE 0)
  have h2 := (hasDerivAt_iff_tendsto_slope_zero.mp (hd ρ₂ V₂ h₂)).mono_left (nhdsGT_le_nhdsNE 0)
  simp only [zero_add, zero_smul, add_zero, h₁.eq_zero, h₂.eq_zero, sub_zero, smul_eq_mul] at h1 h2
  -- the slopes of `ρ₂` are eventually negative, so the points lie in `U`
  have hneg : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ * ρ₂ (p + t • v) < 0 :=
    h2.eventually (eventually_lt_nhds hv)
  have hV : ∀ᶠ t in 𝓝[>] (0 : ℝ), p + t • v ∈ V₁ ∩ V₂ := by
    have hc : ContinuousAt (fun t : ℝ => p + t • v) 0 := by fun_prop
    have hVp : V₁ ∩ V₂ ∈ 𝓝 p := inter_mem (h₁.isOpen.mem_nhds h₁.mem) (h₂.isOpen.mem_nhds h₂.mem)
    have := hc.preimage_mem_nhds (by convert hVp using 2; simp)
    exact nhdsWithin_le_nhds this
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ * ρ₁ (p + t • v) ≤ 0 := by
    filter_upwards [hneg, hV, self_mem_nhdsWithin] with t ht htV htpos
    have ht0 : 0 < t := htpos
    have hρ₂ : ρ₂ (p + t • v) < 0 := by
      by_contra hcon
      push Not at hcon
      have : 0 ≤ t⁻¹ * ρ₂ (p + t • v) := mul_nonneg (inv_nonneg.mpr ht0.le) hcon
      linarith
    have hU : p + t • v ∈ U := h₂.mem_of_neg htV.2 hρ₂
    have hρ₁ : ρ₁ (p + t • v) < 0 := h₁.neg_of_mem htV.1 hU
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht0.le) hρ₁.le
  exact le_of_tendsto h1 hle

/-- **First-order comparison.** The derivatives of two defining functions at the same boundary
point are positively proportional. -/
theorem IsLocalDefiningFunction.exists_fderiv_eq_smul (h₁ : IsLocalDefiningFunction U p ρ₁ V₁)
    (h₂ : IsLocalDefiningFunction U p ρ₂ V₂) :
    ∃ c : ℝ, 0 < c ∧ fderiv ℝ ρ₁ p = c • fderiv ℝ ρ₂ p :=
  exists_pos_smul_eq_of_neg_imp_nonpos h₁.fderiv_ne h₂.fderiv_ne fun _ hv =>
    h₁.fderiv_nonpos_of_fderiv_neg h₂ hv

/-- One half of the second-order comparison on tangent vectors. -/
theorem IsLocalDefiningFunction.fderiv_fderiv_le (h₁ : IsLocalDefiningFunction U p ρ₁ V₁)
    (h₂ : IsLocalDefiningFunction U p ρ₂ V₂) {c : ℝ} (hc : 0 < c)
    (hℓ : fderiv ℝ ρ₁ p = c • fderiv ℝ ρ₂ p) {v : E} (hv : fderiv ℝ ρ₂ p v = 0) :
    fderiv ℝ (fderiv ℝ ρ₁) p v v ≤ c * fderiv ℝ (fderiv ℝ ρ₂) p v v := by
  by_contra hlt
  push Not at hlt
  set a₁ := fderiv ℝ (fderiv ℝ ρ₁) p v v with ha₁
  set a₂ := fderiv ℝ (fderiv ℝ ρ₂) p v v with ha₂
  -- an inward direction for `ρ₂`
  obtain ⟨u, hu⟩ : ∃ u, fderiv ℝ ρ₂ p u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h₂.fderiv_ne (ContinuousLinearMap.ext hcon)
  set ν : E := (1 / fderiv ℝ ρ₂ p u) • u with hν
  have hν₂ : fderiv ℝ ρ₂ p ν = 1 := by
    rw [hν, map_smul, smul_eq_mul, one_div, inv_mul_cancel₀ hu]
  have hν₁ : fderiv ℝ ρ₁ p ν = c := by rw [hℓ, smul_apply, hν₂, smul_eq_mul, mul_one]
  have hv₁ : fderiv ℝ ρ₁ p v = 0 := by rw [hℓ, smul_apply, hv, smul_zero]
  -- the parabola parameter
  set β : ℝ := (-a₂ / 2 + -a₁ / (2 * c)) / 2 with hβ
  have hβ₂ : β + a₂ / 2 < 0 := by
    rw [hβ]
    have : -a₁ / (2 * c) < -a₂ / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hβ₁ : 0 < c * β + a₁ / 2 := by
    rw [hβ]
    have : -a₂ / 2 > -a₁ / (2 * c) := by
      rw [gt_iff_lt, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hc' : c * (-a₁ / (2 * c)) = -a₁ / 2 := by field_simp
    nlinarith
  set η : ℝ := min (-(β + a₂ / 2) / 2) ((c * β + a₁ / 2) / 2) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hρ₁c : ContDiffAt ℝ 2 ρ₁ p := h₁.contDiffOn.contDiffAt (h₁.isOpen.mem_nhds h₁.mem)
  have hρ₂c : ContDiffAt ℝ 2 ρ₂ p := h₂.contDiffOn.contDiffAt (h₂.isOpen.mem_nhds h₂.mem)
  obtain ⟨δ₁, hδ₁, hb₁⟩ := exists_parabola_bound hρ₁c v ν β hη0
  obtain ⟨δ₂, hδ₂, hb₂⟩ := exists_parabola_bound hρ₂c v ν β hη0
  have hcont : ContinuousAt (fun t : ℝ => p + t • v + (β * t ^ 2) • ν) 0 := by fun_prop
  have hVp : V₁ ∩ V₂ ∈ 𝓝 p := inter_mem (h₁.isOpen.mem_nhds h₁.mem) (h₂.isOpen.mem_nhds h₂.mem)
  obtain ⟨δ₃, hδ₃, hV⟩ := Metric.mem_nhds_iff.mp (hcont.preimage_mem_nhds (by
    convert hVp using 2
    simp))
  set t : ℝ := min δ₁ (min δ₂ δ₃) / 2 with ht
  have ht0 : 0 < t := by positivity
  have ht₁ : t < δ₁ := by
    have := min_le_left δ₁ (min δ₂ δ₃)
    rw [ht]; linarith [lt_min hδ₁ (lt_min hδ₂ hδ₃)]
  have ht₂ : t < δ₂ := by
    have := (min_le_right δ₁ (min δ₂ δ₃)).trans (min_le_left δ₂ δ₃)
    rw [ht]; linarith [lt_min hδ₁ (lt_min hδ₂ hδ₃)]
  have ht₃ : t < δ₃ := by
    have := (min_le_right δ₁ (min δ₂ δ₃)).trans (min_le_right δ₂ δ₃)
    rw [ht]; linarith [lt_min hδ₁ (lt_min hδ₂ hδ₃)]
  set z := p + t • v + (β * t ^ 2) • ν with hz
  have hzV : z ∈ V₁ ∩ V₂ := hV (by
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht0]
    exact ht₃)
  have e₁ := hb₁ t ht0 ht₁
  have e₂ := hb₂ t ht0 ht₂
  rw [h₁.eq_zero, hv₁, hν₁] at e₁
  rw [h₂.eq_zero, hv, hν₂] at e₂
  have hρ₂ : ρ₂ z < 0 := by
    have := (abs_le.mp e₂).2
    have hη' : η ≤ -(β + a₂ / 2) / 2 := min_le_left _ _
    have ht2 : 0 < t ^ 2 := by positivity
    nlinarith
  have hρ₁ : 0 < ρ₁ z := by
    have := (abs_le.mp e₁).1
    have hη' : η ≤ (c * β + a₁ / 2) / 2 := min_le_right _ _
    have ht2 : 0 < t ^ 2 := by positivity
    nlinarith
  have hU : z ∈ U := h₂.mem_of_neg hzV.2 hρ₂
  have := h₁.neg_of_mem hzV.1 hU
  linarith

/-- **Second-order comparison.** On tangent vectors, the second derivatives of two defining
functions are proportional with the same positive factor as their first derivatives. -/
theorem IsLocalDefiningFunction.fderiv_fderiv_eq (h₁ : IsLocalDefiningFunction U p ρ₁ V₁)
    (h₂ : IsLocalDefiningFunction U p ρ₂ V₂) {c : ℝ} (hc : 0 < c)
    (hℓ : fderiv ℝ ρ₁ p = c • fderiv ℝ ρ₂ p) {v : E} (hv : fderiv ℝ ρ₂ p v = 0) :
    fderiv ℝ (fderiv ℝ ρ₁) p v v = c * fderiv ℝ (fderiv ℝ ρ₂) p v v := by
  have h1 := h₁.fderiv_fderiv_le h₂ hc hℓ hv
  have hℓ' : fderiv ℝ ρ₂ p = c⁻¹ • fderiv ℝ ρ₁ p := by
    rw [hℓ, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  have hv₁ : fderiv ℝ ρ₁ p v = 0 := by rw [hℓ, smul_apply, hv, smul_zero]
  have h2 := h₂.fderiv_fderiv_le h₁ (inv_pos.mpr hc) hℓ' hv₁
  have : c * fderiv ℝ (fderiv ℝ ρ₂) p v v ≤ fderiv ℝ (fderiv ℝ ρ₁) p v v := by
    have := mul_le_mul_of_nonneg_left h2 hc.le
    rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this
  exact le_antisymm h1 this

/-- The complex tangent space does not depend on the defining function. -/
theorem IsLocalDefiningFunction.isComplexTangent_iff (h₁ : IsLocalDefiningFunction U p ρ₁ V₁)
    (h₂ : IsLocalDefiningFunction U p ρ₂ V₂) (w : E) :
    IsComplexTangent ρ₁ p w ↔ IsComplexTangent ρ₂ p w := by
  obtain ⟨c, hc, hℓ⟩ := h₁.exists_fderiv_eq_smul h₂
  simp only [IsComplexTangent, hℓ, smul_apply, smul_eq_mul,
    mul_eq_zero, hc.ne', false_or]

/-- On complex tangent vectors, the Levi forms of two defining functions are positively
proportional. -/
theorem IsLocalDefiningFunction.exists_leviForm_eq (h₁ : IsLocalDefiningFunction U p ρ₁ V₁)
    (h₂ : IsLocalDefiningFunction U p ρ₂ V₂) :
    ∃ c : ℝ, 0 < c ∧ ∀ w, IsComplexTangent ρ₂ p w → leviForm ρ₁ p w = c * leviForm ρ₂ p w := by
  obtain ⟨c, hc, hℓ⟩ := h₁.exists_fderiv_eq_smul h₂
  refine ⟨c, hc, fun w hw => ?_⟩
  rw [leviForm_eq_fderiv, leviForm_eq_fderiv, h₁.fderiv_fderiv_eq h₂ hc hℓ hw.1,
    h₁.fderiv_fderiv_eq h₂ hc hℓ hw.smul_I.1]
  ring

/-- **The Levi condition can be checked on one defining function.** -/
theorem isLeviPseudoconvexAt_iff_of_defining (h : IsLocalDefiningFunction U p ρ V) :
    IsLeviPseudoconvexAt U p ↔ ∀ w, IsComplexTangent ρ p w → 0 ≤ leviForm ρ p w := by
  constructor
  · intro hL w hw
    exact hL ρ V h w hw
  · intro hL ρ' V' h' w hw
    obtain ⟨c, hc, hlev⟩ := h'.exists_leviForm_eq h
    have hw' : IsComplexTangent ρ p w := (h'.isComplexTangent_iff h w).mp hw
    rw [hlev w hw']
    exact mul_nonneg hc.le (hL w hw')

end Comparison

end SeveralComplexVariables
