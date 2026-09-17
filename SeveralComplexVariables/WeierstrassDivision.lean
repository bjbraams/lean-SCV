/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.Basic
public import SeveralComplexVariables.IdentityPrinciple
public import SeveralComplexVariables.Polydisc
public import SeveralComplexVariables.AnalyticGerm
public import SeveralComplexVariables.CauchyDerivatives
public import SeveralComplexVariables.ContourIntegral
public import SeveralComplexVariables.LocallyUniform
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.AbsMax

/-!
# Analytic Weierstrass division

We distinguish a scalar coordinate on `E × ℂ`. A remainder of degree less than `d`
is represented by its `Fin d` coefficient functions. This includes the zero remainder
when `d = 0`, without using the natural degree of the zero polynomial.

The reference is Jakóbczak–Jarnicki, §1.7, Lemma 1.7.4 and Theorem 1.7.3.
Uniqueness of coordinate-power division is proved from last-coordinate Taylor
coefficients. Existence of the quotient, the uniform bound, and general division
on a fixed polydisc remain pending. The local (germ) consequence is derived from
the latter.
The uniform statement applies to bounded numerators on a common polydisc; the local
statement applies to arbitrary analytic numerators with no common-neighborhood claim.
These analytic statements do not follow just from Mathlib's formal, adic division theorem.
-/

@[expose] public noncomputable section

open Complex Filter Finset Metric Set
open scoped Real Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Evaluate a polynomial of degree less than `d` in the distinguished scalar coordinate.
The coefficients are functions of the parameter alone. -/
def weierstrassRemainder {d : ℕ} (a : Fin d → E → ℂ) (z : E × ℂ) : ℂ :=
  ∑ j : Fin d, a j z.1 * z.2 ^ (j : ℕ)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- The only remainder of degree less than zero is the zero function. -/
@[simp] theorem weierstrassRemainder_zero (a : Fin 0 → E → ℂ) :
    weierstrassRemainder a = 0 := by
  funext z
  simp [weierstrassRemainder]

/-- Analytic coefficients give a jointly analytic polynomial in the scalar coordinate. -/
theorem analyticAt_weierstrassRemainder {d : ℕ} {a : Fin d → E → ℂ} {z : E × ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) z.1) : AnalyticAt ℂ (weierstrassRemainder a) z := by
  apply Finset.analyticAt_fun_sum
  intro j _
  exact ((ha j).comp analyticAt_fst).mul (analyticAt_snd.pow (j : ℕ))

/-- Local analytic division, with remainder degree encoded by its coefficient index. -/
structure IsWeierstrassDivisionAt {d : ℕ} (f g q : E × ℂ → ℂ)
    (a : Fin d → E → ℂ) : Prop where
  quotient_analytic : AnalyticAt ℂ q 0
  coefficient_analytic : ∀ j, AnalyticAt ℂ (a j) 0
  eq : g =ᶠ[𝓝 0] fun z => q z * f z + weierstrassRemainder a z

/-- Division on a product of a parameter domain and a scalar disc. -/
structure IsWeierstrassDivisionOn {d : ℕ} (f g q : E × ℂ → ℂ)
    (a : Fin d → E → ℂ) (V : Set E) (R : ℝ) : Prop where
  quotient_holomorphic : DifferentiableOn ℂ q (V ×ˢ ball 0 R)
  coefficient_holomorphic : ∀ j, DifferentiableOn ℂ (a j) V
  eq : EqOn g (fun z => q z * f z + weierstrassRemainder a z) (V ×ˢ ball 0 R)

/-- An open-domain division identity induces division at the origin. -/
theorem IsWeierstrassDivisionOn.at_zero [FiniteDimensional ℂ E]
    {d : ℕ} {f g q : E × ℂ → ℂ} {a : Fin d → E → ℂ} {V : Set E} {R : ℝ}
    (h : IsWeierstrassDivisionOn f g q a V R) (hV : IsOpen V) (h0 : 0 ∈ V)
    (hR : 0 < R) : IsWeierstrassDivisionAt f g q a := by
  have hz : (0 : E × ℂ) ∈ V ×ˢ ball 0 R := ⟨h0, mem_ball_self hR⟩
  exact ⟨(h.quotient_holomorphic.analyticOnNhd_finiteDimensional
      (hV.prod isOpen_ball)) _ hz,
    fun j => ((h.coefficient_holomorphic j).analyticOnNhd_finiteDimensional hV) _ h0,
    Filter.mem_of_superset ((hV.prod isOpen_ball).mem_nhds hz) (fun _ hx => h.eq hx)⟩

/-- Division by a nonvanishing analytic function is ordinary division, with zero remainder.
This proves the order-zero existence case without Weierstrass division. -/
theorem isWeierstrassDivisionAt_zero {f g : E × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (h0 : f 0 ≠ 0) :
    IsWeierstrassDivisionAt f g (fun z => g z / f z) (fun j : Fin 0 => Fin.elim0 j) := by
  refine ⟨hg.div hf h0, fun j => Fin.elim0 j, ?_⟩
  filter_upwards [hf.continuousAt.eventually_ne h0] with z hz
  simp [weierstrassRemainder, hz]

/-- In order zero the quotient germ is unique whenever the divisor is nonvanishing. -/
theorem IsWeierstrassDivisionAt.unique_zero {f g q q' : E × ℂ → ℂ}
    {a a' : Fin 0 → E → ℂ} (h : IsWeierstrassDivisionAt f g q a)
    (h' : IsWeierstrassDivisionAt f g q' a')
    (hf : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) : q =ᶠ[𝓝 0] q' := by
  filter_upwards [h.eq, h'.eq, hf.continuousAt.eventually_ne h0] with z hz hz' hne
  have he : q z * f z = q' z * f z := by simpa using hz.symm.trans hz'
  exact mul_right_cancel₀ hne he

variable {ι : Type*} [Fintype ι]

/-- Algebraic splitting of the Cauchy kernel into a polynomial part of degree `< d`
and a remainder with a factor `w^d`. -/
theorem weierstrass_kernel_identity (d : ℕ) {s w : ℂ} (hs : s ≠ 0) (hsw : s ≠ w) :
    (∑ j ∈ range d, w ^ j / s ^ (j + 1)) + w ^ d / (s ^ d * (s - w)) = (s - w)⁻¹ := by
  have hne : s - w ≠ 0 := sub_ne_zero.mpr hsw
  have hsne : s ^ d ≠ 0 := pow_ne_zero d hs
  have hgeom : ∑ i ∈ range d, s ^ i * w ^ (d - 1 - i) = (s ^ d - w ^ d) / (s - w) :=
    (Commute.all s w).geom_sum₂ hsw d
  have hpoly : ∑ j ∈ range d, w ^ j / s ^ (j + 1) = (s ^ d - w ^ d) / (s ^ d * (s - w)) := by
    have hreindex : ∑ i ∈ range d, w ^ (d - 1 - i) / s ^ (d - i) =
        ∑ j ∈ range d, w ^ j / s ^ (j + 1) := by
      refine Eq.trans ?_ (sum_range_reflect (fun j => w ^ j / s ^ (j + 1)) d)
      refine sum_congr rfl fun i hi => ?_
      have : d - 1 - i + 1 = d - i := by
        have := mem_range.mp hi
        omega
      rw [this]
    trans ∑ i ∈ range d, w ^ (d - 1 - i) / s ^ (d - i)
    · exact hreindex.symm
    trans (∑ i ∈ range d, s ^ i * w ^ (d - 1 - i)) / s ^ d
    · rw [sum_div]
      refine sum_congr rfl fun i hi => ?_
      have hle : i ≤ d := (mem_range.mp hi).le
      have hsi : s ^ (d - i) ≠ 0 := pow_ne_zero _ hs
      field_simp [hsne, hsi, pow_ne_zero i hs]
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    · rw [hgeom, div_div, mul_comm (s - w)]
  have hsplit : (s ^ d - w ^ d) / (s ^ d * (s - w)) + w ^ d / (s ^ d * (s - w)) =
      (s - w)⁻¹ := by
    rw [← add_div, sub_add_cancel, div_mul_eq_div_div, div_self hsne, one_div]
  rw [hpoly, hsplit]

/-- A jointly holomorphic function on a product remains holomorphic in the last coordinate. -/
theorem differentiableOn_snd_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {V : Set E} {R : ℝ} {g : E × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) {z : E} (hz : z ∈ V) :
    DifferentiableOn ℂ (fun w => g (z, w)) (ball 0 R) := by
  intro w hw
  exact (hg (z, w) ⟨hz, hw⟩).comp w
    ((differentiableAt_const z).prodMk differentiableAt_id).differentiableWithinAt
    (fun t ht => ⟨hz, ht⟩)

/-- Restricting a product slice to a strictly smaller disc gives continuity up to the
closed disc. -/
theorem diffContOnCl_snd_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {V : Set E} {R ρ : ℝ} {g : E × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) {z : E} (hz : z ∈ V)
    (hρ : 0 < ρ) (hρR : ρ < R) :
    DiffContOnCl ℂ (fun w => g (z, w)) (ball 0 ρ) := by
  refine ⟨(differentiableOn_snd_slice hg hz).mono (ball_subset_ball hρR.le), ?_⟩
  rw [closure_ball _ hρ.ne']
  exact hg.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
    (fun w hw => ⟨hz, closedBall_subset_ball hρR hw⟩)

/-- The Taylor coefficients of a polynomial remainder of degree less than `d`. -/
theorem iteratedDeriv_weierstrassRemainder_const {d : ℕ} (a : Fin d → ℂ) (k : ℕ) :
    iteratedDeriv k (fun w : ℂ => ∑ j : Fin d, a j * w ^ (j : ℕ)) 0 =
      if h : k < d then (k.factorial : ℂ) * a ⟨k, h⟩ else 0 := by
  have hsum := iteratedDeriv_fun_sum (I := Finset.univ) (n := k)
    (f := fun j : Fin d => fun w : ℂ => a j * w ^ (j : ℕ))
    (x := (0 : ℂ)) (fun _ _ => by fun_prop)
  simp only [hsum, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  split_ifs with hk
  · rw [Fintype.sum_eq_single ⟨k, hk⟩]
    · simp [mul_comm]
    · intro j hj
      have hjk : k ≠ (j : ℕ) := by
        intro h
        exact hj (Fin.ext h.symm)
      simp [hjk]
  · apply Finset.sum_eq_zero
    intro j _
    have hjk : k ≠ (j : ℕ) :=
      ne_of_gt (j.isLt.trans_le (le_of_not_gt hk))
    simp [hjk]

/-- In coordinate-power division the remainder coefficients are the Taylor coefficients
of the last-coordinate slice. -/
theorem coeff_eq_iteratedDeriv_of_coordinatePower_division {d : ℕ}
    {V : Set (ι → ℂ)} {R : ℝ} {g q : (ι → ℂ) × ℂ → ℂ} {a : Fin d → (ι → ℂ) → ℂ}
    (h : IsWeierstrassDivisionOn (fun z => z.2 ^ d) g q a V R)
    (hR : 0 < R) {z : ι → ℂ} (hz : z ∈ V) (j : Fin d) :
    a j z = ((j : ℕ).factorial : ℂ)⁻¹ *
      iteratedDeriv (j : ℕ) (fun w => g (z, w)) 0 := by
  have hz0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hqA : AnalyticAt ℂ (fun w => q (z, w)) 0 :=
    ((differentiableOn_snd_slice h.quotient_holomorphic hz).analyticOnNhd_finiteDimensional
      isOpen_ball) _ hz0
  have hpow : AnalyticAt ℂ (fun w : ℂ => w ^ d) 0 := analyticAt_id.pow d
  have hprod : AnalyticAt ℂ (fun w => w ^ d * q (z, w)) 0 := hpow.mul hqA
  have hrem : AnalyticAt ℂ (fun w => ∑ k : Fin d, a k z * w ^ (k : ℕ)) 0 := by fun_prop
  have hid : (fun w => g (z, w)) =ᶠ[𝓝 0]
      (fun w => w ^ d * q (z, w) + ∑ k : Fin d, a k z * w ^ (k : ℕ)) :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hz0) fun w hw => by
      have hmem : (z, w) ∈ V ×ˢ ball (0 : ℂ) R := ⟨hz, hw⟩
      simpa [weierstrassRemainder, mul_comm] using h.eq hmem
  have hord : (d : ℕ∞) ≤ analyticOrderAt (fun w => w ^ d * q (z, w)) 0 := by
    have hmul := analyticOrderAt_mul hpow hqA
    have hpow' : analyticOrderAt (fun w : ℂ => w ^ d) 0 = d := by
      have h := analyticOrderAt_pow (analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))) d
      simpa [analyticOrderAt_id, Pi.pow_def] using h
    have heq : analyticOrderAt (fun w => w ^ d * q (z, w)) 0 =
        analyticOrderAt ((fun w : ℂ => w ^ d) * fun w => q (z, w)) 0 := by
      congr 1
    rw [heq, hmul, hpow']
    exact le_self_add
  have hvan (k : ℕ) (hk : k < d) :
      iteratedDeriv k (fun w => w ^ d * q (z, w)) 0 = 0 :=
    ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hprod).mp hord) k hk
  have hder := hid.iteratedDeriv_eq (j : ℕ)
  have hadd :
      iteratedDeriv (j : ℕ)
          (fun w => w ^ d * q (z, w) + ∑ k : Fin d, a k z * w ^ (k : ℕ)) 0 =
        iteratedDeriv (j : ℕ) (fun w => w ^ d * q (z, w)) 0 +
          iteratedDeriv (j : ℕ) (fun w => ∑ k : Fin d, a k z * w ^ (k : ℕ)) 0 := by
    convert iteratedDeriv_add (n := (j : ℕ)) (x := (0 : ℂ))
      hprod.contDiffAt hrem.contDiffAt
  have hj : (j : ℕ) < d := j.isLt
  rw [hder, hadd, hvan _ hj, zero_add, iteratedDeriv_weierstrassRemainder_const, dite_eq_left hj]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j : ℕ))]

/-- Coordinate-power decompositions are unique: remainder coefficients are Taylor
coefficients of the last-coordinate slice, and the quotient is then recovered from
the identity. Continuity fills in the central fibre `w = 0`. -/
theorem unique_coordinatePower_division {d : ℕ} {V : Set (ι → ℂ)} {R : ℝ}
    {g q q' : (ι → ℂ) × ℂ → ℂ} {a a' : Fin d → (ι → ℂ) → ℂ}
    (h : IsWeierstrassDivisionOn (fun z => z.2 ^ d) g q a V R)
    (h' : IsWeierstrassDivisionOn (fun z => z.2 ^ d) g q' a' V R)
    (hR : 0 < R) :
    EqOn q q' (V ×ˢ ball 0 R) ∧ ∀ j, EqOn (a j) (a' j) V := by
  have ha (j : Fin d) : EqOn (a j) (a' j) V := by
    intro z hz
    exact (coeff_eq_iteratedDeriv_of_coordinatePower_division h hR hz j).trans
      (coeff_eq_iteratedDeriv_of_coordinatePower_division h' hR hz j).symm
  refine ⟨?_, ha⟩
  intro z hz
  have hrem : weierstrassRemainder a z = weierstrassRemainder a' z := by
    simp [weierstrassRemainder, ha _ hz.1]
  have hid : q z * z.2 ^ d + weierstrassRemainder a z =
      q' z * z.2 ^ d + weierstrassRemainder a' z :=
    (h.eq hz).symm.trans (h'.eq hz)
  have hmul : q z * z.2 ^ d = q' z * z.2 ^ d := by
    simpa [hrem] using hid
  by_cases hw : z.2 = 0
  · have hqA : AnalyticAt ℂ (fun w => q (z.1, w)) 0 :=
      ((differentiableOn_snd_slice h.quotient_holomorphic hz.1).analyticOnNhd_finiteDimensional
        isOpen_ball) _ (mem_ball_self hR)
    have hqA' : AnalyticAt ℂ (fun w => q' (z.1, w)) 0 :=
      ((differentiableOn_snd_slice h'.quotient_holomorphic hz.1).analyticOnNhd_finiteDimensional
        isOpen_ball) _ (mem_ball_self hR)
    have heq : (fun w => q (z.1, w)) =ᶠ[𝓝[≠] (0 : ℂ)] fun w => q' (z.1, w) := by
      have hball : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∈ ball (0 : ℂ) R :=
        nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hR))
      filter_upwards [hball, self_mem_nhdsWithin] with w hwball hw0
      have hwP : (z.1, w) ∈ V ×ˢ ball (0 : ℂ) R := ⟨hz.1, hwball⟩
      have hremw : weierstrassRemainder a (z.1, w) = weierstrassRemainder a' (z.1, w) := by
        simp [weierstrassRemainder, ha _ hz.1]
      have hidw : q (z.1, w) * w ^ d + weierstrassRemainder a (z.1, w) =
          q' (z.1, w) * w ^ d + weierstrassRemainder a' (z.1, w) :=
        (h.eq hwP).symm.trans (h'.eq hwP)
      have : q (z.1, w) * w ^ d = q' (z.1, w) * w ^ d := by
        simpa [hremw] using hidw
      exact mul_right_cancel₀ (pow_ne_zero d hw0) this
    have hlim : Tendsto (fun w => q (z.1, w)) (𝓝[≠] (0 : ℂ)) (𝓝 (q (z.1, 0))) :=
      hqA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hlim' : Tendsto (fun w => q' (z.1, w)) (𝓝[≠] (0 : ℂ)) (𝓝 (q' (z.1, 0))) :=
      hqA'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have heq0 : q (z.1, 0) = q' (z.1, 0) :=
      tendsto_nhds_unique (hlim.congr' heq) hlim'
    rw [show z = (z.1, (0 : ℂ)) from Prod.ext rfl hw]
    exact heq0
  · exact mul_right_cancel₀ (pow_ne_zero d hw) hmul

/-- Mixed last-coordinate derivatives at the origin are Cauchy integrals on a smaller circle. -/
theorem iteratedDeriv_snd_slice_circleIntegral
    {V : Set (ι → ℂ)} {R ρ : ℝ} {g : (ι → ℂ) × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) {z : ι → ℂ} (hz : z ∈ V)
    (hρ : 0 < ρ) (hρR : ρ < R) (n : ℕ) :
    iteratedDeriv n (fun w => g (z, w)) 0 =
      (n.factorial : ℂ) * (2 * Real.pi * I : ℂ)⁻¹ *
        ∮ s in C(0, ρ), s ^ (-(n + 1 : ℤ)) * g (z, s) := by
  simpa [sub_zero] using
    (diffContOnCl_snd_slice hg hz hρ hρR).iteratedDeriv_eq_circleIntegral_sub_zpow_mul
      hρ n (mem_ball_self hρ)

/-- The Cauchy integral of a jointly holomorphic kernel in the last coordinate remains
holomorphic in the parameters. -/
theorem analyticOnNhd_circleIntegral_snd_zpow_mul
    {V : Set (ι → ℂ)} (hV : IsOpen V) {R ρ : ℝ} {g : (ι → ℂ) × ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (V ×ˢ ball 0 R)) (hρ : 0 < ρ) (hρR : ρ < R) (n : ℕ) :
    AnalyticOnNhd ℂ (fun z => ∮ s in C(0, ρ), s ^ (-(n + 1 : ℤ)) * g (z, s)) V := by
  have hfθ : ContinuousOn (fun s : ℂ => s ^ (-(n + 1 : ℤ))) (sphere 0 ρ) := by
    refine continuousOn_id.zpow₀ (-(n + 1 : ℤ)) fun s hs => Or.inl ?_
    intro h0
    have hsρ : ‖s‖ = ρ := by
      rw [← dist_zero_right]
      exact mem_sphere.mp hs
    have hs00 : s = 0 := h0
    rw [hs00, norm_zero] at hsρ
    linarith
  have hI := analyticOnNhd_circleIntegral_kernel_mul (E := ι → ℂ) hV hg hρ.le hfθ
    (fun z hz s hs =>
      ⟨hz, (sphere_subset_closedBall.trans (closedBall_subset_ball hρR)) hs⟩)
  refine hI.congr hV fun z hz => ?_
  exact circleIntegral.integral_congr hρ.le fun s _ => mul_comm _ _

/-- The Taylor remainder coefficients of a last-coordinate slice depend holomorphically
on the remaining coordinates. -/
theorem differentiableOn_iteratedDeriv_snd_slice
    {V : Set (ι → ℂ)} (hV : IsOpen V) {R : ℝ} {g : (ι → ℂ) × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) (hR : 0 < R) (n : ℕ) :
    DifferentiableOn ℂ (fun z => iteratedDeriv n (fun w => g (z, w)) 0) V := by
  let ρ := R / 2
  have hρ : 0 < ρ := half_pos hR
  have hρR : ρ < R := half_lt_self hR
  have hgA : AnalyticOnNhd ℂ g (V ×ˢ ball 0 R) :=
    hg.analyticOnNhd_finiteDimensional (hV.prod isOpen_ball)
  have hI := analyticOnNhd_circleIntegral_snd_zpow_mul hV hgA hρ hρR n
  have hEq : EqOn (fun z => iteratedDeriv n (fun w => g (z, w)) 0)
      (fun z => (n.factorial : ℂ) * (2 * Real.pi * I : ℂ)⁻¹ *
        ∮ s in C(0, ρ), s ^ (-(n + 1 : ℤ)) * g (z, s)) V :=
    fun z hz => iteratedDeriv_snd_slice_circleIntegral hg hz hρ hρR n
  exact ((hI.const_smul (c := (n.factorial : ℂ) * (2 * Real.pi * I : ℂ)⁻¹)).congr hV
    (fun z hz => (hEq hz).symm)).differentiableOn

/-- Cauchy integral representing the Weierstrass quotient for division by `w^d`. -/
def weierstrassCauchyQuotient (d : ℕ) (g : (ι → ℂ) × ℂ → ℂ) (ρ : ℝ)
    (z : (ι → ℂ) × ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ * ∮ s in C(0, ρ), g (z.1, s) / (s ^ d * (s - z.2))

/-- The Cauchy quotient is jointly holomorphic on a strictly smaller product polydisc. -/
theorem analyticOnNhd_weierstrassCauchyQuotient
    {V : Set (ι → ℂ)} (hV : IsOpen V) {R ρ₀ ρ : ℝ} {g : (ι → ℂ) × ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (V ×ˢ ball 0 R))
    (hρ₀ : 0 < ρ₀) (hρ₀ρ : ρ₀ < ρ) (hρR : ρ < R) (d : ℕ) :
    AnalyticOnNhd ℂ (weierstrassCauchyQuotient d g ρ) (V ×ˢ ball 0 ρ₀) := by
  let W : Set (((ι → ℂ) × ℂ) × ℂ) :=
    {p | p.1.1 ∈ V ∧ p.2 ∈ ball (0 : ℂ) R ∧ p.2 ≠ 0 ∧ p.2 ≠ p.1.2}
  let H : ((ι → ℂ) × ℂ) × ℂ → ℂ := fun p =>
    g (p.1.1, p.2) / (p.2 ^ d * (p.2 - p.1.2))
  have hH : AnalyticOnNhd ℂ H W := by
    intro p hp
    have hnum : AnalyticAt ℂ (fun q : ((ι → ℂ) × ℂ) × ℂ => g (q.1.1, q.2)) p :=
      (hg (p.1.1, p.2) ⟨hp.1, hp.2.1⟩).comp_of_eq
        ((analyticAt_fst (𝕜 := ℂ)).comp (analyticAt_fst (𝕜 := ℂ)) |>.prod
          (analyticAt_snd (𝕜 := ℂ))) rfl
    have hden : AnalyticAt ℂ
        (fun q : ((ι → ℂ) × ℂ) × ℂ => q.2 ^ d * (q.2 - q.1.2)) p :=
      (analyticAt_snd.pow d).mul
        (analyticAt_snd.sub ((analyticAt_snd (𝕜 := ℂ)).comp (analyticAt_fst (𝕜 := ℂ))))
    exact hnum.div hden (mul_ne_zero (pow_ne_zero d hp.2.2.1)
      (sub_ne_zero.mpr hp.2.2.2))
  have hfθ : ContinuousOn (fun _ : ℂ => (1 : ℂ)) (sphere 0 ρ) := continuousOn_const
  have hmem : ∀ x ∈ V ×ˢ ball (0 : ℂ) ρ₀, ∀ s ∈ sphere (0 : ℂ) ρ, (x, s) ∈ W := by
    intro x hx s hs
    have hsρ : ‖s‖ = ρ := by
      rw [← dist_zero_right]
      exact mem_sphere.mp hs
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hsρ
      linarith
    have hsw : s ≠ x.2 := by
      intro h
      have hxρ : ‖x.2‖ < ρ₀ := by simpa [dist_eq_norm] using hx.2
      rw [h] at hsρ
      linarith
    exact ⟨hx.1, (sphere_subset_closedBall.trans (closedBall_subset_ball hρR)) hs, hs0, hsw⟩
  have hI := (analyticOnNhd_circleIntegral_kernel_mul (E := (ι → ℂ) × ℂ)
    (hV.prod isOpen_ball) hH (le_of_lt (hρ₀.trans hρ₀ρ)) hfθ hmem).const_smul
    (c := (2 * Real.pi * I : ℂ)⁻¹)
  refine hI.congr (hV.prod isOpen_ball) fun z hz => ?_
  simp [weierstrassCauchyQuotient, smul_eq_mul, H]

/-- A bound of the form `M / ρ ^ n`, valid for every positive `ρ < R`, persists at `R`
itself by continuity of the bound in `ρ`. -/
theorem le_div_pow_of_forall_lt {M : ℝ} {R : ℝ} (hR : 0 < R) (n : ℕ) {x : ℝ}
    (h : ∀ ρ, 0 < ρ → ρ < R → x ≤ M / ρ ^ n) : x ≤ M / R ^ n := by
  have hcont : ContinuousAt (fun ρ : ℝ => M / ρ ^ n) R :=
    continuousAt_const.div (continuousAt_id.pow n) (pow_ne_zero n hR.ne')
  have htendsto : Tendsto (fun ρ : ℝ => M / ρ ^ n) (nhdsWithin R (Iio R)) (nhds (M / R ^ n)) :=
    hcont.continuousWithinAt
  refine ge_of_tendsto htendsto ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hR).filter_mono nhdsWithin_le_nhds] with ρ hρR hρ0
  exact h ρ hρ0 hρR

/-- Cauchy's estimate for the Taylor coefficients of a last-coordinate slice, uniform up
to the boundary radius `R` even though the function is only assumed holomorphic on the
open polydisc. -/
theorem norm_iteratedDeriv_snd_slice_le {V : Set (ι → ℂ)} {R : ℝ} {g : (ι → ℂ) × ℂ → ℂ}
    {M : ℝ} (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) (hR : 0 < R) {z : ι → ℂ} (hz : z ∈ V)
    (hM : ∀ w ∈ ball (0 : ℂ) R, ‖g (z, w)‖ ≤ M) (n : ℕ) :
    ‖iteratedDeriv n (fun w => g (z, w)) 0‖ ≤ (n.factorial : ℝ) * M / R ^ n := by
  apply le_div_pow_of_forall_lt hR
  intro ρ hρ hρR
  rw [iteratedDeriv_snd_slice_circleIntegral hg hz hρ hρR n, mul_assoc, norm_mul]
  have hkernel : ‖(2 * Real.pi * I : ℂ)⁻¹ * ∮ s in C(0, ρ), s ^ (-(n + 1 : ℤ)) * g (z, s)‖
      ≤ M / ρ ^ n := by
    rw [← smul_eq_mul ((2 * Real.pi * I : ℂ)⁻¹)]
    have hb := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (f := fun s => s ^ (-(n + 1 : ℤ)) * g (z, s)) (c := (0 : ℂ)) (R := ρ)
      (C := M / ρ ^ (n + 1)) hρ.le
      (fun s hs => by
        have hsρ : ‖s‖ = ρ := by rw [← dist_zero_right]; exact mem_sphere.mp hs
        have hs0 : s ≠ 0 := by intro h; rw [h, norm_zero] at hsρ; exact hρ.ne' hsρ.symm
        have hzpow : ‖s ^ (-(n + 1 : ℤ))‖ = (ρ ^ (n + 1))⁻¹ := by
          have he : (-(n + 1 : ℤ)) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
          rw [norm_zpow, hsρ, he, zpow_neg, zpow_natCast]
        rw [norm_mul, hzpow, div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left (hM s ((mem_ball.mpr (by simpa [hsρ] using hρR))))
          (by positivity))
    calc ‖(2 * Real.pi * I : ℂ)⁻¹ * ∮ s in C(0, ρ), s ^ (-(n + 1 : ℤ)) * g (z, s)‖
        ≤ ρ * (M / ρ ^ (n + 1)) := hb
      _ = M / ρ ^ n := by field_simp; ring
  simp only [Complex.norm_natCast]
  calc (n.factorial : ℝ) * ‖(2 * Real.pi * I : ℂ)⁻¹ * ∮ s in C(0, ρ), s ^ (-(n + 1 : ℤ)) * g (z, s)‖
      ≤ (n.factorial : ℝ) * (M / ρ ^ n) := mul_le_mul_of_nonneg_left hkernel (by positivity)
    _ = (n.factorial : ℝ) * M / ρ ^ n := by ring

/-- The Cauchy coefficient of a last-coordinate slice equals a division-kernel circle
integral, matching the shape used by the coordinate-power kernel identity. -/
theorem cauchyCoeff_eq_of_lt {V : Set (ι → ℂ)} {R ρ : ℝ} {g : (ι → ℂ) × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) {w : ι → ℂ} (hw : w ∈ V)
    (hρ : 0 < ρ) (hρR : ρ < R) (j : ℕ) :
    (2 * Real.pi * I : ℂ)⁻¹ * ∮ s in C(0, ρ), g (w, s) / s ^ (j + 1) =
      ((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv j (fun s => g (w, s)) 0 := by
  rw [iteratedDeriv_snd_slice_circleIntegral hg hw hρ hρR j]
  have hEq : EqOn (fun s : ℂ => g (w, s) / s ^ (j + 1))
      (fun s => s ^ (-(j + 1 : ℤ)) * g (w, s)) (sphere (0 : ℂ) ρ) := by
    intro s _
    show g (w, s) / s ^ (j + 1) = s ^ (-(j + 1 : ℤ)) * g (w, s)
    rw [div_eq_inv_mul, show (-(j + 1 : ℤ)) = -((j + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast]
  rw [circleIntegral.integral_congr hρ.le hEq,
    mul_assoc ((j : ℕ).factorial : ℂ) ((2 * Real.pi * I : ℂ)⁻¹),
    inv_mul_cancel_left₀ (by exact_mod_cast j.factorial_ne_zero :
      ((j : ℕ).factorial : ℂ) ≠ 0)]

/-- The Cauchy quotient at a fixed admissible radius solves the coordinate-power
division identity there, with remainder coefficients given by Taylor coefficients
of the last-coordinate slice. -/
theorem coordinatePower_eq_of_lt {V : Set (ι → ℂ)} {R ρ : ℝ} {g : (ι → ℂ) × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) (hρ : 0 < ρ) (hρR : ρ < R) (d : ℕ)
    {w : ι → ℂ} (hw : w ∈ V) {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) ρ) :
    g (w, ζ) = weierstrassRemainder
        (fun j : Fin d => fun v : ι → ℂ => ((j : ℕ).factorial : ℂ)⁻¹ *
          iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0) (w, ζ) +
      ζ ^ d * weierstrassCauchyQuotient d g ρ (w, ζ) := by
  have hζρ : ‖ζ‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hζ
  have hslice : DiffContOnCl ℂ (fun s => g (w, s)) (ball 0 ρ) :=
    diffContOnCl_snd_slice hg hw hρ hρR
  have hcauchy : g (w, ζ) = (2 * Real.pi * I : ℂ)⁻¹ * ∮ s in C(0, ρ), (s - ζ)⁻¹ * g (w, s) := by
    simpa using hslice.iteratedDeriv_eq_circleIntegral_sub_zpow_mul hρ 0 hζ
  have hcontslice : ContinuousOn (fun s => g (w, s)) (sphere (0 : ℂ) ρ) :=
    hg.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun s hs => ⟨hw, (sphere_subset_closedBall.trans (closedBall_subset_ball hρR)) hs⟩)
  have hne0 : ∀ s ∈ sphere (0 : ℂ) ρ, s ≠ 0 := by
    intro s hs hcontra
    have hsρ : ‖s‖ = ρ := by rw [← dist_zero_right]; exact mem_sphere.mp hs
    rw [hcontra, norm_zero] at hsρ; exact hρ.ne' hsρ.symm
  have hnesw : ∀ s ∈ sphere (0 : ℂ) ρ, s ≠ ζ := by
    intro s hs hcontra
    have hsρ : ‖s‖ = ρ := by rw [← dist_zero_right]; exact mem_sphere.mp hs
    rw [hcontra] at hsρ; linarith
  have hEqOn : EqOn (fun s => (s - ζ)⁻¹ * g (w, s))
      (fun s => (∑ j ∈ range d, ζ ^ j / s ^ (j + 1)) * g (w, s) +
        ζ ^ d / (s ^ d * (s - ζ)) * g (w, s)) (sphere (0 : ℂ) ρ) := by
    intro s hs
    show (s - ζ)⁻¹ * g (w, s) =
      (∑ j ∈ range d, ζ ^ j / s ^ (j + 1)) * g (w, s) + ζ ^ d / (s ^ d * (s - ζ)) * g (w, s)
    rw [← add_mul, weierstrass_kernel_identity d (hne0 s hs) (hnesw s hs)]
  rw [circleIntegral.integral_congr hρ.le hEqOn] at hcauchy
  have hcont1 : ContinuousOn (fun s => (∑ j ∈ range d, ζ ^ j / s ^ (j + 1)) * g (w, s))
      (sphere (0 : ℂ) ρ) := by
    apply ContinuousOn.mul _ hcontslice
    apply continuousOn_finsetSum
    intro j _
    exact ContinuousOn.div continuousOn_const (continuousOn_pow _)
      (fun s hs => pow_ne_zero _ (hne0 s hs))
  have hcont2 : ContinuousOn (fun s => ζ ^ d / (s ^ d * (s - ζ)) * g (w, s)) (sphere (0 : ℂ) ρ) := by
    apply ContinuousOn.mul _ hcontslice
    exact ContinuousOn.div continuousOn_const
      ((continuousOn_pow _).mul (continuousOn_id.sub continuousOn_const))
      (fun s hs => mul_ne_zero (pow_ne_zero _ (hne0 s hs)) (sub_ne_zero.mpr (hnesw s hs)))
  have hcirc1 : CircleIntegrable (fun s => (∑ j ∈ range d, ζ ^ j / s ^ (j + 1)) * g (w, s)) 0 ρ :=
    ContinuousOn.circleIntegrable' (by rwa [abs_of_pos hρ])
  have hcirc2 : CircleIntegrable (fun s => ζ ^ d / (s ^ d * (s - ζ)) * g (w, s)) 0 ρ :=
    ContinuousOn.circleIntegrable' (by rwa [abs_of_pos hρ])
  rw [circleIntegral.integral_add hcirc1 hcirc2] at hcauchy
  have hsum : (∮ s in C(0, ρ), (∑ j ∈ range d, ζ ^ j / s ^ (j + 1)) * g (w, s)) =
      ∑ j ∈ range d, ζ ^ j * ∮ s in C(0, ρ), g (w, s) / s ^ (j + 1) := by
    have hcongr : (∮ s in C(0, ρ), (∑ j ∈ range d, ζ ^ j / s ^ (j + 1)) * g (w, s)) =
        ∮ s in C(0, ρ), ∑ j ∈ range d, ζ ^ j * (g (w, s) / s ^ (j + 1)) := by
      apply circleIntegral.integral_congr hρ.le
      intro s _
      show (∑ j ∈ range d, ζ ^ j / s ^ (j + 1)) * g (w, s) =
        ∑ j ∈ range d, ζ ^ j * (g (w, s) / s ^ (j + 1))
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hcongr, circleIntegral.integral_fun_sum (fun j _ => by
      apply ContinuousOn.circleIntegrable' (R := ρ)
      rw [show |ρ| = ρ from abs_of_pos hρ]
      exact ContinuousOn.mul continuousOn_const
        (ContinuousOn.div hcontslice (continuousOn_pow _) (fun s hs => pow_ne_zero _ (hne0 s hs))))]
    exact Finset.sum_congr rfl fun j _ => circleIntegral.integral_const_mul _ _ _ _
  have hquot : (∮ s in C(0, ρ), ζ ^ d / (s ^ d * (s - ζ)) * g (w, s)) =
      ζ ^ d * ∮ s in C(0, ρ), g (w, s) / (s ^ d * (s - ζ)) := by
    rw [← circleIntegral.integral_const_mul]
    exact circleIntegral.integral_congr hρ.le fun s _ => by ring
  rw [hsum, hquot, mul_add] at hcauchy
  have hstep1 : (2 * Real.pi * I : ℂ)⁻¹ *
        ∑ j ∈ range d, ζ ^ j * ∮ s in C(0, ρ), g (w, s) / s ^ (j + 1) =
      ∑ j ∈ range d, (((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv j (fun s => g (w, s)) 0) * ζ ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [mul_left_comm, cauchyCoeff_eq_of_lt hg hw hρ hρR j, mul_comm]
  rw [hstep1] at hcauchy
  rw [hcauchy, weierstrassCauchyQuotient, weierstrassRemainder,
    Fin.sum_univ_eq_sum_range (fun j => ((j : ℕ).factorial : ℂ)⁻¹ *
      iteratedDeriv j (fun s => g (w, s)) 0 * ζ ^ j)]
  ring

/-- The Cauchy quotient at two admissible radii agrees at every nonzero point where
both are defined. -/
theorem weierstrassCauchyQuotient_eq_of_ne {V : Set (ι → ℂ)} {R ρ₁ ρ₂ : ℝ}
    {g : (ι → ℂ) × ℂ → ℂ} (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R))
    (hρ₁ : 0 < ρ₁) (hρ₁R : ρ₁ < R) (hρ₂ : 0 < ρ₂) (hρ₂R : ρ₂ < R) (d : ℕ)
    {w : ι → ℂ} (hw : w ∈ V) {ζ : ℂ} (hζ0 : ζ ≠ 0)
    (hζ₁ : ζ ∈ ball (0 : ℂ) ρ₁) (hζ₂ : ζ ∈ ball (0 : ℂ) ρ₂) :
    weierstrassCauchyQuotient d g ρ₁ (w, ζ) = weierstrassCauchyQuotient d g ρ₂ (w, ζ) := by
  have h1 := coordinatePower_eq_of_lt hg hρ₁ hρ₁R d hw hζ₁
  have h2 := coordinatePower_eq_of_lt hg hρ₂ hρ₂R d hw hζ₂
  have heq : ζ ^ d * weierstrassCauchyQuotient d g ρ₁ (w, ζ) =
      ζ ^ d * weierstrassCauchyQuotient d g ρ₂ (w, ζ) := by
    rw [← add_right_inj (weierstrassRemainder
      (fun j v => ((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0)
      (w, ζ)), ← h1, ← h2]
  exact mul_left_cancel₀ (pow_ne_zero d hζ0) heq

/-- The Cauchy quotient at two admissible radii agrees wherever both are defined. -/
theorem weierstrassCauchyQuotient_eq_of_lt {V : Set (ι → ℂ)} (hV : IsOpen V) {R ρ₁ ρ₂ : ℝ}
    {g : (ι → ℂ) × ℂ → ℂ} (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R))
    (hρ₁ : 0 < ρ₁) (hρ₁R : ρ₁ < R) (hρ₂ : 0 < ρ₂) (hρ₂R : ρ₂ < R) (d : ℕ)
    {w : ι → ℂ} (hw : w ∈ V) {ζ : ℂ} (hζ₁ : ζ ∈ ball (0 : ℂ) ρ₁) (hζ₂ : ζ ∈ ball (0 : ℂ) ρ₂) :
    weierstrassCauchyQuotient d g ρ₁ (w, ζ) = weierstrassCauchyQuotient d g ρ₂ (w, ζ) := by
  rcases eq_or_ne ζ 0 with hζ0 | hζ0
  · subst hζ0
    set ρ₀ := min ρ₁ ρ₂ / 2 with hρ₀def
    have hρ₀pos : 0 < ρ₀ := by positivity
    have hρ₀ρ₁ : ρ₀ < ρ₁ :=
      calc ρ₀ ≤ ρ₁ / 2 := by rw [hρ₀def]; gcongr; exact min_le_left ρ₁ ρ₂
        _ < ρ₁ := by linarith
    have hρ₀ρ₂ : ρ₀ < ρ₂ :=
      calc ρ₀ ≤ ρ₂ / 2 := by rw [hρ₀def]; gcongr; exact min_le_right ρ₁ ρ₂
        _ < ρ₂ := by linarith
    have hgA : AnalyticOnNhd ℂ g (V ×ˢ ball 0 R) := hg.analyticOnNhd_finiteDimensional
      (hV.prod isOpen_ball)
    have hA1 : AnalyticOnNhd ℂ (fun ζ' => weierstrassCauchyQuotient d g ρ₁ (w, ζ')) (ball 0 ρ₀) :=
      fun ζ' hζ' => ((analyticOnNhd_weierstrassCauchyQuotient hV hgA hρ₀pos hρ₀ρ₁ hρ₁R d)
        (w, ζ') ⟨hw, hζ'⟩).comp_of_eq
        ((analyticAt_const (v := w)).prod analyticAt_id) rfl
    have hA2 : AnalyticOnNhd ℂ (fun ζ' => weierstrassCauchyQuotient d g ρ₂ (w, ζ')) (ball 0 ρ₀) :=
      fun ζ' hζ' => ((analyticOnNhd_weierstrassCauchyQuotient hV hgA hρ₀pos hρ₀ρ₂ hρ₂R d)
        (w, ζ') ⟨hw, hζ'⟩).comp_of_eq
        ((analyticAt_const (v := w)).prod analyticAt_id) rfl
    have heqn : (fun ζ' => weierstrassCauchyQuotient d g ρ₁ (w, ζ')) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun ζ' => weierstrassCauchyQuotient d g ρ₂ (w, ζ')) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hρ₀pos))]
        with ζ' hζ'0 hζ'0'
      exact weierstrassCauchyQuotient_eq_of_ne hg hρ₁ hρ₁R hρ₂ hρ₂R d hw hζ'0
        (ball_subset_ball hρ₀ρ₁.le hζ'0') (ball_subset_ball hρ₀ρ₂.le hζ'0')
    have hlim1 : Tendsto (fun ζ' => weierstrassCauchyQuotient d g ρ₁ (w, ζ')) (𝓝[≠] (0 : ℂ))
        (𝓝 (weierstrassCauchyQuotient d g ρ₁ (w, 0))) :=
      (hA1 0 (mem_ball_self hρ₀pos)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto (fun ζ' => weierstrassCauchyQuotient d g ρ₂ (w, ζ')) (𝓝[≠] (0 : ℂ))
        (𝓝 (weierstrassCauchyQuotient d g ρ₂ (w, 0))) :=
      (hA2 0 (mem_ball_self hρ₀pos)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (hlim1.congr' heqn) hlim2
  · exact weierstrassCauchyQuotient_eq_of_ne hg hρ₁ hρ₁R hρ₂ hρ₂R d hw hζ0 hζ₁ hζ₂

/-- The **sharp coordinate-power quotient bound**: the Cauchy quotient at radius `ρ` is
bounded by `(d+1) M / ρ ^ d` throughout the disc, using a bound `M` on the numerator over
the whole domain. The proof compares the numerator to its degree-`< d` Taylor polynomial,
bounded by `(d+1) M` via Cauchy's estimate, then applies the maximum modulus principle to
the quotient itself and lets the comparison radius approach `ρ`. -/
theorem norm_sub_weierstrassRemainder_iteratedDeriv_le {V : Set (ι → ℂ)} {R ρ M : ℝ}
    {g : (ι → ℂ) × ℂ → ℂ} (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) (hρR : ρ < R) (d : ℕ)
    (hM : ∀ z ∈ V ×ˢ ball (0 : ℂ) R, ‖g z‖ ≤ M) {w : ι → ℂ} (hw : w ∈ V) {ζ' : ℂ}
    (hζ' : ζ' ∈ ball (0 : ℂ) ρ) :
    ‖g (w, ζ') - weierstrassRemainder (d := d) (fun j v => ((j : ℕ).factorial : ℂ)⁻¹ *
      iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0) (w, ζ')‖ ≤ ((d + 1 : ℕ) : ℝ) * M := by
  have hζ'ρ : ‖ζ'‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hζ'
  have hζ'R : ‖ζ'‖ < R := hζ'ρ.trans hρR
  have hR0 : 0 < R := (norm_nonneg ζ').trans_lt hζ'R
  have hgb : ‖g (w, ζ')‖ ≤ M := hM (w, ζ') ⟨hw, mem_ball_zero_iff.mpr hζ'R⟩
  have hMnn : 0 ≤ M := (norm_nonneg _).trans hgb
  have haj : ∀ j : Fin d, ‖(((j : ℕ).factorial : ℂ)⁻¹ *
      iteratedDeriv (j : ℕ) (fun s => g (w, s)) 0)‖ ≤ M / R ^ (j : ℕ) := by
    intro j
    have hb := norm_iteratedDeriv_snd_slice_le hg hR0 hw (fun s hs => hM (w, s) ⟨hw, hs⟩)
      (j : ℕ)
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc ((j : ℕ).factorial : ℝ)⁻¹ * ‖iteratedDeriv (j : ℕ) (fun s => g (w, s)) 0‖
        ≤ ((j : ℕ).factorial : ℝ)⁻¹ * (((j : ℕ).factorial : ℝ) * M / R ^ (j : ℕ)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = M / R ^ (j : ℕ) := by field_simp
  have hrem : ‖weierstrassRemainder (d := d) (fun j v => ((j : ℕ).factorial : ℂ)⁻¹ *
      iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0) (w, ζ')‖ ≤ (d : ℝ) * M := by
    unfold weierstrassRemainder
    calc ‖∑ j : Fin d, (((j : ℕ).factorial : ℂ)⁻¹ *
            iteratedDeriv (j : ℕ) (fun s => g (w, s)) 0) * ζ' ^ (j : ℕ)‖
        ≤ ∑ j : Fin d, ‖(((j : ℕ).factorial : ℂ)⁻¹ *
            iteratedDeriv (j : ℕ) (fun s => g (w, s)) 0) * ζ' ^ (j : ℕ)‖ := norm_sum_le _ _
      _ = ∑ j : Fin d, ‖(((j : ℕ).factorial : ℂ)⁻¹ *
            iteratedDeriv (j : ℕ) (fun s => g (w, s)) 0)‖ * ‖ζ'‖ ^ (j : ℕ) := by
            simp [norm_pow]
      _ ≤ ∑ _j : Fin d, (M / R ^ (0 : ℕ)) * R ^ (0 : ℕ) := by
            apply Finset.sum_le_sum
            intro j _
            calc ‖(((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv (j : ℕ)
                  (fun s => g (w, s)) 0)‖ * ‖ζ'‖ ^ (j : ℕ)
                ≤ (M / R ^ (j : ℕ)) * R ^ (j : ℕ) :=
                  mul_le_mul (haj j) (pow_le_pow_left₀ (norm_nonneg _)
                    (hζ'ρ.trans hρR).le _) (by positivity) (by positivity)
              _ = M := by field_simp
              _ = (M / R ^ (0 : ℕ)) * R ^ (0 : ℕ) := by simp
      _ = (d : ℝ) * M := by simp [Finset.sum_const, Finset.card_univ, mul_comm]
  calc ‖g (w, ζ') - weierstrassRemainder (fun j v => ((j : ℕ).factorial : ℂ)⁻¹ *
        iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0) (w, ζ')‖
      ≤ ‖g (w, ζ')‖ + ‖weierstrassRemainder (fun j v => ((j : ℕ).factorial : ℂ)⁻¹ *
        iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0) (w, ζ')‖ := norm_sub_le _ _
    _ ≤ M + (d : ℝ) * M := add_le_add hgb hrem
    _ = ((d + 1 : ℕ) : ℝ) * M := by push_cast; ring

/-- The **sharp coordinate-power quotient bound**: the Cauchy quotient at radius `ρ` is
bounded by `(d+1) M / ρ ^ d` throughout the disc, using a bound `M` on the numerator over
the whole domain. The proof compares the numerator to its degree-`< d` Taylor polynomial,
bounded by `(d+1) M` via `norm_sub_weierstrassRemainder_iteratedDeriv_le`, then applies the
maximum modulus principle to the quotient itself and lets the comparison radius approach `ρ`. -/
theorem norm_weierstrassCauchyQuotient_le {V : Set (ι → ℂ)} (hV : IsOpen V) {R ρ M : ℝ}
    {g : (ι → ℂ) × ℂ → ℂ} (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R))
    (hρ : 0 < ρ) (hρR : ρ < R) (d : ℕ)
    (hM : ∀ z ∈ V ×ˢ ball (0 : ℂ) R, ‖g z‖ ≤ M) {w : ι → ℂ} (hw : w ∈ V) {ζ0 : ℂ}
    (hζ0 : ζ0 ∈ ball (0 : ℂ) ρ) :
    ‖weierstrassCauchyQuotient d g ρ (w, ζ0)‖ ≤ ((d + 1 : ℕ) : ℝ) * M / ρ ^ d := by
  have hR0 : 0 < R := hρ.trans hρR
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM (w, 0) ⟨hw, mem_ball_self hR0⟩)
  have hgA : AnalyticOnNhd ℂ g (V ×ˢ ball 0 R) := hg.analyticOnNhd_finiteDimensional
    (hV.prod isOpen_ball)
  have hψ : ∀ ζ' : ℂ, ζ' ∈ ball (0 : ℂ) ρ →
      ‖g (w, ζ') - weierstrassRemainder (d := d) (fun j v => ((j : ℕ).factorial : ℂ)⁻¹ *
        iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0) (w, ζ')‖ ≤ ((d + 1 : ℕ) : ℝ) * M :=
    fun ζ' hζ' => norm_sub_weierstrassRemainder_iteratedDeriv_le hg hρR d hM hw hζ'
  have hqbound : ∀ ρ', ‖ζ0‖ < ρ' → ρ' < ρ →
      ‖weierstrassCauchyQuotient d g ρ (w, ζ0)‖ ≤ ((d + 1 : ℕ) : ℝ) * M / ρ' ^ d := by
    intro ρ' hζ0ρ' hρ'ρ
    have hρ'pos : 0 < ρ' := (norm_nonneg _).trans_lt hζ0ρ'
    have hbdry : ∀ ζ' ∈ sphere (0 : ℂ) ρ',
        ‖weierstrassCauchyQuotient d g ρ (w, ζ')‖ ≤ ((d + 1 : ℕ) : ℝ) * M / ρ' ^ d := by
      intro ζ' hζ'
      have hζ'ρ' : ‖ζ'‖ = ρ' := by rw [← dist_zero_right]; exact mem_sphere.mp hζ'
      have hζ'0 : ζ' ≠ 0 := by intro h; rw [h, norm_zero] at hζ'ρ'; exact hρ'pos.ne' hζ'ρ'.symm
      have hζ'ball : ζ' ∈ ball (0 : ℂ) ρ := by
        rw [mem_ball_zero_iff, hζ'ρ']; exact hρ'ρ
      have heq := coordinatePower_eq_of_lt hg hρ hρR d hw hζ'ball
      have hpsi := hψ ζ' hζ'ball
      have hval : ζ' ^ d * weierstrassCauchyQuotient d g ρ (w, ζ') =
          g (w, ζ') - weierstrassRemainder (d := d) (fun j v => ((j : ℕ).factorial : ℂ)⁻¹ *
            iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0) (w, ζ') := by
        rw [heq]; ring
      have hnorm : ‖ζ'‖ ^ d * ‖weierstrassCauchyQuotient d g ρ (w, ζ')‖ ≤
          ((d + 1 : ℕ) : ℝ) * M := by
        rw [← norm_pow, ← norm_mul, hval]; exact hpsi
      rw [hζ'ρ'] at hnorm
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < ρ' ^ d), mul_comm]
      exact hnorm
    obtain ⟨ρ'', hρ'ρ'', hρ''ρ⟩ := exists_between hρ'ρ
    have hAslice : AnalyticOnNhd ℂ (fun ζ' => weierstrassCauchyQuotient d g ρ (w, ζ'))
        (ball (0 : ℂ) ρ'') := fun ζ' hζ' =>
      ((analyticOnNhd_weierstrassCauchyQuotient hV hgA (hρ'pos.trans hρ'ρ'') hρ''ρ hρR d)
        (w, ζ') ⟨hw, hζ'⟩).comp_of_eq ((analyticAt_const (v := w)).prod analyticAt_id) rfl
    have hslice : DiffContOnCl ℂ (fun ζ' => weierstrassCauchyQuotient d g ρ (w, ζ'))
        (ball (0 : ℂ) ρ') :=
      ⟨(hAslice.mono (ball_subset_ball hρ'ρ''.le)).differentiableOn, by
        rw [closure_ball (0 : ℂ) hρ'pos.ne']
        exact hAslice.continuousOn.mono (closedBall_subset_ball hρ'ρ'')⟩
    exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hslice
      (fun ζ' hζ' => by rw [frontier_ball (0 : ℂ) hρ'pos.ne'] at hζ'; exact hbdry ζ' hζ')
      (subset_closure (mem_ball_zero_iff.mpr hζ0ρ'))
  have hζ0ρ : ‖ζ0‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hζ0
  have hcont : ContinuousAt (fun ρ' : ℝ => ((d + 1 : ℕ) : ℝ) * M / ρ' ^ d) ρ :=
    continuousAt_const.div (continuousAt_id.pow d) (pow_ne_zero d hρ.ne')
  have htendsto : Tendsto (fun ρ' : ℝ => ((d + 1 : ℕ) : ℝ) * M / ρ' ^ d)
      (nhdsWithin ρ (Iio ρ)) (nhds (((d + 1 : ℕ) : ℝ) * M / ρ ^ d)) :=
    hcont.continuousWithinAt
  refine ge_of_tendsto htendsto ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (eventually_gt_nhds hζ0ρ)] with ρ' hρ'ρ hρ'ζ0
  exact hqbound ρ' hρ'ζ0 hρ'ρ

/-- **Coordinate-power division (Jakóbczak–Jarnicki 1.7.4).** Every holomorphic function
on a polydisc has a unique quotient and polynomial remainder on division by `w^d`.
The quotient estimate applies whenever the numerator is bounded. Existence and the
quotient bound remain pending; uniqueness of any such decomposition is proved above.
Empty parameter index types and `d = 0` are included. -/
theorem coordinatePower_division (d : ℕ) {r : ι → ℝ} {R : ℝ}
    (hr : ∀ i, 0 < r i) (hR : 0 < R) {g : (ι → ℂ) × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (polydiscWithRadii 0 r ×ˢ ball 0 R)) :
    ∃ q : (ι → ℂ) × ℂ → ℂ, ∃ a : Fin d → (ι → ℂ) → ℂ,
      IsWeierstrassDivisionOn (fun z => z.2 ^ d) g q a (polydiscWithRadii 0 r) R ∧
      (∀ M : ℝ, 0 ≤ M →
        (∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖g z‖ ≤ M) →
        ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖q z‖ ≤ ((d + 1 : ℕ) : ℝ) / R ^ d * M) ∧
      (∀ q' a', IsWeierstrassDivisionOn (fun z => z.2 ^ d) g q' a'
          (polydiscWithRadii 0 r) R →
        EqOn q q' (polydiscWithRadii 0 r ×ˢ ball 0 R) ∧
        ∀ j, EqOn (a j) (a' j) (polydiscWithRadii 0 r)) := by
  set V := polydiscWithRadii (0 : ι → ℂ) r with hVdef
  have hVo : IsOpen V := isOpen_polydiscWithRadii _ _
  have hgA : AnalyticOnNhd ℂ g (V ×ˢ ball 0 R) := hg.analyticOnNhd_finiteDimensional
    (hVo.prod isOpen_ball)
  set a : Fin d → (ι → ℂ) → ℂ := fun j w =>
    ((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv (j : ℕ) (fun s => g (w, s)) 0 with hadef
  set q : (ι → ℂ) × ℂ → ℂ := fun z => weierstrassCauchyQuotient d g ((‖z.2‖ + R) / 2) z with hqdef
  have hρz : ∀ ζ : ℂ, ‖ζ‖ < R → 0 < (‖ζ‖ + R) / 2 ∧ ‖ζ‖ < (‖ζ‖ + R) / 2 ∧
      (‖ζ‖ + R) / 2 < R := fun ζ hζ => ⟨by linarith [norm_nonneg ζ], by linarith, by linarith⟩
  have hqanalytic : AnalyticOnNhd ℂ q (V ×ˢ ball 0 R) := by
    rintro z ⟨hz1, hz2⟩
    have hζR : ‖z.2‖ < R := by simpa [mem_ball, dist_eq_norm] using hz2
    obtain ⟨hρ0pos, hρ0ζ, hρ0R⟩ := hρz z.2 hζR
    obtain ⟨ρbig, hρ0ρbig, hρbigR⟩ := exists_between hρ0R
    have hkey : ‖z.2‖ < 2 * ρbig - R := by nlinarith
    obtain ⟨ρ0', hζρ0', hρ0'key⟩ := exists_between hkey
    have hρ0'ρbig : ρ0' < ρbig := by linarith
    have hAbig : AnalyticOnNhd ℂ (weierstrassCauchyQuotient d g ρbig) (V ×ˢ ball 0 ρ0') :=
      analyticOnNhd_weierstrassCauchyQuotient hVo hgA
        ((norm_nonneg z.2).trans_lt hζρ0') hρ0'ρbig hρbigR d
    have hzmem : z ∈ V ×ˢ ball (0 : ℂ) ρ0' := ⟨hz1, mem_ball_zero_iff.mpr hζρ0'⟩
    have heqOn : EqOn q (weierstrassCauchyQuotient d g ρbig) (V ×ˢ ball (0 : ℂ) ρ0') := by
      rintro y ⟨hy1, hy2⟩
      have hy2' : ‖y.2‖ < ρ0' := by simpa [mem_ball, dist_eq_norm] using hy2
      have hy2R : ‖y.2‖ < R := hy2'.trans (hρ0'ρbig.trans hρbigR)
      obtain ⟨hρypos, hρyζ, hρyR⟩ := hρz y.2 hy2R
      have hyρbig : ‖y.2‖ < ρbig := hy2'.trans hρ0'ρbig
      have hρylt : (‖y.2‖ + R) / 2 < ρbig := by linarith
      show weierstrassCauchyQuotient d g ((‖y.2‖ + R) / 2) y =
        weierstrassCauchyQuotient d g ρbig y
      exact weierstrassCauchyQuotient_eq_of_lt hVo hg hρypos hρyR
        ((norm_nonneg y.2).trans_lt hyρbig) hρbigR d hy1
        (mem_ball_zero_iff.mpr hρyζ) (mem_ball_zero_iff.mpr hyρbig)
    have heq : q =ᶠ[𝓝 z] weierstrassCauchyQuotient d g ρbig := by
      filter_upwards [(hVo.prod isOpen_ball).mem_nhds hzmem] with y hy using heqOn hy
    exact (hAbig z hzmem).congr heq.symm
  have haholo : ∀ j, DifferentiableOn ℂ (a j) V := fun j =>
    (differentiableOn_iteratedDeriv_snd_slice hVo hg hR (j : ℕ)).const_mul _
  have hqholo : DifferentiableOn ℂ q (V ×ˢ ball 0 R) :=
    hqanalytic.differentiableOn
  have heqOnV : EqOn g (fun z => q z * (fun z => z.2 ^ d) z + weierstrassRemainder a z)
      (V ×ˢ ball 0 R) := by
    rintro z ⟨hz1, hz2⟩
    have hζR : ‖z.2‖ < R := by simpa [mem_ball, dist_eq_norm] using hz2
    obtain ⟨hρ0pos, hρ0ζ, hρ0R⟩ := hρz z.2 hζR
    have := coordinatePower_eq_of_lt hg hρ0pos hρ0R d hz1 (mem_ball_zero_iff.mpr hρ0ζ)
    show g z = q z * z.2 ^ d + weierstrassRemainder a z
    rw [this]; ring
  refine ⟨q, a, ⟨hqholo, haholo, heqOnV⟩, ?_, ?_⟩
  · intro M hM0 hMb z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hζR : ‖z.2‖ < R := by simpa [mem_ball, dist_eq_norm] using hz2
    obtain ⟨hρ0pos, hρ0ζ, hρ0R⟩ := hρz z.2 hζR
    have hbnd : ∀ ρ', ‖z.2‖ < ρ' → ρ' < R → ‖q z‖ ≤ ((d + 1 : ℕ) : ℝ) * M / ρ' ^ d := by
      intro ρ' hζρ' hρ'R
      have hle := norm_weierstrassCauchyQuotient_le hVo hg ((norm_nonneg z.2).trans_lt hζρ')
        hρ'R d hMb hz1 (mem_ball_zero_iff.mpr hζρ')
      rwa [show q z = weierstrassCauchyQuotient d g ρ' z from
        weierstrassCauchyQuotient_eq_of_lt hVo hg hρ0pos hρ0R
          ((norm_nonneg z.2).trans_lt hζρ') hρ'R d hz1 (mem_ball_zero_iff.mpr hρ0ζ)
          (mem_ball_zero_iff.mpr hζρ')]
    have hcont : ContinuousAt (fun ρ' : ℝ => ((d + 1 : ℕ) : ℝ) * M / ρ' ^ d) R :=
      continuousAt_const.div (continuousAt_id.pow d) (pow_ne_zero d hR.ne')
    have htendsto : Tendsto (fun ρ' : ℝ => ((d + 1 : ℕ) : ℝ) * M / ρ' ^ d)
        (nhdsWithin R (Iio R)) (nhds (((d + 1 : ℕ) : ℝ) * M / R ^ d)) :=
      hcont.continuousWithinAt
    have hfinal : ‖q z‖ ≤ ((d + 1 : ℕ) : ℝ) * M / R ^ d := by
      refine ge_of_tendsto htendsto ?_
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (eventually_gt_nhds hζR)] with ρ' hρ'R hζρ'
      exact hbnd ρ' hζρ' hρ'R
    rw [show ((d + 1 : ℕ) : ℝ) / R ^ d * M = ((d + 1 : ℕ) : ℝ) * M / R ^ d from by ring]
    exact hfinal
  · intro q' a' h'
    exact unique_coordinatePower_division ⟨hqholo, haholo, heqOnV⟩ h' hR

/-- The Picard-iteration approximations to the coordinate-power quotient of `g` by a small
perturbation `h` of `z ^ d`: `s 0 = 0`, and `s (k+1)` is the coordinate-power quotient of
`g - h * s k`. Each approximation is holomorphic on the fixed polydisc. -/
noncomputable def picardApprox (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i) (hR : 0 < R)
    (h g : (ι → ℂ) × ℂ → ℂ) (hg : DifferentiableOn ℂ g (polydiscWithRadii 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydiscWithRadii 0 r ×ˢ ball 0 R)) :
    ℕ → {s : (ι → ℂ) × ℂ → ℂ // DifferentiableOn ℂ s (polydiscWithRadii 0 r ×ˢ ball 0 R)}
  | 0 => ⟨0, differentiableOn_const 0⟩
  | (k + 1) =>
    let prev := picardApprox d r R hr hR h g hg hh k
    ⟨(coordinatePower_division d hr hR (hg.sub (hh.mul prev.2))).choose,
      (coordinatePower_division d hr hR
        (hg.sub (hh.mul prev.2))).choose_spec.choose_spec.1.quotient_holomorphic⟩

/-- The remainder coefficients accompanying `picardApprox`'s quotient at each step. -/
noncomputable def picardApproxA (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i) (hR : 0 < R)
    (h g : (ι → ℂ) × ℂ → ℂ) (hg : DifferentiableOn ℂ g (polydiscWithRadii 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydiscWithRadii 0 r ×ˢ ball 0 R)) (k : ℕ) :
    Fin d → (ι → ℂ) → ℂ :=
  (coordinatePower_division d hr hR
    (hg.sub (hh.mul (picardApprox d r R hr hR h g hg hh k).2))).choose_spec.choose

/-- Each Picard step genuinely divides `g - h * (previous step)` by `z ^ d`. -/
theorem picardApprox_succ_isDiv (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i) (hR : 0 < R)
    (h g : (ι → ℂ) × ℂ → ℂ) (hg : DifferentiableOn ℂ g (polydiscWithRadii 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydiscWithRadii 0 r ×ˢ ball 0 R)) (k : ℕ) :
    IsWeierstrassDivisionOn (fun z => z.2 ^ d)
      (g - h * (picardApprox d r R hr hR h g hg hh k).1)
      (picardApprox d r R hr hR h g hg hh (k + 1)).1
      (picardApproxA d r R hr hR h g hg hh k) (polydiscWithRadii 0 r) R :=
  (coordinatePower_division d hr hR
    (hg.sub (hh.mul (picardApprox d r R hr hR h g hg hh k).2))).choose_spec.choose_spec.1

/-- The quotient bound of `coordinatePower_division`, specialized to a Picard step. -/
theorem picardApprox_succ_bound (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i) (hR : 0 < R)
    (h g : (ι → ℂ) × ℂ → ℂ) (hg : DifferentiableOn ℂ g (polydiscWithRadii 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydiscWithRadii 0 r ×ˢ ball 0 R)) (k : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (hb : ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R,
      ‖(g - h * (picardApprox d r R hr hR h g hg hh k).1) z‖ ≤ M) :
    ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R,
      ‖(picardApprox d r R hr hR h g hg hh (k + 1)).1 z‖ ≤ ((d + 1 : ℕ) : ℝ) / R ^ d * M :=
  (coordinatePower_division d hr hR
    (hg.sub (hh.mul (picardApprox d r R hr hR h g hg hh k).2))).choose_spec.choose_spec.2.1 M
    hM0 hb

/-- Uniqueness of `coordinatePower_division`, specialized to a Picard step: any other valid
decomposition of the same numerator agrees with the Picard step's output. -/
theorem picardApprox_succ_uniq (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i) (hR : 0 < R)
    (h g : (ι → ℂ) × ℂ → ℂ) (hg : DifferentiableOn ℂ g (polydiscWithRadii 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydiscWithRadii 0 r ×ˢ ball 0 R)) (k : ℕ)
    (q' : (ι → ℂ) × ℂ → ℂ) (a' : Fin d → (ι → ℂ) → ℂ)
    (hdiv' : IsWeierstrassDivisionOn (fun z => z.2 ^ d)
      (g - h * (picardApprox d r R hr hR h g hg hh k).1) q' a' (polydiscWithRadii 0 r) R) :
    EqOn (picardApprox d r R hr hR h g hg hh (k + 1)).1 q'
        (polydiscWithRadii 0 r ×ˢ ball 0 R) ∧
      ∀ j, EqOn (picardApproxA d r R hr hR h g hg hh k j) (a' j) (polydiscWithRadii 0 r) :=
  (coordinatePower_division d hr hR
    (hg.sub (hh.mul (picardApprox d r R hr hR h g hg hh k).2))).choose_spec.choose_spec.2.2 q' a'
    hdiv'

/-- The Weierstrass remainder is linear (here, additive) in its coefficient tuple. -/
theorem weierstrassRemainder_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {d : ℕ} (a b : Fin d → E → ℂ) (z : E × ℂ) :
    weierstrassRemainder a z - weierstrassRemainder b z =
      weierstrassRemainder (fun j => a j - b j) z := by
  unfold weierstrassRemainder
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp; ring

/-- Iterated derivatives converge along a locally uniform limit of holomorphic
one-variable functions, evaluated at any point of the domain. -/
theorem tendsto_iteratedDeriv_of_tendstoLocallyUniformlyOn {V : Set ℂ} (hV : IsOpen V) (j : ℕ) :
    ∀ (F : ℕ → ℂ → ℂ) (f' : ℂ → ℂ) (hF : TendstoLocallyUniformlyOn F f' atTop V)
      (_hFa : ∀ n, DifferentiableOn ℂ (F n) V) {x : ℂ} (_hx : x ∈ V),
      Tendsto (fun n => iteratedDeriv j (F n) x) atTop (𝓝 (iteratedDeriv j f' x)) := by
  induction j with
  | zero =>
    intro F f' hF _hFa x hx
    simpa [iteratedDeriv_zero] using hF.tendsto_at hx
  | succ j ih =>
    intro F f' hF hFa x hx
    have hderiv : TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f') atTop V :=
      hF.deriv (Filter.Eventually.of_forall hFa) hV
    have hderivDiff : ∀ n, DifferentiableOn ℂ (deriv (F n)) V := fun n =>
      (DifferentiableOn.analyticOnNhd_finiteDimensional (hFa n) hV).deriv.differentiableOn
    have := ih (deriv ∘ F) (deriv f') hderiv hderivDiff hx
    simpa [iteratedDeriv_succ', Function.comp_def] using this

/-- **Contraction estimate for the Picard iteration.** Consecutive Picard approximations
of the coordinate-power quotient by `g - h * s_k` differ by a geometrically shrinking
amount, given the numerator bound `M` for `g` and the small-perturbation bound on `h`. -/
theorem picardApprox_diff_bound (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i) (hR : 0 < R)
    (h g : (ι → ℂ) × ℂ → ℂ) (hg : DifferentiableOn ℂ g (polydiscWithRadii 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydiscWithRadii 0 r ×ˢ ball 0 R))
    (M : ℝ) (hM0 : 0 ≤ M) (hgb : ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖g z‖ ≤ M)
    (hhb : ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖h z‖ ≤ R ^ d / (2 * (d + 1))) :
    ∀ k, ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R,
      ‖(picardApprox d r R hr hR h g hg hh (k + 1)).1 z -
          (picardApprox d r R hr hR h g hg hh k).1 z‖ ≤
        ((d + 1 : ℕ) : ℝ) / R ^ d * M * (1 / 2) ^ k := by
  intro k
  induction k with
  | zero =>
    intro z hz
    have hb : ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R,
        ‖(g - h * (picardApprox d r R hr hR h g hg hh 0).1) z‖ ≤ M := by
      intro z hz
      show ‖g z - h z * (picardApprox d r R hr hR h g hg hh 0).1 z‖ ≤ M
      simpa [picardApprox] using hgb z hz
    have hbnd := picardApprox_succ_bound d r R hr hR h g hg hh 0 M hM0 hb z hz
    simpa [picardApprox] using hbnd
  | succ k ih =>
    intro z hz
    set sk := (picardApprox d r R hr hR h g hg hh k).1 with hskdef
    set sk1 := (picardApprox d r R hr hR h g hg hh (k + 1)).1 with hsk1def
    set sk2 := (picardApprox d r R hr hR h g hg hh (k + 2)).1 with hsk2def
    set ak := picardApproxA d r R hr hR h g hg hh k with hakdef
    set ak1 := picardApproxA d r R hr hR h g hg hh (k + 1) with hak1def
    have hdivk := picardApprox_succ_isDiv d r R hr hR h g hg hh k
    have hdivk1 := picardApprox_succ_isDiv d r R hr hR h g hg hh (k + 1)
    have hQA : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (h * (sk1 - sk))
        (sk1 - sk2) (fun j => ak j - ak1 j) (polydiscWithRadii 0 r) R := by
      refine ⟨(picardApprox d r R hr hR h g hg hh (k + 1)).2.sub
        (picardApprox d r R hr hR h g hg hh (k + 2)).2,
        fun j => (hdivk.coefficient_holomorphic j).sub (hdivk1.coefficient_holomorphic j), ?_⟩
      intro w hw
      have e1 := hdivk.eq hw
      have e2 := hdivk1.eq hw
      show h w * (sk1 w - sk w) = (sk1 w - sk2 w) * w.2 ^ d +
        weierstrassRemainder (fun j => ak j - ak1 j) w
      rw [← weierstrassRemainder_sub]
      have e1' : g w - h w * sk w = sk1 w * w.2 ^ d + weierstrassRemainder ak w := e1
      have e2' : g w - h w * sk1 w = sk2 w * w.2 ^ d + weierstrassRemainder ak1 w := e2
      have : h w * (sk1 w - sk w) = (sk1 w * w.2 ^ d + weierstrassRemainder ak w) -
          (sk2 w * w.2 ^ d + weierstrassRemainder ak1 w) := by
        rw [← e1', ← e2']; ring
      rw [this]; ring
    obtain ⟨q'', a'', hdiv'', hbound'', huniq''⟩ := coordinatePower_division d hr hR
      (hh.mul ((picardApprox d r R hr hR h g hg hh (k + 1)).2.sub
        (picardApprox d r R hr hR h g hg hh k).2))
    have hEq := (huniq'' (sk1 - sk2) (fun j => ak j - ak1 j) hQA).1
    have hbndM : ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R,
        ‖(h * (sk1 - sk)) z‖ ≤ (R ^ d / (2 * (d + 1))) *
          (((d + 1 : ℕ) : ℝ) / R ^ d * M * (1 / 2) ^ k) := by
      intro z hz
      show ‖h z * (sk1 z - sk z)‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul (hhb z hz) (ih z hz) (norm_nonneg _) (by positivity)
    have hq''bound := hbound'' _ (by positivity) hbndM z hz
    rw [hEq hz] at hq''bound
    have hQval : ‖(sk1 - sk2) z‖ = ‖sk2 z - sk1 z‖ := by
      rw [show (sk1 - sk2) z = sk1 z - sk2 z from rfl, ← norm_neg]
      congr 1; ring
    rw [hQval] at hq''bound
    calc ‖sk2 z - sk1 z‖ ≤ ((d + 1 : ℕ) : ℝ) / R ^ d *
        ((R ^ d / (2 * (d + 1))) * (((d + 1 : ℕ) : ℝ) / R ^ d * M * (1 / 2) ^ k)) := hq''bound
      _ = ((d + 1 : ℕ) : ℝ) / R ^ d * M * (1 / 2) ^ (k + 1) := by
          rw [pow_succ]
          have hRd : R ^ d ≠ 0 := by positivity
          have hd1 : ((d:ℝ) + 1) ≠ 0 := by positivity
          push_cast
          field_simp

/-- **Locally uniform limit of the Picard iteration.** Under the contraction estimate of
`picardApprox_diff_bound`, the Picard approximations converge uniformly on the domain to an
analytic limit, with the geometric tail bound summed over all later steps. -/
theorem exists_tendstoUniformlyOn_picardApprox (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i)
    (hR : 0 < R) (h g : (ι → ℂ) × ℂ → ℂ) (hg : DifferentiableOn ℂ g (polydiscWithRadii 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydiscWithRadii 0 r ×ˢ ball 0 R))
    (M : ℝ) (hM0 : 0 ≤ M) (hgb : ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖g z‖ ≤ M)
    (hhb : ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖h z‖ ≤ R ^ d / (2 * (d + 1))) :
    ∃ S : (ι → ℂ) × ℂ → ℂ,
      AnalyticOnNhd ℂ S (polydiscWithRadii 0 r ×ˢ ball 0 R) ∧
      ∀ n, ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R,
        ‖(picardApprox d r R hr hR h g hg hh n).1 z - S z‖ ≤
          ((d + 1 : ℕ) : ℝ) / R ^ d * M * (1 / 2) ^ n / (1 - 1 / 2) := by
  set sSeq := fun k => picardApprox d r R hr hR h g hg hh k with hsSeqdef
  set B : ℝ := ((d + 1 : ℕ) : ℝ) / R ^ d * M with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hdiff : ∀ k, ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R,
      ‖(sSeq (k + 1)).1 z - (sSeq k).1 z‖ ≤ B * (1 / 2) ^ k :=
    picardApprox_diff_bound d r R hr hR h g hg hh M hM0 hgb hhb
  have hpt : ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, CauchySeq (fun k => (sSeq k).1 z) := by
    intro z hz
    apply cauchySeq_of_le_geometric (r := 1 / 2) (C := B) (by norm_num)
    intro n
    rw [dist_eq_norm, norm_sub_rev]
    exact hdiff n z hz
  have hex : ∀ z : (ι → ℂ) × ℂ, ∃ y : ℂ,
      z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R → Tendsto (fun k => (sSeq k).1 z) atTop (𝓝 y) := by
    intro z
    by_cases hz : z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R
    · obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (hpt z hz)
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun hz' => absurd hz' hz⟩
  choose S hStendsto using hex
  have hSbound : ∀ n, ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R,
      ‖(sSeq n).1 z - S z‖ ≤ B * (1 / 2) ^ n / (1 - 1 / 2) := by
    intro n z hz
    have h := dist_le_of_le_geometric_of_tendsto (r := 1 / 2) (C := B) (by norm_num)
      (f := fun k => (sSeq k).1 z) (fun k => by
        rw [dist_eq_norm, norm_sub_rev]; exact hdiff k z hz)
      (hStendsto z hz) n
    rwa [dist_eq_norm] at h
  have hTU : TendstoUniformlyOn (fun k z => (sSeq k).1 z) S atTop
      (polydiscWithRadii 0 r ×ˢ ball 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rcases eq_or_lt_of_le hB0 with hB0' | hB0'
    · filter_upwards with n z hz
      rw [dist_comm, dist_eq_norm]
      calc ‖(sSeq n).1 z - S z‖ ≤ B * (1 / 2) ^ n / (1 - 1 / 2) := hSbound n z hz
        _ = 0 := by rw [← hB0']; ring
        _ < ε := hε
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
        (show (0:ℝ) < ε * (1 - 1/2) / B by positivity) (by norm_num : (1/2:ℝ) < 1)
      filter_upwards [eventually_ge_atTop N] with n hn z hz
      rw [dist_comm, dist_eq_norm]
      calc ‖(sSeq n).1 z - S z‖ ≤ B * (1 / 2) ^ n / (1 - 1 / 2) := hSbound n z hz
        _ ≤ B * (1 / 2) ^ N / (1 - 1 / 2) := by
              have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
              have hmul : B * (1 / 2 : ℝ) ^ n ≤ B * (1 / 2 : ℝ) ^ N :=
                mul_le_mul_of_nonneg_left hpow hB0
              exact div_le_div_of_nonneg_right hmul (by norm_num)
        _ < ε := by
              rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 1 - 1/2), mul_comm]
              exact (lt_div_iff₀ hB0').mp hN
  have hSanalytic : AnalyticOnNhd ℂ S (polydiscWithRadii 0 r ×ˢ ball 0 R) :=
    TendstoLocallyUniformlyOn.analyticOnNhd_finiteDimensional
      hTU.tendstoLocallyUniformlyOn
      (Filter.Eventually.of_forall fun k =>
        (sSeq k).2.analyticOnNhd_finiteDimensional (isOpen_polydiscWithRadii _ _ |>.prod
          isOpen_ball))
      (isOpen_polydiscWithRadii _ _ |>.prod isOpen_ball)
  exact ⟨S, hSanalytic, hSbound⟩

/-- **The remainder of a Picard limit is itself a Weierstrass remainder.** Given a bound
on the distance from each Picard approximation to a limit `S` (as produced by
`exists_tendstoUniformlyOn_picardApprox`), the limiting perturbed-division remainder
`g - h * S - ζ ^ d * S` is the Weierstrass remainder of the coefficients obtained by
passing derivatives of the numerator's slices to the limit. No identity theorem is used:
each Taylor coefficient of the remainder is recovered directly as the limit of the
corresponding coefficient of the finite Picard step. -/
theorem exists_weierstrassRemainder_eq_of_tendstoUniformlyOn_picardApprox
    (d : ℕ) (r : ι → ℝ) (R : ℝ) (hr : ∀ i, 0 < r i) (hR : 0 < R) (h g : (ι → ℂ) × ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (polydiscWithRadii 0 r ×ˢ ball 0 R))
    (hh : DifferentiableOn ℂ h (polydiscWithRadii 0 r ×ˢ ball 0 R))
    (hhb : ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖h z‖ ≤ R ^ d / (2 * (d + 1)))
    (M : ℝ) (hM0 : 0 ≤ M) (S : (ι → ℂ) × ℂ → ℂ)
    (hSdiff : DifferentiableOn ℂ S (polydiscWithRadii 0 r ×ˢ ball 0 R))
    (hSbound : ∀ n, ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R,
      ‖(picardApprox d r R hr hR h g hg hh n).1 z - S z‖ ≤
        ((d + 1 : ℕ) : ℝ) / R ^ d * M * (1 / 2) ^ n / (1 - 1 / 2)) :
    ∃ a : Fin d → (ι → ℂ) → ℂ, (∀ j, DifferentiableOn ℂ (a j) (polydiscWithRadii (0 : ι → ℂ) r)) ∧
      ∀ w ∈ polydiscWithRadii (0 : ι → ℂ) r, ∀ ζ ∈ ball (0 : ℂ) R,
        g (w, ζ) - h (w, ζ) * S (w, ζ) - ζ ^ d * S (w, ζ) = weierstrassRemainder a (w, ζ) := by
  set sSeq := fun k => picardApprox d r R hr hR h g hg hh k with hsSeqdef
  set B : ℝ := ((d + 1 : ℕ) : ℝ) / R ^ d * M with hBdef
  set rFun : (ι → ℂ) × ℂ → ℂ := fun z => g z - h z * S z - z.2 ^ d * S z with hrFundef
  set aOut : Fin d → (ι → ℂ) → ℂ := fun j w =>
    ((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv (j : ℕ) (fun ζ => rFun (w, ζ)) 0 with haOutdef
  have hrFunDiffFull : DifferentiableOn ℂ rFun (polydiscWithRadii 0 r ×ˢ ball 0 R) := by
    have h4 : DifferentiableOn ℂ (fun z : (ι → ℂ) × ℂ => z.2 ^ d)
        (polydiscWithRadii 0 r ×ˢ ball 0 R) := (differentiableOn_snd).pow d
    exact (hg.sub (hh.mul hSdiff)).sub (h4.mul hSdiff)
  have haDiff : ∀ j, DifferentiableOn ℂ (aOut j) (polydiscWithRadii (0 : ι → ℂ) r) := fun j =>
    (differentiableOn_iteratedDeriv_snd_slice (isOpen_polydiscWithRadii _ _)
      hrFunDiffFull hR (j : ℕ)).const_mul _
  refine ⟨aOut, haDiff, fun w hw ζ hζ => ?_⟩
  set Fk : ℕ → ℂ → ℂ := fun k ζ' =>
    g (w, ζ') - h (w, ζ') * (sSeq k).1 (w, ζ') - ζ' ^ d * (sSeq (k + 1)).1 (w, ζ') with hFkdef
  have hFkeq : ∀ k, ∀ ζ' ∈ ball (0 : ℂ) R, Fk k ζ' =
      weierstrassRemainder (picardApproxA d r R hr hR h g hg hh k) (w, ζ') := by
    intro k ζ' hζ'
    have hthis := (picardApprox_succ_isDiv d r R hr hR h g hg hh k).eq
      (⟨hw, hζ'⟩ : (w, ζ') ∈ polydiscWithRadii 0 r ×ˢ ball 0 R)
    show g (w, ζ') - h (w, ζ') * (sSeq k).1 (w, ζ') - ζ' ^ d * (sSeq (k + 1)).1 (w, ζ') = _
    have hthis' : g (w, ζ') - h (w, ζ') * (sSeq k).1 (w, ζ') =
        (sSeq (k + 1)).1 (w, ζ') * ζ' ^ d +
          weierstrassRemainder (picardApproxA d r R hr hR h g hg hh k) (w, ζ') := hthis
    rw [hthis']; ring
  have hFkvanish : ∀ k j, d ≤ j → iteratedDeriv j (Fk k) 0 = 0 := by
    intro k j hj
    have hev : Fk k =ᶠ[𝓝 (0 : ℂ)] fun ζ' => weierstrassRemainder
        (picardApproxA d r R hr hR h g hg hh k) (w, ζ') :=
      Filter.eventuallyEq_of_mem (ball_mem_nhds 0 hR) (hFkeq k)
    rw [hev.iteratedDeriv_eq j]
    unfold weierstrassRemainder
    have hcalc := iteratedDeriv_weierstrassRemainder_const
      (fun j' => picardApproxA d r R hr hR h g hg hh k j' w) j
    rw [hcalc, dif_neg (by omega)]
  have hFkbound : ∀ k, ∀ ζ' ∈ ball (0 : ℂ) R, ‖Fk k ζ' - rFun (w, ζ')‖ ≤
      (R ^ d / (2 * (d + 1))) * (B * (1 / 2) ^ k / (1 - 1 / 2)) +
        R ^ d * (B * (1 / 2) ^ (k + 1) / (1 - 1 / 2)) := by
    intro k ζ' hζ'
    have hwz' : (w, ζ') ∈ polydiscWithRadii 0 r ×ˢ ball 0 R := ⟨hw, hζ'⟩
    have hb1 := hSbound k (w, ζ') hwz'
    have hb2 := hSbound (k + 1) (w, ζ') hwz'
    have hζ'le : ‖ζ'‖ ≤ R := (mem_ball_zero_iff.mp hζ').le
    have hhle : ‖h (w, ζ')‖ ≤ R ^ d / (2 * (d + 1)) := hhb (w, ζ') hwz'
    have hdiff_eq : Fk k ζ' - rFun (w, ζ') =
        -(h (w, ζ') * ((sSeq k).1 (w, ζ') - S (w, ζ'))) -
          ζ' ^ d * ((sSeq (k + 1)).1 (w, ζ') - S (w, ζ')) := by
      show (g (w, ζ') - h (w, ζ') * (sSeq k).1 (w, ζ') -
          ζ' ^ d * (sSeq (k + 1)).1 (w, ζ')) -
        (g (w, ζ') - h (w, ζ') * S (w, ζ') - ζ' ^ d * S (w, ζ')) = _
      ring
    rw [hdiff_eq]
    calc ‖-(h (w, ζ') * ((sSeq k).1 (w, ζ') - S (w, ζ'))) -
          ζ' ^ d * ((sSeq (k + 1)).1 (w, ζ') - S (w, ζ'))‖
        = ‖h (w, ζ') * ((sSeq k).1 (w, ζ') - S (w, ζ')) +
            ζ' ^ d * ((sSeq (k + 1)).1 (w, ζ') - S (w, ζ'))‖ := by
          rw [← norm_neg]; congr 1; ring
      _ ≤ ‖h (w, ζ') * ((sSeq k).1 (w, ζ') - S (w, ζ'))‖ +
            ‖ζ' ^ d * ((sSeq (k + 1)).1 (w, ζ') - S (w, ζ'))‖ := norm_add_le _ _
      _ = ‖h (w, ζ')‖ * ‖(sSeq k).1 (w, ζ') - S (w, ζ')‖ +
            ‖ζ'‖ ^ d * ‖(sSeq (k + 1)).1 (w, ζ') - S (w, ζ')‖ := by
          rw [norm_mul, norm_mul, norm_pow]
      _ ≤ (R ^ d / (2 * (d + 1))) * (B * (1 / 2) ^ k / (1 - 1 / 2)) +
            R ^ d * (B * (1 / 2) ^ (k + 1) / (1 - 1 / 2)) := by
          gcongr
  have hFktendsto : Tendsto (fun k => (R ^ d / (2 * (d + 1))) * (B * (1 / 2) ^ k / (1 - 1 / 2)) +
      R ^ d * (B * (1 / 2) ^ (k + 1) / (1 - 1 / 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) atTop (𝓝 0) :=
      h1.comp (tendsto_add_atTop_nat 1)
    have e1 : Tendsto (fun k => (R ^ d / (2 * (d + 1))) * (B * (1 / 2) ^ k / (1 - 1 / 2)))
        atTop (𝓝 ((R ^ d / (2 * (d + 1))) * (B * 0 / (1 - 1 / 2)))) :=
      ((h1.const_mul B).div_const (1 - 1/2)).const_mul _
    have e2 : Tendsto (fun k => R ^ d * (B * (1 / 2) ^ (k + 1) / (1 - 1 / 2)))
        atTop (𝓝 (R ^ d * (B * 0 / (1 - 1 / 2)))) :=
      ((h2.const_mul B).div_const (1 - 1/2)).const_mul _
    simpa using e1.add e2
  have hFkTU : TendstoUniformlyOn Fk (fun ζ' => rFun (w, ζ')) atTop (ball (0:ℂ) R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have := (Metric.tendsto_atTop.mp hFktendsto) ε hε
    obtain ⟨N, hN⟩ := this
    filter_upwards [eventually_ge_atTop N] with k hk ζ' hζ'
    rw [dist_comm, dist_eq_norm]
    calc ‖Fk k ζ' - rFun (w, ζ')‖ ≤ _ := hFkbound k ζ' hζ'
      _ = ‖(R ^ d / (2 * (d + 1))) * (B * (1 / 2) ^ k / (1 - 1 / 2)) +
            R ^ d * (B * (1 / 2) ^ (k + 1) / (1 - 1 / 2)) - 0‖ := by
          rw [sub_zero]
          rw [Real.norm_of_nonneg (by positivity)]
      _ < ε := hN k hk
  have hFkDiff : ∀ k, DifferentiableOn ℂ (Fk k) (ball (0 : ℂ) R) := by
    intro k
    have h1 : DifferentiableOn ℂ (fun ζ' => g (w, ζ')) (ball (0:ℂ) R) :=
      differentiableOn_snd_slice hg hw
    have h2 : DifferentiableOn ℂ (fun ζ' => h (w, ζ')) (ball (0:ℂ) R) :=
      differentiableOn_snd_slice hh hw
    have h3 : DifferentiableOn ℂ (fun ζ' => (sSeq k).1 (w, ζ')) (ball (0:ℂ) R) :=
      differentiableOn_snd_slice (sSeq k).2 hw
    have h4 : DifferentiableOn ℂ (fun ζ' => (sSeq (k+1)).1 (w, ζ')) (ball (0:ℂ) R) :=
      differentiableOn_snd_slice (sSeq (k+1)).2 hw
    exact (h1.sub (h2.mul h3)).sub ((differentiableOn_pow d).mul h4)
  have hiter : ∀ j, Tendsto (fun k => iteratedDeriv j (Fk k) 0) atTop
      (𝓝 (iteratedDeriv j (fun ζ' => rFun (w, ζ')) 0)) :=
    fun j => tendsto_iteratedDeriv_of_tendstoLocallyUniformlyOn isOpen_ball j Fk
      (fun ζ' => rFun (w, ζ')) hFkTU.tendstoLocallyUniformlyOn hFkDiff (mem_ball_self hR)
  have hAkTendsto : ∀ j : Fin d, Tendsto (fun k => picardApproxA d r R
      hr hR h g hg hh k j w) atTop (𝓝 (aOut j w)) := by
    intro j
    have h1 := hiter (j : ℕ)
    have heq2 : ∀ k, iteratedDeriv (j : ℕ) (Fk k) 0 =
        ((j : ℕ).factorial : ℂ) * picardApproxA d r R hr hR h g hg hh k j w := by
      intro k
      have hev : Fk k =ᶠ[𝓝 (0 : ℂ)] fun ζ' => weierstrassRemainder (picardApproxA d
          r R hr hR h g hg hh k) (w, ζ') :=
        Filter.eventuallyEq_of_mem (ball_mem_nhds 0 hR) (hFkeq k)
      rw [hev.iteratedDeriv_eq (j : ℕ)]
      unfold weierstrassRemainder
      rw [iteratedDeriv_weierstrassRemainder_const
        (fun j' => picardApproxA d r R hr hR h g hg hh k j' w) (j : ℕ), dif_pos j.isLt]
    have h3 : Tendsto (fun k => ((j : ℕ).factorial : ℂ) * picardApproxA d r R
        hr hR h g hg hh k j w) atTop
        (𝓝 (iteratedDeriv (j : ℕ) (fun ζ' => rFun (w, ζ')) 0)) := by
      simpa only [heq2] using h1
    have hfac_ne : ((j : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast (j : ℕ).factorial_ne_zero
    have h4 := h3.const_mul (((j : ℕ).factorial : ℂ)⁻¹)
    simp only [← mul_assoc, inv_mul_cancel₀ hfac_ne, one_mul] at h4
    exact h4
  have hsum_tendsto : Tendsto (fun k => weierstrassRemainder (picardApproxA d r R
      hr hR h g hg hh k) (w, ζ)) atTop
      (𝓝 (weierstrassRemainder aOut (w, ζ))) := by
    unfold weierstrassRemainder
    exact tendsto_finset_sum Finset.univ (fun j _ => (hAkTendsto j).mul_const (ζ ^ (j : ℕ)))
  have hFk_tendsto_wR : Tendsto (fun k => Fk k ζ) atTop (𝓝 (weierstrassRemainder aOut (w, ζ))) := by
    have heq3 : (fun k => weierstrassRemainder (picardApproxA d r R
        hr hR h g hg hh k) (w, ζ)) = fun k => Fk k ζ :=
      funext fun k => (hFkeq k ζ hζ).symm
    rwa [heq3] at hsum_tendsto
  have hFk_tendsto_r : Tendsto (fun k => Fk k ζ) atTop (𝓝 (rFun (w, ζ))) :=
    hFkTU.tendstoLocallyUniformlyOn.tendsto_at hζ
  exact tendsto_nhds_unique hFk_tendsto_r hFk_tendsto_wR

/-- **Direct uniqueness for the perturbed coordinate-power fixed-point equation.**
If `h` is uniformly small relative to `R` on a domain, any two decompositions of the
*same* `g` against the divisor `z ^ d + h`, each individually bounded there, agree. -/
theorem eqOn_of_isWeierstrassDivisionOn_selfPerturbed {d : ℕ} {r : ι → ℝ} {R : ℝ}
    (hr : ∀ i, 0 < r i) (hR : 0 < R) (h g s s' : (ι → ℂ) × ℂ → ℂ) (a a' : Fin d → (ι → ℂ) → ℂ)
    (hh : DifferentiableOn ℂ h (polydiscWithRadii 0 r ×ˢ ball 0 R))
    (hhb : ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖h z‖ ≤ R ^ d / (2 * (d + 1)))
    (hdiv : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (g - h * s) s a (polydiscWithRadii 0 r) R)
    (hdiv' : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (g - h * s') s' a'
      (polydiscWithRadii 0 r) R)
    (M : ℝ) (hM0 : 0 ≤ M) (hsb : ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖s z - s' z‖ ≤ M) :
    EqOn s s' (polydiscWithRadii 0 r ×ˢ ball 0 R) ∧ ∀ j, EqOn (a j) (a' j) (polydiscWithRadii 0 r) := by
  suffices hs : EqOn s s' (polydiscWithRadii 0 r ×ˢ ball 0 R) by
    refine ⟨hs, ?_⟩
    have hdiv2 : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (g - h * s) s' a'
        (polydiscWithRadii 0 r) R :=
      ⟨hdiv'.quotient_holomorphic,
        hdiv'.coefficient_holomorphic,
        fun z hz => by
          show (g z - h z * s z) = s' z * z.2 ^ d + weierstrassRemainder a' z
          rw [hs hz]
          exact hdiv'.eq hz⟩
    exact (unique_coordinatePower_division hdiv hdiv2 hR).2
  have hQA : ∀ M' : ℝ, 0 ≤ M' →
      (∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖s z - s' z‖ ≤ M') →
      ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖s z - s' z‖ ≤ M' / 2 := by
    intro M' hM'0 hM' z hz
    have hQAdiv : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (h * (s' - s)) (s - s')
        (fun j => a j - a' j) (polydiscWithRadii 0 r) R := by
      refine ⟨hdiv.quotient_holomorphic.sub hdiv'.quotient_holomorphic,
        fun j => (hdiv.coefficient_holomorphic j).sub (hdiv'.coefficient_holomorphic j), ?_⟩
      intro w hw
      have e1 : g w - h w * s w = s w * w.2 ^ d + weierstrassRemainder a w := hdiv.eq hw
      have e2 : g w - h w * s' w = s' w * w.2 ^ d + weierstrassRemainder a' w := hdiv'.eq hw
      show h w * (s' w - s w) = (s w - s' w) * w.2 ^ d + weierstrassRemainder (fun j => a j - a' j) w
      rw [← weierstrassRemainder_sub]
      have : h w * (s' w - s w) = (s w * w.2 ^ d + weierstrassRemainder a w) -
          (s' w * w.2 ^ d + weierstrassRemainder a' w) := by rw [← e1, ← e2]; ring
      rw [this]; ring
    have hhdiff : DifferentiableOn ℂ (h * (s' - s)) (polydiscWithRadii 0 r ×ˢ ball 0 R) :=
      hh.mul (hdiv'.quotient_holomorphic.sub hdiv.quotient_holomorphic)
    obtain ⟨q'', a'', hdiv'', hbound'', huniq''⟩ := coordinatePower_division d hr hR hhdiff
    have hEq := (huniq'' (s - s') (fun j => a j - a' j) hQAdiv).1
    have hb : ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖(h * (s' - s)) z‖ ≤
        (R ^ d / (2 * (d + 1))) * M' := by
      intro z hz
      show ‖h z * (s' z - s z)‖ ≤ _
      rw [norm_mul, ← norm_sub_rev (s z) (s' z)]
      exact mul_le_mul (hhb z hz) (hM' z hz) (norm_nonneg _) (by positivity)
    have hq''bound := hbound'' _ (by positivity) hb z hz
    rw [hEq hz] at hq''bound
    calc ‖s z - s' z‖ = ‖(s - s') z‖ := rfl
      _ ≤ ((d + 1 : ℕ) : ℝ) / R ^ d * ((R ^ d / (2 * (d + 1))) * M') := hq''bound
      _ = M' / 2 := by
          have hRd : R ^ d ≠ 0 := by positivity
          have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
          push_cast
          field_simp
  have hind : ∀ n, ∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖s z - s' z‖ ≤ M * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simpa using hsb
    | succ n ih =>
      intro z hz
      have := hQA (M * (1/2)^n) (by positivity) ih z hz
      calc ‖s z - s' z‖ ≤ M * (1/2)^n / 2 := this
        _ = M * (1/2)^(n+1) := by ring
  intro z hz
  have htendsto : Tendsto (fun n => M * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)
    simpa using this.const_mul M
  have hle : ‖s z - s' z‖ ≤ 0 :=
    ge_of_tendsto htendsto (Filter.Eventually.of_forall fun n => hind n z hz)
  have := norm_nonneg (s z - s' z)
  have heq0 : ‖s z - s' z‖ = 0 := le_antisymm hle this
  exact sub_eq_zero.mp (norm_eq_zero.mp heq0)

/-- Every open neighborhood of the origin in `(ι → ℂ) × ℂ` contains a product of a
constant-radius polydisc and a ball of the same radius. -/
theorem exists_polydisc_ball_subset {U : Set ((ι → ℂ) × ℂ)}
    (hU : IsOpen U) (h0 : (0 : (ι → ℂ) × ℂ) ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ polydiscWithRadii (0 : ι → ℂ) (fun _ => ε) ×ˢ ball (0 : ℂ) ε ⊆ U := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  refine ⟨ε, hε, fun z hz => hsub ?_⟩
  rw [mem_ball, dist_zero_right, Prod.norm_def]
  rw [polydiscWithRadii_const_eq_ball (0 : ι → ℂ) hε] at hz
  obtain ⟨h1, h2⟩ := hz
  apply max_lt
  · simpa [mem_ball, dist_zero_right] using h1
  · simpa [mem_ball, dist_zero_right] using h2

/-- **Coordinate-power normalization with a nonvanishing leading factor.** A holomorphic
function of finite order `d` in the distinguished coordinate decomposes, on some initial
polydisc-ball, as `f1 * z.2 ^ d` plus a Weierstrass remainder whose coefficients vanish at
the parameter origin; moreover `f1` itself is nonzero throughout a (possibly smaller)
polydisc-ball. This is Steps 1–4 of the proof of `weierstrass_division`. -/
theorem exists_coordinatePower_leadingFactor_ne_zero {d : ℕ} {f : (ι → ℂ) × ℂ → ℂ}
    {U : Set ((ι → ℂ) × ℂ)} (hU : IsOpen U) (h0 : 0 ∈ U) (hf : DifferentiableOn ℂ f U)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    ∃ (f1 : (ι → ℂ) × ℂ → ℂ) (c : Fin d → (ι → ℂ) → ℂ) (ε₀ ε₁ : ℝ), 0 < ε₀ ∧ 0 < ε₁ ∧
      polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₀) ×ˢ ball (0 : ℂ) ε₀ ⊆ U ∧
      IsWeierstrassDivisionOn (fun z => z.2 ^ d) f f1 c
        (polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₀)) ε₀ ∧
      (∀ j, c j 0 = 0) ∧
      polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁ ⊆
        polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₀) ×ˢ ball (0 : ℂ) ε₀ ∧
      ∀ z ∈ polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁, f1 z ≠ 0 := by
  obtain ⟨ε₀, hε₀, hε₀U⟩ := exists_polydisc_ball_subset hU h0
  have hf0 : DifferentiableOn ℂ f (polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₀) ×ˢ ball 0 ε₀) :=
    hf.mono hε₀U
  obtain ⟨f1, c, hfdiv, hf1bound, hf1uniq⟩ :=
    coordinatePower_division d (fun _ => hε₀) hε₀ hf0
  have hz0V : (0 : ι → ℂ) ∈ polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₀) :=
    mem_polydiscWithRadii.mpr fun i => by simpa using hε₀
  have hforder : AnalyticAt ℂ (fun w : ℂ => f (0, w)) 0 :=
    (differentiableOn_snd_slice hf0 hz0V).analyticOnNhd_finiteDimensional isOpen_ball
      0 (mem_ball_self hε₀)
  have hcj0 : ∀ j : Fin d, c j 0 = 0 := by
    intro j
    rw [coeff_eq_iteratedDeriv_of_coordinatePower_division hfdiv hε₀ hz0V j]
    have hle : (d : ℕ∞) ≤ analyticOrderAt (fun w : ℂ => f (0, w)) 0 := horder.ge
    rw [(natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hforder).mp hle (j : ℕ) j.isLt]
    simp
  have hf1_eq : ∀ ζ ∈ ball (0 : ℂ) ε₀, f (0, ζ) = f1 (0, ζ) * ζ ^ d := by
    intro ζ hζ
    have := hfdiv.eq (Set.mk_mem_prod hz0V hζ)
    simpa [weierstrassRemainder, hcj0, mul_comm] using this
  have hf1A0 : AnalyticAt ℂ (fun ζ : ℂ => f1 (0, ζ)) 0 :=
    (differentiableOn_snd_slice hfdiv.quotient_holomorphic hz0V).analyticOnNhd_finiteDimensional
      isOpen_ball 0 (mem_ball_self hε₀)
  have horder' : analyticOrderAt (fun ζ : ℂ => f1 (0, ζ) * ζ ^ d) 0 = d := by
    rw [← analyticOrderAt_congr (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds
      (mem_ball_self hε₀)) hf1_eq)]
    exact horder
  have hf1ord0 : analyticOrderAt (fun ζ : ℂ => f1 (0, ζ)) 0 = 0 := by
    have hpow : AnalyticAt ℂ (fun ζ : ℂ => ζ ^ d) 0 := analyticAt_id.pow d
    have hpow' : analyticOrderAt (fun ζ : ℂ => ζ ^ d) 0 = d := by
      have h := analyticOrderAt_pow (analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))) d
      simpa [analyticOrderAt_id, Pi.pow_def] using h
    have hmul : analyticOrderAt (fun ζ : ℂ => f1 (0, ζ) * ζ ^ d) 0 =
        analyticOrderAt (fun ζ : ℂ => f1 (0, ζ)) 0 + analyticOrderAt (fun ζ : ℂ => ζ ^ d) 0 :=
      analyticOrderAt_mul hf1A0 hpow
    rw [hmul, hpow'] at horder'
    set y := analyticOrderAt (fun ζ : ℂ => f1 (0, ζ)) 0 with hy
    clear_value y
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      rw [show ((⊤ : ℕ∞) + (d : ℕ∞)) = ⊤ from rfl] at horder'
      exact absurd horder' (ENat.natCast_ne_top d).symm
    | coe n =>
      have hcast : ((n + d : ℕ) : ℕ∞) = ((d : ℕ) : ℕ∞) := horder'
      have hn : n + d = d := WithTop.coe_injective hcast
      have hn0 : n = 0 := by omega
      rw [hn0]
      rfl
  have hf1ne0 : f1 (0, 0) ≠ 0 := hf1A0.analyticOrderAt_eq_zero.mp hf1ord0
  have hz00 : ((0 : ι → ℂ), (0 : ℂ)) ∈
      polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₀) ×ˢ ball (0 : ℂ) ε₀ :=
    ⟨hz0V, mem_ball_self hε₀⟩
  have hf1contAt : ContinuousAt f1 (0, 0) :=
    ((hfdiv.quotient_holomorphic.analyticOnNhd_finiteDimensional
      ((isOpen_polydiscWithRadii _ _).prod isOpen_ball)) _ hz00).continuousAt
  have hf1ev : ∀ᶠ z in 𝓝 ((0 : ι → ℂ), (0 : ℂ)), f1 z ≠ 0 :=
    hf1contAt.eventually_ne hf1ne0
  obtain ⟨S, hSf1, hSopen, hS0⟩ := _root_.eventually_nhds_iff.mp hf1ev
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := exists_polydisc_ball_subset
    (hSopen.inter ((isOpen_polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₀)).prod isOpen_ball))
    ⟨hS0, hz00⟩
  have hε₁ε₀ : polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁ ⊆
      polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₀) ×ˢ ball (0 : ℂ) ε₀ :=
    fun z hz => (hε₁sub hz).2
  have hf1ne0' : ∀ z ∈ polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁, f1 z ≠ 0 :=
    fun z hz => hSf1 z (hε₁sub hz).1
  exact ⟨f1, c, ε₀, ε₁, hε₀, hε₁, hε₀U, hfdiv, hcj0, hε₁ε₀, hf1ne0'⟩

/-- **A uniformly small perturbation of the coordinate power.** Given a coordinate-power
decomposition `f = f1 * z.2 ^ d + weierstrassRemainder c` with `f1` nonvanishing on a
polydisc-ball of radius `ε₁`, the perturbation `weierstrassRemainder c / f1` is analytic
there and, on a smaller polydisc-ball, uniformly bounded by `R₂ ^ d / (2 * (d + 1))`: small
enough for the Picard iteration against the divisor `z ^ d` to contract. This is Steps 5–6
of the proof of `weierstrass_division`. The bound `δ` on `‖f1‖` over a fixed compact set is
also returned, since the germ-uniqueness argument reuses it at a further-shrunk radius. -/
theorem exists_perturbation_bound_of_coordinatePower_leadingFactor {d : ℕ} {f : (ι → ℂ) × ℂ → ℂ}
    {f1 : (ι → ℂ) × ℂ → ℂ} {c : Fin d → (ι → ℂ) → ℂ} {ε₀ ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (hε₁ε₀ : polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁ ⊆
      polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₀) ×ˢ ball (0 : ℂ) ε₀)
    (hfdiv : IsWeierstrassDivisionOn (fun z => z.2 ^ d) f f1 c
      (polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₀)) ε₀)
    (hcj0 : ∀ j, c j 0 = 0)
    (hf1ne0' : ∀ z ∈ polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁, f1 z ≠ 0) :
    ∃ R₂ δ r₃ : ℝ, 0 < R₂ ∧ R₂ < ε₁ ∧ 0 < δ ∧ 0 < r₃ ∧ r₃ ≤ ε₁ / 2 ∧
      DifferentiableOn ℂ (fun z => weierstrassRemainder c z / f1 z)
        (polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁) ∧
      (∀ j, Tendsto (c j) (𝓝 0) (𝓝 0)) ∧
      (∀ z ∈ closedPolydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁ / 2) ×ˢ closedBall (0 : ℂ) R₂,
        δ ≤ ‖f1 z‖) ∧
      ∀ w ∈ polydiscWithRadii (0 : ι → ℂ) (fun _ => r₃), ∀ ζ ∈ ball (0 : ℂ) R₂,
        ‖weierstrassRemainder c (w, ζ) / f1 (w, ζ)‖ ≤ R₂ ^ d / (2 * (d + 1)) := by
  have hpoly1sub : polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁) ⊆
      polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₀) :=
    fun z hz => (hε₁ε₀ (Set.mk_mem_prod hz (mem_ball_self hε₁))).1
  have hcA1 : ∀ j, DifferentiableOn ℂ (c j) (polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁)) :=
    fun j => (hfdiv.coefficient_holomorphic j).mono hpoly1sub
  have hremA1 : DifferentiableOn ℂ (weierstrassRemainder c)
      (polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁) := by
    unfold weierstrassRemainder
    apply DifferentiableOn.fun_sum
    intro j _
    exact ((hcA1 j).comp differentiableOn_fst (fun z hz => hz.1)).mul
      (differentiableOn_snd.pow (j : ℕ))
  have hf1A1 : DifferentiableOn ℂ f1
      (polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁) :=
    hfdiv.quotient_holomorphic.mono hε₁ε₀
  have hhA1 : DifferentiableOn ℂ (fun z => weierstrassRemainder c z / f1 z)
      (polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁) := by
    simp_rw [div_eq_mul_inv]
    exact hremA1.mul (hf1A1.inv hf1ne0')
  set R₂ : ℝ := ε₁ / 2 with hR₂def
  have hR₂pos : 0 < R₂ := by positivity
  have hR₂ε₁ : R₂ < ε₁ := by rw [hR₂def]; linarith
  set K : Set ((ι → ℂ) × ℂ) :=
    closedPolydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁ / 2) ×ˢ closedBall (0 : ℂ) R₂ with hKdef
  have hKsub : K ⊆ polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁ := by
    apply Set.prod_mono
    · exact closedPolydiscWithRadii_subset_polydiscWithRadii _ (fun _ => by linarith)
    · exact closedBall_subset_ball hR₂ε₁
  have hKcompact : IsCompact K :=
    (isCompact_closedPolydiscWithRadii _ _).prod (isCompact_closedBall _ _)
  have hKne : K.Nonempty := ⟨(0, 0), by
    refine ⟨mem_closedPolydiscWithRadii.mpr fun i => ?_, mem_closedBall_self hR₂pos.le⟩
    simpa using (half_pos hε₁).le⟩
  have hf1contK : ContinuousOn f1 K := (hf1A1.mono hKsub).continuousOn
  obtain ⟨zmin, hzminK, hzminmin⟩ := hKcompact.exists_isMinOn hKne hf1contK.norm
  set δ : ℝ := ‖f1 zmin‖ with hδdef
  have hδpos : 0 < δ := norm_pos_iff.mpr (hf1ne0' zmin (hKsub hzminK))
  have hδle : ∀ z ∈ K, δ ≤ ‖f1 z‖ := fun z hz => hzminmin hz
  set εc : ℝ := δ * R₂ ^ d / (2 * (d + 1) * (d + 1) * (max R₂ 1) ^ d) with hεcdef
  have hεcpos : 0 < εc := by
    rw [hεcdef]
    have : 0 < max R₂ 1 := lt_max_of_lt_right one_pos
    positivity
  have hcj0' : ∀ j : Fin d, Tendsto (c j) (𝓝 0) (𝓝 0) := fun j =>
    (hcj0 j) ▸ ((hcA1 j).continuousOn.continuousAt (isOpen_polydiscWithRadii _ _ |>.mem_nhds
      (mem_polydiscWithRadii.mpr fun i => by simpa using half_pos hε₁)))
  have hcjev : ∀ j : Fin d, ∀ᶠ w in 𝓝 (0 : ι → ℂ), ‖c j w‖ < εc := fun j => by
    have hz : Tendsto (fun w => ‖c j w‖) (𝓝 0) (𝓝 0) := by
      simpa using (hcj0' j).norm
    exact hz.eventually_lt_const hεcpos
  have hcjall : ∀ᶠ w in 𝓝 (0 : ι → ℂ), ∀ j : Fin d, ‖c j w‖ < εc := eventually_all.mpr hcjev
  obtain ⟨r₂, hr₂pos, hr₂sub⟩ := Metric.eventually_nhds_iff.mp hcjall
  set r₃ : ℝ := min r₂ (ε₁ / 2) with hr₃def
  have hr₃pos : 0 < r₃ := lt_min hr₂pos (half_pos hε₁)
  have hr₃r₂ : r₃ ≤ r₂ := min_le_left _ _
  have hr₃ε₁ : r₃ ≤ ε₁ / 2 := min_le_right _ _
  have hM2pos : (0:ℝ) < max R₂ 1 := lt_max_of_lt_right one_pos
  have hRj_le (j : ℕ) (hj : j < d) : R₂ ^ j ≤ (max R₂ 1) ^ d := by
    rcases le_total 1 R₂ with hR1 | hR1
    · calc R₂ ^ j ≤ R₂ ^ d := pow_le_pow_right₀ hR1 hj.le
        _ ≤ (max R₂ 1) ^ d := pow_le_pow_left₀ hR₂pos.le (le_max_left _ _) d
    · calc R₂ ^ j ≤ 1 ^ j := pow_le_pow_left₀ hR₂pos.le hR1 j
        _ = 1 := one_pow j
        _ ≤ (max R₂ 1) ^ d := one_le_pow₀ (le_max_right _ _)
  have hhbound : ∀ w ∈ polydiscWithRadii (0 : ι → ℂ) (fun _ => r₃), ∀ ζ ∈ ball (0 : ℂ) R₂,
      ‖weierstrassRemainder c (w, ζ) / f1 (w, ζ)‖ ≤ R₂ ^ d / (2 * (d + 1)) := by
    intro w hw ζ hζ
    have hwr3 : ‖w‖ < r₃ := by
      simpa [pi_norm_lt_iff hr₃pos, mem_polydiscWithRadii] using hw
    have hwr2 : dist w (0 : ι → ℂ) < r₂ := by
      rw [dist_zero_right]; exact hwr3.trans_le hr₃r₂
    have hcbound : ∀ j : Fin d, ‖c j w‖ < εc := hr₂sub hwr2
    have hζR2 : ‖ζ‖ < R₂ := by simpa [mem_ball, dist_zero_right] using hζ
    have hwK : (w, ζ) ∈ K := by
      refine ⟨mem_closedPolydiscWithRadii.mpr fun i => ?_, mem_closedBall_iff_norm.mpr ?_⟩
      · show dist (w i) (0 : ℂ) ≤ ε₁ / 2
        rw [dist_zero_right]
        exact le_of_lt (calc ‖w i‖ ≤ ‖w‖ := norm_le_pi_norm w i
          _ < r₃ := hwr3
          _ ≤ ε₁ / 2 := hr₃ε₁)
      · rw [sub_zero]; exact hζR2.le
    have hf1lb : δ ≤ ‖f1 (w, ζ)‖ := hδle _ hwK
    have hnum : ‖weierstrassRemainder c (w, ζ)‖ ≤ ((d:ℝ)) * εc * (max R₂ 1) ^ d := by
      unfold weierstrassRemainder
      calc ‖∑ j : Fin d, c j w * ζ ^ (j : ℕ)‖ ≤ ∑ j : Fin d, ‖c j w * ζ ^ (j:ℕ)‖ :=
            norm_sum_le _ _
        _ = ∑ j : Fin d, ‖c j w‖ * ‖ζ‖ ^ (j:ℕ) := by simp [norm_mul, norm_pow]
        _ ≤ ∑ _j : Fin d, εc * (max R₂ 1) ^ d := by
              apply Finset.sum_le_sum
              intro j _
              apply mul_le_mul (hcbound j).le
                (le_trans (pow_le_pow_left₀ (norm_nonneg _) hζR2.le (j:ℕ)) (hRj_le (j:ℕ) j.isLt))
                (by positivity) (by positivity)
        _ = (d:ℝ) * εc * (max R₂ 1) ^ d := by
              simp [Finset.sum_const, Finset.card_univ]; ring
    have hf1pos : 0 < ‖f1 (w, ζ)‖ := hδpos.trans_le hf1lb
    rw [norm_div]
    calc ‖weierstrassRemainder c (w, ζ)‖ / ‖f1 (w, ζ)‖
        ≤ ((d:ℝ) * εc * (max R₂ 1) ^ d) / ‖f1 (w, ζ)‖ := by
          apply div_le_div_of_nonneg_right hnum hf1pos.le
      _ ≤ ((d:ℝ) * εc * (max R₂ 1) ^ d) / δ := by
          apply div_le_div_of_nonneg_left (by positivity) hδpos hf1lb
      _ = (d:ℝ) * R₂ ^ d / (2 * (d + 1) * (d + 1)) := by
          rw [hεcdef]; field_simp
      _ ≤ R₂ ^ d / (2 * (d + 1)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [pow_pos hR₂pos d]
  exact ⟨R₂, δ, r₃, hR₂pos, hR₂ε₁, hδpos, hr₃pos, hr₃ε₁, hhA1, hcj0', hδle, hhbound⟩

/-- **Weierstrass division (Jakóbczak–Jarnicki 1.7.3).** A divisor whose central
scalar slice has finite order `d` admits division of every bounded holomorphic numerator
on a fixed polydisc. The quotient bound is uniform in the numerator. Uniqueness is local,
so it also compares decompositions initially defined on smaller neighborhoods.
Proof pending: normalize the divisor and iterate coordinate-power division estimates. -/
theorem weierstrass_division {d : ℕ} {f : (ι → ℂ) × ℂ → ℂ}
    {U : Set ((ι → ℂ) × ℂ)} (hU : IsOpen U) (h0 : 0 ∈ U)
    (hf : DifferentiableOn ℂ f U)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    ∃ (r : ι → ℝ) (R C : ℝ), (∀ i, 0 < r i) ∧ 0 < R ∧ 0 < C ∧
      polydiscWithRadii 0 r ×ˢ ball 0 R ⊆ U ∧
      ∀ (g : (ι → ℂ) × ℂ → ℂ),
        DifferentiableOn ℂ g (polydiscWithRadii 0 r ×ˢ ball 0 R) →
        ∀ M : ℝ, 0 ≤ M → (∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖g z‖ ≤ M) →
        ∃ (q : (ι → ℂ) × ℂ → ℂ) (a : Fin d → (ι → ℂ) → ℂ),
          IsWeierstrassDivisionOn f g q a (polydiscWithRadii 0 r) R ∧
          (∀ z ∈ polydiscWithRadii 0 r ×ˢ ball 0 R, ‖q z‖ ≤ C * M) ∧
          (∀ q' a', IsWeierstrassDivisionAt f g q' a' →
            q =ᶠ[𝓝 0] q' ∧ ∀ j, a j =ᶠ[𝓝 0] a' j) := by
  -- Steps 1–4: normalize `f`, and shrink to where the leading factor `f1` is nonzero.
  obtain ⟨f1, c, ε₀, ε₁, hε₀, hε₁, hε₀U, hfdiv, hcj0, hε₁ε₀, hf1ne0'⟩ :=
    exists_coordinatePower_leadingFactor_ne_zero hU h0 hf horder
  -- Steps 5–6: the perturbation `h := weierstrassRemainder c / f1` is small on a smaller
  -- (polydisc, ball).
  obtain ⟨R₂, δ, r₃, hR₂pos, hR₂ε₁, hδpos, hr₃pos, hr₃ε₁, hhA1, hcj0', hδle, hhbound⟩ :=
    exists_perturbation_bound_of_coordinatePower_leadingFactor hε₁ hε₁ε₀ hfdiv hcj0 hf1ne0'
  set hh : (ι → ℂ) × ℂ → ℂ := fun z => weierstrassRemainder c z / f1 z with hhdef
  set K : Set ((ι → ℂ) × ℂ) :=
    closedPolydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁ / 2) ×ˢ closedBall (0 : ℂ) R₂ with hKdef
  -- Step 7: assemble the final domain, and restrict f, h to it.
  have hr₃ε₁' : r₃ ≤ ε₁ := hr₃ε₁.trans (by linarith)
  have hR₂ε₁' : R₂ ≤ ε₁ := hR₂ε₁.le
  have hFINALsubε₁ : polydiscWithRadii (0 : ι → ℂ) (fun _ => r₃) ×ˢ ball (0 : ℂ) R₂ ⊆
      polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁ :=
    Set.prod_mono (polydiscWithRadii_mono _ (fun _ => hr₃ε₁')) (ball_subset_ball hR₂ε₁')
  have hFINALsub : polydiscWithRadii (0 : ι → ℂ) (fun _ => r₃) ×ˢ ball (0 : ℂ) R₂ ⊆ U :=
    hFINALsubε₁.trans (fun z hz => hε₀U (hε₁ε₀ hz))
  have hfFINAL : DifferentiableOn ℂ f
      (polydiscWithRadii (0 : ι → ℂ) (fun _ => r₃) ×ˢ ball (0 : ℂ) R₂) :=
    hf.mono hFINALsub
  have hhFINAL : DifferentiableOn ℂ (fun z => weierstrassRemainder c z / f1 z)
      (polydiscWithRadii (0 : ι → ℂ) (fun _ => r₃) ×ˢ ball (0 : ℂ) R₂) :=
    hhA1.mono hFINALsubε₁
  have hhboundFINAL : ∀ z ∈ polydiscWithRadii (0 : ι → ℂ) (fun _ => r₃) ×ˢ ball (0 : ℂ) R₂,
      ‖weierstrassRemainder c z / f1 z‖ ≤ R₂ ^ d / (2 * (d + 1)) :=
    fun z hz => hhbound z.1 hz.1 z.2 hz.2
  refine ⟨fun _ => r₃, R₂, 2 * ((d : ℝ) + 1) / (R₂ ^ d * δ), fun _ => hr₃pos, hR₂pos,
    by positivity, hFINALsub, ?_⟩
  intro g hg M hM0 hMb
  set domFINAL : Set ((ι → ℂ) × ℂ) :=
    polydiscWithRadii (0 : ι → ℂ) (fun _ => r₃) ×ˢ ball (0 : ℂ) R₂ with hdomFINALdef
  set sSeq := fun k => picardApprox d (fun _ => r₃) R₂ (fun _ => hr₃pos) hR₂pos hh g hg hhFINAL k
    with hsSeqdef
  set B : ℝ := ((d + 1 : ℕ) : ℝ) / R₂ ^ d * M with hBdef
  obtain ⟨S, hSanalytic, hSbound⟩ := exists_tendstoUniformlyOn_picardApprox d (fun _ => r₃) R₂
    (fun _ => hr₃pos) hR₂pos hh g hg hhFINAL M hM0 hMb hhboundFINAL
  set rFun : (ι → ℂ) × ℂ → ℂ := fun z => g z - hh z * S z - z.2 ^ d * S z with hrFundef
  obtain ⟨aOut, haFINAL, hkey⟩ := exists_weierstrassRemainder_eq_of_tendstoUniformlyOn_picardApprox
    d (fun _ => r₃) R₂ (fun _ => hr₃pos) hR₂pos hh g hg hhFINAL hhboundFINAL M hM0 S
    hSanalytic.differentiableOn hSbound
  -- Step 9: assemble q, and the division identity.
  have hf1ne0FINAL : ∀ z ∈ domFINAL, f1 z ≠ 0 := fun z hz => hf1ne0' z (hFINALsubε₁ hz)
  have hf_eq2 : ∀ z ∈ domFINAL, f z = f1 z * (z.2 ^ d + hh z) := by
    intro z hz
    have hz0 : z ∈ polydiscWithRadii (0 : ι → ℂ) (fun _ => ε₀) ×ˢ ball (0 : ℂ) ε₀ :=
      hε₁ε₀ (hFINALsubε₁ hz)
    have h1 : f z = f1 z * z.2 ^ d + weierstrassRemainder c z := hfdiv.eq hz0
    have h2 : weierstrassRemainder c z = hh z * f1 z := by
      show weierstrassRemainder c z = weierstrassRemainder c z / f1 z * f1 z
      rw [div_mul_cancel₀ _ (hf1ne0FINAL z hz)]
    rw [h2] at h1
    rw [h1]; ring
  set q : (ι → ℂ) × ℂ → ℂ := fun z => S z / f1 z with hqdef
  have hf1FINAL : DifferentiableOn ℂ f1 domFINAL :=
    hfdiv.quotient_holomorphic.mono (hFINALsubε₁.trans hε₁ε₀)
  have hqDiff : DifferentiableOn ℂ q domFINAL := by
    show DifferentiableOn ℂ (fun z => S z / f1 z) domFINAL
    simp_rw [div_eq_mul_inv]
    exact hSanalytic.differentiableOn.mul (hf1FINAL.inv hf1ne0FINAL)
  have hDivEq : EqOn g (fun z => q z * f z + weierstrassRemainder aOut z) domFINAL := by
    intro z hz
    have hkz : g z - hh z * S z - z.2 ^ d * S z = weierstrassRemainder aOut z := by
      simpa using hkey z.1 hz.1 z.2 hz.2
    show g z = q z * f z + weierstrassRemainder aOut z
    have heqf := hf_eq2 z hz
    have hqf : q z * f z = S z * (z.2 ^ d + hh z) := by
      show (S z / f1 z) * f z = _
      rw [heqf]
      field_simp [hf1ne0FINAL z hz]
    rw [hqf]
    linear_combination hkz
  have hdomFINALsubK : domFINAL ⊆ K := by
    apply Set.prod_mono
    · intro w hw
      exact mem_closedPolydiscWithRadii.mpr fun i =>
        (mem_polydiscWithRadii.mp hw i).le.trans hr₃ε₁
    · exact ball_subset_closedBall
  refine ⟨q, aOut, ⟨hqDiff, haFINAL, hDivEq⟩, ?_, ?_⟩
  · intro z hz
    have hS0eq : (sSeq 0).1 = 0 := rfl
    have hb0 := hSbound 0 z hz
    rw [hS0eq] at hb0
    have hSb : ‖S z‖ ≤ 2 * B := by
      have hthis : ‖(0:ℂ) - S z‖ ≤ B * (1/2)^0 / (1 - 1/2) := hb0
      rw [zero_sub, norm_neg] at hthis
      norm_num at hthis
      linarith
    have hf1ge : δ ≤ ‖f1 z‖ := hδle _ (hdomFINALsubK hz)
    have hf1pos' : 0 < ‖f1 z‖ := hδpos.trans_le hf1ge
    show ‖S z / f1 z‖ ≤ 2 * ((d:ℝ) + 1) / (R₂ ^ d * δ) * M
    rw [norm_div]
    calc ‖S z‖ / ‖f1 z‖ ≤ (2 * B) / ‖f1 z‖ := div_le_div_of_nonneg_right hSb hf1pos'.le
      _ ≤ (2 * B) / δ := div_le_div_of_nonneg_left (by positivity) hδpos hf1ge
      _ = 2 * ((d:ℝ) + 1) / (R₂ ^ d * δ) * M := by
          rw [hBdef]; push_cast; field_simp
  · intro q' a' hdiv'
    -- Find an actual small polydisc-ball neighborhood of 0 where q', a' are analytic,
    -- the germ equation holds, and which is contained in domFINAL.
    have hevQ : ∀ᶠ z in 𝓝 (0 : (ι → ℂ) × ℂ),
        AnalyticAt ℂ q' z ∧ g z = q' z * f z + weierstrassRemainder a' z :=
      hdiv'.quotient_analytic.eventually_analyticAt.and hdiv'.eq
    obtain ⟨V', hV'ev, hV'open, hV'0⟩ := _root_.eventually_nhds_iff.mp hevQ
    have hevAall : ∀ᶠ w in 𝓝 (0 : ι → ℂ), ∀ j, AnalyticAt ℂ (a' j) w :=
      Filter.eventually_all.mpr fun j => (hdiv'.coefficient_analytic j).eventually_analyticAt
    obtain ⟨W', hW'ev, hW'open, hW'0⟩ := _root_.eventually_nhds_iff.mp hevAall
    have h00 : (0 : (ι → ℂ) × ℂ) ∈ domFINAL :=
      ⟨mem_polydiscWithRadii.mpr fun i => by simpa using hr₃pos, mem_ball_self hR₂pos⟩
    obtain ⟨ρ₀, hρ₀pos, hρ₀sub⟩ := exists_polydisc_ball_subset
      (hV'open.inter ((hW'open.prod isOpen_univ).inter
        ((isOpen_polydiscWithRadii (0 : ι → ℂ) (fun _ => r₃)).prod isOpen_ball)))
      ⟨hV'0, ⟨hW'0, trivial⟩, h00⟩
    -- Shrink once more so the same radius can be used for both containment and contraction.
    obtain ⟨ρ, hρpos, hρρ₀⟩ := exists_between hρ₀pos
    have hρsub : polydiscWithRadii (0 : ι → ℂ) (fun _ => ρ) ×ˢ ball (0 : ℂ) ρ ⊆
        V' ∩ ((W' ×ˢ (univ : Set ℂ)) ∩ (polydiscWithRadii (0 : ι → ℂ) (fun _ => r₃) ×ˢ ball (0 : ℂ) R₂)) :=
      (Set.prod_mono (polydiscWithRadii_mono _ (fun _ => hρρ₀.le)) (ball_subset_ball hρρ₀.le)).trans
        hρ₀sub
    -- A fresh contraction bound for h on a possibly smaller polydisc-ball of radius ρ.
    set εc₃ : ℝ := δ * ρ ^ d / (2 * (d + 1) * (d + 1) * (max ρ 1) ^ d) with hεc₃def
    have hM3pos : (0:ℝ) < max ρ 1 := lt_max_of_lt_right one_pos
    have hεc₃pos : 0 < εc₃ := by rw [hεc₃def]; positivity
    have hcjev₃ : ∀ j : Fin d, ∀ᶠ w in 𝓝 (0 : ι → ℂ), ‖c j w‖ < εc₃ := fun j => by
      have hz : Tendsto (fun w => ‖c j w‖) (𝓝 0) (𝓝 0) := by simpa using (hcj0' j).norm
      exact hz.eventually_lt_const hεc₃pos
    have hcjall₃ : ∀ᶠ w in 𝓝 (0 : ι → ℂ), ∀ j : Fin d, ‖c j w‖ < εc₃ :=
      eventually_all.mpr hcjev₃
    obtain ⟨r₄, hr₄pos, hr₄sub⟩ := Metric.eventually_nhds_iff.mp hcjall₃
    set r₅ : ℝ := min r₄ ρ with hr₅def
    have hr₅pos : 0 < r₅ := lt_min hr₄pos hρpos
    have hr₅r₄ : r₅ ≤ r₄ := min_le_left _ _
    have hr₅ρ : r₅ ≤ ρ := min_le_right _ _
    have hRj_le3 : ∀ j < d, ρ ^ j ≤ (max ρ 1) ^ d := by
      intro j hj
      rcases le_total 1 ρ with hρ1 | hρ1
      · calc ρ ^ j ≤ ρ ^ d := pow_le_pow_right₀ hρ1 hj.le
          _ ≤ (max ρ 1) ^ d := pow_le_pow_left₀ hρpos.le (le_max_left _ _) d
      · calc ρ ^ j ≤ 1 ^ j := pow_le_pow_left₀ hρpos.le hρ1 j
          _ = 1 := one_pow j
          _ ≤ (max ρ 1) ^ d := one_le_pow₀ (le_max_right _ _)
    have hdomsub5 : polydiscWithRadii (0 : ι → ℂ) (fun _ => r₅) ×ˢ ball (0 : ℂ) ρ ⊆ domFINAL := by
      intro z hz
      have hz' : z ∈ polydiscWithRadii (0 : ι → ℂ) (fun _ => ρ) ×ˢ ball (0 : ℂ) ρ :=
        ⟨mem_polydiscWithRadii.mpr fun i => (mem_polydiscWithRadii.mp hz.1 i).trans_le hr₅ρ, hz.2⟩
      exact (hρsub hz').2.2
    have hhb3 : ∀ z ∈ polydiscWithRadii (0 : ι → ℂ) (fun _ => r₅) ×ˢ ball (0 : ℂ) ρ,
        ‖hh z‖ ≤ ρ ^ d / (2 * (d + 1)) := by
      rintro ⟨w, ζ⟩ ⟨hw, hζ⟩
      have hwr5 : ‖w‖ < r₅ := by simpa [pi_norm_lt_iff hr₅pos, mem_polydiscWithRadii] using hw
      have hwr4 : dist w (0 : ι → ℂ) < r₄ := by
        rw [dist_zero_right]; exact hwr5.trans_le hr₅r₄
      have hcbound : ∀ j : Fin d, ‖c j w‖ < εc₃ := hr₄sub hwr4
      have hζρ : ‖ζ‖ < ρ := by simpa [mem_ball, dist_zero_right] using hζ
      have hnum : ‖weierstrassRemainder c (w, ζ)‖ ≤ (d : ℝ) * εc₃ * (max ρ 1) ^ d := by
        unfold weierstrassRemainder
        calc ‖∑ j : Fin d, c j w * ζ ^ (j : ℕ)‖ ≤ ∑ j : Fin d, ‖c j w * ζ ^ (j:ℕ)‖ :=
              norm_sum_le _ _
          _ = ∑ j : Fin d, ‖c j w‖ * ‖ζ‖ ^ (j:ℕ) := by simp [norm_pow]
          _ ≤ ∑ _j : Fin d, εc₃ * (max ρ 1) ^ d := by
                apply Finset.sum_le_sum; intro j _
                exact mul_le_mul (hcbound j).le
                  (le_trans (pow_le_pow_left₀ (norm_nonneg _) hζρ.le (j:ℕ)) (hRj_le3 (j:ℕ) j.isLt))
                  (by positivity) (by positivity)
          _ = (d:ℝ) * εc₃ * (max ρ 1) ^ d := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                ring
      have hwK : (w, ζ) ∈ K := hdomFINALsubK (hdomsub5 ⟨hw, hζ⟩)
      have hf1lb3 : δ ≤ ‖f1 (w, ζ)‖ := hδle _ hwK
      have hf1pos3 : 0 < ‖f1 (w, ζ)‖ := hδpos.trans_le hf1lb3
      show ‖weierstrassRemainder c (w, ζ) / f1 (w, ζ)‖ ≤ _
      rw [norm_div]
      calc ‖weierstrassRemainder c (w, ζ)‖ / ‖f1 (w, ζ)‖
          ≤ ((d:ℝ) * εc₃ * (max ρ 1) ^ d) / ‖f1 (w, ζ)‖ :=
            div_le_div_of_nonneg_right hnum hf1pos3.le
        _ ≤ ((d:ℝ) * εc₃ * (max ρ 1) ^ d) / δ := div_le_div_of_nonneg_left (by positivity) hδpos hf1lb3
        _ = (d:ℝ) * ρ ^ d / (2 * (d + 1) * (d + 1)) := by rw [hεc₃def]; field_simp
        _ ≤ ρ ^ d / (2 * (d + 1)) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [pow_pos hρpos d]
    set dom5 : Set ((ι → ℂ) × ℂ) := polydiscWithRadii (0 : ι → ℂ) (fun _ => r₅) ×ˢ ball (0 : ℂ) ρ
      with hdom5def
    have hz'of : ∀ z ∈ dom5, z ∈ polydiscWithRadii (0 : ι → ℂ) (fun _ => ρ) ×ˢ ball (0 : ℂ) ρ :=
      fun z hz => ⟨mem_polydiscWithRadii.mpr fun i =>
        (mem_polydiscWithRadii.mp hz.1 i).trans_le hr₅ρ, hz.2⟩
    have hVmem : ∀ z ∈ dom5, z ∈ V' := fun z hz => (hρsub (hz'of z hz)).1
    have hWmem : ∀ w ∈ polydiscWithRadii (0 : ι → ℂ) (fun _ => r₅), w ∈ W' := fun w hw =>
      ((hρsub (hz'of (w, 0) ⟨hw, mem_ball_self hρpos⟩)).2.1 : (w, (0:ℂ)) ∈ W' ×ˢ (univ : Set ℂ)).1
    have hq'Adiff : DifferentiableOn ℂ q' dom5 := fun z hz =>
      ((hV'ev z (hVmem z hz)).1).differentiableAt.differentiableWithinAt
    have ha'Adiff : ∀ j, DifferentiableOn ℂ (a' j) (polydiscWithRadii (0 : ι → ℂ) (fun _ => r₅)) :=
      fun j w hw => ((hW'ev w (hWmem w hw)) j).differentiableAt.differentiableWithinAt
    have hf1diff5 : DifferentiableOn ℂ f1 dom5 := hf1FINAL.mono hdomsub5
    set s' : (ι → ℂ) × ℂ → ℂ := fun z => q' z * f1 z with hs'def
    have hs'diff : DifferentiableOn ℂ s' dom5 := hq'Adiff.mul hf1diff5
    have hhFINAL5 : DifferentiableOn ℂ hh dom5 := hhFINAL.mono hdomsub5
    have hpoly53 : polydiscWithRadii (0 : ι → ℂ) (fun _ => r₅) ⊆
        polydiscWithRadii (0 : ι → ℂ) (fun _ => r₃) :=
      fun w hw => (hdomsub5 (⟨hw, mem_ball_self hρpos⟩ : (w, (0:ℂ)) ∈ dom5)).1
    have hdiv' : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (g - hh * s') s' a'
        (polydiscWithRadii (0 : ι → ℂ) (fun _ => r₅)) ρ := by
      refine ⟨hs'diff, ha'Adiff, ?_⟩
      intro z hz
      have heqz : g z = q' z * f z + weierstrassRemainder a' z := (hV'ev z (hVmem z hz)).2
      have heqf5 : f z = f1 z * (z.2 ^ d + hh z) := hf_eq2 z (hdomsub5 hz)
      show g z - hh z * s' z = s' z * z.2 ^ d + weierstrassRemainder a' z
      simp only [hs'def]
      rw [heqz, heqf5]
      ring
    have hSdiv : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (g - hh * S) S aOut
        (polydiscWithRadii (0 : ι → ℂ) (fun _ => r₅)) ρ := by
      refine ⟨hSanalytic.differentiableOn.mono hdomsub5, fun j => (haFINAL j).mono hpoly53, ?_⟩
      intro z hz
      have hthis : g z = q z * f z + weierstrassRemainder aOut z := hDivEq (hdomsub5 hz)
      show g z - hh z * S z = S z * z.2 ^ d + weierstrassRemainder aOut z
      have hqf : q z * f z = S z * (z.2 ^ d + hh z) := by
        have heqf5 : f z = f1 z * (z.2 ^ d + hh z) := hf_eq2 z (hdomsub5 hz)
        show (S z / f1 z) * f z = _
        rw [heqf5]
        field_simp [hf1ne0FINAL z (hdomsub5 hz)]
      rw [hqf] at hthis
      linear_combination hthis
    -- Since ρ < ρ₀, the closed polydisc-ball of radius ρ still lies in `V' ∩ W' ∩ domFINAL`,
    -- giving compactness for a bound on `S - s'` without any further shrinking.
    have hclosedsub : closedPolydiscWithRadii (0 : ι → ℂ) (fun _ => ρ) ×ˢ closedBall (0 : ℂ) ρ ⊆
        V' ∩ ((W' ×ˢ (univ : Set ℂ)) ∩ (polydiscWithRadii (0 : ι → ℂ) (fun _ => r₃) ×ˢ ball (0 : ℂ) R₂)) :=
      (Set.prod_mono (closedPolydiscWithRadii_subset_polydiscWithRadii _ (fun _ => hρρ₀))
        (closedBall_subset_ball hρρ₀)).trans hρ₀sub
    have hVmemC : ∀ z ∈ closedPolydiscWithRadii (0 : ι → ℂ) (fun _ => ρ) ×ˢ closedBall (0 : ℂ) ρ,
        z ∈ V' := fun z hz => (hclosedsub hz).1
    have hf1diffC : DifferentiableOn ℂ f1
        (closedPolydiscWithRadii (0 : ι → ℂ) (fun _ => ρ) ×ˢ closedBall (0 : ℂ) ρ) :=
      hf1FINAL.mono (fun z hz => (hclosedsub hz).2.2)
    have hq'diffC : DifferentiableOn ℂ q'
        (closedPolydiscWithRadii (0 : ι → ℂ) (fun _ => ρ) ×ˢ closedBall (0 : ℂ) ρ) := fun z hz =>
      ((hV'ev z (hVmemC z hz)).1).differentiableAt.differentiableWithinAt
    have hMbound : ∃ M3 : ℝ, 0 ≤ M3 ∧ ∀ z ∈ dom5, ‖S z - s' z‖ ≤ M3 := by
      have hScont : ContinuousOn S
          (closedPolydiscWithRadii (0 : ι → ℂ) (fun _ => ρ) ×ˢ closedBall (0 : ℂ) ρ) :=
        (hSanalytic.differentiableOn.mono (fun z hz => (hclosedsub hz).2.2)).continuousOn
      have hs'cont : ContinuousOn s'
          (closedPolydiscWithRadii (0 : ι → ℂ) (fun _ => ρ) ×ˢ closedBall (0 : ℂ) ρ) :=
        (hq'diffC.mul hf1diffC).continuousOn
      have hcompact : IsCompact (closedPolydiscWithRadii (0 : ι → ℂ) (fun _ => ρ) ×ˢ
          closedBall (0 : ℂ) ρ) :=
        (isCompact_closedPolydiscWithRadii _ _).prod (isCompact_closedBall _ _)
      obtain ⟨C1, hC1⟩ := hcompact.bddAbove_image (hScont.sub hs'cont).norm
      refine ⟨max C1 0, le_max_right _ _, fun z hz => (hC1 ⟨z, ?_, rfl⟩).trans (le_max_left _ _)⟩
      refine ⟨mem_closedPolydiscWithRadii.mpr fun i => ?_, mem_closedBall_iff_norm.mpr ?_⟩
      · show dist (z.1 i) (0 : ℂ) ≤ ρ
        rw [dist_zero_right]
        have : dist (z.1 i) ((0 : ι → ℂ) i) < r₅ := mem_polydiscWithRadii.mp hz.1 i
        rw [Pi.zero_apply, dist_zero_right] at this
        exact this.le.trans hr₅ρ
      · rw [sub_zero]; exact (mem_ball_zero_iff.mp hz.2).le
    obtain ⟨M3, hM30, hM3b⟩ := hMbound
    obtain ⟨hSeqs', haOuteqa'⟩ := eqOn_of_isWeierstrassDivisionOn_selfPerturbed
      (fun _ => hr₅pos) hρpos hh g S s' aOut a' hhFINAL5 hhb3 hSdiv hdiv' M3 hM30 hM3b
    have hqeqq' : EqOn q q' dom5 := by
      intro z hz
      show S z / f1 z = q' z
      rw [hSeqs' hz]
      show s' z / f1 z = q' z
      rw [hs'def]
      exact mul_div_cancel_right₀ _ (hf1ne0FINAL z (hdomsub5 hz))
    have h05 : (0 : (ι → ℂ) × ℂ) ∈ dom5 :=
      ⟨mem_polydiscWithRadii.mpr fun i => by simpa using hr₅pos, mem_ball_self hρpos⟩
    have hnbhd : dom5 ∈ 𝓝 (0 : (ι → ℂ) × ℂ) :=
      (isOpen_polydiscWithRadii _ _ |>.prod isOpen_ball).mem_nhds h05
    refine ⟨Filter.eventuallyEq_of_mem hnbhd hqeqq', fun j => Filter.eventuallyEq_of_mem
      ((isOpen_polydiscWithRadii (0 : ι → ℂ) (fun _ => r₅)).mem_nhds
        (mem_polydiscWithRadii.mpr fun i => by simpa using hr₅pos)) (haOuteqa' j)⟩

/-- Analytic Weierstrass division for arbitrary numerator germs. No boundedness assumption
is needed because the representatives can be restricted to a smaller neighborhood.
This proof depends on the pending uniform division theorem. -/
theorem weierstrass_division_at {d : ℕ} {f g : (ι → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    ∃ (q : (ι → ℂ) × ℂ → ℂ) (a : Fin d → (ι → ℂ) → ℂ),
      IsWeierstrassDivisionAt f g q a ∧
      ∀ q' a', IsWeierstrassDivisionAt f g q' a' →
        q =ᶠ[𝓝 0] q' ∧ ∀ j, a j =ᶠ[𝓝 0] a' j := by
  have hb : ∀ᶠ z in 𝓝 0, ‖g z‖ < ‖g 0‖ + 1 :=
    hg.continuousAt.norm.eventually_lt_const (lt_add_one _)
  obtain ⟨U, hsub, hU, h0⟩ := _root_.eventually_nhds_iff.mp
    (hf.eventually_analyticAt.and (hg.eventually_analyticAt.and hb))
  obtain ⟨r, R, C, hr, hR, _, hPU, hdiv⟩ :=
    weierstrass_division hU h0 (fun z hz => (hsub z hz).1.differentiableAt.differentiableWithinAt)
      horder
  obtain ⟨q, a, hqa, _, huniq⟩ := hdiv g
    (fun z hz => (hsub z (hPU hz)).2.1.differentiableAt.differentiableWithinAt)
    (‖g 0‖ + 1) (by positivity) (fun z hz => (hsub z (hPU hz)).2.2.le)
  refine ⟨q, a, hqa.at_zero (isOpen_polydiscWithRadii _ _) ?_ hR, huniq⟩
  simpa using hr

/-- Two local division decompositions agree as germs, including every remainder coefficient.
This is a consequence of the pending uniform division theorem. -/
theorem IsWeierstrassDivisionAt.unique {d : ℕ} {f g q q' : (ι → ℂ) × ℂ → ℂ}
    {a a' : Fin d → (ι → ℂ) → ℂ}
    (h : IsWeierstrassDivisionAt f g q a) (h' : IsWeierstrassDivisionAt f g q' a')
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    q =ᶠ[𝓝 0] q' ∧ ∀ j, a j =ᶠ[𝓝 0] a' j := by
  obtain ⟨q₀, a₀, _, hu⟩ := weierstrass_division_at hf hg horder
  exact ⟨(hu q a h).1.symm.trans (hu q' a' h').1,
    fun j => ((hu q a h).2 j).symm.trans ((hu q' a' h').2 j)⟩

/-- Local uniqueness extends to the whole product domain by the identity theorem.
In particular this gives uniqueness on the fixed polydisc in the bounded division theorem. -/
theorem IsWeierstrassDivisionOn.unique {d : ℕ} {f g q q' : (ι → ℂ) × ℂ → ℂ}
    {a a' : Fin d → (ι → ℂ) → ℂ} {V : Set (ι → ℂ)} {R : ℝ}
    (h : IsWeierstrassDivisionOn f g q a V R) (h' : IsWeierstrassDivisionOn f g q' a' V R)
    (hV : IsOpen V) (hconn : IsPreconnected V) (h0 : 0 ∈ V) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (V ×ˢ ball 0 R))
    (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R))
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    EqOn q q' (V ×ˢ ball 0 R) ∧ ∀ j, EqOn (a j) (a' j) V := by
  have hz : (0 : (ι → ℂ) × ℂ) ∈ V ×ˢ ball 0 R := ⟨h0, mem_ball_self hR⟩
  have ho : IsOpen (V ×ˢ ball (0 : ℂ) R) := hV.prod isOpen_ball
  obtain ⟨hq, ha⟩ := (h.at_zero hV h0 hR).unique (h'.at_zero hV h0 hR)
    ((hf.analyticOnNhd_finiteDimensional ho) _ hz)
    ((hg.analyticOnNhd_finiteDimensional ho) _ hz) horder
  exact ⟨eqOn_of_holomorphic_of_eventuallyEq ho
      (hconn.prod (convex_ball (0 : ℂ) R).isPreconnected)
      h.quotient_holomorphic h'.quotient_holomorphic hz hq,
    fun j => eqOn_of_holomorphic_of_eventuallyEq hV hconn
      (h.coefficient_holomorphic j) (h'.coefficient_holomorphic j) h0 (ha j)⟩

/-- Division transports along a continuous linear equivalence of the parameter space. -/
theorem IsWeierstrassDivisionAt.comp_equiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (φ : F ≃L[ℂ] E) {d : ℕ} {f g q : E × ℂ → ℂ} {a : Fin d → E → ℂ}
    (h : IsWeierstrassDivisionAt f g q a) :
    IsWeierstrassDivisionAt (fun z : F × ℂ => f (φ z.1, z.2)) (fun z : F × ℂ => g (φ z.1, z.2))
      (fun z : F × ℂ => q (φ z.1, z.2)) (fun j x => a j (φ x)) := by
  have hφ : AnalyticAt ℂ φ (0 : F) := φ.toContinuousLinearMap.analyticAt 0
  have hφmap : φ (0 : F) = 0 := φ.map_zero
  have hpair : AnalyticAt ℂ (fun z : F × ℂ => (φ z.1, z.2)) (0 : F × ℂ) :=
    (hφ.comp_of_eq analyticAt_fst rfl).prod analyticAt_snd
  have h0 : (fun z : F × ℂ => (φ z.1, z.2)) 0 = (0 : E × ℂ) := by simp [hφmap]
  have ht : Tendsto (fun z : F × ℂ => (φ z.1, z.2)) (𝓝 0) (𝓝 (0 : E × ℂ)) := by
    rw [← h0]; exact hpair.continuousAt.tendsto
  refine ⟨h.quotient_analytic.comp_of_eq hpair h0,
    fun j => (h.coefficient_analytic j).comp_of_eq hφ hφmap,
    (h.eq.comp_tendsto ht).mono fun z hz => by
      simpa [weierstrassRemainder] using hz⟩

/-- **Weierstrass division for analytic germs on any finite-dimensional parameter space.**
Obtained by transporting the coordinate version along a basis; no choice of coordinates
occurs in the statement. -/
theorem weierstrass_division_at_findim [FiniteDimensional ℂ E] {d : ℕ} {f g : E × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    ∃ (q : E × ℂ → ℂ) (a : Fin d → E → ℂ),
      IsWeierstrassDivisionAt f g q a ∧
      ∀ q' a', IsWeierstrassDivisionAt f g q' a' →
        q =ᶠ[𝓝 0] q' ∧ ∀ j, a j =ᶠ[𝓝 0] a' j := by
  set e := (Module.finBasis ℂ E).equivFunL with he_def
  set fg : (Fin (Module.finrank ℂ E) → ℂ) × ℂ → ℂ := fun z => f (e.symm z.1, z.2) with hfg_def
  set gg : (Fin (Module.finrank ℂ E) → ℂ) × ℂ → ℂ := fun z => g (e.symm z.1, z.2) with hgg_def
  have hfg0 : (fun w : ℂ => fg (0, w)) = fun w : ℂ => f (0, w) := by funext w; simp [hfg_def]
  have hfgan : AnalyticAt ℂ fg 0 :=
    hf.comp_of_eq (((e.symm.toContinuousLinearMap.analyticAt 0).comp_of_eq analyticAt_fst rfl).prod
      analyticAt_snd) (by simp)
  have hggan : AnalyticAt ℂ gg 0 :=
    hg.comp_of_eq (((e.symm.toContinuousLinearMap.analyticAt 0).comp_of_eq analyticAt_fst rfl).prod
      analyticAt_snd) (by simp)
  have hfgorder : analyticOrderAt (fun w : ℂ => fg (0, w)) 0 = d := by rw [hfg0]; exact horder
  obtain ⟨q, a, Hq, huniqq⟩ := weierstrass_division_at hfgan hggan hfgorder
  have hf_eq : f = fun z : E × ℂ => fg (e z.1, z.2) := by funext z; simp [hfg_def]
  have hg_eq : g = fun z : E × ℂ => gg (e z.1, z.2) := by funext z; simp [hgg_def]
  have Hf : IsWeierstrassDivisionAt f g (fun z : E × ℂ => q (e z.1, z.2))
      (fun j x => a j (e x)) := by
    rw [hf_eq, hg_eq]; exact Hq.comp_equiv e
  refine ⟨_, _, Hf, fun q' a' Hq' => ?_⟩
  have Hq'' : IsWeierstrassDivisionAt fg gg (fun z => q' (e.symm z.1, z.2))
      (fun j x => a' j (e.symm x)) := by
    rw [hfg_def, hgg_def]; exact Hq'.comp_equiv e.symm
  obtain ⟨huq, hab⟩ := huniqq _ _ Hq''
  have ht : Tendsto (fun z : E × ℂ => (e z.1, z.2)) (𝓝 0)
      (𝓝 (0 : (Fin (Module.finrank ℂ E) → ℂ) × ℂ)) := by
    have h0 : (fun z : E × ℂ => (e z.1, z.2)) 0 = (0 : (Fin (Module.finrank ℂ E) → ℂ) × ℂ) := by
      simp
    rw [← h0]
    exact (((e.toContinuousLinearMap.analyticAt 0).comp_of_eq analyticAt_fst rfl).prod
      analyticAt_snd).continuousAt.tendsto
  refine ⟨(huq.comp_tendsto ht).mono fun z hz => ?_, fun j => ?_⟩
  · simpa using hz
  · have htj : Tendsto e (𝓝 (0 : E)) (𝓝 (0 : Fin (Module.finrank ℂ E) → ℂ)) := by
      simpa using (e.toContinuousLinearMap.analyticAt 0).continuousAt.tendsto
    exact ((hab j).comp_tendsto htj).mono fun x hx => by simpa using hx

/-- A local division identity is an identity in the project's ring of analytic germs. -/
theorem IsWeierstrassDivisionAt.germ_eq {d : ℕ} {f g q : E × ℂ → ℂ}
    {a : Fin d → E → ℂ} (h : IsWeierstrassDivisionAt f g q a)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    AnalyticGerm.ofAnalyticAt g hg =
      AnalyticGerm.ofAnalyticAt q h.quotient_analytic * AnalyticGerm.ofAnalyticAt f hf +
      AnalyticGerm.ofAnalyticAt (weierstrassRemainder a)
        (analyticAt_weierstrassRemainder h.coefficient_analytic) := by
  apply Subtype.ext
  exact Germ.coe_eq.mpr h.eq

end SeveralComplexVariables
