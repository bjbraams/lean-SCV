/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.Analyticity
public import SeveralComplexVariables.Polydisc

/-!
# Weierstrass division predicates

A remainder of degree less than `d` is represented by its `Fin d` coefficient
functions on the parameter space. We define division at the origin and on a
product domain, prove the elementary order-zero case, and pass between local
division and division on a sufficiently small polydisc. The case `d = 0` and
empty finite parameter index types are included.

The existence theorem for a general divisor is in
`SeveralComplexVariables.WeierstrassDivision`.
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

/-- The Weierstrass remainder is linear (here, additive) in its coefficient tuple. -/
theorem weierstrassRemainder_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {d : ℕ} (a b : Fin d → E → ℂ) (z : E × ℂ) :
    weierstrassRemainder a z - weierstrassRemainder b z =
      weierstrassRemainder (fun j => a j - b j) z := by
  unfold weierstrassRemainder
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp; ring

variable {ι : Type*} [Fintype ι]

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

/-- A germ division identity holds as a holomorphic division on a sufficiently
small polydisc-ball inside any prescribed open neighborhood of the origin. -/
theorem IsWeierstrassDivisionAt.exists_divisionOn {d : ℕ}
    {f g q : (ι → ℂ) × ℂ → ℂ} {a : Fin d → (ι → ℂ) → ℂ}
    (h : IsWeierstrassDivisionAt f g q a)
    {U : Set ((ι → ℂ) × ℂ)} (hU : IsOpen U) (h0 : 0 ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ polydiscWithRadii 0 (fun _ => ρ) ×ˢ ball 0 ρ ⊆ U ∧
      IsWeierstrassDivisionOn f g q a (polydiscWithRadii 0 (fun _ => ρ)) ρ := by
  obtain ⟨V, hV, hVo, hV0⟩ := _root_.eventually_nhds_iff.mp
    (h.quotient_analytic.eventually_analyticAt.and h.eq)
  obtain ⟨W, hW, hWo, hW0⟩ := _root_.eventually_nhds_iff.mp
    (Filter.eventually_all.mpr fun j => (h.coefficient_analytic j).eventually_analyticAt)
  obtain ⟨ρ, hρ, hsub⟩ := exists_polydisc_ball_subset
    (hVo.inter ((hWo.prod isOpen_univ).inter hU)) ⟨hV0, ⟨hW0, trivial⟩, h0⟩
  refine ⟨ρ, hρ, fun z hz => (hsub hz).2.2, ?_, ?_, ?_⟩
  · intro z hz
    exact (hV z (hsub hz).1).1.differentiableAt.differentiableWithinAt
  · intro j w hw
    exact (hW w (hsub (show (w, (0 : ℂ)) ∈ _ from ⟨hw, mem_ball_self hρ⟩)).2.1.1 j).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (hV z (hsub hz).1).2

end SeveralComplexVariables
