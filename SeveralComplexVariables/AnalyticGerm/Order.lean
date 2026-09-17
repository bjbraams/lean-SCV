/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.AnalyticGerm.CoordinateChange
public import SeveralComplexVariables.PolydiscTaylor
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# Total order of analytic germs

The Taylor series of a scalar germ in finite complex coordinates is a Mathlib
`MvPowerSeries`. Its `order` is the least total degree with a nonzero coefficient,
with infinity for the zero series. This is different from order along a chosen axis.
The empty coordinate type `Fin 0` is included.

The basic order characterization and sum rules use Mathlib directly. Taylor uniqueness
and the infinite-order criterion follow from the convergent polydisc expansion.
The product rule and coordinate invariance remain pending. Exact total order along
a last-axis after a linear change follows Suwa, Lemma 1.2: the leading homogeneous
part is a nonzero polynomial, hence nonvanishing at some point, which is then sent
to the last basis vector. These are classical local analytic facts, as in Suwa §1.4,
rather than a development of local algebra.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped Classical Topology

namespace SeveralComplexVariables.AnalyticGerm

variable {n m : ℕ} {x : Fin n → ℂ}

/-- The multivariate Taylor series depends only on the function germ. -/
theorem holomorphicTaylorSeries_congr {f g : (Fin n → ℂ) → ℂ}
    (h : f =ᶠ[𝓝 x] g) : holomorphicTaylorSeries f x = holomorphicTaylorSeries g x := by
  obtain ⟨U, hU, ho, hx⟩ := _root_.eventually_nhds_iff.mp h
  funext k
  dsimp [holomorphicTaylorSeries, multiIndexDeriv]
  rw [iteratedPartialDeriv_congrOn ho hU (multiIndexList k) hx]

/-- Taylor series of a scalar analytic germ, independent of its representative. -/
def taylorSeries (f : AnalyticGerm x) : MvPowerSeries (Fin n) ℂ :=
  f.val.liftOn (fun g => holomorphicTaylorSeries g x)
    (fun _ _ h => holomorphicTaylorSeries_congr h)

/-- Taylor series of a represented germ is the existing Taylor series of the function. -/
@[simp] theorem taylorSeries_ofAnalyticAt (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f x) :
    taylorSeries (ofAnalyticAt f hf) = holomorphicTaylorSeries f x := rfl

/-- Taylor series preserve addition of analytic germs. -/
theorem taylorSeries_add (f g : AnalyticGerm x) :
    taylorSeries (f + g) = taylorSeries f + taylorSeries g := by
  obtain ⟨f, hf, rfl⟩ := exists_rep f
  obtain ⟨g, hg, rfl⟩ := exists_rep g
  obtain ⟨U, hsub, hU, hx⟩ := _root_.eventually_nhds_iff.mp
    (hf.eventually_analyticAt.and hg.eventually_analyticAt)
  have hA : ∀ b ∈ (Finset.univ : Finset Bool),
      AnalyticOnNhd ℂ (if b then f else g) U := by
    intro b _ z hz
    cases b
    · exact (hsub z hz).2
    · exact (hsub z hz).1
  change holomorphicTaylorSeries (f + g) x =
    holomorphicTaylorSeries f x + holomorphicTaylorSeries g x
  funext k
  have hD : iteratedPartialDeriv (multiIndexList k) (f + g) x =
      iteratedPartialDeriv (multiIndexList k) f x +
        iteratedPartialDeriv (multiIndexList k) g x := by
    simpa [Fintype.sum_bool, Pi.add_def] using
      (iteratedPartialDeriv_finset_sum Finset.univ hA hU (multiIndexList k) hx)
  change (∏ i, (k i).factorial : ℂ)⁻¹ * iteratedPartialDeriv (multiIndexList k) (f + g) x =
    (∏ i, (k i).factorial : ℂ)⁻¹ * iteratedPartialDeriv (multiIndexList k) f x +
    (∏ i, (k i).factorial : ℂ)⁻¹ * iteratedPartialDeriv (multiIndexList k) g x
  rw [hD, mul_add]

/-- The zero germ has zero Taylor series, including in dimension zero. -/
@[simp] theorem taylorSeries_zero : taylorSeries (0 : AnalyticGerm x) = 0 := by
  have hz : ∀ l : List (Fin n), iteratedPartialDeriv l (0 : (Fin n → ℂ) → ℂ) = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
        change partialDeriv i (iteratedPartialDeriv l 0) = 0
        rw [ih]
        funext z
        simp [partialDeriv]
  change holomorphicTaylorSeries (0 : (Fin n → ℂ) → ℂ) x = 0
  funext k
  change holomorphicTaylorSeries (0 : (Fin n → ℂ) → ℂ) x k = 0
  simp [holomorphicTaylorSeries, multiIndexDeriv, hz]

/-- Total order of vanishing: the least total degree in the germ's Taylor series. -/
def order (f : AnalyticGerm x) : ℕ∞ := (taylorSeries f).order

/-- The total order is computed by Mathlib's multivariate power-series order. -/
theorem order_eq_taylorSeries_order (f : AnalyticGerm x) :
    order f = (taylorSeries f).order := rfl

/-- The constant Taylor coefficient is evaluation at the base point. -/
@[simp] theorem constantCoeff_taylorSeries (f : AnalyticGerm x) :
    (taylorSeries f).constantCoeff = eval x f := by
  obtain ⟨g, hg, rfl⟩ := exists_rep f
  change holomorphicTaylorSeries g x 0 = g x
  simp [holomorphicTaylorSeries, multiIndexDeriv, multiIndexList, iteratedPartialDeriv]

/-- A germ has order zero exactly when it is a unit. -/
@[simp] theorem order_eq_zero_iff (f : AnalyticGerm x) : order f = 0 ↔ IsUnit f := by
  rw [isUnit_iff, order]
  have h := MvPowerSeries.order_ne_zero_iff_constCoeff_eq_zero (f := taylorSeries f)
  simpa using not_congr h

/-- The zero germ has infinite total order. -/
@[simp] theorem order_zero : order (0 : AnalyticGerm x) = ⊤ := by
  simp [order]

/-- Distinct orders prevent cancellation of the leading terms of a sum. -/
theorem order_add_of_ne {f g : AnalyticGerm x} (h : order f ≠ order g) :
    order (f + g) = min (order f) (order g) := by
  simpa only [order, taylorSeries_add] using MvPowerSeries.order_add_of_order_ne h

/-- A scalar analytic germ is determined to be zero by its Taylor coefficients.
The proof uses the convergent polydisc Taylor expansion, including dimension zero. -/
@[simp] theorem taylorSeries_eq_zero_iff (f : AnalyticGerm x) :
    taylorSeries f = 0 ↔ f = 0 := by
  classical
  constructor
  · intro hzero
    obtain ⟨g, hg, rfl⟩ := exists_rep f
    change holomorphicTaylorSeries g x = 0 at hzero
    have hb : ∀ᶠ z in 𝓝 x, ‖g z‖ < ‖g x‖ + 1 :=
      hg.continuousAt.norm.eventually_lt_const (by linarith)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hg.eventually_analyticAt.and hb)
    have hr₂ : 0 < r / 2 := half_pos hr
    have hsub : closedPolydiscWithRadii x (fun _ => r / 2) ⊆ ball x r := by
      rw [closedPolydiscWithRadii_const, closedPolydisc_eq_closedBall hr₂.le]
      exact closedBall_subset_ball (half_lt_self hr)
    have hA : AnalyticOnNhd ℂ g (closedPolydiscWithRadii x (fun _ => r / 2)) :=
      fun z hz => (hball (hsub hz)).1
    have hslice : ∀ z ∈ closedPolydiscWithRadii x (fun _ => r / 2), ∀ i,
        AnalyticAt ℂ (fun w => g (Function.update z i w)) (z i) := by
      intro z hz i
      convert hA.analyticAt_update hz i using 1
      funext w
      congr 1
      funext j
      by_cases hj : j = i
      · subst j; simp
      · simp [Function.update, hj]
    have hcoeff : ∀ m : Fin n → ℕ,
        polydiscCauchyCoeffWithRadii g x (fun _ => r / 2) m = 0 := by
      intro m
      simpa only [hzero, MvPowerSeries.coeff_zero, Finsupp.coe_equivFunOnFinite_symm] using
        (coeff_holomorphicTaylorSeries (fun _ => hr₂) hA.continuousOn hslice
          (Finsupp.equivFunOnFinite.symm m)).symm
    have he : g =ᶠ[𝓝 x] 0 := by
      filter_upwards [ball_mem_nhds x hr₂] with z hz
      have hh : ∀ i, ‖(z - x) i‖ < r / 2 := by
        intro i
        exact lt_of_le_of_lt (norm_le_pi_norm (z - x) i)
          (by simpa only [mem_ball, dist_eq_norm] using hz)
      have hsum := hasSum_polydiscTaylor (fun _ => hr₂) hh hA.continuousOn hslice
        (fun z hz => (hball (hsub hz)).2.le)
      have hxz : x + (z - x) = z := by abel
      have hsum0 : HasSum (fun _ : Fin n → ℕ => (0 : ℂ)) (g z) := by
        simpa only [hcoeff, smul_zero, hxz] using hsum
      exact hsum0.unique hasSum_zero
    exact Subtype.ext (Germ.coe_eq.mpr he)
  · rintro rfl
    exact taylorSeries_zero

/-- The multivariate Taylor-series map is injective on analytic germs. -/
theorem taylorSeries_injective : Function.Injective (taylorSeries (x := x)) := by
  let T : AnalyticGerm x →+ MvPowerSeries (Fin n) ℂ :=
    { toFun := taylorSeries
      map_zero' := taylorSeries_zero
      map_add' := taylorSeries_add }
  intro f g h
  have hs : taylorSeries (f - g) = 0 := by
    change T (f - g) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr h
  exact sub_eq_zero.mp ((taylorSeries_eq_zero_iff _).mp hs)

/-- Infinite order is equivalent to being the zero germ, by uniqueness of the convergent
multivariate Taylor expansion. -/
@[simp] theorem order_eq_top_iff (f : AnalyticGerm x) : order f = ⊤ ↔ f = 0 := by
  rw [order, MvPowerSeries.order_eq_top_iff, taylorSeries_eq_zero_iff]

/-- The order of a product is the sum of the orders, including zero germs.
Pending proof: multiplicativity of the Taylor-series map and `MvPowerSeries.order_mul`. -/
theorem order_mul (f g : AnalyticGerm x) : order (f * g) = order f + order g := by
  sorry

/-- Cancellation can only raise the order of a sum. -/
theorem min_order_le_add (f g : AnalyticGerm x) :
    min (order f) (order g) ≤ order (f + g) := by
  simpa only [order, taylorSeries_add] using
    (MvPowerSeries.min_order_le_add (f := taylorSeries f) (g := taylorSeries g))

/-- An analytic change of coordinates preserves total order.
Pending proof: compare lowest homogeneous terms under the invertible derivative. -/
theorem order_pullbackEquiv (e : (Fin n → ℂ) ≃ₜ (Fin m → ℂ))
    (he : AnalyticAt ℂ e x) (hi : AnalyticAt ℂ e.symm (e x))
    (f : AnalyticGerm (e x)) : order (pullbackEquiv e x he hi f) = order f := by
  sorry

/-- Exact order is characterized by the first nonzero total-degree Taylor coefficient. -/
theorem order_eq_nat_iff (f : AnalyticGerm x) (d : ℕ) :
    order f = d ↔
      (∃ k, MvPowerSeries.coeff k (taylorSeries f) ≠ 0 ∧ k.degree = d) ∧
      ∀ k, k.degree < d → MvPowerSeries.coeff k (taylorSeries f) = 0 :=
  MvPowerSeries.order_eq_nat

/-- A linear automorphism sending the last coordinate axis to the line through `c`,
provided the `i`-th coordinate of `c` is nonzero. This is the shear used in Suwa,
Lemma 1.2, after swapping `i` with the last index. -/
def shearToLastAxis (c : Fin (n + 1) → ℂ) (i : Fin (n + 1)) (hi : c i ≠ 0) :
    (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun z j := if j = i then z i * c i else z j + z i * c j
  invFun z j := if j = i then z i / c i else z j - (z i / c i) * c j
  left_inv z := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hi]
    · simp [hj]; field_simp [hi]; ring
  right_inv z := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hi]
    · simp [hj]
  map_add' z w := by
    ext j
    by_cases hj : j = i
    · simp [hj]; ring
    · simp [hj]; ring
  map_smul' a z := by
    ext j
    by_cases hj : j = i
    · simp [hj, smul_eq_mul]; ring
    · simp [hj, smul_eq_mul]; ring

/-- The shear sends the `i`-th axis to the line through `c`. -/
theorem shearToLastAxis_single (c : Fin (n + 1) → ℂ) (i : Fin (n + 1)) (hi : c i ≠ 0)
    (w : ℂ) : shearToLastAxis c i hi (Pi.single i w) = w • c := by
  ext j
  by_cases hj : j = i
  · subst j; simp [shearToLastAxis, Pi.single_eq_same, smul_eq_mul]
  · simp [shearToLastAxis, hj, smul_eq_mul]

/-- **Suwa, Lemma 1.2.** A linear change makes the order on the last axis equal to the
total order. Positive ambient dimension is explicit; units are permitted and give
order zero. Pending: evaluate the leading homogeneous part and compare one-variable
order along the resulting line. -/
theorem exists_coordinate_change_order {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0) (hne : ofAnalyticAt f hf ≠ 0) :
    ∃ L : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ),
      analyticOrderAt (fun w : ℂ => f (L (Pi.single (Fin.last n) w))) 0 =
        order (ofAnalyticAt f hf) := by
  sorry

end SeveralComplexVariables.AnalyticGerm
