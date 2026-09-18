/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Elementary facts on scalar actions and continuous linear functionals

## Main results

* `Complex.smul_eq_re_smul_add_im_smul`: A complex scalar acts on a vector of a complex module
  through its real and imaginary parts.
* `ContinuousLinearMap.exists_apply_eq_one_of_ne_zero`: A nonzero continuous linear functional
  attains the value `1` on a nonzero vector.
-/

public section

/-- A complex scalar acts on a vector through its real and imaginary parts. -/
theorem Complex.smul_eq_re_smul_add_im_smul {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ζ : ℂ) (c : E) : ζ • c = ζ.re • c + ζ.im • (Complex.I • c) := by
  conv_lhs => rw [← Complex.re_add_im ζ]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

/-- A nonzero continuous linear functional attains the value `1` on a nonzero vector. -/
theorem ContinuousLinearMap.exists_apply_eq_one_of_ne_zero {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {ℓ : E →L[𝕜] 𝕜}
    (hℓ : ℓ ≠ 0) : ∃ ν, ℓ ν = 1 ∧ 0 < ‖ν‖ := by
  have hℓ' : (ℓ : E →ₗ[𝕜] 𝕜) ≠ 0 := fun h => hℓ (ContinuousLinearMap.coe_injective h)
  obtain ⟨ν, hν⟩ := LinearMap.surjective hℓ' 1
  refine ⟨ν, hν, norm_pos_iff.mpr fun h0 => ?_⟩
  rw [h0, map_zero] at hν
  exact zero_ne_one hν

end
