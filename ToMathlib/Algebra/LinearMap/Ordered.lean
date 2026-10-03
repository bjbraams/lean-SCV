/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# Linear functionals and inclusion of half-spaces

Inclusion of negative half-spaces characterizes nonnegative proportionality of
linear functionals over a linearly ordered field. No topology on the module is needed.
The intended Mathlib home is `Algebra/Module/LinearMap/Ordered`.
-/

public section
namespace LinearMap
variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] {f g : E →ₗ[𝕜] 𝕜}

/-- Inclusion of negative half-spaces forces nonnegative proportionality. -/
theorem exists_nonneg_smul_eq_of_neg_imp_nonpos (hg : g ≠ 0)
    (h : ∀ v, g v < 0 → f v ≤ 0) : ∃ c : 𝕜, 0 ≤ c ∧ f = c • g := by
  obtain ⟨u, hu⟩ := g.surjective hg 1
  have hc : 0 ≤ f u := by
    have := h (-u) (by simp [hu])
    simpa using this
  have hker : ∀ v, g v = 0 → f v = 0 := by
    intro v hv
    by_contra hn
    have hg' : g (((f u + 1) / f v) • v - u) < 0 := by
      simp [map_sub, map_smul, hv, hu]
    have hf := h _ hg'
    simp only [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hn] at hf
    linarith
  refine ⟨f u, hc, ?_⟩
  ext v
  have hv : g (v - g v • u) = 0 := by simp [hu]
  have hf := hker _ hv
  simpa [sub_eq_zero, mul_comm] using hf

/-- If both functionals are nonzero, the proportionality factor is strictly positive. -/
theorem exists_pos_smul_eq_of_neg_imp_nonpos (hf : f ≠ 0) (hg : g ≠ 0)
    (h : ∀ v, g v < 0 → f v ≤ 0) : ∃ c : 𝕜, 0 < c ∧ f = c • g := by
  obtain ⟨c, hc, hfg⟩ := exists_nonneg_smul_eq_of_neg_imp_nonpos hg h
  refine ⟨c, lt_of_le_of_ne hc ?_, hfg⟩
  intro hz
  apply hf
  simp [← hz] at hfg
  exact hfg

end LinearMap
