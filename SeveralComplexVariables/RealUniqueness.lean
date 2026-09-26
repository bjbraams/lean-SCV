/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.RealUniqueness
public import Mathlib.Analysis.Complex.CauchyIntegral

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Analytic uniqueness from positive real parameters

This file records uniqueness principles for holomorphic functions whose values are known only on
the positive real locus. They are useful for transporting certain identities proved using real
probability measures to their complex analytic continuations.

## Main results

`AnalyticOnNhd.eqOn_of_eventuallyEq_ofReal` is one-variable uniqueness from agreement on a real
germ, on a connected continuation domain. `AnalyticOnNhd.eq_of_eqOn_posReal` is uniqueness of
entire functions of one variable from the positive reals. `AnalyticOnNhd.eq_of_eqOn_posReal_pi`
is the corresponding statement for entire functions of finitely many variables. All three
results allow values in any complex normed space; completeness of the target is not needed.

## References

* V. Scheidemann, *Introduction to Complex Analysis in Several Variables*,
  Birkhäuser, 2005 (background on holomorphic functions of several variables).
-/

open Complex Set Filter
open scoped Topology

public noncomputable section RealUniqueness

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Two entire functions of finitely many complex variables which agree on all vectors of strictly
positive real parameters agree everywhere. No complex-open agreement hypothesis is needed. -/
theorem AnalyticOnNhd.eq_of_eqOn_posReal_pi {ι : Type*} [Fintype ι]
    {F G : (ι → ℂ) → H} (hF : AnalyticOnNhd ℂ F univ)
    (hG : AnalyticOnNhd ℂ G univ)
    (hEq : ∀ b : ι → ℝ, (∀ i, 0 < b i) →
      F (fun i ↦ (b i : ℂ)) = G (fun i ↦ (b i : ℂ))) : F = G := by
  classical
  have hstep : ∀ s : Finset ι, ∀ b : ι → ℂ,
      (∀ i, i ∉ s → ∃ x : ℝ, 0 < x ∧ b i = (x : ℂ)) → F b = G b := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro b hb
        choose r hr hbr using fun i ↦ hb i (by simp)
        have hb_eq : b = fun i ↦ (r i : ℂ) := by
          funext i
          exact hbr i
        rw [hb_eq]
        exact hEq r hr
    | @insert a s ha ih =>
        intro b hb
        let L : ℂ → (ι → ℂ) := fun w ↦ Function.update b a w
        have hL : AnalyticOnNhd ℂ L univ := by
          intro w _
          apply AnalyticAt.pi
          intro i
          by_cases hia : i = a
          · subst i
            have heq : (fun x : ℂ ↦ L x a) = id := by
              funext x
              simp [L]
            rw [heq]
            exact analyticAt_id
          · simpa [L, hia] using
              (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ b i) w)
        have hslices : (fun w ↦ F (L w)) = (fun w ↦ G (L w)) := by
          apply AnalyticOnNhd.eq_of_eqOn_posReal
          · intro w _
            exact (hF (L w) (mem_univ _)).comp_of_eq (hL w (mem_univ _)) rfl
          · intro w _
            exact (hG (L w) (mem_univ _)).comp_of_eq (hL w (mem_univ _)) rfl
          · intro x hx
            apply ih
            intro i his
            by_cases hia : i = a
            · subst i
              exact ⟨x, hx, by simp [L]⟩
            · simpa [L, hia] using hb i (by simp [his, hia])
        have := congrFun hslices (b a)
        simpa [L] using this
  funext b
  exact hstep Finset.univ b (by simp)

end RealUniqueness
