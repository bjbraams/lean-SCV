/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Iterated derivatives of locally uniform limits in one complex variable

A locally uniformly convergent sequence of holomorphic functions on an open subset of the
complex plane has convergent iterated derivatives at every point of that set. The conclusion
identifies each derivative limit with the corresponding iterated derivative of the limiting
function.

## Main results

* `Complex.tendsto_iteratedDeriv_of_tendstoLocallyUniformlyOn`: Iterated derivatives converge
  along a locally uniform limit of holomorphic one-variable functions, evaluated at any point of
  the domain.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Filter Set
open scoped Topology

namespace Complex

/-- Iterated derivatives converge along a locally uniform limit of holomorphic one-variable
functions, evaluated at any point of the domain. -/
theorem tendsto_iteratedDeriv_of_tendstoLocallyUniformlyOn {V : Set ℂ} (hV : IsOpen V) (j : ℕ) :
    ∀ (F : ℕ → ℂ → ℂ) (f' : ℂ → ℂ), TendstoLocallyUniformlyOn F f' atTop V →
      (∀ n, DifferentiableOn ℂ (F n) V) → ∀ {x : ℂ}, x ∈ V →
      Tendsto (fun n ↦ iteratedDeriv j (F n) x) atTop (𝓝 (iteratedDeriv j f' x)) := by
  induction j with
  | zero =>
    intro F f' hF _hFa x hx
    simpa [iteratedDeriv_zero] using hF.tendsto_at hx
  | succ j ih =>
    intro F f' hF hFa x hx
    have hderiv : TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f') atTop V :=
      hF.deriv (Filter.Eventually.of_forall hFa) hV
    have hderivDiff : ∀ n, DifferentiableOn ℂ (deriv (F n)) V := fun n ↦
      (DifferentiableOn.analyticOnNhd (hFa n) hV).deriv.differentiableOn
    have := ih (deriv ∘ F) (deriv f') hderiv hderivDiff hx
    simpa [iteratedDeriv_succ', Function.comp_def] using this

end Complex
