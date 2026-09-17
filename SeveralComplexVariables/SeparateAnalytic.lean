/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.Basic

/-!
# Separate analyticity

Hartogs' theorem asserts joint analyticity from analyticity of all coordinate slices,
without continuity or local boundedness assumptions. Its proof is pending. The versions
with those extra hypotheses are proved in `Osgood` and `LocallyBounded`.

References: Boas (2013), Section 2.4; Jakóbczak--Jarnicki (2021), Theorem 1.5.1.
-/

public section

open Function Metric Set
open scoped Classical Topology

namespace SeveralComplexVariables

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Hartogs' separate-holomorphy theorem.** On an open finite complex coordinate domain,
analyticity of every coordinate slice implies joint analyticity, with no continuity or local
boundedness hypothesis. Proof pending; the versions with those extra hypotheses are already
proved in `Osgood` and `LocallyBounded`. Empty and singleton coordinate types are included. -/
theorem analyticOnNhd_of_separately_analytic
    {ι : Type*} [Fintype ι] {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hU : IsOpen U)
    (hf : ∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i)) :
    AnalyticOnNhd ℂ f U := by
  sorry

end SeveralComplexVariables
