/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.AnalyticGerm.Factorization
public import SeveralComplexVariables.AnalyticGerm.Weierstrass

/-!
# Persistence of relative primality

Relative primality is an open condition on the base point for two fixed analytic
representatives in finite dimension. We use `IsRelPrime`, not the stronger Bezout
condition `IsCoprime`. A germ at one point is not evaluated at other points; instead,
the statement explicitly takes the germs of the same representatives nearby.
The analytic persistence argument is pending; openness is its direct consequence.
-/

public section

open Filter Set
open scoped Topology

namespace SeveralComplexVariables.AnalyticGerm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Relatively prime germs of two analytic representatives remain relatively prime nearby.
Pending proof: simultaneous preparation and polynomial elimination in the parameter ring.
Neither germ is required to be nonzero: the relatively prime zero case forces a unit. -/
theorem eventually_isRelPrime_ofAnalyticAt {f g : E → ℂ} {x : E}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (h : IsRelPrime (ofAnalyticAt f hf) (ofAnalyticAt g hg)) :
    ∀ᶠ y in 𝓝 x, ∃ (hfy : AnalyticAt ℂ f y) (hgy : AnalyticAt ℂ g y),
      IsRelPrime (ofAnalyticAt f hfy) (ofAnalyticAt g hgy) := by
  sorry

/-- The locus where two functions are analytic and their germs are relatively prime is open.
This consequence depends on the pending persistence theorem. -/
theorem isOpen_isRelPrime_locus (f g : E → ℂ) :
    IsOpen {x | ∃ (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x),
      IsRelPrime (ofAnalyticAt f hf) (ofAnalyticAt g hg)} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨hf, hg, h⟩
  exact eventually_isRelPrime_ofAnalyticAt hf hg h

end SeveralComplexVariables.AnalyticGerm
