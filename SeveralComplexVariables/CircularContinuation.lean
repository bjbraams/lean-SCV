/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.Circular
public import SeveralComplexVariables.IdentityPrinciple
public import SeveralComplexVariables.LocallyUniform

/-!
# Homogeneous expansion and continuation on circular domains

The terms are diagonals of Mathlib continuous multilinear Taylor coefficients, hence
homogeneous polynomials. Convergence is grouped by total degree, not by individual
coordinate monomials. The principal convergence theorem is pending.
Reference: Scheidemann (2005), Theorem 2.1.8. Banach-valued targets are allowed.
-/

public noncomputable section

open Set

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The homogeneous term of degree `k` of a multilinear power series centered at zero. -/
def homogeneousTerm (p : FormalMultilinearSeries ℂ E F) (k : ℕ) (z : E) : F :=
  p k (fun _ => z)

omit [FiniteDimensional ℂ E] [CompleteSpace F] in
/-- The degree is expressed by the usual scalar homogeneity identity. -/
theorem homogeneousTerm_smul (p : FormalMultilinearSeries ℂ E F) (k : ℕ) (c : ℂ) (z : E) :
    homogeneousTerm p k (c • z) = c ^ k • homogeneousTerm p k z := by
  simpa [homogeneousTerm] using (p k).map_smul_univ (fun _ => c) (fun _ => z)

/-- Homogeneous Taylor expansion on a circular domain extends to its balanced hull.
Proof pending: Cauchy projections under common rotations, analytic uniqueness, and
compact majorants on radial contractions. The chosen Taylor series is supplied explicitly. -/
theorem homogeneous_expansion_balancedHull {U : Set E} (ho : IsOpen U)
    (hc : IsPreconnected U) (hrot : IsCircular U) (hzero : (0 : E) ∈ U)
    {f : E → F} (hf : AnalyticOnNhd ℂ f U) {p : FormalMultilinearSeries ℂ E F}
    (hp : HasFPowerSeriesAt f p 0) :
    HasSumLocallyUniformlyOn (homogeneousTerm p) f U ∧
      HasSumLocallyUniformlyOn (homogeneousTerm p) (fun z => ∑' k, homogeneousTerm p k z)
        (balancedHull ℂ U) ∧
      AnalyticOnNhd ℂ (fun z => ∑' k, homogeneousTerm p k z) (balancedHull ℂ U) := by
  sorry

/-- A holomorphic function on a circular domain containing zero extends to its balanced hull.
Depends on homogeneous expansion. -/
theorem exists_extension_balancedHull {U : Set E} (ho : IsOpen U)
    (hc : IsPreconnected U) (hrot : IsCircular U) (hzero : (0 : E) ∈ U)
    {f : E → F} (hf : AnalyticOnNhd ℂ f U) :
    ∃ g, AnalyticOnNhd ℂ g (balancedHull ℂ U) ∧ EqOn g f U := by
  obtain ⟨p, hp⟩ := hf 0 hzero
  obtain ⟨hs, _, ha⟩ := homogeneous_expansion_balancedHull ho hc hrot hzero hf hp
  exact ⟨_, ha, fun z hz => (hs.hasSum hz).tsum_eq⟩

/-- Extensions to the balanced hull are unique. This uses only the proved identity theorem
and geometry, independently of the pending existence theorem. -/
theorem eqOn_balancedHull_of_eqOn {U : Set E} (ho : IsOpen U) (hzero : (0 : E) ∈ U)
    {f g : E → F} (hf : AnalyticOnNhd ℂ f (balancedHull ℂ U))
    (hg : AnalyticOnNhd ℂ g (balancedHull ℂ U)) (he : EqOn f g U) :
    EqOn f g (balancedHull ℂ U) :=
  identity_theorem (ho.balancedHull hzero)
    (isPathConnected_balancedHull ⟨0, hzero⟩).isConnected.isPreconnected
    hf.differentiableOn hg.differentiableOn ho ⟨0, hzero⟩ (subset_balancedHull ℂ) he

end SeveralComplexVariables
