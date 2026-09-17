/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.AnalyticGerm.CoordinateChange
public import SeveralComplexVariables.WeierstrassDivision
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherianity of analytic germ rings

Jakóbczak–Jarnicki, Proposition 1.8.6: scalar analytic germs on finite-dimensional
complex spaces form Noetherian rings. The analytic induction step is explicitly
pending: normalize a nonzero element of an ideal, divide by it, and use finite
generation of the resulting submodule of the finite module of remainder coefficients.
The dimension induction, zero-dimensional base case, and coordinate transport are
proved here from that step. No claim is made for infinite-dimensional source spaces.
-/

@[expose] public noncomputable section

namespace SeveralComplexVariables.AnalyticGerm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Analytic induction step for Noetherianity. Pending proof: coordinate normalization,
Weierstrass division, and finite generation of the module of remainder coefficients.
The zero ideal is handled separately; division is applied to a nonzero ideal element. -/
theorem ideal_fg_prod [FiniteDimensional ℂ E]
    [IsNoetherianRing (AnalyticGerm (0 : E))]
    (I : Ideal (AnalyticGerm (0 : E × ℂ))) : I.FG := by
  sorry

/-- The origin germ ring in `n` complex coordinates is Noetherian, by induction using
`ideal_fg_prod`. In dimension zero it is the scalar field. -/
theorem isNoetherianRing_coordinates (n : ℕ) :
    IsNoetherianRing (AnalyticGerm (0 : Fin n → ℂ)) := by
  induction n with
  | zero =>
      exact isNoetherianRing_of_ringEquiv ℂ (equivComplexOfSubsingleton (0 : Fin 0 → ℂ)).symm
  | succ n ih =>
      let := ih
      let : IsNoetherianRing (AnalyticGerm (0 : (Fin n → ℂ) × ℂ)) :=
        (isNoetherianRing_iff_ideal_fg _).mpr ideal_fg_prod
      let e : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × ℂ :=
        (LinearEquiv.piCongrLeft ℂ (fun _ => ℂ) (finSuccEquiv n)).trans
          ((LinearEquiv.piOptionEquivProd ℂ).trans (LinearEquiv.prodComm ℂ _ _))
      exact isNoetherianRing_of_ringEquiv _
        (linearEquivPullbackZero e.toContinuousLinearEquiv).toRingEquiv

/-- Scalar analytic germs at any point of a finite-dimensional complex normed space
form a Noetherian ring. This instance depends on the pending analytic induction step. -/
instance [FiniteDimensional ℂ E] (x : E) : IsNoetherianRing (AnalyticGerm x) := by
  let e := (Module.finBasis ℂ E).equivFunL
  let := isNoetherianRing_coordinates (Module.finrank ℂ E)
  let : IsNoetherianRing (AnalyticGerm (0 : E)) :=
    isNoetherianRing_of_ringEquiv _ (linearEquivPullbackZero e).toRingEquiv
  exact isNoetherianRing_of_ringEquiv _ (translateEquiv x).symm.toRingEquiv

/-- Every ideal of finite-dimensional analytic germs has finitely many generators. -/
theorem ideal_fg [FiniteDimensional ℂ E] {x : E} (I : Ideal (AnalyticGerm x)) : I.FG :=
  (isNoetherianRing_iff_ideal_fg _).mp inferInstance I

end SeveralComplexVariables.AnalyticGerm
