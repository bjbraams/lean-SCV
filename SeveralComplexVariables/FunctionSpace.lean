/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Holomorphic.FunctionSpace
public import SeveralComplexVariables.LocallyUniform

/-!
# Several-variable holomorphic function spaces

The shared compact-open function space is defined in
`ToMathlib.Analysis.Holomorphic.FunctionSpace`. This module retains the previous names, proves
closedness and completeness using the several-variable Weierstrass theorem, and supplies
continuous coordinate differentiation.

## Main results

* `SeveralComplexVariables.isClosed_holomorphicSubmodule`: Weierstrass convergence makes the
  holomorphic submodule closed.
* `SeveralComplexVariables.continuous_holomorphicPartialDeriv`: Coordinate differentiation is
  continuous for the compact-open topology.

## References

* V. Scheidemann, *Introduction to Complex Analysis in Several Variables*,
  Birkhäuser, 2005 (background on holomorphic functions of several variables).
-/

public noncomputable section

open Filter Set
open scoped Topology

namespace SeveralComplexVariables

export Complex (openExtension openExtension_apply openExtension_coe holomorphicSubmodule
  HolomorphicMap tendsto_iff_openExtension continuous_holomorphicMap_eval
  holomorphicMap_tendsto_iff holomorphicRestrict continuous_holomorphicRestrict)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [CompleteSpace F]

/-- Weierstrass convergence makes the holomorphic submodule closed. -/
theorem isClosed_holomorphicSubmodule [FiniteDimensional ℂ E] (U : TopologicalSpace.Opens E) :
    IsClosed (holomorphicSubmodule (F := F) U : Set C(U, F)) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  rw [isClosed_iff_forall_filter]
  intro f l hl hmem hlim
  have hc : Tendsto (fun g : C(U, F) => g) l (𝓝 f) := hlim
  exact (tendsto_iff_openExtension.mp hc).analyticOnNhd_of_finiteDimensional
    (le_principal_iff.mp hmem) U.isOpen

/-- The compact-open uniform space of holomorphic maps into a Banach space is complete. -/
instance [FiniteDimensional ℂ E] (U : TopologicalSpace.Opens E) : CompleteSpace (HolomorphicMap U
  F) :=
  (isClosed_holomorphicSubmodule (F := F) U).isComplete.completeSpace_coe

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate differentiation as an operator on holomorphic maps. -/
def holomorphicPartialDeriv (U : TopologicalSpace.Opens (ι → ℂ)) (i : ι)
    (f : HolomorphicMap U F) : HolomorphicMap U F := by
  have ha := f.property.partialDeriv U.isOpen i
  refine ⟨⟨fun z => partialDeriv i (openExtension U f.val) z,
    ha.continuousOn.domRestrict⟩, ?_⟩
  apply AnalyticOnNhd.congr U.isOpen ha
  intro z hz
  rw [openExtension_apply U _ hz]
  rfl

/-- Coordinate differentiation is continuous for the compact-open topology. -/
theorem continuous_holomorphicPartialDeriv (U : TopologicalSpace.Opens (ι → ℂ)) (i : ι) :
    Continuous (holomorphicPartialDeriv (F := F) U i) := by
  rw [continuous_iff_continuousAt]
  intro f
  change Tendsto _ (𝓝 f) _
  rw [holomorphicMap_tendsto_iff]
  have hlim := (holomorphicMap_tendsto_iff (f := fun g : HolomorphicMap U F => g)).mp
    (tendsto_id : Tendsto (fun g : HolomorphicMap U F => g) (𝓝 f) (𝓝 f))
  have hd := hlim.partialDeriv (Eventually.of_forall fun g => g.property) U.isOpen i
  apply (hd.congr (fun g z hz => ?_)).congr_right (fun z hz => ?_)
  all_goals
    rw [openExtension_apply U _ hz]
    rfl

end SeveralComplexVariables

end
