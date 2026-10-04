/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import ToMathlib.Analysis.Holomorphic.FunctionSpace

/-!
# Closedness of spaces of holomorphic maps on the complex plane

The proof uses Mathlib's Banach-valued Weierstrass theorem from
`Mathlib.Analysis.Complex.LocallyUniformLimit`. This supplies the closedness input for
our Montel and Vitali results. See the header of
`ToMathlib.Analysis.Holomorphic.NormalFamily` for the related RMT4, Mathlib PR #33505,
and TauCeti developments and the planned review upon adoption of that PR.

Mathlib's Weierstrass theorem makes the holomorphic submodule of continuous maps closed
for the compact-open topology. Consequently, holomorphic maps on an open subset of `ℂ`
with values in a complex Banach space form a complete uniform space.

## Main results

* `Complex.isClosed_holomorphicSubmodule`: the holomorphic submodule is closed.
* The `CompleteSpace` instance for `Complex.HolomorphicMap U F`.
-/

public section

open Filter Set
open scoped Topology

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Holomorphic maps on an open subset of the complex plane form a closed submodule
of continuous maps for the compact-open topology. -/
theorem isClosed_holomorphicSubmodule (U : TopologicalSpace.Opens ℂ) :
    IsClosed (holomorphicSubmodule (F := F) U : Set C(U, F)) := by
  rw [isClosed_iff_forall_filter]
  intro f l hl hmem hlim
  have hc : Tendsto (fun g : C(U, F) ↦ g) l (𝓝 f) := hlim
  have ha : ∀ᶠ g in l, AnalyticOnNhd ℂ (openExtension U g) U :=
    le_principal_iff.mp hmem
  have hd := (tendsto_iff_openExtension.mp hc).differentiableOn
    (ha.mono fun g hg ↦ hg.differentiableOn) U.isOpen
  exact fun z hz ↦ hd.analyticAt (U.isOpen.mem_nhds hz)

/-- Holomorphic maps from an open subset of `ℂ` to a complex Banach space are complete
for the compact-open uniformity. -/
instance (U : TopologicalSpace.Opens ℂ) : CompleteSpace (HolomorphicMap U F) :=
  (isClosed_holomorphicSubmodule (F := F) U).isComplete.completeSpace_coe

end Complex
