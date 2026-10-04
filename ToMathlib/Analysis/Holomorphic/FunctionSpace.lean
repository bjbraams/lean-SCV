/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.UniformConvergence
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Shared spaces of holomorphic maps

This bundled-map API supports the Montel and Vitali development in
`ToMathlib.Analysis.Holomorphic.NormalFamily`, whose header credits related work by
Vincent Beffara (RMT4), Yury Kudryashov
([Mathlib PR #33505](https://github.com/leanprover-community/mathlib4/pull/33505)),
and TauCeti. Review this interface alongside that development upon the anticipated
adoption of the PR; its adoption need not replace every part of our API.

Holomorphic maps on an open subset of a complex normed space form a submodule of continuous
maps, with the induced compact-open topology and uniformity. This file defines the space,
restriction and evaluation, and identifies convergence with locally uniform convergence.
Closedness and completeness for domains in `ℂ` are proved in
`ToMathlib.Analysis.Holomorphic.LocallyUniformLimit`. The definitions here also support
several-variable domains without requiring their limit theory.

The extension by zero is used only to express analyticity on the open domain; no regularity
at its boundary is asserted.

## Main results

* `Complex.HolomorphicMap`: Holomorphic maps on an open domain, with the induced compact-open
  topology and uniformity.
* `Complex.HolomorphicMap.tendsto_iff`: The inherited topology on holomorphic maps is precisely
  locally uniform convergence.
* `Complex.continuous_holomorphicMap_eval`: Evaluation at a point is continuous in the
  compact-open topology.
* `Complex.holomorphicRestrict`: Restriction to a smaller open domain preserves holomorphy.
* `Complex.continuous_holomorphicRestrict`: Restriction is continuous for the compact-open
  topology.

## References

* `Mathlib.Topology.Algebra.UniformConvergence`: formal background used by this module.
* `Mathlib.Topology.ContinuousMap.Algebra`: formal background used by this module.
* `Mathlib.Topology.UniformSpace.CompactConvergence`: formal background used by this module.
-/

public noncomputable section

open Filter Set
open scoped Topology

namespace Complex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

open scoped Classical in
/-- Extend a continuous map on an open domain by zero; used only for local analytic predicates. -/
@[expose] def openExtension (U : TopologicalSpace.Opens E) (f : C(U, F)) (z : E) : F :=
  if hz : z ∈ U then f ⟨z, hz⟩ else 0

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- The value of the extension by zero at a point of the open set. -/
theorem openExtension_apply (U : TopologicalSpace.Opens E)
    (f : C(U, F)) {z : E} (hz : z ∈ U) : openExtension U f z = f ⟨z, hz⟩ :=
  dite_eq_left hz

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- The extension by zero restricts to the original function. -/
@[simp] theorem openExtension_coe (U : TopologicalSpace.Opens E)
    (f : C(U, F)) (z : U) : openExtension U f z = f z := by
  simp [openExtension, z.property]

/-- Holomorphic maps are a submodule of continuous maps on the open domain. -/
@[expose] def holomorphicSubmodule (U : TopologicalSpace.Opens E) : Submodule ℂ C(U, F) where
  carrier := {f | AnalyticOnNhd ℂ (openExtension U f) U}
  zero_mem' := by
    change AnalyticOnNhd ℂ (openExtension U 0) U
    have h : openExtension U (0 : C(U, F)) = fun _ ↦ 0 := by
      funext z
      simp [openExtension]
    rw [h]
    exact analyticOnNhd_const
  add_mem' := by
    intro f g hf hg
    change AnalyticOnNhd ℂ (openExtension U (f + g)) U
    have h : openExtension U (f + g) = openExtension U f + openExtension U g := by
      funext z
      by_cases hz : z ∈ U <;> simp [openExtension, hz]
    rw [h]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change AnalyticOnNhd ℂ (openExtension U (c • f)) U
    have h : openExtension U (c • f) = c • openExtension U f := by
      funext z
      by_cases hz : z ∈ U <;> simp [openExtension, hz]
    rw [h]
    exact hf.const_smul

/-- Holomorphic maps on an open domain, with the induced compact-open topology and uniformity. -/
abbrev HolomorphicMap (U : TopologicalSpace.Opens E) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℂ F] : Type _ := ↥(holomorphicSubmodule (F := F) U)

/-- Holomorphic maps act on points of their open domain. -/
instance (U : TopologicalSpace.Opens E) : FunLike (HolomorphicMap U F) U F where
  coe f := f.val
  coe_injective _ _ h := Subtype.ext (DFunLike.coe_injective h)

/-- Holomorphic maps have the standard continuous-map interface. -/
instance (U : TopologicalSpace.Opens E) : ContinuousMapClass (HolomorphicMap U F) U F where
  map_continuous f := f.val.continuous

namespace HolomorphicMap

variable {U : TopologicalSpace.Opens E}

/-- Holomorphic maps are equal when their values agree on the domain. -/
@[ext] theorem ext {f g : HolomorphicMap U F} (h : ∀ z, f z = g z) : f = g :=
  DFunLike.ext _ _ h

/-- The underlying continuous map has the same values as the holomorphic map. -/
@[simp] theorem coe_val (f : HolomorphicMap U F) : (f.val : U → F) = f := rfl

/-- The zero holomorphic map vanishes at every point. -/
@[simp] theorem zero_apply (z : U) : (0 : HolomorphicMap U F) z = 0 := rfl

/-- Addition of holomorphic maps is pointwise. -/
@[simp] theorem add_apply (f g : HolomorphicMap U F) (z : U) :
    (f + g) z = f z + g z := rfl

/-- Negation of holomorphic maps is pointwise. -/
@[simp] theorem neg_apply (f : HolomorphicMap U F) (z : U) : (-f) z = -f z := rfl

/-- Subtraction of holomorphic maps is pointwise. -/
@[simp] theorem sub_apply (f g : HolomorphicMap U F) (z : U) :
    (f - g) z = f z - g z := rfl

/-- Scalar multiplication of holomorphic maps is pointwise. -/
@[simp] theorem smul_apply (c : ℂ) (f : HolomorphicMap U F) (z : U) :
    (c • f) z = c • f z := rfl

/-- A holomorphic map is continuous on its domain. -/
@[continuity, fun_prop] theorem continuous (f : HolomorphicMap U F) : Continuous f :=
  f.val.continuous

/-- Compact-open convergence is locally uniform convergence on the domain itself. -/
theorem tendsto_iff [LocallyCompactSpace U] {κ : Type*} {l : Filter κ}
    {f : κ → HolomorphicMap U F} {g : HolomorphicMap U F} :
    Tendsto f l (𝓝 g) ↔ TendstoLocallyUniformly (fun n ↦ (f n : U → F)) g l := by
  rw [tendsto_subtype_rng, ContinuousMap.tendsto_iff_tendstoLocallyUniformly]
  rfl

end HolomorphicMap

/-- Subtraction is uniformly continuous for the compact-open uniformity on holomorphic maps. -/
instance (U : TopologicalSpace.Opens E) : IsUniformAddGroup (HolomorphicMap U F) where
  uniformContinuous_sub := by
    apply isUniformEmbedding_subtype_val.uniformContinuous_iff.mpr
    apply ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.uniformContinuous_iff.mpr
    have h : UniformContinuous (fun f : HolomorphicMap U F ↦
        ContinuousMap.toUniformOnFunIsCompact f.val) :=
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.uniformContinuous.comp
        uniformContinuous_subtype_val
    exact (h.comp uniformContinuous_fst).sub (h.comp uniformContinuous_snd)

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- Convergence in the continuous-map space is exactly locally uniform convergence of the ambient
extensions on the open domain. -/
theorem tendsto_iff_openExtension [LocallyCompactSpace E] {U : TopologicalSpace.Opens E}
    {κ : Type*} {l : Filter κ} {f : κ → C(U, F)} {g : C(U, F)} :
    Tendsto f l (𝓝 g) ↔
      TendstoLocallyUniformlyOn (fun n ↦ openExtension U (f n)) (openExtension U g) l U := by
  let := U.isOpen.locallyCompactSpace
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simp only [Function.comp_def, openExtension_coe]
  rfl

/-- Evaluation at a point is continuous in the compact-open topology. -/
theorem continuous_holomorphicMap_eval (U : TopologicalSpace.Opens E) (z : U) :
    Continuous (fun f : HolomorphicMap U F ↦ f.val z) :=
  (continuous_eval_const z).comp continuous_subtype_val

/-- The inherited topology on holomorphic maps is precisely locally uniform convergence. -/
theorem holomorphicMap_tendsto_iff [LocallyCompactSpace E] {U : TopologicalSpace.Opens E}
    {κ : Type*} {l : Filter κ} {f : κ → HolomorphicMap U F} {g : HolomorphicMap U F} :
    Tendsto f l (𝓝 g) ↔ TendstoLocallyUniformlyOn
      (fun n ↦ openExtension U (f n).val) (openExtension U g.val) l U := by
  rw [tendsto_subtype_rng, tendsto_iff_openExtension]

/-- Restriction to a smaller open domain preserves holomorphy. -/
@[expose] def holomorphicRestrict {U V : TopologicalSpace.Opens E} (hVU : V ≤ U)
    (f : HolomorphicMap U F) : HolomorphicMap V F := by
  let inc : C(V, U) := ⟨fun z ↦ ⟨z, hVU z.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  refine ⟨f.val.comp inc, ?_⟩
  apply AnalyticOnNhd.congr V.isOpen (f.property.mono hVU)
  intro z hz
  rw [openExtension_apply U _ (hVU hz), openExtension_apply V _ hz]
  rfl

/-- Restriction is continuous for the compact-open topology. -/
theorem continuous_holomorphicRestrict {U V : TopologicalSpace.Opens E}
    (hVU : V ≤ U) : Continuous (holomorphicRestrict (F := F) hVU) := by
  apply Continuous.subtype_mk
  exact (ContinuousMap.continuous_precomp
    ⟨fun z : V ↦ (⟨z, hVU z.property⟩ : U), continuous_subtype_val.subtype_mk _⟩).comp
      continuous_subtype_val

/-- Evaluation as a continuous complex-linear map for the compact-open topology. -/
@[expose] def holomorphicEvalCLM (U : TopologicalSpace.Opens E) (z : U) :
    HolomorphicMap U F →L[ℂ] F where
  toFun f := f.val z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_holomorphicMap_eval U z

/-- Restriction as a continuous complex-linear map between compact-open spaces. -/
@[expose] def holomorphicRestrictCLM {U V : TopologicalSpace.Opens E} (hVU : V ≤ U) :
    HolomorphicMap U F →L[ℂ] HolomorphicMap V F where
  toFun := holomorphicRestrict hVU
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_holomorphicRestrict hVU

/-- Restrict an ambient analytic function to its open domain as a holomorphic map. -/
@[expose] def holomorphicMapOfAnalyticOnNhd (U : TopologicalSpace.Opens E) (f : E → F)
    (hf : AnalyticOnNhd ℂ f U) : HolomorphicMap U F :=
  ⟨⟨fun z ↦ f z, hf.continuousOn.domRestrict⟩,
    hf.congr U.isOpen (fun z hz ↦ by rw [openExtension_apply U _ hz]; rfl)⟩

/-- Restricting an ambient analytic function preserves its values. -/
@[simp] theorem holomorphicMapOfAnalyticOnNhd_apply (U : TopologicalSpace.Opens E)
    (f : E → F) (hf : AnalyticOnNhd ℂ f U) (z : U) :
    holomorphicMapOfAnalyticOnNhd U f hf z = f z := rfl

/-- Restriction evaluates the original map at the same point. -/
@[simp] theorem holomorphicRestrict_apply {U V : TopologicalSpace.Opens E} (hVU : V ≤ U)
    (f : HolomorphicMap U F) (z : V) :
    holomorphicRestrict hVU f z = f ⟨z, hVU z.property⟩ := rfl

/-- Restriction to the original domain is the identity. -/
@[simp] theorem holomorphicRestrict_refl {U : TopologicalSpace.Opens E}
    (f : HolomorphicMap U F) : holomorphicRestrict le_rfl f = f := by
  ext z
  rfl

/-- Successive restrictions agree with direct restriction. -/
@[simp] theorem holomorphicRestrict_trans {U V W : TopologicalSpace.Opens E}
    (hVU : V ≤ U) (hWV : W ≤ V) (f : HolomorphicMap U F) :
    holomorphicRestrict hWV (holomorphicRestrict hVU f) =
      holomorphicRestrict (hWV.trans hVU) f := by
  ext z
  rfl

/-- The evaluation operator evaluates the bundled map. -/
@[simp] theorem holomorphicEvalCLM_apply (U : TopologicalSpace.Opens E) (z : U)
    (f : HolomorphicMap U F) : holomorphicEvalCLM U z f = f z := rfl

/-- The restriction operator agrees with restriction of bundled maps. -/
@[simp] theorem holomorphicRestrictCLM_apply {U V : TopologicalSpace.Opens E} (hVU : V ≤ U)
    (f : HolomorphicMap U F) : holomorphicRestrictCLM hVU f = holomorphicRestrict hVU f := rfl

end Complex

end
