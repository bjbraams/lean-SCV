/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.AnalyticSet.Codimension
public import SeveralComplexVariables.FunctionSpace.Extension

/-!
# Restriction across analytic sets of codimension at least two

Scheidemann's second Riemann theorem is stated as an isomorphism of holomorphic
algebras. The forward map below is restriction. Injectivity uses density;
surjectivity uses the proved second Riemann extension theorem.
Disconnected and empty domains are allowed. No assertion about continuity of the
inverse is needed for this algebraic formulation.
-/

@[expose] public noncomputable section

open Set

namespace SeveralComplexVariables

/-- **Second Riemann extension theorem, algebraic form.** Restriction across an analytic
subset of slice codimension at least two is an isomorphism of complex algebras.
Surjectivity follows from automatic local boundedness and the first Riemann theorem. -/
def analyticSetRestrictionAlgEquiv {ι : Type*} [Fintype ι]
    {U V : TopologicalSpace.Opens (ι → ℂ)} {A : Set (ι → ℂ)}
    (hA : IsAnalyticSet U A) (hcodim : HasComplexSliceCodimensionAtLeast A 2)
    (hV : (V : Set (ι → ℂ)) = (U : Set (ι → ℂ)) \ A) :
    HolomorphicAlgebra U ≃ₐ[ℂ] HolomorphicAlgebra V := by
  have hVU : V ≤ U := by
    change (V : Set (ι → ℂ)) ⊆ (U : Set (ι → ℂ))
    rw [hV]
    exact sdiff_subset
  have hd : (U : Set (ι → ℂ)) ⊆ closure (V : Set (ι → ℂ)) := by
    rw [hV]
    exact hA.subset_closure_sdiff (hcodim.interior_eq_empty (by decide))
  have hi := holomorphicRestrict_injective_of_subset_closure (F := ℂ) hVU hd
  have hs : Function.Surjective (holomorphicRestrict (F := ℂ) hVU) := by
    apply holomorphicRestrict_surjective hVU
    intro f hf
    obtain ⟨g, hg, he⟩ := hA.exists_extension_of_codimension_two hcodim (hV ▸ hf)
    exact ⟨g, hg, hV ▸ he⟩
  exact AlgEquiv.ofBijective (holomorphicRestrictAlgHom hVU)
    (by simpa only [holomorphicRestrictAlgHom_coe, Function.Bijective] using And.intro hi hs)

/-- The forward algebra equivalence is exactly restriction to the complement. -/
@[simp] theorem analyticSetRestrictionAlgEquiv_apply {ι : Type*} [Fintype ι]
    {U V : TopologicalSpace.Opens (ι → ℂ)} {A : Set (ι → ℂ)}
    (hA : IsAnalyticSet U A) (hcodim : HasComplexSliceCodimensionAtLeast A 2)
    (hV : (V : Set (ι → ℂ)) = (U : Set (ι → ℂ)) \ A) (f : HolomorphicAlgebra U) :
    analyticSetRestrictionAlgEquiv hA hcodim hV f =
      holomorphicRestrict (show V ≤ U from by
        change (V : Set (ι → ℂ)) ⊆ (U : Set (ι → ℂ))
        rw [hV]
        exact sdiff_subset) f := by
  simp [analyticSetRestrictionAlgEquiv]

end SeveralComplexVariables
