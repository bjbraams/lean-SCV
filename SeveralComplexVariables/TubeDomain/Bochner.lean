/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.TubeDomain.StarConvex
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Bochner's tube theorem for connected bases in coordinates

Let `Ω ⊆ ℝⁿ` be open and connected, `p ∈ Ω`, and let `Ã` be the maximal star-convex extension
base with respect to `p`, which is convex. If `Ω` were not contained in `Ã`, a path in `Ω` from
`p` would leave `Ã` at a first point `x₁ ∈ Ω ∩ ∂Ã`. Every extension agrees with the original
function near the path points before `x₁`, by propagation of local agreement along the path,
hence on the tube over the convex set `Ã ∩ B(x₁, r)`. The two functions therefore define a
holomorphic function on the tube over `Ã ∪ B(x₁, r)`, which is star-convex with respect to
`x₁`; the star-convex case of the theorem extends it to the tube over the convex hull, which
belongs to the family, contradicting maximality. Hence `Ω ⊆ Ã`, and the extension to the tube
over the convex hull of `Ω` follows.

References: Hörmander §2.5, Theorem 2.5.10 (b); Scheidemann §6.3, Theorem 6.3.1, Step 2.
-/

@[expose] public noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace SeveralComplexVariables

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The union of an open convex set with a ball around a point of its closure is star-convex
with respect to that point. -/
theorem starConvex_union_ball_of_mem_closure {A : Set (Fin n → ℝ)} (hA : Convex ℝ A)
    (hAo : IsOpen A) {x : Fin n → ℝ} (hx : x ∈ closure A) {r : ℝ} (hr : 0 < r) :
    StarConvex ℝ x (A ∪ ball x r) := by
  intro y hy a b ha hb hab
  rcases hy with hyA | hyB
  · rcases ha.lt_or_eq with ha' | ha'
    · rcases hb.lt_or_eq with hb' | hb'
      · left
        have hmem : a • x + b • y ∈ openSegment ℝ x y := ⟨a, b, ha', hb', hab, rfl⟩
        have hint := hA.openSegment_closure_interior_subset_interior hx
          (by rwa [hAo.interior_eq] : y ∈ interior A) hmem
        rwa [hAo.interior_eq] at hint
      · right
        subst hb'
        rw [add_zero] at hab
        rw [zero_smul, add_zero, hab, one_smul]
        exact mem_ball_self hr
    · left
      subst ha'
      rw [zero_add] at hab
      rw [zero_smul, zero_add, hab, one_smul]
      exact hyA
  · right
    exact (convex_ball x r) (mem_ball_self hr) hyB ha hb hab

/-- **Bochner's tube theorem in coordinates.** Every Banach-valued holomorphic function on the
tube over an open connected base in `ℝⁿ` extends to the tube over the convex hull. -/
theorem exists_extension_tubeDomain_convexHull_fin {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (hc : IsConnected Ω) {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f (tubeDomain Ω)) :
    ∃ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain (convexHull ℝ Ω)) ∧
      EqOn g f (tubeDomain Ω) := by
  classical
  obtain ⟨p, hp⟩ := hc.nonempty
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ p hp
  have hpÃ : p ∈ maxStar F Ω p := mem_maxStar_of_ball hr hrΩ
  have hÃo : IsOpen (maxStar F Ω p) := isOpen_maxStar
  have hÃc : Convex ℝ (maxStar F Ω p) := convex_maxStar hpÃ
  have hΩÃ : Ω ⊆ maxStar F Ω p := by
    by_contra hnot
    obtain ⟨x₀, hx₀Ω, hx₀⟩ := not_subset.mp hnot
    obtain ⟨γ, hγ⟩ := (hΩ.isConnected_iff_isPathConnected.mp hc).joinedIn p hp x₀ hx₀Ω
    have hγΩ : ∀ t, γ.extend t ∈ Ω := by
      intro t
      have hmem : γ.extend t ∈ range γ.extend := mem_range_self t
      rw [Path.extend_range] at hmem
      obtain ⟨u, hu⟩ := hmem
      rw [← hu]
      exact hγ u
    set S : Set ℝ := Icc (0 : ℝ) 1 ∩ γ.extend ⁻¹' (maxStar F Ω p)ᶜ with hS
    have hSc : IsClosed S := isClosed_Icc.inter (hÃo.isClosed_compl.preimage γ.continuous_extend)
    have hSne : S.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, by
      show γ.extend 1 ∉ maxStar F Ω p
      rw [Path.extend_one]
      exact hx₀⟩
    have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
    have hsS : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
    have hs01 : sInf S ∈ Icc (0 : ℝ) 1 := hsS.1
    have hx₁ : γ.extend (sInf S) ∉ maxStar F Ω p := hsS.2
    have h0S : (0 : ℝ) ∉ S := fun h => h.2 (by
      show γ.extend 0 ∈ maxStar F Ω p
      rw [Path.extend_zero]
      exact hpÃ)
    have hs0 : 0 < sInf S := lt_of_le_of_ne hs01.1 fun h => h0S (h ▸ hsS)
    have hprefix : ∀ t, 0 ≤ t → t < sInf S → γ.extend t ∈ maxStar F Ω p := by
      intro t ht0 hts
      by_contra h
      exact notMem_of_lt_csInf hts hSbdd ⟨⟨ht0, hts.le.trans hs01.2⟩, h⟩
    have hx₁Ω : γ.extend (sInf S) ∈ Ω := hγΩ _
    have htend : Tendsto γ.extend (𝓝[<] sInf S) (𝓝 (γ.extend (sInf S))) :=
      (γ.continuous_extend.tendsto _).mono_left nhdsWithin_le_nhds
    have hx₁cl : γ.extend (sInf S) ∈ closure (maxStar F Ω p) := by
      apply mem_closure_of_tendsto htend
      filter_upwards [Ioo_mem_nhdsLT hs0] with t ht
      exact hprefix t ht.1.le ht.2
    obtain ⟨r₁, hr₁, hr₁Ω⟩ := Metric.isOpen_iff.mp hΩ _ hx₁Ω
    have hev : ∀ᶠ t in 𝓝[<] sInf S, γ.extend t ∈ ball (γ.extend (sInf S)) r₁ :=
      htend (isOpen_ball.mem_nhds (mem_ball_self hr₁))
    obtain ⟨t₀, ht₀, ht₀ball⟩ := Filter.nonempty_of_mem (Filter.inter_mem (Ioo_mem_nhdsLT hs0) hev)
    have ht₀Ã : γ.extend t₀ ∈ maxStar F Ω p := hprefix t₀ ht₀.1.le ht₀.2
    have hA₁o : IsOpen (maxStar F Ω p ∪ ball (γ.extend (sInf S)) r₁) := hÃo.union isOpen_ball
    have hA₁s : StarConvex ℝ (γ.extend (sInf S)) (maxStar F Ω p ∪ ball (γ.extend (sInf S)) r₁) :=
      starConvex_union_ball_of_mem_closure hÃc hÃo hx₁cl hr₁
    have hx₁A₁ : γ.extend (sInf S) ∈ maxStar F Ω p ∪ ball (γ.extend (sInf S)) r₁ :=
      Or.inr (mem_ball_self hr₁)
    have hBmem : convexHull ℝ (maxStar F Ω p ∪ ball (γ.extend (sInf S)) r₁) ∈ starFamily F Ω p := by
      refine ⟨hA₁o.convexHull, (convex_convexHull ℝ _).starConvex
        (subset_convexHull ℝ _ (Or.inl hpÃ)), ?_⟩
      intro f₀ hf₀
      obtain ⟨g₀, hg₀, hg₀f⟩ := tubeExtends_maxStar hpÃ f₀ hf₀
      have hK : IsPreconnected ((fun t => ofRealPi (γ.extend t)) '' Icc 0 t₀) :=
        isPreconnected_Icc.image _
          (by fun_prop : Continuous fun t => ofRealPi (γ.extend t)).continuousOn
      have hKU : (fun t => ofRealPi (γ.extend t)) '' Icc 0 t₀ ⊆ tubeDomain (Ω ∩ maxStar F Ω p) := by
        rintro _ ⟨t, ht, rfl⟩
        rw [ofRealPi_mem_tubeDomain]
        exact ⟨hγΩ t, hprefix t ht.1 (ht.2.trans_lt ht₀.2)⟩
      have hnear : g₀ =ᶠ[𝓝 (ofRealPi (γ.extend t₀))] f₀ := by
        refine eventuallyEq_of_isPreconnected (isOpen_tubeDomain (hΩ.inter hÃo))
          (hf₀.mono (tubeDomain_mono inter_subset_left))
          (hg₀.mono (tubeDomain_mono inter_subset_right)) hK hKU
          ⟨0, ⟨le_rfl, ht₀.1.le⟩, ?_⟩ hg₀f ⟨t₀, ⟨ht₀.1.le, le_rfl⟩, rfl⟩
        simp
      have hAB : EqOn g₀ f₀ (tubeDomain (maxStar F Ω p ∩ ball (γ.extend (sInf S)) r₁)) := by
        have hpt : γ.extend t₀ ∈ maxStar F Ω p ∩ ball (γ.extend (sInf S)) r₁ := ⟨ht₀Ã, ht₀ball⟩
        exact (hg₀.mono (tubeDomain_mono inter_subset_left)).eqOn_of_preconnected_of_eventuallyEq
          (hf₀.mono (tubeDomain_mono (inter_subset_right.trans hr₁Ω)))
          (isPreconnected_tubeDomain (hÃc.inter (convex_ball _ r₁)).isPreconnected)
          (ofRealPi_mem_tubeDomain.mpr hpt) hnear
      set g₁ : (Fin n → ℂ) → F := fun z => if z ∈ tubeDomain (maxStar F Ω p) then g₀ z else f₀ z
        with hg₁
      have hg₁a : AnalyticOnNhd ℂ g₁ (tubeDomain (maxStar F Ω p ∪ ball (γ.extend (sInf S)) r₁)) := by
        intro z hz
        rw [tubeDomain_union] at hz
        rcases hz with hzA | hzB
        · have : g₁ =ᶠ[𝓝 z] g₀ :=
            eventuallyEq_of_mem ((isOpen_tubeDomain hÃo).mem_nhds hzA) fun w hw => by
              simp [hg₁, hw]
          exact (hg₀ z hzA).congr this.symm
        · have : g₁ =ᶠ[𝓝 z] f₀ := by
            refine eventuallyEq_of_mem ((isOpen_tubeDomain isOpen_ball).mem_nhds hzB) fun w hw => ?_
            by_cases hwA : w ∈ tubeDomain (maxStar F Ω p)
            · simp only [hg₁, hwA, ite_true]
              exact hAB ⟨hwA, hw⟩
            · simp only [hg₁, hwA, ite_false]
          exact (hf₀ z (tubeDomain_mono hr₁Ω hzB)).congr this.symm
      have hg₁f : g₁ =ᶠ[𝓝 (ofRealPi p)] f₀ := by
        have : g₁ =ᶠ[𝓝 (ofRealPi p)] g₀ :=
          eventuallyEq_of_mem ((isOpen_tubeDomain hÃo).mem_nhds (ofRealPi_mem_tubeDomain.mpr hpÃ))
            fun w hw => by simp [hg₁, hw]
        exact this.trans hg₀f
      obtain ⟨g₂, hg₂, hg₂g₁⟩ :=
        exists_extension_tubeDomain_convexHull_of_starConvex hA₁o hA₁s hx₁A₁ hg₁a
      refine ⟨g₂, hg₂, ?_⟩
      have : g₂ =ᶠ[𝓝 (ofRealPi p)] g₁ :=
        eventuallyEq_of_mem ((isOpen_tubeDomain hA₁o).mem_nhds
          (ofRealPi_mem_tubeDomain.mpr (Or.inl hpÃ))) hg₂g₁
      exact this.trans hg₁f
    exact hx₁ (subset_maxStar_of_mem hBmem (subset_convexHull ℝ _ hx₁A₁))
  have hconv : convexHull ℝ Ω ⊆ maxStar F Ω p := convexHull_min hΩÃ hÃc
  obtain ⟨g, hg, hgf⟩ := tubeExtends_maxStar hpÃ f hf
  refine ⟨g, hg.mono (tubeDomain_mono hconv), ?_⟩
  exact (hg.mono (tubeDomain_mono hΩÃ)).eqOn_of_preconnected_of_eventuallyEq hf
    (isPreconnected_tubeDomain hc.isPreconnected) (ofRealPi_mem_tubeDomain.mpr hp) hgf

end SeveralComplexVariables
