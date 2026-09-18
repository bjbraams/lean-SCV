/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.TubeDomain.Disc
public import SeveralComplexVariables.TubeDomain.Gluing
public import SeveralComplexVariables.HolomorphicConvexity.ThullenBanach

/-!
# The maximal star-convex extension tube and Bochner's theorem for star-convex bases

Fix a Banach space `F`, a base `Ω ⊆ ℝⁿ` and a point `p`. The star-convex open sets `A` with
respect to `p` such that every `F`-valued holomorphic function on the tube over `Ω` extends
holomorphically to the tube over `A`, agreeing with it near the real point `p`, form a family
closed under unions: the union `maxStar` again has the extension property, because two members
meet in a star-convex set whose tube is connected. The maximal tube is convex. Indeed, for two
points `t₁, t₂` of `maxStar`, the scaled triangles with vertex `p` lie in `maxStar` by an
induction on the scale: on a slightly smaller triangle every point lies on a parabolic analytic
disc with boundary over the two sides through `p`, so by the disc hull lemma and Thullen's
continuation lemma every function continues to a ball of a uniform radius, these local
continuations glue along the convex triangle, and maximality absorbs the enlarged tube.

Consequently, for an open star-convex base, every holomorphic function on the tube extends to
the tube over the convex hull. This is part (a) of Hörmander's proof of Bochner's theorem.

References: Hörmander §2.5, Theorem 2.5.10 (a); Scheidemann §6.3, Theorem 6.3.1, Step 1.
-/

@[expose] public noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace SeveralComplexVariables

variable {n : ℕ} (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Every `F`-valued holomorphic function on the tube over `Ω` extends holomorphically to the
tube over `A`, agreeing with the original near the real point `p`. -/
def TubeExtends (Ω A : Set (Fin n → ℝ)) (p : Fin n → ℝ) : Prop :=
  ∀ f : (Fin n → ℂ) → F, AnalyticOnNhd ℂ f (tubeDomain Ω) →
    ∃ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain A) ∧ g =ᶠ[𝓝 (ofRealPi p)] f

/-- The family of open star-convex extension bases. -/
def starFamily (Ω : Set (Fin n → ℝ)) (p : Fin n → ℝ) : Set (Set (Fin n → ℝ)) :=
  {A | IsOpen A ∧ StarConvex ℝ p A ∧ TubeExtends F Ω A p}

/-- The maximal star-convex extension base. -/
def maxStar (Ω : Set (Fin n → ℝ)) (p : Fin n → ℝ) : Set (Fin n → ℝ) :=
  ⋃₀ starFamily F Ω p

variable {F}

section Family

variable {Ω : Set (Fin n → ℝ)} {p : Fin n → ℝ}

omit [CompleteSpace F] in
theorem isOpen_maxStar : IsOpen (maxStar F Ω p) := isOpen_sUnion fun _ hA => hA.1

omit [CompleteSpace F] in
theorem starConvex_maxStar : StarConvex ℝ p (maxStar F Ω p) :=
  starConvex_sUnion fun _ hA => hA.2.1

omit [CompleteSpace F] in
theorem subset_maxStar_of_mem {A : Set (Fin n → ℝ)} (hA : A ∈ starFamily F Ω p) :
    A ⊆ maxStar F Ω p := subset_sUnion_of_mem hA

omit [CompleteSpace F] in
/-- A ball around `p` inside `Ω` belongs to the family. -/
theorem ball_mem_starFamily {r : ℝ} (hr0 : 0 < r) (hr : ball p r ⊆ Ω) :
    ball p r ∈ starFamily F Ω p :=
  ⟨isOpen_ball, (convex_ball p r).starConvex (mem_ball_self hr0),
    fun f hf => ⟨f, hf.mono (tubeDomain_mono hr), EventuallyEq.rfl⟩⟩

omit [CompleteSpace F] in
theorem mem_maxStar_of_ball {r : ℝ} (hr0 : 0 < r) (hr : ball p r ⊆ Ω) : p ∈ maxStar F Ω p :=
  subset_maxStar_of_mem (ball_mem_starFamily hr0 hr) (mem_ball_self hr0)

/-- The tube over a star-convex set containing its center is preconnected. -/
theorem isPreconnected_tubeDomain_of_starConvex {A : Set (Fin n → ℝ)} (hA : StarConvex ℝ p A)
    (hp : p ∈ A) : IsPreconnected (tubeDomain A) :=
  isPreconnected_tubeDomain (hA.isPathConnected hp).isConnected.isPreconnected

omit [CompleteSpace F] in
/-- Two extensions agreeing with a function near `p` agree on the tube over the intersection
of star-convex bases. -/
theorem eqOn_of_starConvex {A B : Set (Fin n → ℝ)} (hA : StarConvex ℝ p A)
    (hB : StarConvex ℝ p B) {f g₁ g₂ : (Fin n → ℂ) → F}
    (hg₁ : AnalyticOnNhd ℂ g₁ (tubeDomain A)) (hg₂ : AnalyticOnNhd ℂ g₂ (tubeDomain B))
    (h₁ : g₁ =ᶠ[𝓝 (ofRealPi p)] f) (h₂ : g₂ =ᶠ[𝓝 (ofRealPi p)] f) :
    EqOn g₁ g₂ (tubeDomain (A ∩ B)) := by
  rcases (A ∩ B).eq_empty_or_nonempty with he | hne
  · rw [he, tubeDomain_empty]
    exact fun _ h => h.elim
  have hp : p ∈ A ∩ B := (hA.inter hB).mem hne
  exact (hg₁.mono (tubeDomain_mono inter_subset_left)).eqOn_of_preconnected_of_eventuallyEq
    (hg₂.mono (tubeDomain_mono inter_subset_right))
    (isPreconnected_tubeDomain_of_starConvex (hA.inter hB) hp)
    (ofRealPi_mem_tubeDomain.mpr hp) (h₁.trans h₂.symm)

omit [CompleteSpace F] in
/-- The maximal base has the extension property. -/
theorem tubeExtends_maxStar (hp : p ∈ maxStar F Ω p) : TubeExtends F Ω (maxStar F Ω p) p := by
  classical
  intro f hf
  have hchoice : ∀ A : Set (Fin n → ℝ), A ∈ starFamily F Ω p →
      ∃ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain A) ∧ g =ᶠ[𝓝 (ofRealPi p)] f :=
    fun A hA => hA.2.2 f hf
  choose! g hga hgf using hchoice
  let G : (Fin n → ℂ) → F := fun z =>
    if hz : ∃ A ∈ starFamily F Ω p, z ∈ tubeDomain A then g (Classical.choose hz) z else 0
  have hG : ∀ A ∈ starFamily F Ω p, ∀ z ∈ tubeDomain A, G z = g A z := by
    intro A hA z hz
    have hex : ∃ A ∈ starFamily F Ω p, z ∈ tubeDomain A := ⟨A, hA, hz⟩
    simp only [G]
    split_ifs
    obtain ⟨hA', hz'⟩ := Classical.choose_spec hex
    exact eqOn_of_starConvex hA'.2.1 hA.2.1 (hga _ hA') (hga A hA) (hgf _ hA') (hgf A hA)
      ⟨hz', hz⟩
  obtain ⟨A₀, hA₀, hpA₀⟩ := mem_sUnion.mp hp
  refine ⟨G, ?_, ?_⟩
  · intro z hz
    obtain ⟨A, hA, hzA⟩ := mem_sUnion.mp hz
    have : G =ᶠ[𝓝 z] g A :=
      eventuallyEq_of_mem ((isOpen_tubeDomain hA.1).mem_nhds hzA) fun w hw => hG A hA w hw
    exact (hga A hA z hzA).congr this.symm
  · have : G =ᶠ[𝓝 (ofRealPi p)] g A₀ :=
      eventuallyEq_of_mem ((isOpen_tubeDomain hA₀.1).mem_nhds (ofRealPi_mem_tubeDomain.mpr hpA₀))
        fun w hw => hG A₀ hA₀ w hw
    exact this.trans (hgf A₀ hA₀)

omit [CompleteSpace F] in
/-- **Maximality.** An open star-convex base to which every function on the maximal tube
extends is contained in the maximal base. -/
theorem maxStar_maximal (hp : p ∈ maxStar F Ω p) {B : Set (Fin n → ℝ)} (hB : IsOpen B)
    (hBs : StarConvex ℝ p B)
    (hext : ∀ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain (maxStar F Ω p)) →
      ∃ G : (Fin n → ℂ) → F, AnalyticOnNhd ℂ G (tubeDomain B) ∧
        EqOn G g (tubeDomain (maxStar F Ω p))) :
    B ⊆ maxStar F Ω p := by
  apply subset_maxStar_of_mem
  refine ⟨hB, hBs, fun f hf => ?_⟩
  obtain ⟨g, hg, hgf⟩ := tubeExtends_maxStar hp f hf
  obtain ⟨G, hG, hGg⟩ := hext g hg
  refine ⟨G, hG, ?_⟩
  have : G =ᶠ[𝓝 (ofRealPi p)] g :=
    eventuallyEq_of_mem ((isOpen_tubeDomain isOpen_maxStar).mem_nhds
      (ofRealPi_mem_tubeDomain.mpr hp)) hGg
  exact this.trans hgf

end Family

section Triangle

variable {A : Set (Fin n → ℝ)} {p t₁ t₂ : Fin n → ℝ}

/-- **Local continuation on a shrunken triangle.** If the tube over the triangle of scale `a`
lies in the tube over `A` and balls of radius `δ` around the two sides through `p` lie in the
tube over `A`, then every function holomorphic on the tube over `A` continues to the ball of
radius `δ` around each point of the tube over the triangle of a smaller scale `b`. -/
theorem exists_local_continuation_tri (hA : IsOpen A) {a : ℝ} (ha1 : a ≤ 1)
    (htri : tri p t₁ t₂ a ⊆ A) {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ w ∈ tubeDomain (segment ℝ p t₁ ∪ segment ℝ p t₂), ball w δ ⊆ tubeDomain A)
    {b : ℝ} (hba : b ≤ a) (hlt : b = 0 ∨ b < a)
    {g : (Fin n → ℂ) → F} (hg : AnalyticOnNhd ℂ g (tubeDomain A)) :
    ∀ ζ ∈ tubeDomain (tri p t₁ t₂ b), ∃ k : (Fin n → ℂ) → F,
      AnalyticOnNhd ℂ k (ball ζ δ) ∧ k =ᶠ[𝓝 ζ] g := by
  intro ζ hζ
  obtain ⟨u, v, huv, hvb, hre⟩ := mem_tubeDomain.mp hζ
  rcases huv.lt_or_eq with hlt' | heq
  · have hv0 : 0 < v := (abs_nonneg u).trans_lt hlt'
    have hbpos : 0 < b := hv0.trans_le hvb
    have hba' : b < a := by
      rcases hlt with h | h
      · exact absurd h hbpos.ne'
      · exact h
    have ha : 0 < a := hbpos.trans hba'
    set s₁ : Fin n → ℝ := p + a • (t₁ - p) with hs₁
    set s₂ : Fin n → ℝ := p + a • (t₂ - p) with hs₂
    have htri' : tri p s₁ s₂ 1 ⊆ A := by rw [← tri_scale p t₁ t₂ ha]; exact htri
    have huv' : |u / a| < v / a := by
      rw [abs_div, abs_of_pos ha]
      exact div_lt_div_of_pos_right hlt' ha
    have hv1 : v / a < 1 := (div_lt_one ha).mpr (hvb.trans_lt hba')
    obtain ⟨c, hc0, -, hreg, hdisc⟩ := exists_parabolaDisc_of_lt p s₁ s₂ huv' hv1 (imPi ζ)
    have hζeq : parabolaDisc p s₁ s₂ c (imPi ζ) ((u / a : ℝ) : ℂ) = ζ := by
      rw [hdisc, hs₁, hs₂, triPt_scale p t₁ t₂ ha.ne', ← hre]
      exact ofRealPi_rePi_add_I_smul_ofRealPi_imPi ζ
    have hhull := parabolaDisc_mem_holomorphicHull p s₁ s₂ htri' hc0 (imPi ζ) (subset_closure hreg)
    rw [hζeq] at hhull
    have hK : IsCompact (parabolaDisc p s₁ s₂ c (imPi ζ) '' frontier (parabolaRegion c)) :=
      isCompact_image_frontier_parabolaRegion p s₁ s₂ hc0 _
    have hKS : parabolaDisc p s₁ s₂ c (imPi ζ) '' frontier (parabolaRegion c) ⊆
        tubeDomain (segment ℝ p t₁ ∪ segment ℝ p t₂) := by
      refine (parabolaDisc_frontier_subset p s₁ s₂ hc0 _).trans (tubeDomain_mono ?_)
      exact union_subset_union (segment_scaled_subset p ha.le ha1 t₁)
        (segment_scaled_subset p ha.le ha1 t₂)
    have hball : ∀ w ∈ parabolaDisc p s₁ s₂ c (imPi ζ) '' frontier (parabolaRegion c),
        ball w δ ⊆ tubeDomain A := fun w hw => hS w (hKS hw)
    obtain ⟨h1, h2⟩ := taylor_continuation_on_holomorphicHull_vector (isOpen_tubeDomain hA) hK hδ
      hball hhull hg
    exact ⟨_, h1, h2⟩
  · have hmem : ζ ∈ tubeDomain (segment ℝ p t₁ ∪ segment ℝ p t₂) := by
      rw [mem_tubeDomain, hre]
      exact triPt_mem_union_segment p t₁ t₂ heq (hvb.trans (hba.trans ha1))
    exact ⟨g, hg.mono (hS ζ hmem), EventuallyEq.rfl⟩

/-- **One step of the triangle induction.** Under maximality, the `δ`-thickening of the tube
over the triangle of a smaller scale is absorbed into `A`. -/
theorem thickening_tri_subset_of_maximal (hA : IsOpen A) (hAs : StarConvex ℝ p A) (hp : p ∈ A)
    (hmax : ∀ B : Set (Fin n → ℝ), IsOpen B → StarConvex ℝ p B →
      (∀ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain A) →
        ∃ G : (Fin n → ℂ) → F, AnalyticOnNhd ℂ G (tubeDomain B) ∧ EqOn G g (tubeDomain A)) →
      B ⊆ A)
    {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ w ∈ tubeDomain (segment ℝ p t₁ ∪ segment ℝ p t₂), ball w δ ⊆ tubeDomain A)
    {a b : ℝ} (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hba : b ≤ a) (hlt : b = 0 ∨ b < a)
    (htri : tri p t₁ t₂ a ⊆ A) : thickening δ (tri p t₁ t₂ b) ⊆ A := by
  classical
  set L := tri p t₁ t₂ b with hL
  set N := thickening δ L with hN
  have hLconv : Convex ℝ L := convex_tri p t₁ t₂ b
  have hpL : p ∈ L := mem_tri_self p t₁ t₂ hb0
  have hLA : L ⊆ A := (tri_mono p t₁ t₂ hba).trans htri
  have hNo : IsOpen N := isOpen_thickening
  have hNc : Convex ℝ N := hLconv.thickening δ
  have hpN : p ∈ N := self_subset_thickening hδ L hpL
  have hNs : StarConvex ℝ p N := hNc.starConvex hpN
  have hTN : tubeDomain N ⊆ ⋃ ζ ∈ tubeDomain L, ball ζ δ := by
    intro z hz
    rw [mem_tubeDomain, hN, Metric.mem_thickening_iff] at hz
    obtain ⟨y, hy, hdist⟩ := hz
    refine mem_iUnion₂.mpr ⟨ofRealPi y + I • ofRealPi (imPi z), ?_, ?_⟩
    · rw [mem_tubeDomain, rePi_add, rePi_ofRealPi, rePi_I_smul_ofRealPi, add_zero]
      exact hy
    · rw [mem_ball, dist_eq_norm]
      have hz := ofRealPi_rePi_add_I_smul_ofRealPi_imPi z
      have : z - (ofRealPi y + I • ofRealPi (imPi z)) = ofRealPi (rePi z - y) := by
        rw [ofRealPi_sub]
        nth_rewrite 1 [← hz]
        abel
      rw [this, norm_ofRealPi, ← dist_eq_norm]
      exact hdist
  have hsub : A ∪ N ⊆ A := by
    refine hmax (A ∪ N) (hA.union hNo) (hAs.union hNs) fun g hg => ?_
    have hloc := exists_local_continuation_tri hA ha1 htri hδ hS hba hlt hg
    obtain ⟨H, hHa, hHg⟩ := exists_glue_of_local_continuations (isOpen_tubeDomain hA)
      (convex_tubeDomain hLconv) (tubeDomain_mono hLA) hg hδ hloc
    have hHN : AnalyticOnNhd ℂ H (tubeDomain N) := hHa.mono hTN
    have hAN : EqOn H g (tubeDomain (A ∩ N)) := by
      have hpAN : p ∈ A ∩ N := ⟨hp, hpN⟩
      exact (hHN.mono (tubeDomain_mono inter_subset_right)).eqOn_of_preconnected_of_eventuallyEq
        (hg.mono (tubeDomain_mono inter_subset_left))
        (isPreconnected_tubeDomain_of_starConvex (hAs.inter hNs) hpAN)
        (ofRealPi_mem_tubeDomain.mpr hpAN) (hHg _ (ofRealPi_mem_tubeDomain.mpr hpL))
    refine ⟨fun z => if z ∈ tubeDomain A then g z else H z, ?_, fun z hz => by simp [hz]⟩
    intro z hz
    rw [tubeDomain_union] at hz
    rcases hz with hzA | hzN
    · have : (fun z => if z ∈ tubeDomain A then g z else H z) =ᶠ[𝓝 z] g :=
        eventuallyEq_of_mem ((isOpen_tubeDomain hA).mem_nhds hzA) fun w hw => by simp [hw]
      exact (hg z hzA).congr this.symm
    · have : (fun z => if z ∈ tubeDomain A then g z else H z) =ᶠ[𝓝 z] H := by
        refine eventuallyEq_of_mem ((isOpen_tubeDomain hNo).mem_nhds hzN) fun w hw => ?_
        by_cases hwA : w ∈ tubeDomain A
        · simp only [hwA, ite_true]
          exact (hAN ⟨hwA, hw⟩).symm
        · simp only [hwA, ite_false]
      exact (hHN z hzN).congr this.symm
  exact subset_union_right.trans hsub

/-- **The triangle lemma.** Under maximality, the full triangle with vertex `p` and two
points of `A` lies in `A`. -/
theorem tri_subset_of_maximal (hA : IsOpen A) (hAs : StarConvex ℝ p A) (hp : p ∈ A)
    (hmax : ∀ B : Set (Fin n → ℝ), IsOpen B → StarConvex ℝ p B →
      (∀ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain A) →
        ∃ G : (Fin n → ℂ) → F, AnalyticOnNhd ℂ G (tubeDomain B) ∧ EqOn G g (tubeDomain A)) →
      B ⊆ A)
    (ht₁ : t₁ ∈ A) (ht₂ : t₂ ∈ A) : tri p t₁ t₂ 1 ⊆ A := by
  have hS_sub : segment ℝ p t₁ ∪ segment ℝ p t₂ ⊆ A :=
    union_subset (hAs.segment_subset ht₁) (hAs.segment_subset ht₂)
  have hS_cpt : IsCompact (segment ℝ p t₁ ∪ segment ℝ p t₂) := by
    refine IsCompact.union ?_ ?_ <;>
      · rw [segment_eq_image']
        exact isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδ, hδA⟩ := hS_cpt.exists_thickening_subset_open hA hS_sub
  have hS : ∀ w ∈ tubeDomain (segment ℝ p t₁ ∪ segment ℝ p t₂), ball w δ ⊆ tubeDomain A :=
    fun w hw => ball_subset_tubeDomain
      ((ball_subset_thickening (E := segment ℝ p t₁ ∪ segment ℝ p t₂) (x := rePi w) hw δ).trans hδA)
  set D : ℝ := ‖triDir₁ p t₁ t₂‖ + ‖triDir₂ p t₁ t₂‖ with hD
  have hD0 : 0 ≤ D := by positivity
  rcases hD0.lt_or_eq with hDpos | hDzero
  swap
  · have h1 : triDir₁ p t₁ t₂ = 0 :=
      norm_eq_zero.mp (by linarith [norm_nonneg (triDir₁ p t₁ t₂), norm_nonneg (triDir₂ p t₁ t₂)])
    have h2 : triDir₂ p t₁ t₂ = 0 :=
      norm_eq_zero.mp (by linarith [norm_nonneg (triDir₁ p t₁ t₂), norm_nonneg (triDir₂ p t₁ t₂)])
    rintro x ⟨u, v, -, -, rfl⟩
    simpa [triPt, h1, h2] using hp
  set δ₁ : ℝ := δ / (4 * D) with hδ₁def
  set ε : ℝ := min (1 / 2) (δ / (4 * D)) with hεdef
  have hδ₁ : 0 < δ₁ := by positivity
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hεD : ε ≤ δ / (4 * D) := min_le_right _ _
  have key : ∀ a : ℝ, 0 ≤ a → a ≤ 1 → tri p t₁ t₂ a ⊆ A →
      ∀ a' : ℝ, a ≤ a' → a' ≤ 1 → a' ≤ a + δ₁ → tri p t₁ t₂ a' ⊆ A := by
    intro a ha0 ha1 htri a' haa' ha'1 ha'δ
    set b : ℝ := (1 - ε) * a with hb
    have hb0 : 0 ≤ b := mul_nonneg (by linarith) ha0
    have hba : b ≤ a := by nlinarith
    have hlt : b = 0 ∨ b < a := by
      rcases ha0.lt_or_eq with h | h
      · right; nlinarith
      · left; rw [hb, ← h, mul_zero]
    have hthick := thickening_tri_subset_of_maximal hA hAs hp hmax hδ hS ha1 hb0 hba hlt htri
    rintro x ⟨u, v, huv, hva', rfl⟩
    by_cases hvb : v ≤ b
    · exact hthick (self_subset_thickening hδ _ ⟨u, v, huv, hvb, rfl⟩)
    · push Not at hvb
      have hv0 : 0 < v := hb0.trans_lt hvb
      set μ : ℝ := b / v with hμ
      have hμ0 : 0 ≤ μ := div_nonneg hb0 hv0.le
      have hμ1 : μ ≤ 1 := (div_le_one hv0).mpr hvb.le
      have hμv : μ * v = b := div_mul_cancel₀ b hv0.ne'
      apply hthick
      rw [Metric.mem_thickening_iff]
      refine ⟨triPt p t₁ t₂ (μ * u) (μ * v), ⟨μ * u, μ * v, ?_, ?_, rfl⟩, ?_⟩
      · rw [abs_mul, abs_of_nonneg hμ0]
        exact mul_le_mul_of_nonneg_left huv hμ0
      · rw [hμv]
      · rw [dist_eq_norm]
        have hdiff : triPt p t₁ t₂ u v - triPt p t₁ t₂ (μ * u) (μ * v) =
            ((1 - μ) * u) • triDir₁ p t₁ t₂ + ((1 - μ) * v) • triDir₂ p t₁ t₂ := by
          simp only [triPt]
          module
        have h1 : v - b ≤ (a' - a) + ε * a := by rw [hb]; nlinarith
        have h2 : (a' - a) + ε * a ≤ δ₁ + ε := by nlinarith
        calc ‖triPt p t₁ t₂ u v - triPt p t₁ t₂ (μ * u) (μ * v)‖
            = ‖((1 - μ) * u) • triDir₁ p t₁ t₂ + ((1 - μ) * v) • triDir₂ p t₁ t₂‖ := by rw [hdiff]
          _ ≤ ‖((1 - μ) * u) • triDir₁ p t₁ t₂‖ + ‖((1 - μ) * v) • triDir₂ p t₁ t₂‖ :=
              norm_add_le _ _
          _ = (1 - μ) * |u| * ‖triDir₁ p t₁ t₂‖ + (1 - μ) * v * ‖triDir₂ p t₁ t₂‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
                abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - μ), abs_of_pos hv0]
          _ ≤ (1 - μ) * v * ‖triDir₁ p t₁ t₂‖ + (1 - μ) * v * ‖triDir₂ p t₁ t₂‖ := by
              gcongr
          _ = (v - b) * D := by rw [hD, ← hμv]; ring
          _ ≤ (δ₁ + ε) * D := mul_le_mul_of_nonneg_right (h1.trans h2) hDpos.le
          _ ≤ (δ / (4 * D) + δ / (4 * D)) * D := by gcongr
          _ = δ / 2 := by field_simp; ring
          _ < δ := half_lt_self hδ
  have hind : ∀ k : ℕ, tri p t₁ t₂ (min 1 (k * δ₁)) ⊆ A := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero, zero_mul, min_eq_right zero_le_one, tri_zero]
      simpa using hp
    | succ k ih =>
      have hk0 : (0 : ℝ) ≤ k * δ₁ := by positivity
      refine key (min 1 (k * δ₁)) (le_min zero_le_one hk0) (min_le_left _ _) ih _ ?_
        (min_le_left _ _) ?_
      · exact min_le_min_left _ (by push_cast; nlinarith)
      · rcases le_or_gt 1 (k * δ₁) with h | h
        · rw [min_eq_left h]
          exact le_add_of_le_of_nonneg (min_le_left _ _) hδ₁.le
        · rw [min_eq_right h.le]
          push_cast
          refine (min_le_right _ _).trans ?_
          rw [add_mul, one_mul]
  obtain ⟨k, hk⟩ := exists_nat_ge (1 / δ₁)
  have hk1 : 1 ≤ k * δ₁ := by
    rw [div_le_iff₀ hδ₁] at hk
    linarith
  have := hind k
  rwa [min_eq_left hk1] at this

end Triangle

section Convex

variable {Ω : Set (Fin n → ℝ)} {p : Fin n → ℝ}

/-- **The maximal star-convex extension base is convex.** -/
theorem convex_maxStar (hp : p ∈ maxStar F Ω p) : Convex ℝ (maxStar F Ω p) := by
  rw [convex_iff_segment_subset]
  intro t₁ ht₁ t₂ ht₂
  exact (segment_subset_tri p t₁ t₂).trans (tri_subset_of_maximal isOpen_maxStar starConvex_maxStar
    hp (fun _ hB hBs hext => maxStar_maximal hp hB hBs hext) ht₁ ht₂)

/-- **Bochner's tube theorem for star-convex bases.** Every Banach-valued holomorphic function
on the tube over an open star-convex base extends to the tube over the convex hull. -/
theorem exists_extension_tubeDomain_convexHull_of_starConvex (hΩ : IsOpen Ω)
    (hs : StarConvex ℝ p Ω) (hp : p ∈ Ω) {f : (Fin n → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f (tubeDomain Ω)) :
    ∃ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain (convexHull ℝ Ω)) ∧
      EqOn g f (tubeDomain Ω) := by
  have hΩmem : Ω ∈ starFamily F Ω p := ⟨hΩ, hs, fun f hf => ⟨f, hf, EventuallyEq.rfl⟩⟩
  have hΩsub : Ω ⊆ maxStar F Ω p := subset_maxStar_of_mem hΩmem
  have hpm : p ∈ maxStar F Ω p := hΩsub hp
  have hconv : convexHull ℝ Ω ⊆ maxStar F Ω p := convexHull_min hΩsub (convex_maxStar hpm)
  obtain ⟨g, hg, hgf⟩ := tubeExtends_maxStar hpm f hf
  refine ⟨g, hg.mono (tubeDomain_mono hconv), ?_⟩
  exact (hg.mono (tubeDomain_mono hΩsub)).eqOn_of_preconnected_of_eventuallyEq hf
    (isPreconnected_tubeDomain_of_starConvex hs hp) (ofRealPi_mem_tubeDomain.mpr hp) hgf

end Convex

end SeveralComplexVariables
