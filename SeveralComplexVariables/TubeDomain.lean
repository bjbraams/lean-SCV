/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.DomainOfHolomorphy
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Convex.Topology

/-!
# Tube domains and Bochner's tube theorem

The tube over a real base consists of complex points whose real parts belong to that
base. The tube theorem extends functions to the tube over the real convex hull, inside
the same complex coordinate space. No abstract envelope is constructed. Connectedness
of the base is essential to the extension theorem. Banach-valued targets and empty
coordinate types are retained.

Bochner extension is a pending analytic theorem. Elementary tube geometry and extension
uniqueness are proved; the convex-base characterization of tube domains of holomorphy
is deduced from Bochner extension and the proved convex-domain example.

References: Scheidemann §6.3; Hörmander §2.5, Theorem 2.5.10.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace SeveralComplexVariables

variable {ι : Type*}

/-- The tube over a real coordinate set; imaginary coordinates are unrestricted. -/
def tubeDomain (Ω : Set (ι → ℝ)) : Set (ι → ℂ) :=
  {z | (fun i => (z i).re) ∈ Ω}

/-- A real point belongs to a tube exactly when it belongs to the base. -/
@[simp] theorem ofReal_mem_tubeDomain {Ω : Set (ι → ℝ)} {x : ι → ℝ} :
    (fun i => (x i : ℂ)) ∈ tubeDomain Ω ↔ x ∈ Ω := by simp [tubeDomain]

/-- Tubes are monotone in their real bases. -/
theorem tubeDomain_mono {Ω Ξ : Set (ι → ℝ)} (h : Ω ⊆ Ξ) : tubeDomain Ω ⊆ tubeDomain Ξ :=
  fun _ hz => h hz

/-- A nonempty real base has a nonempty tube. -/
theorem nonempty_tubeDomain {Ω : Set (ι → ℝ)} (h : Ω.Nonempty) : (tubeDomain Ω).Nonempty := by
  obtain ⟨x, hx⟩ := h
  exact ⟨fun i => (x i : ℂ), ofReal_mem_tubeDomain.mpr hx⟩

/-- The tube over an open base is open. -/
theorem isOpen_tubeDomain {Ω : Set (ι → ℝ)} (ho : IsOpen Ω) : IsOpen (tubeDomain Ω) :=
  ho.preimage (by fun_prop)

/-- Real convexity of the base implies real convexity of its tube. -/
theorem convex_tubeDomain {Ω : Set (ι → ℝ)} (hc : Convex ℝ Ω) : Convex ℝ (tubeDomain Ω) := by
  intro x hx y hy a b ha hb hab
  have h := hc hx hy ha hb hab
  simpa [tubeDomain, Pi.smul_def, Pi.add_def, smul_eq_mul] using h

/-- Every tube is contained in the tube over the convex hull of its base. -/
theorem tubeDomain_subset_convexHull_base (Ω : Set (ι → ℝ)) :
    tubeDomain Ω ⊆ tubeDomain (convexHull ℝ Ω) := tubeDomain_mono (_root_.subset_convexHull ℝ Ω)

variable [Fintype ι]

/-- **Bochner's tube theorem.** Every Banach-valued holomorphic function on a tube with
connected open base extends to the tube over its real convex hull. Proof pending:
continuation through convex combinations of real base points. -/
theorem exists_extension_tubeDomain_convexHull {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {Ω : Set (ι → ℝ)}
    (ho : IsOpen Ω) (hc : IsConnected Ω) {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f (tubeDomain Ω)) :
    ∃ g : (ι → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain (convexHull ℝ Ω)) ∧
      EqOn g f (tubeDomain Ω) := by
  sorry

/-- Uniqueness of a tube extension to the convexified base, independently of Bochner's
existence theorem. Only a nonempty open original base is needed. -/
theorem eqOn_of_tubeDomain_extension {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {Ω : Set (ι → ℝ)}
    (ho : IsOpen Ω) (hn : Ω.Nonempty) {f g : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f (tubeDomain (convexHull ℝ Ω)))
    (hg : AnalyticOnNhd ℂ g (tubeDomain (convexHull ℝ Ω)))
    (he : EqOn f g (tubeDomain Ω)) : EqOn f g (tubeDomain (convexHull ℝ Ω)) := by
  obtain ⟨a, ha⟩ := nonempty_tubeDomain hn
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_tubeDomain (convex_convexHull ℝ Ω)).isPreconnected
    (tubeDomain_subset_convexHull_base Ω ha)
  filter_upwards [(isOpen_tubeDomain ho).mem_nhds ha] with z hz
  exact he hz

/-- The convexified tube is a common scalar extension domain. Depends on Bochner's
pending extension theorem, without asserting a universal abstract envelope property. -/
theorem isCommonAnalyticExtension_tubeDomain_convexHull {Ω : Set (ι → ℝ)}
    (ho : IsOpen Ω) (hc : IsConnected Ω) :
    IsCommonAnalyticExtension (tubeDomain Ω) (tubeDomain (convexHull ℝ Ω)) :=
  isCommonAnalyticExtension_of_forall (tubeDomain_subset_convexHull_base Ω)
    (fun _ hf => exists_extension_tubeDomain_convexHull ho hc hf)

/-- A tube with connected open base is a domain of holomorphy exactly when its base is
convex. The forward implication depends on Bochner's pending extension theorem. -/
theorem isDomainOfHolomorphy_tubeDomain_iff {Ω : Set (ι → ℝ)}
    (ho : IsOpen Ω) (hc : IsConnected Ω) :
    IsDomainOfHolomorphy (tubeDomain Ω) ↔ Convex ℝ Ω := by
  constructor
  · intro h
    have he := h.eq_of_commonExtension (isOpen_tubeDomain ho) (nonempty_tubeDomain hc.nonempty)
      (isOpen_tubeDomain (ho.convexHull (𝕜 := ℝ)))
      ⟨(nonempty_tubeDomain hc.nonempty).mono (tubeDomain_subset_convexHull_base Ω),
        (convex_tubeDomain (convex_convexHull ℝ Ω)).isPreconnected⟩
      (isCommonAnalyticExtension_tubeDomain_convexHull ho hc)
    have heq : convexHull ℝ Ω = Ω := by
      apply Subset.antisymm _ (_root_.subset_convexHull ℝ Ω)
      intro x hx
      apply ofReal_mem_tubeDomain.mp
      rw [← he]
      exact ofReal_mem_tubeDomain.mpr hx
    rw [← heq]
    exact convex_convexHull ℝ Ω
  · intro h
    exact isDomainOfHolomorphy_of_convex (convex_tubeDomain h) (isOpen_tubeDomain ho)

end SeveralComplexVariables
