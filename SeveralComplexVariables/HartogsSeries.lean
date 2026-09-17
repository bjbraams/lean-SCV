/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.Basic
public import SeveralComplexVariables.HartogsDomain
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Hartogs–Taylor and Hartogs–Laurent expansions

Functions take values in a complex Banach space, and the base is a finite-dimensional
complex normed space (possibly zero dimensional). Taylor coefficients are the normalized
iterated derivatives in the fiber variable at zero. On an open complete Hartogs set these
coefficients are holomorphic on the base and the expansion converges locally uniformly.

The Laurent theorem assumes Hartogs symmetry and, separately, preconnected fibers.
Its coefficients are single-valued holomorphic functions on the projected base. Without
the fiber assumption, coefficients need only be locally functions of the base variable;
connectedness of the total set does not repair that issue. Thus we make explicit the
hypothesis needed for the global-base interpretation of Range's Exercise E.1.10.
Negative coefficients vanish on fibers containing zero. Integer powers in Lean are
totalized at zero, so this vanishing is recorded as part of the Laurent statement.

`HasSumLocallyUniformlyOn` uses finite subsets of the index type, including for the
integer-indexed Laurent series. It gives unconditional pointwise convergence and uniform
convergence on compact subsets. We use `ℤ → E → F`, rather than the algebraic `LaurentSeries`,
whose support must be bounded below and therefore excludes general essential singularities.
Neither theorem needs the base or the total set to be
connected or nonempty. The two main expansion theorems currently have pending proofs;
their pointwise and compact-convergence consequences depend on them.

References: Shabat (1991), I §3.8, Theorem 1 and the Hartogs–Laurent expansion, pp. 34–36;
Range (1986), Chapter I, E.1.9–E.1.10.
-/

@[expose] public noncomputable section

open Set

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The Taylor coefficient in the distinguished fiber coordinate, centered at zero. -/
def hartogsTaylorCoeff (f : E × ℂ → F) (k : ℕ) (z : E) : F :=
  ((k.factorial : ℂ)⁻¹) • iteratedDeriv k (fun w => f (z, w)) 0

/-- The constant coefficient is restriction to the zero section. -/
@[simp] theorem hartogsTaylorCoeff_zero (f : E × ℂ → F) (z : E) :
    hartogsTaylorCoeff f 0 z = f (z, 0) := by
  simp [hartogsTaylorCoeff]

variable [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace F] {U : Set (E × ℂ)} {f : E × ℂ → F}

/-- **Hartogs–Taylor expansion.** Holomorphic functions on open complete Hartogs sets
have holomorphic Taylor coefficients on the base and a locally uniformly convergent
fiber expansion. Proof pending: use local product neighborhoods, the Cauchy formula,
and one-variable Taylor convergence on each centered disc fiber. -/
theorem hartogsTaylor_expansion (hU : IsOpen U) (hH : IsCompleteHartogs U)
    (hf : DifferentiableOn ℂ f U) :
    (∀ k, DifferentiableOn ℂ (hartogsTaylorCoeff f k) (hartogsBase U)) ∧
      HasSumLocallyUniformlyOn
        (fun k (p : E × ℂ) => p.2 ^ k • hartogsTaylorCoeff f k p.1) f U := by
  sorry

/-- The canonical Hartogs–Taylor coefficients are holomorphic on the projected base.
This follows from the pending Taylor expansion theorem. -/
theorem differentiableOn_hartogsTaylorCoeff (hU : IsOpen U) (hH : IsCompleteHartogs U)
    (hf : DifferentiableOn ℂ f U) (k : ℕ) :
    DifferentiableOn ℂ (hartogsTaylorCoeff f k) (hartogsBase U) :=
  (hartogsTaylor_expansion hU hH hf).1 k

/-- The Hartogs–Taylor series sums to the function at every point of the set.
This follows from the pending Taylor expansion theorem. -/
theorem hasSum_hartogsTaylor (hU : IsOpen U) (hH : IsCompleteHartogs U)
    (hf : DifferentiableOn ℂ f U) {p : E × ℂ} (hp : p ∈ U) :
    HasSum (fun k => p.2 ^ k • hartogsTaylorCoeff f k p.1) (f p) :=
  (hartogsTaylor_expansion hU hH hf).2.hasSum hp

/-- Hartogs–Taylor sums converge uniformly on each compact subset of the set.
This follows from the pending Taylor expansion theorem. -/
theorem tendstoUniformlyOn_hartogsTaylor (hU : IsOpen U) (hH : IsCompleteHartogs U)
    (hf : DifferentiableOn ℂ f U) {K : Set (E × ℂ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn
      (fun s : Finset ℕ => fun p : E × ℂ => ∑ k ∈ s, p.2 ^ k • hartogsTaylorCoeff f k p.1)
      f Filter.atTop K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((hartogsTaylor_expansion hU hH hf).2.mono hKU)

/-- **Hartogs–Laurent expansion with connected nonempty fibers.** The coefficients are
holomorphic on the whole projected base, the series converges locally uniformly, and
negative coefficients vanish on every fiber containing zero. Proof pending: use the
one-variable Laurent formula and connected fibers to glue local coefficient functions.
The independent fiber hypothesis is essential for this global-base formulation. -/
theorem exists_hartogsLaurent_expansion (hU : IsOpen U) (hH : IsHartogs U)
    (hfib : HasPreconnectedFibers U) (hf : DifferentiableOn ℂ f U) :
    ∃ a : ℤ → E → F,
      (∀ k, DifferentiableOn ℂ (a k) (hartogsBase U)) ∧
      (∀ z, (z, 0) ∈ U → ∀ k : ℤ, k < 0 → a k z = 0) ∧
      HasSumLocallyUniformlyOn (fun k (p : E × ℂ) => p.2 ^ k • a k p.1) f U := by
  sorry

/-- A pointwise version of the Hartogs–Laurent expansion, retaining global holomorphic
coefficients and their vanishing at the zero section. Depends on the pending expansion. -/
theorem exists_hasSum_hartogsLaurent (hU : IsOpen U) (hH : IsHartogs U)
    (hfib : HasPreconnectedFibers U) (hf : DifferentiableOn ℂ f U) :
    ∃ a : ℤ → E → F,
      (∀ k, DifferentiableOn ℂ (a k) (hartogsBase U)) ∧
      (∀ z, (z, 0) ∈ U → ∀ k : ℤ, k < 0 → a k z = 0) ∧
      ∀ p ∈ U, HasSum (fun k => p.2 ^ k • a k p.1) (f p) := by
  obtain ⟨a, ha, hzero, hsum⟩ := exists_hartogsLaurent_expansion hU hH hfib hf
  exact ⟨a, ha, hzero, fun _ hp => hsum.hasSum hp⟩

end SeveralComplexVariables
