/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.ZeroSets.Basic
public import Mathlib.Topology.Germ
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The local ring of analytic germs

An analytic germ is a Mathlib `Filter.Germ` with a representative analytic at the base point.
Equality is agreement on a neighborhood, rather than equality just at the base point.
The scalar germs form a complex algebra and an integral domain. Evaluation detects its units,
identifies its unique maximal ideal with the germs vanishing at the base point, and identifies
the quotient with `ℂ`. Analytic maps act contravariantly by complex algebra homomorphisms.

The motivating references are Suwa (2024), Section 1.4, Propositions 1.5--1.7, and
Jakóbczak--Jarnicki (2021), Section 1.8. We use `AnalyticAt` for convergent power series;
on finite-dimensional complex domains this agrees with the project's holomorphic convention.
The construction also works on arbitrary complex normed spaces, including the zero space.
Analytic Weierstrass division and preparation are not asserted here.
-/

@[expose] public noncomputable section

open Filter Set Metric
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The subring of germs admitting a representative analytic at the base point. -/
def analyticGermSubring (x : E) : Subring (Germ (𝓝 x) ℂ) where
  carrier := {φ | ∃ f : E → ℂ, AnalyticAt ℂ f x ∧ (f : Germ (𝓝 x) ℂ) = φ}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩

/-- Membership of a represented germ is exactly analyticity of that representative. -/
@[simp] theorem mem_analyticGermSubring {x : E} {f : E → ℂ} :
    (f : Germ (𝓝 x) ℂ) ∈ analyticGermSubring x ↔ AnalyticAt ℂ f x := by
  constructor
  · rintro ⟨g, hg, heq⟩
    exact hg.congr (Germ.coe_eq.mp heq)
  · intro hf
    exact ⟨f, hf, rfl⟩

/-- Scalar analytic germs at `x`, with the ring operations inherited from Mathlib germs. -/
abbrev AnalyticGerm (x : E) := ↥(analyticGermSubring x)

namespace AnalyticGerm

variable {x : E}

/-- The germ of a function analytic at the base point. -/
def ofAnalyticAt (f : E → ℂ) (hf : AnalyticAt ℂ f x) : AnalyticGerm x :=
  ⟨f, f, hf, rfl⟩

/-- Every analytic germ has an analytic representative. -/
theorem exists_rep (φ : AnalyticGerm x) :
    ∃ (f : E → ℂ) (hf : AnalyticAt ℂ f x), ofAnalyticAt f hf = φ := by
  obtain ⟨f, hf, heq⟩ := φ.property
  exact ⟨f, hf, Subtype.ext heq⟩

/-- Analytic germs have no zero divisors, by the analytic identity principle. -/
instance : NoZeroDivisors (AnalyticGerm x) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    obtain ⟨f, hf, rfl⟩ := exists_rep a
    obtain ⟨g, hg, rfl⟩ := exists_rep b
    have hfg : (fun y => f y * g y) =ᶠ[𝓝 x] 0 :=
      Germ.coe_eq.mp (congrArg Subtype.val hab)
    rcases eventuallyEq_zero_or_eventuallyEq_zero_of_mul hf hg hfg with h | h
    · exact Or.inl (Subtype.ext (Germ.coe_eq.mpr h))
    · exact Or.inr (Subtype.ext (Germ.coe_eq.mpr h))

/-- The ring of scalar analytic germs is an integral domain. -/
instance : IsDomain (AnalyticGerm x) := NoZeroDivisors.to_isDomain _

/-- Two analytic representatives define the same germ exactly when they agree nearby. -/
@[simp] theorem ofAnalyticAt_eq_iff {f g : E → ℂ}
    {hf : AnalyticAt ℂ f x} {hg : AnalyticAt ℂ g x} :
    ofAnalyticAt f hf = ofAnalyticAt g hg ↔ f =ᶠ[𝓝 x] g := by
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

/-- The zero germ is represented by the zero function. -/
theorem ofAnalyticAt_zero : ofAnalyticAt (0 : E → ℂ) analyticAt_const = (0 : AnalyticGerm x) := rfl

/-- Sums of analytic representatives compute sums of germs. -/
theorem ofAnalyticAt_add (f g : E → ℂ) (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    ofAnalyticAt (f + g) (hf.add hg) = ofAnalyticAt f hf + ofAnalyticAt g hg := rfl

/-- Products of analytic representatives compute products of germs. -/
theorem ofAnalyticAt_mul (f g : E → ℂ) (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    ofAnalyticAt (f * g) (hf.mul hg) = ofAnalyticAt f hf * ofAnalyticAt g hg := rfl

/-- Powers of analytic representatives compute powers of germs. -/
theorem ofAnalyticAt_pow (f : E → ℂ) (hf : AnalyticAt ℂ f x) (n : ℕ) :
    ofAnalyticAt (f ^ n) (hf.pow n) = ofAnalyticAt f hf ^ n := rfl

/-- Finite sums of analytic representatives compute finite sums of germs. -/
theorem ofAnalyticAt_sum {κ : Type*} (s : Finset κ) (f : κ → E → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) x) (hs : AnalyticAt ℂ (∑ i ∈ s, f i) x) :
    ofAnalyticAt (∑ i ∈ s, f i) hs = ∑ i ∈ s, ofAnalyticAt (f i) (hf i) := by
  apply Subtype.ext
  show ((∑ i ∈ s, f i : E → ℂ) : Germ (𝓝 x) ℂ) =
      ((∑ i ∈ s, ofAnalyticAt (f i) (hf i) : AnalyticGerm x) : Germ (𝓝 x) ℂ)
  rw [AddSubmonoidClass.coe_finsetSum]
  exact map_sum (Filter.Germ.coeRingHom (𝓝 x)) f s

/-- Evaluation of an analytic germ at its base point, as a ring homomorphism. -/
def eval (x : E) : AnalyticGerm x →+* ℂ :=
  Germ.valueRingHom.comp (analyticGermSubring x).subtype

/-- Evaluation of a represented germ is evaluation of its representative. -/
@[simp] theorem eval_ofAnalyticAt (f : E → ℂ) (hf : AnalyticAt ℂ f x) :
    eval x (ofAnalyticAt f hf) = f x := rfl

/-- Constant functions define a ring homomorphism into analytic germs. -/
def const (x : E) : ℂ →+* AnalyticGerm x where
  toFun c := ofAnalyticAt (fun _ => c) analyticAt_const
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Analytic germs form a complex algebra via constant germs. -/
instance : Algebra ℂ (AnalyticGerm x) := (const x).toAlgebra

/-- Evaluation of a constant germ recovers its constant value. -/
@[simp] theorem eval_const (c : ℂ) : eval x (const x c) = c := rfl

/-- Evaluation onto the scalar field is surjective. -/
theorem eval_surjective (x : E) : Function.Surjective (eval x) :=
  fun c => ⟨const x c, rfl⟩

/-- Evaluation also preserves the complex algebra structure. -/
def evalAlgHom (x : E) : AnalyticGerm x →ₐ[ℂ] ℂ where
  __ := eval x
  commutes' _ := rfl

section Pullback

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Composition with an analytic map pulls scalar germs back as a complex algebra homomorphism.
Mathlib's `compTendsto` makes the construction independent of representatives. -/
def pullback (f : E → F) (hf : AnalyticAt ℂ f x) :
    AnalyticGerm (f x) →ₐ[ℂ] AnalyticGerm x where
  toFun φ := ⟨φ.val.compTendsto f hf.continuousAt, by
    obtain ⟨g, hg, heq⟩ := φ.property
    refine ⟨g ∘ f, hg.comp hf, ?_⟩
    rw [← heq]
    rfl⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by
    obtain ⟨g, hg, rfl⟩ := exists_rep a
    obtain ⟨h, hh, rfl⟩ := exists_rep b
    rfl
  map_mul' a b := by
    obtain ⟨g, hg, rfl⟩ := exists_rep a
    obtain ⟨h, hh, rfl⟩ := exists_rep b
    rfl
  commutes' _ := rfl

/-- Pullback of a represented germ is represented by composition. -/
@[simp] theorem pullback_ofAnalyticAt (f : E → F) (hf : AnalyticAt ℂ f x)
    (g : F → ℂ) (hg : AnalyticAt ℂ g (f x)) :
    pullback f hf (ofAnalyticAt g hg) = ofAnalyticAt (g ∘ f) (hg.comp hf) := rfl

/-- Pullback along a map whose value at the source point is only known up to a stated
equation, letting the target germ's base point be phrased as any value equal to `f x`.
Matches `pullback` definitionally once the equation is substituted. -/
def pullback_of_eq (f : E → F) (hf : AnalyticAt ℂ f x) {y : F} (hy : f x = y) :
    AnalyticGerm y →ₐ[ℂ] AnalyticGerm x :=
  hy ▸ pullback f hf

/-- Pullback along an equation-adjusted map of a represented germ is represented by
composition. -/
@[simp] theorem pullback_of_eq_ofAnalyticAt (f : E → F) (hf : AnalyticAt ℂ f x) {y : F}
    (hy : f x = y) (g : F → ℂ) (hg : AnalyticAt ℂ g y) :
    pullback_of_eq f hf hy (ofAnalyticAt g hg) = ofAnalyticAt (g ∘ f) (hg.comp_of_eq hf hy) := by
  subst hy
  rfl

/-- Evaluation commutes with pullback at the corresponding base points. -/
@[simp] theorem eval_pullback (f : E → F) (hf : AnalyticAt ℂ f x)
    (φ : AnalyticGerm (f x)) : eval x (pullback f hf φ) = eval (f x) φ := by
  obtain ⟨g, hg, rfl⟩ := exists_rep φ
  rfl

/-- Pullback by the identity fixes every analytic germ. -/
@[simp] theorem pullback_id (φ : AnalyticGerm x) :
    pullback id analyticAt_id φ = φ := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  rfl

/-- Pullbacks compose in the reverse order to their analytic maps. -/
theorem pullback_comp (f : E → F) (hf : AnalyticAt ℂ f x)
    (g : F → G) (hg : AnalyticAt ℂ g (f x)) (φ : AnalyticGerm (g (f x))) :
    pullback (g ∘ f) (hg.comp hf) φ = pullback f hf (pullback g hg φ) := by
  obtain ⟨h, hh, rfl⟩ := exists_rep φ
  rfl

end Pullback

/-- An analytic germ is invertible exactly when its value at the base point is nonzero. -/
theorem isUnit_iff (φ : AnalyticGerm x) : IsUnit φ ↔ eval x φ ≠ 0 := by
  constructor
  · intro h
    exact (h.map (eval x)).ne_zero
  · obtain ⟨f, hf, rfl⟩ := exists_rep φ
    intro h
    have hne : f x ≠ 0 := h
    let ψ := ofAnalyticAt (fun y => (f y)⁻¹) (hf.inv hne)
    have hmul : ofAnalyticAt f hf * ψ = 1 := by
      apply Subtype.ext
      apply Germ.coe_eq.mpr
      filter_upwards [hf.continuousAt.eventually_ne hne] with y hy
      exact mul_inv_cancel₀ hy
    exact ⟨⟨ofAnalyticAt f hf, ψ, hmul, by rwa [mul_comm]⟩, rfl⟩

/-- Pullback preserves and reflects units, as required of a homomorphism of local rings. -/
theorem isUnit_pullback_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E → F) (hf : AnalyticAt ℂ f x) (φ : AnalyticGerm (f x)) :
    IsUnit (pullback f hf φ) ↔ IsUnit φ := by
  simp only [isUnit_iff, eval_pullback]

/-- The ring of analytic germs is local. -/
instance : IsLocalRing (AnalyticGerm x) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    rw [isUnit_iff, isUnit_iff]
    by_cases ha : eval x a = 0
    · right
      have hv := congrArg (eval x) h
      have hb : eval x b = 1 := by simpa [ha] using hv
      rw [hb]
      exact one_ne_zero
    · exact Or.inl ha

/-- The unique maximal ideal consists precisely of germs vanishing at the base point. -/
@[simp] theorem mem_maximalIdeal_iff (φ : AnalyticGerm x) :
    φ ∈ IsLocalRing.maximalIdeal (AnalyticGerm x) ↔ eval x φ = 0 := by
  simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff]

/-- Evaluation has the unique maximal ideal as its kernel. -/
theorem maximalIdeal_eq_ker_eval (x : E) :
    IsLocalRing.maximalIdeal (AnalyticGerm x) = RingHom.ker (eval x) := by
  ext φ
  exact mem_maximalIdeal_iff φ

/-- Quotienting analytic germs by the evaluation kernel gives the complex numbers. -/
def quotientKerEvalEquiv (x : E) :
    AnalyticGerm x ⧸ RingHom.ker (eval x) ≃+* ℂ :=
  (eval x).quotientKerEquivOfSurjective (eval_surjective x)

/-- The quotient by the unique maximal ideal is canonically the complex numbers. -/
def quotientMaximalIdealEquiv (x : E) :
    AnalyticGerm x ⧸ IsLocalRing.maximalIdeal (AnalyticGerm x) ≃+* ℂ :=
  (Ideal.quotEquivOfEq (maximalIdeal_eq_ker_eval x)).trans (quotientKerEvalEquiv x)

/-- In dimension zero, every analytic germ is the constant germ of its value. -/
theorem const_eval_of_subsingleton [Subsingleton E] (φ : AnalyticGerm x) :
    const x (eval x φ) = φ := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall fun y => congrArg f (Subsingleton.elim x y)

/-- Analytic germs on a zero-dimensional domain form exactly the scalar field. -/
def equivComplexOfSubsingleton [Subsingleton E] (x : E) : AnalyticGerm x ≃+* ℂ :=
  RingEquiv.ofBijective (eval x) ⟨fun a b h => by
    rw [← const_eval_of_subsingleton a, ← const_eval_of_subsingleton b, h],
    eval_surjective x⟩

end AnalyticGerm
end SeveralComplexVariables

