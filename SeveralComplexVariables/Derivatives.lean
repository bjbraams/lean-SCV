/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import SeveralComplexVariables.Basic

/-!
# Coordinate derivatives of holomorphic functions

Coordinate differentiation is defined using one-variable slices, and identified with
evaluation of the Fréchet derivative on a coordinate vector. Holomorphy of derivatives
is inherited from Mathlib's general Fréchet derivative theorem. Mixed derivatives can be
indexed by coordinate lists or multi-indices; permutation invariance identifies these forms.
-/

@[expose] public noncomputable section

open Complex Filter Function Set
open scoped Classical Topology

namespace SeveralComplexVariables

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Differentiate in coordinate `i`, holding all other coordinates fixed. -/
def partialDeriv (i : ι) (f : (ι → ℂ) → F) (z : ι → ℂ) : F :=
  deriv (fun w => f (update z i w)) (z i)

/-- The derivative of a coordinate slice is the corresponding Fréchet derivative value. -/
theorem hasDerivAt_update_of_differentiableAt {f : (ι → ℂ) → F} {z : ι → ℂ}
    (hf : DifferentiableAt ℂ f z) (i : ι) :
    HasDerivAt (fun w => f (update z i w)) (fderiv ℂ f z (Pi.single i 1)) (z i) := by
  have hf' : HasFDerivAt f (fderiv ℂ f z) (update z i (z i)) := by simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt (z i) (hasDerivAt_update z i (z i))

/-- Coordinate derivatives are Fréchet derivatives evaluated on coordinate vectors. -/
theorem partialDeriv_eq_fderiv {f : (ι → ℂ) → F} {z : ι → ℂ}
    (hf : DifferentiableAt ℂ f z) (i : ι) :
    partialDeriv i f z = fderiv ℂ f z (Pi.single i 1) :=
  (hasDerivAt_update_of_differentiableAt hf i).deriv

/-- A coordinate derivative only depends on the germ of the function. -/
theorem partialDeriv_congr {f g : (ι → ℂ) → F} {z : ι → ℂ}
    (hfg : f =ᶠ[𝓝 z] g) (i : ι) : partialDeriv i f z = partialDeriv i g z := by
  apply Filter.EventuallyEq.deriv_eq
  have ht : Tendsto (update z i) (𝓝 (z i)) (𝓝 z) := by
    simpa using (hasDerivAt_update z i (z i)).continuousAt.tendsto
  exact hfg.comp_tendsto ht

/-- The Fréchet derivative is recovered from the coordinate derivatives. -/
theorem fderiv_eq_sum_partialDeriv {f : (ι → ℂ) → F} {z : ι → ℂ}
    (hf : DifferentiableAt ℂ f z) (v : ι → ℂ) :
    fderiv ℂ f z v = ∑ i, v i • partialDeriv i f z := by
  simp_rw [partialDeriv_eq_fderiv hf, ← map_smul, ← map_sum]
  congr 1
  ext j
  simp [Pi.single_apply]

/-- Coordinate differentiation respects subtraction at differentiability points. -/
theorem partialDeriv_sub {f g : (ι → ℂ) → F} {z : ι → ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) (i : ι) :
    partialDeriv i (f - g) z = partialDeriv i f z - partialDeriv i g z := by
  exact deriv_sub (hasDerivAt_update_of_differentiableAt hf i).differentiableAt
    (hasDerivAt_update_of_differentiableAt hg i).differentiableAt

/-- Holomorphy restricts to each coordinate slice. -/
theorem _root_.AnalyticOnNhd.analyticAt_update {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) {z : ι → ℂ} (hz : z ∈ U) (i : ι) :
    AnalyticAt ℂ (fun w => f (update z i w)) (z i) := by
  have hu : AnalyticAt ℂ (update z i) (z i) :=
    analyticAt_iff_eventually_differentiableAt.mpr
      (Eventually.of_forall fun w => (hasDerivAt_update z i w).differentiableAt)
  exact (hf z hz).comp_of_eq hu (update_eq_self i z)

/-- Coordinate differentiation commutes with a finite sum of differentiable functions. -/
theorem partialDeriv_finset_sum {α : Type*} {f : α → (ι → ℂ) → F}
    (t : Finset α) {z : ι → ℂ} (hf : ∀ a ∈ t, DifferentiableAt ℂ (f a) z) (i : ι) :
    partialDeriv i (fun w => ∑ a ∈ t, f a w) z = ∑ a ∈ t, partialDeriv i (f a) z := by
  exact deriv_fun_sum fun a ha => (hasDerivAt_update_of_differentiableAt (hf a ha) i).differentiableAt

variable [CompleteSpace F]

/-- Every coordinate derivative of an analytic function is analytic. -/
theorem _root_.AnalyticOnNhd.partialDeriv {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U) (i : ι) :
    AnalyticOnNhd ℂ (partialDeriv i f) U := by
  intro z hz
  have ha : AnalyticAt ℂ (fun w => fderiv ℂ f w (Pi.single i 1)) z := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using!
      ((ContinuousLinearMap.apply ℂ F (Pi.single i (1 : ℂ))).analyticAt
        (fderiv ℂ f z)).comp_of_eq (hf z hz).fderiv rfl
  apply ha.congr
  filter_upwards [hU.eventually_mem hz] with w hw
  exact (partialDeriv_eq_fderiv (hf w hw).differentiableAt i).symm

/-- Repeated coordinate differentiation, with the leftmost coordinate acting last. -/
def iteratedPartialDeriv : List ι → ((ι → ℂ) → F) → (ι → ℂ) → F
  | [], f => f
  | i :: is, f => partialDeriv i (iteratedPartialDeriv is f)

/-- Differentiate a coordinate derivative by composing the second Fréchet derivative
with evaluation on its coordinate vector. -/
theorem hasFDerivAt_partialDeriv {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U) {z : ι → ℂ} (hz : z ∈ U) (i : ι) :
    HasFDerivAt (partialDeriv i f)
      ((ContinuousLinearMap.apply ℂ F (Pi.single i 1)).comp
        (fderiv ℂ (fderiv ℂ f) z)) z := by
  have H := (ContinuousLinearMap.apply ℂ F (Pi.single i (1 : ℂ))).hasFDerivAt.comp z
    (hf z hz).fderiv.differentiableAt.hasFDerivAt
  apply H.congr_of_eventuallyEq
  filter_upwards [hU.eventually_mem hz] with w hw
  exact partialDeriv_eq_fderiv (hf w hw).differentiableAt i

/-- Mixed coordinate derivatives commute for a holomorphic function. -/
theorem partialDeriv_partialDeriv_comm {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U) {z : ι → ℂ} (hz : z ∈ U) (i j : ι) :
    partialDeriv i (partialDeriv j f) z = partialDeriv j (partialDeriv i f) z := by
  rw [partialDeriv_eq_fderiv (hasFDerivAt_partialDeriv hf hU hz j).differentiableAt,
    partialDeriv_eq_fderiv (hasFDerivAt_partialDeriv hf hU hz i).differentiableAt,
    (hasFDerivAt_partialDeriv hf hU hz j).fderiv,
    (hasFDerivAt_partialDeriv hf hU hz i).fderiv]
  exact (hf z hz).contDiffAt.isSymmSndFDerivAt_of_omega (Pi.single i 1) (Pi.single j 1)

/-- All iterated coordinate derivatives are holomorphic on the original open domain. -/
theorem _root_.AnalyticOnNhd.iteratedPartialDeriv {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U) (is : List ι) :
    AnalyticOnNhd ℂ (iteratedPartialDeriv is f) U := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact ih.partialDeriv hU i

/-- Iterated coordinate derivatives depend only on the multiplicity of each coordinate,
not on their order in the differentiation list. -/
theorem iteratedPartialDeriv_perm {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U) {is js : List ι} (h : is.Perm js) :
    EqOn (iteratedPartialDeriv is f) (iteratedPartialDeriv js f) U := by
  induction h with
  | nil => intro z hz; rfl
  | cons i h ih =>
      intro z hz
      apply partialDeriv_congr
      filter_upwards [hU.eventually_mem hz] with w hw
      exact ih hw
  | swap i j is =>
      intro z hz
      exact partialDeriv_partialDeriv_comm (hf.iteratedPartialDeriv hU is) hU hz j i
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

omit [CompleteSpace F] in
/-- Iterated coordinate derivatives agree on an open set where the original functions agree. -/
theorem iteratedPartialDeriv_congrOn {U : Set (ι → ℂ)} {f g : (ι → ℂ) → F}
    (hU : IsOpen U) (hfg : EqOn f g U) (is : List ι) :
    EqOn (iteratedPartialDeriv is f) (iteratedPartialDeriv is g) U := by
  induction is with
  | nil => exact hfg
  | cons i is ih =>
    intro z hz
    apply partialDeriv_congr
    filter_upwards [hU.eventually_mem hz] with w hw
    exact ih hw

/-- Mixed coordinate differentiation commutes with finite sums of holomorphic functions. -/
theorem iteratedPartialDeriv_finset_sum {α : Type*} {U : Set (ι → ℂ)}
    {f : α → (ι → ℂ) → F} (t : Finset α) (hf : ∀ a ∈ t, AnalyticOnNhd ℂ (f a) U)
    (hU : IsOpen U) (is : List ι) :
    EqOn (iteratedPartialDeriv is (fun z => ∑ a ∈ t, f a z))
      (fun z => ∑ a ∈ t, iteratedPartialDeriv is (f a) z) U := by
  induction is with
  | nil => intro z hz; rfl
  | cons i is ih =>
    intro z hz
    change partialDeriv i (iteratedPartialDeriv is (fun w => ∑ a ∈ t, f a w)) z = _
    have heq : iteratedPartialDeriv is (fun w => ∑ a ∈ t, f a w) =ᶠ[𝓝 z]
        (fun w => ∑ a ∈ t, iteratedPartialDeriv is (f a) w) :=
      (hU.eventually_mem hz).mono (fun w hw => ih hw)
    rw [partialDeriv_congr heq i]
    exact partialDeriv_finset_sum t
      (fun a ha => ((hf a ha).iteratedPartialDeriv hU is z hz).differentiableAt) i

section MultiIndex

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A canonical list containing coordinate `i` exactly `m i` times. -/
def multiIndexList (m : Fin d → ℕ) : List (Fin d) :=
  (List.ofFn (fun i => List.replicate (m i) i)).flatten

/-- The canonical coordinate list has the prescribed multiplicities. -/
@[simp] theorem count_multiIndexList (m : Fin d → ℕ) (i : Fin d) :
    (multiIndexList m).count i = m i := by
  simp [multiIndexList, List.count_flatten, List.map_ofFn, List.count_replicate,
    List.sum_ofFn]

/-- The mixed coordinate derivative of multi-index `m`, in canonical coordinate order.
For holomorphic maps, permutation invariance makes the choice of order immaterial. -/
def multiIndexDeriv (m : Fin d → ℕ) (f : (Fin d → ℂ) → E) : (Fin d → ℂ) → E :=
  iteratedPartialDeriv (multiIndexList m) f

variable [CompleteSpace E]

/-- The mixed derivative can be computed in any order with the prescribed multiplicities. -/
theorem iteratedPartialDeriv_eq_multiIndexDeriv {U : Set (Fin d → ℂ)}
    {f : (Fin d → ℂ) → E} (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U)
    {z : Fin d → ℂ} (hz : z ∈ U) {is : List (Fin d)} {m : Fin d → ℕ}
    (hm : ∀ i, is.count i = m i) : iteratedPartialDeriv is f z = multiIndexDeriv m f z := by
  apply iteratedPartialDeriv_perm hf hU _ hz
  apply List.perm_iff_count.mpr
  simpa using hm

end MultiIndex

/-- The complex Jacobian in the standard coordinate bases. -/
def complexJacobian {κ : Type*} (f : (ι → ℂ) → (κ → ℂ)) (z : ι → ℂ) : Matrix κ ι ℂ :=
  fun j i => partialDeriv i (fun w => f w j) z

/-- Entries of the complex Jacobian are the coordinate entries of the Fréchet derivative. -/
theorem complexJacobian_apply {κ : Type*} [Fintype κ]
    {f : (ι → ℂ) → (κ → ℂ)} {z : ι → ℂ} (hf : DifferentiableAt ℂ f z)
    (j : κ) (i : ι) : complexJacobian f z j i = fderiv ℂ f z (Pi.single i 1) j := by
  rw [complexJacobian, partialDeriv_eq_fderiv (differentiableAt_pi.mp hf j), fderiv_apply hf j]
  rfl

omit [CompleteSpace F] in
/-- The coordinate chain rule, with an arbitrary complex normed outer target. -/
theorem partialDeriv_comp {κ : Type*} [Fintype κ]
    {f : (ι → ℂ) → (κ → ℂ)} {g : (κ → ℂ) → F} {z : ι → ℂ}
    (hg : DifferentiableAt ℂ g (f z)) (hf : DifferentiableAt ℂ f z) (i : ι) :
    partialDeriv i (g ∘ f) z = ∑ j, complexJacobian f z j i • partialDeriv j g (f z) := by
  rw [partialDeriv_eq_fderiv (hg.comp z hf), fderiv_comp z hg hf]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_eq_sum_partialDeriv hg]
  simp_rw [complexJacobian_apply hf]

/-- Jacobians compose by matrix multiplication. -/
theorem complexJacobian_comp {κ ν : Type*} [Fintype κ] [Fintype ν]
    {f : (ι → ℂ) → (κ → ℂ)} {g : (κ → ℂ) → (ν → ℂ)} {z : ι → ℂ}
    (hg : DifferentiableAt ℂ g (f z)) (hf : DifferentiableAt ℂ f z) :
    complexJacobian (g ∘ f) z = complexJacobian g (f z) * complexJacobian f z := by
  ext j i
  change partialDeriv i ((fun w => g w j) ∘ f) z = _
  rw [partialDeriv_comp (differentiableAt_pi.mp hg j) hf]
  simp [Matrix.mul_apply, complexJacobian, smul_eq_mul, mul_comm]

/-- The complex Jacobian is Mathlib's matrix of the complex Fréchet derivative
in the standard coordinate bases. -/
theorem complexJacobian_eq_toMatrix {κ : Type*} [Fintype κ]
    {f : (ι → ℂ) → (κ → ℂ)} {z : ι → ℂ} (hf : DifferentiableAt ℂ f z) :
    complexJacobian f z = LinearMap.toMatrix' (fderiv ℂ f z).toLinearMap := by
  ext j i
  exact complexJacobian_apply hf j i

/-- The Jacobian of the identity map is the identity matrix, including with no coordinates. -/
theorem complexJacobian_id (z : ι → ℂ) : complexJacobian id z = 1 := by
  rw [complexJacobian_eq_toMatrix differentiableAt_id]
  simp

/-- The determinant form of the chain rule for maps between equal coordinate spaces. -/
theorem det_complexJacobian_comp {f g : (ι → ℂ) → (ι → ℂ)} {z : ι → ℂ}
    (hg : DifferentiableAt ℂ g (f z)) (hf : DifferentiableAt ℂ f z) :
    (complexJacobian (g ∘ f) z).det =
      (complexJacobian g (f z)).det * (complexJacobian f z).det := by
  rw [complexJacobian_comp hg hf, Matrix.det_mul]

/-- A square complex Jacobian has nonzero determinant exactly when the Fréchet derivative
is invertible. Differentiability is explicit because the derivative is otherwise totalized. -/
theorem det_complexJacobian_ne_zero_iff {f : (ι → ℂ) → (ι → ℂ)} {z : ι → ℂ}
    (hf : DifferentiableAt ℂ f z) :
    (complexJacobian f z).det ≠ 0 ↔ (fderiv ℂ f z).IsInvertible := by
  have hm : (complexJacobian f z).mulVec = fderiv ℂ f z := by
    funext v
    rw [complexJacobian_eq_toMatrix hf]
    exact LinearMap.toMatrix'_mulVec _ v
  have hi : Function.Injective (fderiv ℂ f z) ↔ (complexJacobian f z).det ≠ 0 := by
    rw [← hm, Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero]
  constructor
  · intro h
    have hinj := hi.mpr h
    exact ⟨(LinearEquiv.ofBijective (fderiv ℂ f z).toLinearMap
      ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩
  · exact fun h => hi.mp h.injective

end SeveralComplexVariables

end
