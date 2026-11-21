/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Physlib.Relativity.Tensors.RealTensor.Species
/-!

# Lorentz Vectors

In this module we define Lorentz vectors as real Lorentz tensors with a single up index.
We create an API around Lorentz vectors to make working with them as easy as possible.

-/

@[expose] public section

open Module
open Matrix
open MatrixGroups
open Complex
open TensorProduct

noncomputable section

namespace Lorentz

/-- Real contravariant Lorentz vector, the real Lorentz tensor `v^μ` with one upper index. -/
abbrev Vector (d : ℕ := 3) := Tensor (Tensor.realLorentz d) ![Tensor.realLorentz.up]

namespace Vector

open Tensor

/-- The components `v^μ` of a Lorentz vector. -/
noncomputable def toCoord {d : ℕ} : Vector d ≃ₗ[ℝ] (Fin 1 ⊕ Fin d → ℝ) :=
  ((realLorentz d).oneIndexEquiv realLorentz.up).toLinearEquiv.symm ≪≫ₗ
    ((realLorentz d).basis realLorentz.up).equivFun

/-- The components of the tensor of a vector `x` of the index space are its components. -/
lemma toCoord_oneIndexEquiv {d : ℕ} (x : (realLorentz d).V realLorentz.up) :
    toCoord ((realLorentz d).oneIndexEquiv realLorentz.up x) = x := by
  change ((realLorentz d).basis realLorentz.up).equivFun
    (((realLorentz d).oneIndexEquiv realLorentz.up).toLinearEquiv.symm
      (((realLorentz d).oneIndexEquiv realLorentz.up).toLinearEquiv x)) = _
  rw [LinearEquiv.symm_apply_apply]
  funext μ
  rw [Module.Basis.equivFun_apply]
  rfl

/-- The components of `v` are the components of its vector of the index space. -/
lemma toCoord_apply {d : ℕ} (v : Vector d) :
    toCoord v = ((realLorentz d).oneIndexEquiv realLorentz.up).symm v := by
  conv_lhs => rw [← ((realLorentz d).oneIndexEquiv realLorentz.up).apply_symm_apply v]
  exact toCoord_oneIndexEquiv _

/-- The components of `v` in the basis of the color of its index. -/
lemma toCoord_eq_equivFun {d : ℕ} (v : Vector d) :
    toCoord v = ((realLorentz d).basis realLorentz.up).equivFun
      (((realLorentz d).oneIndexEquiv realLorentz.up).symm v) :=
  rfl

-- `toCoord` goes through `PiTensorProduct`. Unfolding it in `whnf` is expensive (it made a
-- `fun_prop` call cost 136k heartbeats instead of 1k), so it is irreducible from here on.
attribute [irreducible] toCoord

/-- `v μ` is the component `v^μ`. -/
instance {d} : CoeFun (Vector d) (fun _ => Fin 1 ⊕ Fin d → ℝ) where
  coe := fun v => toCoord v

/-- The equivalence between `Vector d` and `EuclideanSpace ℝ (Fin 1 ⊕ Fin d)`. -/
def equivEuclid (d : ℕ) :
    Vector d ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1 ⊕ Fin d) :=
  toCoord ≪≫ₗ (WithLp.linearEquiv _ _ _).symm

@[simp]
lemma equivEuclid_apply (d : ℕ) (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    equivEuclid d v i = v i := rfl

@[ext]
lemma eq_of_apply_eq {d : ℕ} {v w : Vector d} (h : ∀ i, v i = w i) : v = w := by
  apply (equivEuclid d).injective
  ext i
  simpa using h i

instance (d : ℕ) : Norm (Vector d) where
  norm := fun v => ‖equivEuclid d v‖

lemma norm_eq_equivEuclid (d : ℕ) (v : Vector d) :
    ‖v‖ = ‖equivEuclid d v‖ := rfl

@[simp]
lemma abs_component_le_norm {d : ℕ} (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    |v i| ≤ ‖v‖ := by
  simp [norm_eq_equivEuclid, PiLp.norm_eq_of_L2, -Fintype.sum_sum_type]
  refine Real.abs_le_sqrt ?_
  trans ∑ j ∈ {i}, (v j) ^ 2
  · simp
  refine Finset.sum_le_univ_sum_of_nonneg (fun i => by positivity)

instance isNormedAddCommGroup (d : ℕ) : NormedAddCommGroup (Vector d) :=
  NormedAddCommGroup.induced _ _ (equivEuclid d) (equivEuclid d).injective

instance isNormedSpace (d : ℕ) : NormedSpace ℝ (Vector d) where
  norm_smul_le c v := by
    simp only [norm_eq_equivEuclid, map_smul]
    exact norm_smul_le c (equivEuclid d v)
open InnerProductSpace

instance (d : ℕ) : Inner ℝ (Vector d) where
  inner := fun v w => ⟪equivEuclid d v, equivEuclid d w⟫_ℝ

lemma inner_eq_equivEuclid (d : ℕ) (v w : Vector d) :
    ⟪v, w⟫_ℝ = ⟪equivEuclid d v, equivEuclid d w⟫_ℝ := rfl

/-- The Euclidean inner product structure on `CoVector`. -/
instance innerProductSpace (d : ℕ) : InnerProductSpace ℝ (Vector d) where
  norm_sq_eq_re_inner v := by
    simp only [inner_eq_equivEuclid, norm_eq_equivEuclid]
    exact InnerProductSpace.norm_sq_eq_re_inner (equivEuclid d v)
  conj_inner_symm x y := by
    simp only [inner_eq_equivEuclid]
    exact InnerProductSpace.conj_inner_symm (equivEuclid d x) (equivEuclid d y)
  add_left x y z := by
    simp only [inner_eq_equivEuclid, map_add]
    exact InnerProductSpace.add_left (equivEuclid d x) (equivEuclid d y) (equivEuclid d z)
  smul_left x y r := by
    simp only [inner_eq_equivEuclid, map_smul]
    exact InnerProductSpace.smul_left (equivEuclid d x) (equivEuclid d y) r

/-- The inner product on `Vector d` as a sum over components. -/
lemma inner_eq_sum {d : ℕ} (v w : Vector d) : ⟪v, w⟫_ℝ = ∑ μ, v μ * w μ := by
  rw [inner_eq_equivEuclid, PiLp.inner_apply]
  simp [mul_comm]

/-- The instance of a `ChartedSpace` on `Vector d`. -/
instance : ChartedSpace (Vector d) (Vector d) := chartedSpaceSelf (Vector d)

lemma ext_of_apply {d} {v w : Vector d} (h : ∀ i, v i = w i) : v = w := by
  apply (equivEuclid d).injective
  ext i
  simpa using h i

@[simp]
lemma apply_smul {d : ℕ} (c : ℝ) (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    (c • v) i = c * v i := by simp

@[simp]
lemma apply_add {d : ℕ} (v w : Vector d) (i : Fin 1 ⊕ Fin d) :
    (v + w) i = v i + w i := by simp

@[simp]
lemma apply_sub {d : ℕ} (v w : Vector d) (i : Fin 1 ⊕ Fin d) :
    (v - w) i = v i - w i := by simp

lemma apply_sum {d : ℕ} {ι : Type} [Fintype ι] (f : ι → Vector d) (i : Fin 1 ⊕ Fin d) :
    (∑ j, f j) i = ∑ j, f j i := by
  simp [map_sum]

@[simp]
lemma neg_apply {d : ℕ} (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    (-v) i = - v i := by simp

@[simp]
lemma zero_apply {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    (0 : Vector d) i = 0 := by simp

/-- The continuous linear map from a Lorentz vector to one of its coordinates. -/
def coordCLM {d : ℕ} (i : Fin 1 ⊕ Fin d) : Vector d →L[ℝ] ℝ := LinearMap.toContinuousLinearMap {
  toFun v := v i
  map_add' := by simp
  map_smul' := by simp}

lemma coordCLM_apply {d : ℕ} (i : Fin 1 ⊕ Fin d) (v : Vector d) :
    coordCLM i v = v i := rfl

@[fun_prop]
lemma coord_continuous {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    Continuous (fun v : Vector d => v i) :=
  (coordCLM i).continuous

@[fun_prop]
lemma coord_contDiff {n} {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    ContDiff ℝ n (fun v : Vector d => v i) :=
  (coordCLM i).contDiff

@[fun_prop]
lemma coord_differentiable {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    Differentiable ℝ (fun v : Vector d => v i) :=
  (coordCLM i).differentiable

@[fun_prop]
lemma coord_differentiableAt {d : ℕ} (i : Fin 1 ⊕ Fin d) (v : Vector d) :
    DifferentiableAt ℝ (fun v : Vector d => v i) v :=
  (coordCLM i).differentiableAt

/-- A component of a continuous vector-valued map is continuous. -/
@[fun_prop]
lemma continuous_apply_comp {d : ℕ} {α : Type*} [TopologicalSpace α] {f : α → Vector d}
    (hf : Continuous f) (μ : Fin 1 ⊕ Fin d) : Continuous (fun x => f x μ) :=
  (coordCLM μ).continuous.comp hf

/-- A component of a differentiable vector-valued map is differentiable. The components are
`toCoord`, not function application, so `fun_prop` needs this composition form. -/
@[fun_prop]
lemma differentiable_apply_comp {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Vector d} (hf : Differentiable ℝ f) (μ : Fin 1 ⊕ Fin d) :
    Differentiable ℝ (fun x => f x μ) :=
  (coordCLM μ).differentiable.comp hf

/-- A component of a `C^n` vector-valued map is `C^n`. -/
@[fun_prop]
lemma contDiff_apply_comp {n : WithTop ℕ∞} {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → Vector d} (hf : ContDiff ℝ n f) (μ : Fin 1 ⊕ Fin d) :
    ContDiff ℝ n (fun x => f x μ) :=
  (coordCLM μ).contDiff.comp hf

/-- The continuous linear equivalence between `Vector d` and Euclidean space. -/
def euclidCLE (d : ℕ) : Vector d ≃L[ℝ] EuclideanSpace ℝ (Fin 1 ⊕ Fin d) :=
  LinearEquiv.toContinuousLinearEquiv (equivEuclid d)

/-- The continuous linear equivalence between `Vector d` and the corresponding `Pi` type. -/
def equivPi (d : ℕ) :
    Vector d ≃L[ℝ] Π (_ : Fin 1 ⊕ Fin d), ℝ :=
  LinearEquiv.toContinuousLinearEquiv toCoord

@[simp]
lemma equivPi_apply {d : ℕ} (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    equivPi d v i = v i := rfl

@[fun_prop]
lemma continuous_of_apply {d : ℕ} {α : Type*} [TopologicalSpace α]
    (f : α → Vector d)
    (h : ∀ i : Fin 1 ⊕ Fin d, Continuous (fun x => f x i)) :
    Continuous f := by
  rw [← (equivPi d).comp_continuous_iff]
  apply continuous_pi
  intro i
  simp only [Function.comp_apply, equivPi_apply]
  fun_prop

lemma differentiable_apply {d : ℕ} {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (f : α → Vector d) :
    (∀ i : Fin 1 ⊕ Fin d, Differentiable ℝ (fun x => f x i)) ↔ Differentiable ℝ f := by
  apply Iff.intro
  · intro h
    rw [← (Lorentz.Vector.equivPi d).comp_differentiable_iff]
    exact differentiable_pi'' h
  · intro h ν
    change Differentiable ℝ (Lorentz.Vector.coordCLM ν ∘ f)
    apply Differentiable.comp
    · fun_prop
    · exact h

lemma contDiff_apply {n : WithTop ℕ∞} {d : ℕ} {α : Type*}
    [NormedAddCommGroup α] [NormedSpace ℝ α]
    (f : α → Vector d) :
    (∀ i : Fin 1 ⊕ Fin d, ContDiff ℝ n (fun x => f x i)) ↔ ContDiff ℝ n f := by
  apply Iff.intro
  · intro h
    rw [← (Lorentz.Vector.equivPi d).comp_contDiff_iff]
    apply contDiff_pi'
    intro ν
    exact h ν
  · intro h ν
    change ContDiff ℝ n (Lorentz.Vector.coordCLM ν ∘ f)
    apply ContDiff.comp
    · fun_prop
    · exact h

lemma fderiv_apply {d : ℕ} {α : Type*}
    [NormedAddCommGroup α] [NormedSpace ℝ α]
    (f : α → Vector d) (h : Differentiable ℝ f)
    (x : α) (dt : α) (ν : Fin 1 ⊕ Fin d) :
    fderiv ℝ f x dt ν = fderiv ℝ (fun y => f y ν) x dt := by
  change _ = (fderiv ℝ (Lorentz.Vector.coordCLM ν ∘ f) x) dt
  rw [fderiv_comp _ (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rfl

@[simp]
lemma fderiv_coord {d : ℕ} (μ : Fin 1 ⊕ Fin d) (x : Vector d) :
    fderiv ℝ (fun v : Vector d => v μ) x = coordCLM μ := by
  change fderiv ℝ (coordCLM μ) x = coordCLM μ
  simp

/-!

## Basis

-/

/-- The basis on `Vector d` indexed by `Fin 1 ⊕ Fin d`. -/
def basis {d : ℕ} : Basis (Fin 1 ⊕ Fin d) ℝ (Vector d) :=
  (Pi.basisFun ℝ _).map toCoord.symm

@[simp]
lemma basis_apply {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) :
    basis μ ν = if μ = ν then 1 else 0 := by
  simp [basis, Pi.single_apply, eq_comm]

lemma basis_repr_apply {d : ℕ} (p : Vector d) (μ : Fin 1 ⊕ Fin d) :
    basis.repr p μ = p μ := by
  simp [basis]

lemma map_apply_eq_basis_mulVec {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) (p : Vector d) :
    ⇑(f p) = (LinearMap.toMatrix basis basis) f *ᵥ ⇑p := by
  simpa only [funext (basis_repr_apply _)] using
    (LinearMap.toMatrix_mulVec_repr basis basis f p).symm

lemma sum_basis_eq_zero_iff {d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ) :
    (∑ μ, f μ • basis μ) = 0 ↔ ∀ μ, f μ = 0 := by
  apply Iff.intro
  · intro h
    have h1 := (linearIndependent_iff').mp basis.linearIndependent Finset.univ f h
    intro μ
    exact h1 μ (by simp)
  · intro h
    simp [h]

lemma sum_inl_inr_basis_eq_zero_iff {d : ℕ} (f₀ : ℝ) (f : Fin d → ℝ) :
    f₀ • basis (Sum.inl 0) + (∑ i, f i • basis (Sum.inr i)) = 0 ↔
    f₀ = 0 ∧ ∀ i, f i = 0 := by
  let f' : Fin 1 ⊕ Fin d → ℝ := fun μ =>
    match μ with
    | Sum.inl 0 => f₀
    | Sum.inr i => f i
  have h1 : f₀ • basis (Sum.inl 0) + (∑ i, f i • basis (Sum.inr i))
    = ∑ μ, f' μ • basis μ := by simp [f']
  rw [h1, sum_basis_eq_zero_iff]
  simp [f']

/-!

## C. The Spatial part

-/

/-- Extract spatial components from a Lorentz vector,
    returning them as a vector in Euclidean space. -/
abbrev spatialPart {d : ℕ} (v : Vector d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => v (Sum.inr i)

lemma spatialPart_apply_eq_toCoord {d : ℕ} (v : Vector d) (i : Fin d) :
    spatialPart v i = v (Sum.inr i) := rfl

lemma spatialPart_basis_sum_inr {d : ℕ} (i : Fin d) (j : Fin d) :
    spatialPart (basis (Sum.inr i)) j =
      (Finsupp.single (Sum.inr i : Fin 1 ⊕ Fin d) 1) (Sum.inr j) := by
  simp [basis_apply]
  rw [Finsupp.single_apply]
  simp

lemma spatialPart_basis_sum_inl {d : ℕ} (i : Fin d) :
    spatialPart (basis (Sum.inl 0)) i = 0 := by simp

/-- The spatial part of a Lorentz vector as a continuous linear map. -/
def spatialCLM (d : ℕ) : Vector d →L[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun v := WithLp.toLp 2 fun i => v (Sum.inr i)
  map_add' v1 v2 := by ext; simp
  map_smul' c v := by ext; simp
  cont := by fun_prop

lemma spatialCLM_apply_eq_spatialPart {d : ℕ} (v : Vector d) (i : Fin d) :
    spatialCLM d v i = spatialPart v i := rfl

@[simp]
lemma spatialCLM_basis_sum_inl {d : ℕ} :
    spatialCLM d (basis (Sum.inl 0)) = 0 := by
  ext i
  exact spatialPart_basis_sum_inl i

@[simp]
lemma spatialCLM_basis_sum_inr {d : ℕ} (i : Fin d) :
    spatialCLM d (basis (Sum.inr i)) = EuclideanSpace.basisFun (Fin d) ℝ i := by
  ext j
  rw [spatialCLM_apply_eq_spatialPart, spatialPart_basis_sum_inr i j]
  simp [Finsupp.single_apply]
  congr 1
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-!

## The Temporal component

-/

/-- Extract time component from a Lorentz vector -/
abbrev timeComponent {d : ℕ} (v : Vector d) : ℝ :=
  v (Sum.inl 0)

lemma timeComponent_basis_sum_inr {d : ℕ} (i : Fin d) :
    timeComponent (basis (Sum.inr i)) = 0 := by simp

lemma timeComponent_basis_sum_inl {d : ℕ} :
    timeComponent (d := d) (basis (Sum.inl 0)) = 1 := by simp

/-- The temporal part of a Lorentz vector as a continuous linear map. -/
def temporalCLM (d : ℕ) : Vector d →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => v (Sum.inl 0)
    map_add' := by simp
    map_smul' := by simp}

lemma temporalCLM_apply_eq_timeComponent {d : ℕ} (v : Vector d) :
    temporalCLM d v = timeComponent v := rfl

@[simp]
lemma temporalCLM_basis_sum_inr {d : ℕ} (i : Fin d) :
    temporalCLM d (basis (Sum.inr i)) = 0 := by
  simp [temporalCLM_apply_eq_timeComponent, basis_apply]

@[simp]
lemma temporalCLM_basis_sum_inl {d : ℕ} :
    temporalCLM d (basis (Sum.inl 0)) = 1 := by
  simp [temporalCLM_apply_eq_timeComponent, basis_apply]

/-- The continuous linear map corresponding to the creation of a
  Lorentz Vector with only a non-zero temporal component. -/
def ofTemporalComponent {d : ℕ} : ℝ →L[ℝ] Vector d where
  toFun xt := xt • basis (Sum.inl 0)
  map_add' := by simp [add_smul]
  map_smul' := by simp [smul_smul]

/-- The continuous linear map corresponding to the creation of a
  Lorentz Vector with only non-zero spatial components. -/
def ofSpatialComponent {d : ℕ} : EuclideanSpace ℝ (Fin d) →L[ℝ] Vector d where
  toFun xs := ∑ i, xs i • basis (Sum.inr i)
  map_add' xs ys := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' c xs := by
    simp [smul_smul, Finset.smul_sum]

/-!

## Smoothness

-/

open Manifold in
/-- The structure of a smooth manifold on Vector . -/
def asSmoothManifold (d : ℕ) : ModelWithCorners ℝ (Vector d) (Vector d) := 𝓘(ℝ, Vector d)

/-!

## Properties of the inner product (note not the Minkowski product)

-/
open InnerProductSpace

lemma basis_inner {d : ℕ} (μ : Fin 1 ⊕ Fin d) (p : Lorentz.Vector d) :
    ⟪Lorentz.Vector.basis μ, p⟫_ℝ = p μ := by
  simp [inner_eq_sum]

lemma inner_basis {d : ℕ} (p : Lorentz.Vector d) (μ : Fin 1 ⊕ Fin d) :
    ⟪p, Lorentz.Vector.basis μ⟫_ℝ = p μ := by
  simp [inner_eq_sum]

/-- A vector with zero time component and zero spatial part is zero. -/
lemma eq_zero_of_timeComponent_of_spatialPart {d : ℕ} {u : Vector d} (h0 : u.timeComponent = 0)
    (hs : u.spatialPart = 0) : u = 0 := by
  refine ext_of_apply fun i => ?_
  rcases i with i | i
  · fin_cases i
    simpa using h0
  · have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) hs
    simpa [spatialPart_apply_eq_toCoord] using this

/-- The spatial components of a vector whose spatial part has zero norm vanish. -/
lemma apply_inr_eq_zero_of_norm_spatialPart {d : ℕ} {u : Vector d} (h : ‖u.spatialPart‖ = 0)
    (i : Fin d) : u (Sum.inr i) = 0 := by
  have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) (norm_eq_zero.mp h)
  simpa [spatialPart_apply_eq_toCoord] using this

end Vector

end Lorentz
