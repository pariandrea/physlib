/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.ForMathlib.Schouten
public import Physlib.Mathematics.ForMathlib.SesquilinearForm
public import Physlib.Mathematics.ForMathlib.TensorProductMatrix
public import Physlib.Mathematics.Tensors.LinearMap
/-!

# Invariant forms, metrics, and lowering and raising indices

An invariant form takes an index to its dual color, lowering an upper index and raising a lower
one.

## i. Overview

For Lorentz tensors the invariant form is the Minkowski metric `η_μν` with inverse `η^μν`. It
lowers `v_ν = η_νμ v^μ`, raises `w^ν = η^νμ w_μ`, and the two are inverse,
`v^μ η_μν η^νρ = v^ρ`.

The class `S.HasForm κ` is a chosen invariant nondegenerate bilinear form `g_μν` on the upper
space of the kind `κ`. Not every kind has one, as the SU(3) triplet has none. The form at the lower
variance `g^μν`, the two-index tensors `S.form c` and their inverse relation are derived from it.
Symmetry, as for `η`, and antisymmetry, as for the Weyl `ε`, are the optional classes
`S.IsSymmetricForm κ` and `S.IsAntisymmetricForm κ`, stated once on the form of the upper space.
The form tensors at both variances inherit them (`Species.comm_form_eq_smul_of_bilin`).

`S.toDual c` contracts a vector with the second index of the form, lowering an upper index,
`v_ν = g_νμ v^μ`, and raising a lower one, `w^ν = g^νμ w_μ`, and `S.toDualAt i` does so at the
index `i` of a tensor. Lowering is Mathlib's `LinearMap.BilinForm.toDual` of the flipped form, and
raising is its inverse. In any basis its matrix is `LinearMap.BilinForm.toMatrix` of the form.
For the antisymmetric `ε`, where the order of the indices matters,
lowering gives `ψ_α = ε_αβ ψ^β`, the convention of Wess and Bagger and of Dreiner, Haber and
Martin.

## ii. Key results

- `Species.HasForm` is an invariant form on a kind with its inverse, `g_μν` and `g^μν`, with
  `Species.form`, `Species.form_invariant` and `Species.form_inverse`.
- `Species.IsSymmetricForm` and `Species.IsAntisymmetricForm` say that the form is symmetric or
  antisymmetric, Mathlib's `IsSymm` and `IsAlt`. At both variances, `Species.form_symm` and
  `Species.form_antisymm`, from `Species.comm_form_eq_smul_of_bilin`, in components
  `Species.formMatrix_symm` and `Species.formMatrix_antisymm`. `Species.comm_form_eq_smul` gives
  the index swap from the components of the form.
- `Species.formBilin` reads the form as a Mathlib bilinear form, symmetric by
  `Species.isSymm_formBilin` and alternating by `Species.isAlt_formBilin`.
- `Species.toDual` lowers an upper index and raises a lower one, and `Species.toDual_toDual` that
  raising undoes lowering.
- `Species.formTensor` is the form as a tensor on two indices.
- `Species.toDualAt` lowers or raises one index of a tensor, with
  `Species.toDualAt_toDualAt`, `Species.toDualAt_eq_intertwiningMapAt` and, in components,
  `Species.tensorBasis_repr_toDualAt`.
- `Species.toDualAt_eq_contr` proves that lowering is contracting with the form,
  `T^…_ν… = g_νμ T^…μ…`.
- `Species.formMatrix_schouten` is the Schouten identity for an antisymmetric form on a kind with
  two labels in components, `g^γρ δ^α_α' = g^γα' δ^α_ρ - g^ρα' δ^α_γ`,
  `LinearMap.IsAlt.schouten_basis` for `formBilin`.

## iii. Table of contents

- A. Invariant forms and metrics
- B. Lowering and raising vectors
  - B.1. Lowering in any basis
  - B.2. Symmetric and antisymmetric forms
- C. The form as a tensor
- D. Lowering and raising at one index
- E. Forms on a kind with two labels

## iv. References

* None.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensor

namespace Species

variable {k : Type} [RCLike k] {K : Type} {G : Type} [Group G]

/-!

## A. Invariant forms and metrics

-/

/-- An invariant nondegenerate bilinear form identifies a representation with its dual,
`v ↦ B v`, Mathlib's `LinearMap.BilinForm.toDual`. -/
noncomputable def _root_.LinearMap.BilinForm.toDualEquiv {V : Type} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] {ρ : Representation k G V}
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v) : ρ.Equiv ρ.dual :=
  .mk (B.toDual hB) fun g => LinearMap.ext fun v => LinearMap.ext fun u => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.BilinForm.toDual_def hB,
      Representation.dual_apply, Module.Dual.transpose_apply]
    rw [← hinv g⁻¹, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one,
      one_apply_eq_self]

variable (S : Species k G K) in
/-- A chosen invariant nondegenerate bilinear form `g(u, v) = u^μ g_μν v^ν` on the upper space of
the kind `κ`. The form at the lower variance, its inverse, lowering and raising are derived. It
need not be symmetric, so it covers both `η` and the Weyl `ε`. -/
class HasForm (κ : K) where
  /-- The form on upper vectors, `g(u, v) = u^μ g_μν v^ν`. -/
  bilin : LinearMap.BilinForm k (S.V ⟨κ, .up⟩)
  /-- The form is invariant, `g(Λu, Λv) = g(u, v)` for every `Λ : G`. -/
  bilin_invariant : ∀ (Λ : G) (u v : S.V ⟨κ, .up⟩),
    bilin (S.rep ⟨κ, .up⟩ Λ u) (S.rep ⟨κ, .up⟩ Λ v) = bilin u v
  /-- The form is nondegenerate. -/
  bilin_nondegenerate : bilin.Nondegenerate

variable {S : Species k G K}

-- The coordinate layer. It enters only a declaration whose statement mentions `basisIdx`.
variable {basisIdx : K → Type} [B : S.HasBasis basisIdx] [∀ κ, Fintype (basisIdx κ)]
  [∀ κ, DecidableEq (basisIdx κ)]

variable (S) in
/-- The form `g_μν` on the upper space of `κ`. -/
noncomputable abbrev bilin (κ : K) [S.HasForm κ] : LinearMap.BilinForm k (S.V ⟨κ, .up⟩) :=
  HasForm.bilin

variable (S) in
/-- The form as the map `v ↦ g(v, ·)`, `v^μ ↦ v^μ g_μν`, contracting with its first index. It is
Mathlib's `LinearMap.BilinForm.toDual`. -/
noncomputable def bilinEquiv (κ : K) [S.HasForm κ] : (S.rep ⟨κ, .up⟩).Equiv (S.rep ⟨κ, .down⟩) :=
  (S.bilin κ).toDualEquiv HasForm.bilin_nondegenerate HasForm.bilin_invariant

@[simp] lemma bilinEquiv_apply (κ : K) [S.HasForm κ] (u v : S.V ⟨κ, .up⟩) :
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _
      (@DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.bilinEquiv κ) u) v =
        S.bilin κ u v :=
  LinearMap.BilinForm.toDual_def HasForm.bilin_nondegenerate

variable (S) in
/-- The form at the color `c` as the linear map `V c.dual → V c` contracting with its first index:
`v^μ ↦ v^μ g_μν` at a lower color, and its inverse `w_μ ↦ w_μ g^μν` at an upper color. -/
noncomputable def formLin : (c : Color K) → [S.HasForm c.kind] → S.V c.dual ≃ₗ[k] S.V c
  | ⟨κ, .up⟩, _ => (S.bilinEquiv κ).toLinearEquiv.symm
  | ⟨κ, .down⟩, _ => (S.bilinEquiv κ).toLinearEquiv

/-- The form at the color `c`, `g^μν` at an upper color and `g_μν` at a lower one, the tensor of
`formLin c`. -/
noncomputable def form (c : Color K) [S.HasForm c.kind] : S.V c ⊗[k] S.V c :=
  S.toLin.symm (S.formLin c).toLinearMap

/-- The linear map of the form is `formLin`. -/
lemma toLin_form (c : Color K) [S.HasForm c.kind] :
    S.toLin (form c) = (S.formLin c).toLinearMap :=
  S.toLin.apply_symm_apply _

/-- The form is invariant, `Λ g = g` for every `Λ : G`. -/
lemma form_invariant (c : Color K) [inst : S.HasForm c.kind] (Λ : G) :
    TensorProduct.map (S.rep c Λ) (S.rep c Λ) (form c) = form c := by
  refine (S.isIntertwiningMap_toLin_iff _).1 ⟨fun g v => ?_⟩ Λ
  rw [toLin_form]
  match c, inst with
  | ⟨κ, .up⟩, _ =>
    exact Representation.IntertwiningMap.isIntertwining _ _
      (S.bilinEquiv κ).symm.toIntertwiningMap g v
  | ⟨κ, .down⟩, _ =>
    exact Representation.IntertwiningMap.isIntertwining _ _ (S.bilinEquiv κ).toIntertwiningMap g v

/-- The forms at `c` and at `c.dual` are inverse as linear maps, `v^μ g_μν g^νρ = v^ρ` at an
upper color `c`. -/
lemma form_inverse (c : Color K) [inst : S.HasForm c.kind] :
    S.toLin (form c) ∘ₗ S.toLin (form c.dual) = LinearMap.id := by
  rw [toLin_form, toLin_form]
  match c, inst with
  | ⟨κ, .up⟩, _ => exact (S.bilinEquiv κ).toLinearEquiv.symm_comp
  | ⟨κ, .down⟩, _ => exact (S.bilinEquiv κ).toLinearEquiv.comp_symm

/-- The linear map of the form at `c` is bijective. -/
lemma toLin_form_bijective (c : Color K) [S.HasForm c.kind] :
    Function.Bijective (S.toLin (form c)) :=
  Function.bijective_iff_has_inverse.mpr ⟨S.toLin (form c.dual),
    LinearMap.congr_fun (form_inverse c.dual), LinearMap.congr_fun (form_inverse c)⟩

variable (S) in
/-- The form at `c` read as a bilinear form on `V c.dual`, `(u, v) ↦ u_μ g^μν v_ν`, with the first
argument contracted with the first index of the form. -/
noncomputable def formBilin (c : Color K) [S.HasForm c.kind] :
    LinearMap.BilinForm k (S.V c.dual) :=
  (TensorProduct.curry (S.contr c.dual).toLinearMap).flip ∘ₗ S.toLin (form c)

lemma formBilin_apply (c : Color K) [S.HasForm c.kind] (u v : S.V c.dual) :
    S.formBilin c u v = S.contr c.dual (v ⊗ₜ S.toLin (form c) u) :=
  rfl

variable (S) in
/-- The components of the form at `c`, `g^μν` at an upper color and `g_μν` at a lower one, its
coordinates in Mathlib's product basis. Component lemmas of a species are stated on it, so that
`simp` finds them at a literal color. -/
noncomputable def formMatrix (c : Color K) [S.HasForm c.kind] :
    Matrix (basisIdx c.kind) (basisIdx c.kind) k :=
  fun μ ν => ((S.basis c).tensorProduct (S.basis c)).repr (form c) (μ, ν)

/-- The components of the form are Mathlib's matrix of `formBilin c` in the basis of `c.dual`,
`g^μν = g(e^μ, e^ν)`. -/
lemma formMatrix_eq_toMatrix (c : Color K) [S.HasForm c.kind] :
    S.formMatrix c = LinearMap.BilinForm.toMatrix (S.basis c.dual) (S.formBilin c) := by
  ext μ ν
  rw [LinearMap.BilinForm.toMatrix_apply, formBilin_apply, contr_tmul_eq_sum_basis]
  simp only [Module.Basis.repr_self, Finsupp.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  refine ((S.repr_toLin (S.basis c) (form c) _ ν).trans ?_).symm
  simp [Finsupp.single_apply, formMatrix]

/-- The form on two basis vectors is a component of the form, `g(e^μ, e^ν) = g^μν`. -/
lemma formBilin_basis (c : Color K) [S.HasForm c.kind] (μ ν : basisIdx c.kind) :
    S.formBilin c (S.basis c.dual μ) (S.basis c.dual ν) = S.formMatrix c μ ν := by
  rw [formMatrix_eq_toMatrix, LinearMap.BilinForm.toMatrix_apply]

/-- Swapping the two indices of the form scales it by `r` when its components do,
`g^νμ = r g^μν`. -/
lemma comm_form_eq_smul (c : Color K) [S.HasForm c.kind] (r : k)
    (h : ∀ μ ν, S.formMatrix c ν μ = r * S.formMatrix c μ ν) :
    TensorProduct.comm k (S.V c) (S.V c) (form c) = r • form c :=
  ((S.basis c).comm_eq_smul_iff _ r).2 h

/-!

## B. Lowering and raising vectors

-/

variable (S) in
/-- Lowering an upper index, `v^μ ↦ v_ν = g_νμ v^μ`, contracting with the second index of the
form. It is Mathlib's `LinearMap.BilinForm.toDual` of the flipped form, `v ↦ g(·, v)`. -/
noncomputable def lower (κ : K) [S.HasForm κ] : (S.rep ⟨κ, .up⟩).Equiv (S.rep ⟨κ, .down⟩) :=
  (S.bilin κ).flip.toDualEquiv HasForm.bilin_nondegenerate.flip
    fun g u v => HasForm.bilin_invariant g v u

/-- The lowered vector `v_ν` evaluated on `u` is `g(u, v)`. -/
@[simp] lemma lower_apply (κ : K) [S.HasForm κ] (u v : S.V ⟨κ, .up⟩) :
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _
      (@DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.lower κ) v) u =
        S.bilin κ u v :=
  LinearMap.BilinForm.toDual_def HasForm.bilin_nondegenerate.flip

variable (S) in
/-- The vector `v` of color `c` contracted with the second index of the form. It lowers an upper
index, `v^μ ↦ g_νμ v^μ` (`lower`), and raises a lower one, `w_μ ↦ g^νμ w_μ`, the inverse. -/
noncomputable def toDual : (c : Color K) → [S.HasForm c.kind] → (S.rep c).Equiv (S.rep c.dual)
  | ⟨κ, .up⟩, _ => S.lower κ
  | ⟨κ, .down⟩, _ => (S.lower κ).symm

/-- Raising undoes lowering, `(v_ν)^ν = v^ν`. The types of the coercions are `no_index`, so that it
fires at a written-out color (`Species` §A.1). -/
@[simp]
lemma toDual_toDual : ∀ (c : Color K) [S.HasForm c.kind] (v : S.V c),
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.toDual c.dual)
      (@DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.toDual c) v) = v
  | ⟨κ, .up⟩, _, v => (S.lower κ).toLinearEquiv.symm_apply_apply v
  | ⟨κ, .down⟩, _, v => (S.lower κ).toLinearEquiv.apply_symm_apply v

/-- `toDual_toDual` at written-out colors, `(v_ν)^ν = v^ν`. `simp` writes the dual of `⟨κ, up⟩` as
`⟨κ, down⟩` (`Color.dual_mk`), where `toDual_toDual` does not unify. -/
@[simp]
lemma toDual_down_toDual_up (κ : K) [S.HasForm κ] (v : S.V ⟨κ, .up⟩) :
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.toDual ⟨κ, .down⟩)
      (@DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.toDual ⟨κ, .up⟩) v) = v :=
  toDual_toDual ⟨κ, .up⟩ v

/-- `toDual_toDual` at written-out colors, `(w^ν)_ν = w_ν`. -/
@[simp]
lemma toDual_up_toDual_down (κ : K) [S.HasForm κ] (w : S.V ⟨κ, .down⟩) :
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.toDual ⟨κ, .up⟩)
      (@DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.toDual ⟨κ, .down⟩) w) = w :=
  toDual_toDual ⟨κ, .down⟩ w

/-- `lower_apply` at the written-out color: the lowered vector `v_ν` evaluated on `u` is
`g(u, v)`. -/
@[simp]
lemma toDual_up_apply (κ : K) [S.HasForm κ] (u v : S.V ⟨κ, .up⟩) :
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _
      (@DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.toDual ⟨κ, .up⟩) v) u =
        S.bilin κ u v :=
  lower_apply κ u v

/-- The raised vector `w^ν` is the vector with `g(u, w^ν) = w(u)` for every `u`. -/
@[simp]
lemma bilin_toDual_down (κ : K) [S.HasForm κ] (u : S.V ⟨κ, .up⟩) (w : S.V ⟨κ, .down⟩) :
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _
      (@DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.bilin κ) u)
      (@DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.toDual ⟨κ, .down⟩) w) = w u := by
  rw [← toDual_up_apply, toDual_up_toDual_down]

/-- Lowering an upper index is Mathlib's `LinearMap.BilinForm.toDual` of the flipped form. -/
lemma toDual_up_eq_toDual (κ : K) [S.HasForm κ] :
    (S.toDual ⟨κ, .up⟩).toLinearEquiv =
      (S.bilin κ).flip.toDual HasForm.bilin_nondegenerate.flip :=
  rfl

/-- The two ways of contracting a lower vector with the inverse form agree,
`β(g⁻¹ α) = α(raise β)`, where `g⁻¹` inverts `v ↦ g(v, ·)`. -/
lemma apply_bilinEquiv_symm (κ : K) [S.HasForm κ] (α β : S.V ⟨κ, .down⟩) :
    β ((S.bilinEquiv κ).symm α) = α ((S.lower κ).symm β) := by
  obtain ⟨w, rfl⟩ := (S.bilinEquiv κ).toLinearEquiv.surjective α
  obtain ⟨y, rfl⟩ := (S.lower κ).toLinearEquiv.surjective β
  rw [Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
    Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.symm_apply_apply, Representation.Equiv.symm_apply_apply, lower_apply,
    bilinEquiv_apply]

/-- At a lower color the form is `bilin`, `g(u, v) = u^μ g_μν v^ν`. -/
lemma formBilin_down (κ : K) [S.HasForm κ] : S.formBilin ⟨κ, .down⟩ = S.bilin κ :=
  LinearMap.ext₂ fun u v => by
    rw [formBilin_apply, toLin_form]
    exact bilinEquiv_apply κ u v

/-- At an upper color the form is the inverse form on lower vectors, `g⁻¹(α, β) = α(raise β)`. -/
lemma formBilin_up_apply (κ : K) [S.HasForm κ] (α β : S.V ⟨κ, .down⟩) :
    S.formBilin ⟨κ, .up⟩ α β = α (S.toDual ⟨κ, .down⟩ β) := by
  rw [formBilin_apply, toLin_form]
  exact apply_bilinEquiv_symm κ α β

/-!

### B.1. Lowering in any basis

-/

section anyBasis

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Lowering in any basis `b` of the upper space, with its dual basis at the lower space:
`v_ν = g_νμ v^μ` with `g_νμ = g(b_ν, b_μ)`, Mathlib's `BilinForm.toMatrix`. -/
lemma dualBasis_repr_toDual_up (κ : K) [S.HasForm κ] (b : Module.Basis ι k (S.V ⟨κ, .up⟩))
    (v : S.V ⟨κ, .up⟩) :
    ⇑(b.dualBasis.repr (S.toDual ⟨κ, .up⟩ v)) =
      (S.bilin κ).toMatrix b *ᵥ ⇑(b.repr v) := by
  ext ν
  rw [Module.Basis.dualBasis_repr]
  change S.lower κ v (b ν) = _
  rw [lower_apply, LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b]
  simp [Finsupp.single_eq_pi_single]

/-- The matrix of the form in a basis is invertible. -/
lemma isUnit_det_toMatrix_bilin (κ : K) [S.HasForm κ] (b : Module.Basis ι k (S.V ⟨κ, .up⟩)) :
    IsUnit ((S.bilin κ).toMatrix b).det :=
  ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 HasForm.bilin_nondegenerate).isUnit

/-- Raising in any basis `b`: `w^ν = g^νμ w_μ` with `g^νμ` the inverse of the matrix of the
form. -/
lemma repr_toDual_down (κ : K) [S.HasForm κ] (b : Module.Basis ι k (S.V ⟨κ, .up⟩))
    (α : S.V ⟨κ, .down⟩) :
    ⇑(b.repr (S.toDual ⟨κ, .down⟩ α)) =
      ((S.bilin κ).toMatrix b)⁻¹ *ᵥ ⇑(b.dualBasis.repr α) := by
  have h := dualBasis_repr_toDual_up κ b (S.toDual ⟨κ, .down⟩ α)
  rw [show S.toDual ⟨κ, .up⟩ (S.toDual ⟨κ, .down⟩ α) = α from toDual_toDual ⟨κ, .down⟩ α] at h
  rw [h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_toMatrix_bilin κ b),
    Matrix.one_mulVec]

/-- The matrix of the inverse form in the dual basis of any basis `b` is the inverse of the matrix
of the form, `g^μν = (g_μν)⁻¹`. -/
lemma toMatrix_formBilin_up (κ : K) [S.HasForm κ] (b : Module.Basis ι k (S.V ⟨κ, .up⟩)) :
    (S.formBilin ⟨κ, .up⟩).toMatrix b.dualBasis =
      ((S.bilin κ).toMatrix b)⁻¹ := by
  ext μ ν
  rw [LinearMap.BilinForm.toMatrix_apply, formBilin_up_apply, Module.Basis.dualBasis_apply,
    congrFun (repr_toDual_down κ b _) μ]
  simp [Matrix.mulVec, dotProduct, Finsupp.single_apply]

/-- The matrices of the form and of its inverse are inverse in every basis,
`g_μν g^νρ = δ_μ^ρ`. -/
lemma toMatrix_bilin_mul_toMatrix_formBilin_up (κ : K) [S.HasForm κ]
    (b : Module.Basis ι k (S.V ⟨κ, .up⟩)) :
    (S.bilin κ).toMatrix b * (S.formBilin ⟨κ, .up⟩).toMatrix b.dualBasis =
      1 := by
  rw [toMatrix_formBilin_up, Matrix.mul_nonsing_inv _ (isUnit_det_toMatrix_bilin κ b)]

end anyBasis

/-- The components of the form at a lower color are the matrix of `bilin`. -/
lemma formMatrix_down (κ : K) [S.HasForm κ] :
    S.formMatrix ⟨κ, .down⟩ = (S.bilin κ).toMatrix (S.basis ⟨κ, .up⟩) := by
  rw [formMatrix_eq_toMatrix, formBilin_down]

/-- The components of the form at an upper color are the inverse of those at the lower one. -/
lemma formMatrix_up (κ : K) [S.HasForm κ] :
    S.formMatrix ⟨κ, .up⟩ = ((S.bilin κ).toMatrix (S.basis ⟨κ, .up⟩))⁻¹ :=
  (formMatrix_eq_toMatrix _).trans (toMatrix_formBilin_up κ (S.basis ⟨κ, .up⟩))

/-- Lowering or raising a vector in components, `v_ν = g_νμ v^μ`. -/
lemma basis_repr_toDual (c : Color K) [inst : S.HasForm c.kind] (v : S.V c)
    (ν : basisIdx c.kind) :
    (S.basis c.dual).repr (S.toDual c v) ν = ∑ μ, (S.basis c).repr v μ *
      S.formMatrix c.dual ν μ := by
  match c, inst with
  | ⟨κ, .up⟩, _ =>
    refine (congrFun (dualBasis_repr_toDual_up κ (S.basis ⟨κ, .up⟩) v) ν).trans ?_
    change _ = ∑ μ, _ * S.formMatrix ⟨κ, .down⟩ ν μ
    rw [formMatrix_down]
    simp [Matrix.mulVec, dotProduct, mul_comm, LinearMap.BilinForm.toMatrix_apply]
  | ⟨κ, .down⟩, _ =>
    refine (congrFun (repr_toDual_down κ (S.basis ⟨κ, .up⟩) v) ν).trans ?_
    change _ = ∑ μ, _ * S.formMatrix ⟨κ, .up⟩ ν μ
    rw [formMatrix_up]
    simp [Matrix.mulVec, dotProduct, mul_comm]

/-- Lowering or raising is the linear map of the form with its indices swapped: the vector is
contracted with the second index of the form at `c.dual`. -/
lemma toDual_eq_toLin_comm (c : Color K) [inst : S.HasForm c.kind] :
    (S.toDual c).toLinearMap = S.toLin (TensorProduct.comm k _ _ (form c.dual)) := by
  refine LinearMap.ext fun u => ext_contr fun v => ?_
  match c, inst with
  | ⟨κ, .up⟩, _ =>
    refine Eq.trans ?_ (S.contr_toLin_comm (form (⟨κ, .down⟩ : Color K)) u v).symm
    rw [toLin_form]
    exact (lower_apply κ v u).trans (bilinEquiv_apply κ v u).symm
  | ⟨κ, .down⟩, _ =>
    refine Eq.trans ?_ (S.contr_toLin_comm (form (⟨κ, .up⟩ : Color K)) u v).symm
    rw [toLin_form]
    exact (apply_bilinEquiv_symm κ v u).symm

/-- Contracting with the second index of the form at `c.dual` and then with the second index of the
form at `c` is the identity: raising undoes lowering, read through `toLin`. -/
lemma toLin_comm_comp_comm_form (c : Color K) [S.HasForm c.kind] :
    S.toLin (TensorProduct.comm k _ _ (form c)) ∘ₗ
      S.toLin (TensorProduct.comm k _ _ (form c.dual)) = LinearMap.id := by
  have h := toDual_eq_toLin_comm (S := S) c.dual
  rw [← h, ← toDual_eq_toLin_comm c]
  exact LinearMap.ext fun v => toDual_toDual c v

/-- Lowering at `c.dual` is the inverse of lowering at `c`. -/
lemma toDual_dual : ∀ (c : Color K) [S.HasForm c.kind], S.toDual c.dual = (S.toDual c).symm
  | ⟨_, .up⟩, _ | ⟨_, .down⟩, _ => rfl

/-!

### B.2. Symmetric and antisymmetric forms

Symmetry is stated once, on the form `g` of the upper space. The inverse form, the form tensors at
both variances and the conjugate form (`Conjugation`) inherit it.

-/

variable (S) in
/-- The form on the kind `κ` is symmetric, `g(u, v) = g(v, u)`, as `η`. A metric is a symmetric
form. -/
class IsSymmetricForm (κ : K) [S.HasForm κ] : Prop where
  /-- The form is symmetric, Mathlib's `LinearMap.BilinForm.IsSymm`. -/
  isSymm : (S.bilin κ).IsSymm

variable (S) in
/-- The form on the kind `κ` is antisymmetric, `g(u, u) = 0` and so `g(u, v) = -g(v, u)`, as the
Weyl `ε`. -/
class IsAntisymmetricForm (κ : K) [S.HasForm κ] : Prop where
  /-- The form is alternating, Mathlib's `LinearMap.IsAlt`. -/
  isAlt : LinearMap.IsAlt (S.bilin κ)

/-- If swapping the arguments of the form scales it by `r`, lowering is `r` times contracting with
the first index of the form, `g(·, v) = r g(v, ·)`. -/
lemma toDual_up_eq_smul_bilinEquiv (κ : K) [S.HasForm κ] (r : k)
    (h : ∀ u v, S.bilin κ u v = r * S.bilin κ v u) (v : S.V ⟨κ, .up⟩) :
    S.toDual ⟨κ, .up⟩ v = r • S.bilinEquiv κ v :=
  LinearMap.ext fun u => by
    rw [toDual_up_apply, LinearMap.smul_apply, bilinEquiv_apply, smul_eq_mul, h]

/-- If swapping the arguments of the form scales it by `r` with `r² = 1`, swapping the two indices
of the form scales it by `r` at both variances, `g_νμ = r g_μν` and `g^νμ = r g^μν`. -/
lemma comm_form_eq_smul_of_bilin (κ : K) [S.HasForm κ] (r : k) (hr : r * r = 1)
    (h : ∀ u v, S.bilin κ u v = r * S.bilin κ v u) :
    ∀ v : Variance, TensorProduct.comm k _ _ (form (S := S) ⟨κ, v⟩) = r • form ⟨κ, v⟩
  | .down => S.toLin.injective <| LinearMap.ext fun x =>
    (LinearMap.congr_fun (toDual_eq_toLin_comm (S := S) ⟨κ, .up⟩) x).symm.trans <|
      (toDual_up_eq_smul_bilinEquiv κ r h x).trans <| by rw [map_smul, toLin_form]; rfl
  | .up => S.toLin.injective <| LinearMap.ext fun w =>
    (LinearMap.congr_fun (toDual_eq_toLin_comm (S := S) ⟨κ, .down⟩) w).symm.trans <| by
      rw [map_smul, toLin_form]
      -- Raising is `r` times the inverse of `bilinEquiv`, since lowering is `r` times it.
      refine (S.toDual ⟨κ, .up⟩).toLinearEquiv.injective ?_
      change S.toDual ⟨κ, .up⟩ (S.toDual ⟨κ, .down⟩ w) =
        S.toDual ⟨κ, .up⟩ (r • (S.bilinEquiv κ).symm w)
      rw [toDual_up_toDual_down, map_smul, toDual_up_eq_smul_bilinEquiv κ r h, smul_smul, hr,
        one_smul]
      exact ((S.bilinEquiv κ).toLinearEquiv.apply_symm_apply w).symm

/-- A symmetric form, `g_μν = g_νμ`, at both variances. -/
lemma form_symm (c : Color K) [S.HasForm c.kind] [S.IsSymmetricForm c.kind] :
    TensorProduct.comm k (S.V c) (S.V c) (form c) = form c :=
  (comm_form_eq_smul_of_bilin c.kind 1 (one_mul 1) (fun u v => by
    rw [one_mul, (IsSymmetricForm.isSymm (S := S)).eq]) c.variance).trans (one_smul k _)

/-- The components of a symmetric form are symmetric, `g^νμ = g^μν`. -/
lemma formMatrix_symm (c : Color K) [S.HasForm c.kind] [S.IsSymmetricForm c.kind]
    (μ ν : basisIdx c.kind) : S.formMatrix c ν μ = S.formMatrix c μ ν :=
  (((S.basis c).comm_eq_smul_iff _ 1).1 ((form_symm c).trans (one_smul k _).symm) μ ν).trans
    (one_mul _)

/-- A symmetric form is symmetric as a bilinear form, Mathlib's `LinearMap.BilinForm.IsSymm`. -/
lemma isSymm_formBilin (c : Color K) [S.HasForm c.kind] [S.IsSymmetricForm c.kind] :
    (S.formBilin c).IsSymm :=
  ⟨fun u v => by
    simpa only [formBilin_apply, form_symm] using S.contr_toLin_comm (form c) u v⟩

/-- An antisymmetric form, `g_μν = -g_νμ`, at both variances. -/
lemma form_antisymm (c : Color K) [S.HasForm c.kind] [S.IsAntisymmetricForm c.kind] :
    TensorProduct.comm k (S.V c) (S.V c) (form c) = -form c :=
  (comm_form_eq_smul_of_bilin c.kind (-1) (by rw [neg_one_mul, neg_neg]) (fun u v => by
    rw [neg_one_mul, (IsAntisymmetricForm.isAlt (S := S)).neg]) c.variance).trans
    (neg_one_smul k _)

/-- The components of an antisymmetric form are antisymmetric, `g^νμ = -g^μν`. -/
lemma formMatrix_antisymm (c : Color K) [S.HasForm c.kind] [S.IsAntisymmetricForm c.kind]
    (μ ν : basisIdx c.kind) : S.formMatrix c ν μ = -S.formMatrix c μ ν :=
  (((S.basis c).comm_eq_smul_iff _ (-1)).1
    ((form_antisymm c).trans (neg_one_smul k _).symm) μ ν).trans (neg_one_mul _)

/-- An antisymmetric form is alternating as a bilinear form, `g(u, u) = 0`, Mathlib's
`LinearMap.IsAlt`. It uses that `k` has characteristic zero. -/
lemma isAlt_formBilin (c : Color K) [S.HasForm c.kind] [S.IsAntisymmetricForm c.kind] :
    LinearMap.IsAlt (S.formBilin c) := fun u => by
  have h := S.contr_toLin_comm (form c) u u
  rw [form_antisymm, map_neg, LinearMap.neg_apply, tmul_neg, map_neg] at h
  rw [formBilin_apply]
  exact CharZero.neg_eq_self_iff.mp h

/-!

## C. The form as a tensor

-/

variable (S) in
/-- The form at `c` as a tensor with colors `![c, c]`, `g^μν` at an upper color and `g_μν` at a
lower one. -/
noncomputable def formTensor (c : Color K) [S.HasForm c.kind] : Tensor S ![c, c] :=
  S.twoIndexEquiv c c (S.form c)

/-- The form is an invariant tensor. Every group element fixes it, as every Lorentz
transformation fixes the Minkowski metric `η`. -/
lemma formTensor_invariant (c : Color K) [S.HasForm c.kind] (Λ : G) :
    Λ • S.formTensor c = S.formTensor c :=
  (S.twoIndexEquiv c c).toIntertwiningMap.map_invariant (form_invariant (S := S) c Λ)

/-- The components of the form tensor are those of the form, `g_μν` at the pair of labels
`(μ 0, μ 1)`. -/
lemma tensorBasis_repr_formTensor (c : Color K) [S.HasForm c.kind]
    (μ : Π j, basisIdx (![c, c] j).kind) :
    (S.tensorBasis ![c, c]).repr (S.formTensor c) μ = S.formMatrix c (μ 0) (μ 1) := by
  rw [formTensor, tensorBasis_repr_twoIndexEquiv]
  rfl

/-- A symmetric form is symmetric under the index swap as a tensor, `g^μν = g^νμ`. -/
lemma formTensor_symm (c : Color K) [S.HasForm c.kind] [S.IsSymmetricForm c.kind] :
    S.reindex (ColorEquiv.swapTwo c c) (S.formTensor c) = S.formTensor c := by
  rw [formTensor, reindex_swapTwo_twoIndexEquiv, form_symm]

/-- An antisymmetric form is antisymmetric under the index swap as a tensor,
`g^μν = -g^νμ`. -/
lemma formTensor_antisymm (c : Color K) [S.HasForm c.kind] [S.IsAntisymmetricForm c.kind] :
    S.reindex (ColorEquiv.swapTwo c c) (S.formTensor c) = -S.formTensor c := by
  rw [formTensor, reindex_swapTwo_twoIndexEquiv, form_antisymm, map_neg]

/-!

## D. Lowering and raising at one index

-/

variable {ι : Type} [DecidableEq ι]

variable (S) in
/-- `S.toDual` at the index `i` of a tensor and the identity at the other indices, as in
`T^μν ↦ T^μ_ν` for `i` the second index. The index has the color `a` by `ha`, and the form is the
one at the kind of `a`. The colors `c'` of the result have the dual color at `i` by `hi` and agree
with `c` elsewhere by `h`. It is `congrAt` of `toDual`. -/
noncomputable def toDualAt {c c' : ι → Color K} (i : ι) (a : Color K) (ha : c i = a)
    [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x) :
    (S.tensorRep c).Equiv (S.tensorRep c') :=
  S.congrAt i (((S.cast ha).trans (S.toDual a)).trans (S.cast hi.symm)) h

/-- Raising at an index undoes lowering at that index, `(T^μ_ν)^ν = T^μν`. -/
lemma toDualAt_toDualAt {c c' : ι → Color K} (i : ι) (a : Color K) (ha : c i = a)
    [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) :
    S.toDualAt i a.dual hi ha (fun x hx => (h x hx).symm) (S.toDualAt i a ha hi h t) = t := by
  rw [toDualAt, toDualAt, toDual_dual, show ((S.cast hi).trans (S.toDual a).symm).trans
    (S.cast ha.symm) = (((S.cast ha).trans (S.toDual a)).trans
      (S.cast hi.symm)).symm from rfl, ← congrAt_symm]
  exact (S.congrAt i _ h).symm_apply_apply t

/-- Lowering or raising at an index is `intertwiningMapAt` of `toDual` at that index. -/
lemma toDualAt_eq_intertwiningMapAt {c c' : ι → Color K} (i : ι) (a : Color K) (ha : c i = a)
    [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) :
    S.toDualAt i a ha hi h t = S.intertwiningMapAt i (((S.cast ha).trans
      (S.toDual a)).trans (S.cast hi.symm)).toIntertwiningMap h t :=
  congrAt_eq_intertwiningMapAt i _ h t

/-- Lowering or raising at an index is the linear map `linearMapAt` of `toDual` at that index.
Chains of lowerings and raisings compose index by index through `mapIndices_mapIndices`. -/
lemma toDualAt_eq_linearMapAt {c c' : ι → Color K} (i : ι) (a : Color K) (ha : c i = a)
    [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) :
    S.toDualAt i a ha hi h t = S.linearMapAt i (((S.cast ha).trans
      (S.toDual a)).trans (S.cast hi.symm)).toLinearMap h t :=
  rfl

/-- Lowering or raising the index `i` in components, `T^…_ν… = ∑ ρ, g_νρ T^…ρ…`. The basis index
`updateBasisIdx i h φ ρ` is `φ` with `ρ` at the index `i`. -/
lemma tensorBasis_repr_toDualAt [Fintype ι] {c c' : ι → Color K} (i : ι) (a : Color K)
    (ha : c i = a) [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x)
    (t : Tensor S c) (φ : Π x, basisIdx (c' x).kind) :
    (S.tensorBasis c').repr (S.toDualAt i a ha hi h t) φ =
      ∑ ρ : basisIdx (c i).kind, S.formMatrix a.dual
        (cast (congrArg (basisIdx ∘ Color.kind) hi) (φ i))
        (cast (congrArg (basisIdx ∘ Color.kind) ha) ρ : basisIdx a.kind) *
        (S.tensorBasis c).repr t (updateBasisIdx i h φ ρ) := by
  subst ha
  refine (tensorBasis_repr_intertwiningMapAt i _ h t φ).trans
    (Finset.sum_congr rfl fun ρ _ => congrArg (· * _) ?_)
  rw [LinearMap.toMatrix_apply]
  change (S.basis (c' i)).repr
    (S.cast hi.symm (S.toDual (c i) (S.basis (c i) ρ))) (φ i) = _
  rw [basis_repr_cast, basis_repr_toDual]
  simp [Finsupp.single_apply]

/-- Lowering or raising at the index `i` is contracting that index with the second index of the
form, `T^…_ν… = g_νμ T^…μ…`. -/
lemma toDualAt_eq_contr {c c' : ι → Color K} (i : ι) (a : Color K) (ha : c i = a)
    [S.HasForm a.kind] (hi : c' i = a.dual) (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) :
    S.toDualAt i a ha hi h t = Tensor.contr (ColorEquiv.matMulAt i a a.dual ha hi h)
      (S.tmulEquiv c ![a.dual, a.dual]
        (t ⊗ₜ S.reindex (ColorEquiv.swapTwo a.dual a.dual) (S.formTensor a.dual))) := by
  rw [formTensor, reindex_swapTwo_twoIndexEquiv, Tensor.contr_matMulAt, toDualAt,
    congrAt_eq_intertwiningMapAt, ← toDual_eq_toLin_comm]
  rfl

/-!

## E. Forms on a kind with two labels

-/

/-- The Schouten identity in components, `g^γρ δ^α_α' = g^γα' δ^α_ρ - g^ρα' δ^α_γ`, for an
antisymmetric form on a kind with two labels, such as the Weyl `ε`. -/
lemma formMatrix_schouten (c : Color K) [S.HasForm c.kind] [S.IsAntisymmetricForm c.kind]
    (h2 : Fintype.card (basisIdx c.kind) = 2) (γ ρ α' α : basisIdx c.kind) :
    S.formMatrix c γ ρ * (if α = α' then 1 else 0) =
      S.formMatrix c γ α' * (if ρ = α then 1 else 0) -
        S.formMatrix c ρ α' * (if γ = α then 1 else 0) := by
  simpa only [formBilin_basis] using
    (isAlt_formBilin (S := S) c).schouten_basis (S.basis c.dual) h2 γ ρ α' α

end Species

end Tensor
