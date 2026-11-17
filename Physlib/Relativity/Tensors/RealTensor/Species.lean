/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.ElabTactics
public import Physlib.Relativity.LorentzGroup.Basic
public import Physlib.Mathematics.ForMathlib.Contraction
import Mathlib.LinearAlgebra.Matrix.IsDiag
/-!

# The species of real Lorentz tensors

Real Lorentz tensors in `d + 1` dimensions as a species, with the Minkowski metric `η`.

## i. Overview

Real Lorentz tensors have one kind of index, the vector index `vec`. An upper index has the color
`⟨vec, up⟩` and a lower index the color `⟨vec, down⟩`. A color is the kind and variance of an
index. The species assigns to it a space: `V ⟨vec, up⟩ = Lorentz.Vector d`, the contravariant
vectors `v^μ` with basis `e_μ`, and `V ⟨vec, down⟩ = Lorentz.CoVector d`, the covariant vectors
`w_μ` with basis `e^μ`. Both are functions `Fin 1 ⊕ Fin d → ℝ` with Mathlib's analysis, so
`V ⟨vec, up⟩ = ℝ⁴` for `d = 3`. The labels `μ` run over `Fin 1 ⊕ Fin d`, with `Sum.inl 0` the
time direction and `Sum.inr i` the space directions. A Lorentz transformation
`Λ : LorentzGroup d` acts on an upper index by `(Λv)^μ = Λ^μ_ν v^ν` and on a lower index by
`(Λw)_μ = (Λ⁻¹)^ν_μ w_ν`. The two colors are named `realLorentz.up` and `realLorentz.down`, and
`ℝT[d, up, down]` is the space of the tensors `T^μ_ν`, under `open scoped Tensor.realLorentz`.

The contraction `u^μ w_μ` is the coordinate pairing `∑ μ, u^μ w_μ` of the two bases and the
delta is `δ_μ^ν = ∑ μ, e^μ ⊗ e_μ`. The one physical input is that the pairing is Lorentz invariant
(`realLorentz.coordPairing_rep`). The metric is `η = ∑ μ, η_μμ e_μ ⊗ e_μ` (`realLorentz.metric`),
with the matrix `diag(1, -1, …, -1)` at both colors.

So the general results apply. For example `η^μν η_νρ = δ^μ_ρ` is
`Species.contr_formTensor_formTensor` at `up`, and lowering an index, `v^μ ↦ v_ν = η_νμ v^μ`, is
`(realLorentz d).toDual up`.

The Lorentz vectors and covectors, the spaces of the two colors, are tensors with one upper index
and one lower index respectively (`Tensorial`). A vector transforms by `Λ *ᵥ v` and a covector by
`(Λ⁻¹)ᵀ *ᵥ ω`, and both enter index notation directly, as in `{v | μ ⊗ ω | μ}ᵀ` for `v^μ ω_μ`.

## ii. Key results

- `realLorentz.coordPairing_rep` : the pairing `v^μ ω_μ` is Lorentz invariant.
- `realLorentz` : the species of real Lorentz tensors, with the colors `realLorentz.up` and
  `realLorentz.down` and the spaces of tensors `ℝT[d, up, down]` (scoped).
- `realLorentz.metric` and the instances `(realLorentz d).HasForm κ` and
  `(realLorentz d).IsSymmetricForm κ` : the Minkowski metric `η`.
- `realLorentz.tensorBasis_repr_formTensor` : the components of `η^μν` and `η_μν` are the
  Minkowski matrix.
- `realLorentz.vectorTensorial` and `realLorentz.coVectorTensorial` : Lorentz vectors and
  covectors as tensors, with the actions `Lorentz.Vector.rep` and `Lorentz.CoVector.rep`.
- `realLorentz.tensorBasis_repr_toTensor_vector` and
  `realLorentz.tensorBasis_repr_toTensor_coVector` : the components of the tensor of a vector or a
  covector are its components, and `realLorentz.toTensor_symm_vector_apply` : the converse for a
  vector.
- `realLorentz.tensorBasis_repr_toTensor_vector_tmul` and
  `realLorentz.tensorBasis_repr_toTensor_coVector_tmul` : the components of the tensor of an
  element of `Vector d ⊗ Vector d` or `CoVector d ⊗ Vector d` are its coordinates in the product
  basis.
- `realLorentz.tensorBasis_repr_contr_vector_coVector` : the contraction `v^μ ω_μ` is
  `∑ μ, v^μ ω_μ`, and `realLorentz.contr_vector_coVector_rep` : it is Lorentz invariant.
- `realLorentz.tensorBasis_repr_formTensor_contr_vector` : the Minkowski product `⟪v, w⟫ₘ` is the
  contraction `η_μν v^μ w^ν`.
- `realLorentz.basis_repr_toDual` and `realLorentz.tensorBasis_repr_toDualAt` : lowering or raising
  an index multiplies its component by `η_νν`.
- `realLorentz.tensorBasis_repr_toDualAt_contr_vector_tmul` : the contraction `F_μν G^μν` in
  components.

## iii. Table of contents

- A. The species
- B. The Minkowski metric
- C. Components of the metric
- D. Lorentz vectors and covectors as tensors

## iv. References

* None.

-/

@[expose] public section

open TensorProduct Matrix

namespace Tensor

/-!

## A. The species

-/

/-- The kinds of real Lorentz index. There is one, the vector index `vec`, carried up as `v^μ` and
down as `w_μ`. -/
inductive realLorentz.Kind
  /-- The Lorentz vector index. -/
  | vec

namespace realLorentz

/-- The basis `e_μ` of the components `Fin 1 ⊕ Fin d → ℝ` of a vector at a real Lorentz index, the
same at both colors. -/
noncomputable abbrev indexBasis (d : ℕ) (_c : Color Kind) :
    Module.Basis (Fin 1 ⊕ Fin d) ℝ (Fin 1 ⊕ Fin d → ℝ) :=
  Pi.basisFun ℝ _

/-- The action of the Lorentz group on the components of a vector at an index, `Λ *ᵥ v` up and
`(Λ⁻¹)ᵀ *ᵥ w` down. Both colors have the components `Fin 1 ⊕ Fin d → ℝ`. The tensors of the two
colors are still different types, since they are built on `Species.colored`. -/
noncomputable def indexRep (d : ℕ) :
    (c : Color Kind) → Representation ℝ (LorentzGroup d) (Fin 1 ⊕ Fin d → ℝ)
  | ⟨_, .up⟩ => {
      toFun Λ := Matrix.toLinAlgEquiv (Pi.basisFun ℝ _) Λ
      map_one' := EmbeddingLike.map_eq_one_iff.mpr rfl
      map_mul' x y := by simp only [lorentzGroupIsGroup_mul_coe, _root_.map_mul] }
  | ⟨_, .down⟩ => {
      toFun Λ := Matrix.toLinAlgEquiv (Pi.basisFun ℝ _) (LorentzGroup.transpose Λ⁻¹)
      map_one' := by
        simp only [inv_one, LorentzGroup.transpose_one, lorentzGroupIsGroup_one_coe,
          _root_.map_one]
      map_mul' x y := by
        simp only [_root_.mul_inv_rev, LorentzGroup.inv_eq_dual, LorentzGroup.transpose_mul,
          lorentzGroupIsGroup_mul_coe, _root_.map_mul] }

lemma indexRep_toMatrix_up (d : ℕ) (κ : Kind) (Λ : LorentzGroup d) :
    LinearMap.toMatrix (indexBasis d ⟨κ, .up⟩) (indexBasis d ⟨κ, .up⟩) (indexRep d ⟨κ, .up⟩ Λ) =
      Λ.1 :=
  (LinearEquiv.eq_symm_apply (LinearMap.toMatrix _ _)).mp rfl

lemma indexRep_toMatrix_down (d : ℕ) (κ : Kind) (Λ : LorentzGroup d) :
    LinearMap.toMatrix (indexBasis d ⟨κ, .down⟩) (indexBasis d ⟨κ, .down⟩)
      (indexRep d ⟨κ, .down⟩ Λ) = Λ.1⁻¹ᵀ := by
  rw [← LorentzGroup.coe_inv]
  exact (LinearEquiv.eq_symm_apply (LinearMap.toMatrix _ _)).mp rfl

/-- The action at an upper index is `Λ *ᵥ v`. -/
lemma indexRep_up_apply (d : ℕ) (κ : Kind) (Λ : LorentzGroup d) (x : Fin 1 ⊕ Fin d → ℝ) :
    indexRep d ⟨κ, .up⟩ Λ x = Λ.1 *ᵥ x := by
  funext μ
  rw [← Pi.basisFun_repr ℝ _ (indexRep d _ Λ x) μ,
    ← LinearMap.toMatrix_mulVec_repr (indexBasis d _) (indexBasis d _), indexRep_toMatrix_up]
  simp [Matrix.mulVec, dotProduct]

/-- The action at a lower index is `(Λ⁻¹)ᵀ *ᵥ w`. -/
lemma indexRep_down_apply (d : ℕ) (κ : Kind) (Λ : LorentzGroup d) (x : Fin 1 ⊕ Fin d → ℝ) :
    indexRep d ⟨κ, .down⟩ Λ x = (Λ⁻¹).1ᵀ *ᵥ x := by
  funext μ
  rw [← Pi.basisFun_repr ℝ _ (indexRep d _ Λ x) μ,
    ← LinearMap.toMatrix_mulVec_repr (indexBasis d _) (indexBasis d _), indexRep_toMatrix_down,
    LorentzGroup.coe_inv]
  simp [Matrix.mulVec, dotProduct]

/-- The coordinate pairing of an index with its dual is Lorentz invariant. At a lower index it is
the pairing at the upper index with its factors swapped (`Species.invariant_of_up`). -/
lemma coordPairing_rep (d : ℕ) : ∀ (c : Color Kind) (Λ : LorentzGroup d)
    (x y : Fin 1 ⊕ Fin d → ℝ),
    (indexBasis d c).coordPairing (indexBasis d c.dual)
        (indexRep d c Λ x ⊗ₜ indexRep d c.dual Λ y) =
      (indexBasis d c).coordPairing (indexBasis d c.dual) (x ⊗ₜ y) :=
  Species.invariant_of_up (basisIdx := fun _ => Fin 1 ⊕ Fin d) _ _ fun κ Λ x y => by
    simp only [Module.Basis.coordPairing_tmul, Module.Basis.equivFun_apply, Pi.basisFun_repr,
      indexRep_up_apply, indexRep_down_apply]
    change (Λ.1 *ᵥ x) ⬝ᵥ ((Λ⁻¹).1ᵀ *ᵥ y) = x ⬝ᵥ y
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
      ← lorentzGroupIsGroup_mul_coe, inv_mul_cancel,
      lorentzGroupIsGroup_one_coe, Matrix.one_mulVec]

end realLorentz

open realLorentz in
/-- Real Lorentz tensors in `d + 1` dimensions, on the components `Fin 1 ⊕ Fin d → ℝ` with the
actions `Λ *ᵥ v` up and `(Λ⁻¹)ᵀ *ᵥ w` down. The labels `Fin 1 ⊕ Fin d` put time first. -/
noncomputable def realLorentz (d : ℕ) :
    Species ℝ (LorentzGroup d) Kind (fun _ => Fin 1 ⊕ Fin d) where
  V _ := Fin 1 ⊕ Fin d → ℝ
  rep := indexRep d
  basis := indexBasis d
  invariant := coordPairing_rep d

namespace realLorentz

lemma basis_eq (d : ℕ) (c : Color Kind) : (realLorentz d).basis c = indexBasis d c := rfl

/-- The color of an upper Lorentz index, `v^μ`. -/
abbrev up : Color Kind := ⟨.vec, .up⟩

/-- The color of a lower Lorentz index, `w_μ`. -/
abbrev down : Color Kind := ⟨.vec, .down⟩

/-- The real Lorentz tensors in `d + 1` dimensions with the colors listed, as `ℝT[d, up, down]` for
`T^μ_ν`. The colors are read in the namespace `realLorentz`. The notation is active under
`open scoped Tensor.realLorentz`. -/
scoped syntax (name := realLorentzSyntax) "ℝT[" term,+ "]" : term

macro_rules (kind := realLorentzSyntax)
  | `(ℝT[$d]) => `(Tensor (Tensor.realLorentz $d) ![])
  | `(ℝT[$d, $cs,*]) => `(Tensor (Tensor.realLorentz $d) (open Tensor.realLorentz in ![$cs,*]))

end realLorentz

/-!

## B. The Minkowski metric

-/

namespace realLorentz

/-- The Minkowski metric `∑ μ, η_μμ e_μ ⊗ e_μ` at the color `c`, with `η = diag(1, -1, …, -1)`:
`η^μν` at an upper color and `η_μν` at a lower one. -/
noncomputable def metric (d : ℕ) (c : Color Kind) : (realLorentz d).V c ⊗[ℝ] (realLorentz d).V c :=
  ∑ μ, minkowskiMatrix μ μ • ((realLorentz d).basis c μ ⊗ₜ (realLorentz d).basis c μ)

/-- The coordinates of `metric d c` in Mathlib's product basis are the Minkowski matrix. -/
lemma basis_tensorProduct_repr_metric (d : ℕ) (c : Color Kind) (μ ν : Fin 1 ⊕ Fin d) :
    (((realLorentz d).basis c).tensorProduct ((realLorentz d).basis c)).repr (metric d c) (μ, ν) =
      minkowskiMatrix μ ν := by
  let b := (realLorentz d).basis c
  have h : metric d c = (b.tensorProductToMatrix b).symm minkowskiMatrix := by
    rw [← (show Matrix.IsDiag (@minkowskiMatrix d) by
      rw [minkowskiMatrix.as_diagonal]; exact Matrix.isDiag_diagonal _).diagonal_diag,
      Module.Basis.tensorProductToMatrix_symm_diagonal]
    rfl
  rw [h]
  exact congrFun₂ ((b.tensorProductToMatrix b).apply_symm_apply minkowskiMatrix) μ ν

/-- The metric is Lorentz invariant, `Λ η Λᵀ = η` at an upper color and `Λ⁻¹ᵀ η Λ⁻¹ = η` at a
lower one. -/
lemma metric_invariant (d : ℕ) (c : Color Kind) (Λ : LorentzGroup d) :
    TensorProduct.map ((realLorentz d).rep c Λ) ((realLorentz d).rep c Λ) (metric d c) =
      metric d c := by
  let e := ((realLorentz d).basis c).tensorProductToMatrix ((realLorentz d).basis c)
  have he : e (metric d c) = minkowskiMatrix := Matrix.ext (basis_tensorProduct_repr_metric d c)
  refine e.injective ((Module.Basis.tensorProductToMatrix_map _ _ _ _ _).trans ?_)
  rw [he]
  match c with
  | ⟨_, .up⟩ =>
    rw [show LinearMap.toMatrix ((realLorentz d).basis up) ((realLorentz d).basis up)
        ((realLorentz d).rep up Λ) = Λ.1 from indexRep_toMatrix_up d .vec Λ,
      LorentzGroup.mul_minkowskiMatrix_mul_transpose]
  | ⟨_, .down⟩ =>
    rw [show LinearMap.toMatrix ((realLorentz d).basis down) ((realLorentz d).basis down)
        ((realLorentz d).rep down Λ) = Λ.1⁻¹ᵀ from indexRep_toMatrix_down d .vec Λ,
      Matrix.transpose_transpose, ← LorentzGroup.coe_inv,
      LorentzGroup.transpose_mul_minkowskiMatrix_mul_self]

/-- The metrics at a color and at its dual are inverse, `η^μν η_νρ = δ^μ_ρ`. -/
lemma metric_inverse (d : ℕ) (c : Color Kind) :
    (realLorentz d).toLin (metric d c) ∘ₗ (realLorentz d).toLin (metric d c.dual) =
      LinearMap.id :=
  Module.Basis.coordTensorHomEquiv_comp_of_mul_eq_one _ _ _ _ <| by
    simp only [basis_tensorProduct_repr_metric]
    exact minkowskiMatrix.sq

end realLorentz

/-- The Minkowski metric `η`, `diag(1, -1, …, -1)` at both colors of every kind. The signature is
mostly minus. -/
noncomputable instance (d : ℕ) (κ : realLorentz.Kind) : (realLorentz d).HasForm κ where
  formAt v := realLorentz.metric d ⟨κ, v⟩
  formAt_invariant v := realLorentz.metric_invariant d ⟨κ, v⟩
  formAt_inverse v := realLorentz.metric_inverse d ⟨κ, v⟩

/-- The Minkowski metric is symmetric. -/
instance (d : ℕ) (κ : realLorentz.Kind) : (realLorentz d).IsSymmetricForm κ where
  comm_form v := by
    change TensorProduct.comm ℝ _ _ (realLorentz.metric d ⟨κ, v⟩) = realLorentz.metric d ⟨κ, v⟩
    simp [realLorentz.metric]

/-!

## C. Components of the metric

-/

namespace realLorentz

/-- The components of the metric are the Minkowski matrix, `η_μν` at a lower color and `η^μν` at an
upper one. -/
lemma formMatrix_apply (d : ℕ) (c : Color Kind) (μ ν : Fin 1 ⊕ Fin d) :
    (realLorentz d).formMatrix c μ ν = minkowskiMatrix μ ν :=
  basis_tensorProduct_repr_metric d c μ ν

/-- The components of the metric are the Minkowski matrix `diag(1, -1, …, -1)`: at the labels
`![α, β]` they are `η^αβ` at an upper color and `η_αβ` at a lower one. The labels are any
`μ : Fin 2 → Fin 1 ⊕ Fin d`, as in `Species.tensorBasis_repr_twoIndexEquiv`. -/
lemma tensorBasis_repr_formTensor (d : ℕ) (c : Color Kind) (μ : Fin 2 → Fin 1 ⊕ Fin d) :
    ((realLorentz d).tensorBasis ![c, c]).repr ((realLorentz d).formTensor c) μ =
      minkowskiMatrix (μ 0) (μ 1) := by
  rw [Species.tensorBasis_repr_formTensor, formMatrix_apply]

/-- Lowering or raising a vector in components, `v_ν = η_νν v^ν`: the Minkowski metric is
diagonal. -/
lemma basis_repr_toDual (d : ℕ) (c : Color Kind) (v : (realLorentz d).V c)
    (ν : Fin 1 ⊕ Fin d) :
    ((realLorentz d).basis c.dual).repr ((realLorentz d).toDual c v) ν =
      minkowskiMatrix ν ν * ((realLorentz d).basis c).repr v ν := by
  simp [Species.basis_repr_toDual c v ν, formMatrix_apply,
    minkowskiMatrix.as_diagonal, Matrix.diagonal_apply, mul_comm]

/-- Lowering or raising the index `i` in components, `T^…_ν… = η_νν T^…ν…`: the
Minkowski metric is diagonal. -/
lemma tensorBasis_repr_toDualAt (d : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    {c c' : ι → Color Kind} (i : ι) (a : Color Kind) (ha : c i = a) (hi : c' i = a.dual)
    (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor (realLorentz d) c) (φ : ι → Fin 1 ⊕ Fin d) :
    ((realLorentz d).tensorBasis c').repr ((realLorentz d).toDualAt i a ha hi h t) φ =
      minkowskiMatrix (φ i) (φ i) * ((realLorentz d).tensorBasis c).repr t φ := by
  subst ha
  -- The basis index is the same type at every color, so updating `φ` at `i` by `φ i` is `φ`.
  have hφ : Species.updateBasisIdx (basisIdx := fun _ => Fin 1 ⊕ Fin d) i h φ (φ i) = φ :=
    funext fun x => by
      by_cases hx : x = i
      · subst hx; simp
      · simp [hx]
  simp [Species.tensorBasis_repr_toDualAt i _ rfl hi h, formMatrix_apply,
    minkowskiMatrix.as_diagonal, Matrix.diagonal_apply, hφ]

/-- `η^00 = 1` and `η^11 = -1` in `3 + 1` dimensions: the signature is mostly minus. -/
example : ((realLorentz 3).tensorBasis ![up, up]).repr ((realLorentz 3).formTensor up)
      ![.inl 0, .inl 0] = 1 ∧
    ((realLorentz 3).tensorBasis ![up, up]).repr ((realLorentz 3).formTensor up)
      ![.inr 0, .inr 0] = -1 := by
  simp [tensorBasis_repr_formTensor, minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]

/-- `η_μν η^μν = d + 1`: contracting both indices of `η_μν` with those of `η^μν` gives the number
of dimensions. -/
example (d : ℕ) : ((realLorentz d).tensorBasis ![]).repr
    {(realLorentz d).formTensor down | μ ν ⊗ (realLorentz d).formTensor up | μ ν}ᵀ
    (fun i => i.elim0) = d + 1 := by
  rw [Tensor.tensorBasis_repr_contr_two_pairs]
  simp only [Species.tensorBasis_repr_reindex, Species.tensorBasis_repr_tmulEquiv,
    tensorBasis_repr_formTensor]
  simp [minkowskiMatrix.as_diagonal, Matrix.diagonal_apply, Fintype.sum_sum_type, add_comm]

/-- `ℝT[3, up, down]` is the space of tensors `T^μ_ν` in four dimensions. -/
example : ℝT[3, up, down] = Tensor (realLorentz 3) ![up, down] := rfl
end realLorentz

end Tensor
