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
index. The species gives the vector kind the components `Fin 1 ⊕ Fin d → ℝ`, with the basis `e_μ`
(`indexBasis`). A lower index is Mathlib's `Module.Dual` of it, built by the framework, so the two
colors have different types. The labels `μ` run over `Fin 1 ⊕ Fin d`, with `Sum.inl 0` the time
direction and `Sum.inr i` the space directions. A Lorentz transformation
`Λ : LorentzGroup d` acts on an upper index by `(Λv)^μ = Λ^μ_ν v^ν` and on a lower index by
`(Λw)_μ = (Λ⁻¹)^ν_μ w_ν`. The two colors are named `realLorentz.up` and `realLorentz.down`, and
`ℝT[d, up, down]` is the space of the tensors `T^μ_ν`, under `open scoped Tensor.realLorentz`.

The contraction `u^μ w_μ` is the coordinate pairing `∑ μ, u^μ w_μ` of the two bases and the
delta is `δ_μ^ν = ∑ μ, e^μ ⊗ e_μ`. The one physical input is that the pairing is Lorentz invariant
(`realLorentz.coordPairing_rep`). The metric is the form `u^μ η_μν v^ν` on upper vectors
(`realLorentz.minkowskiBilin`), with the matrix `diag(1, -1, …, -1)` at both colors.

So the general results apply. For example `η^μν η_νρ = δ^μ_ρ` is
`Species.contr_formTensor_formTensor` at `up`, and lowering an index, `v^μ ↦ v_ν = η_νμ v^μ`, is
`(realLorentz d).toDual up`.

The Lorentz vectors are the tensors with one upper index,
`Lorentz.Vector d = Tensor (realLorentz d) ![up]`, and the covectors those with one lower index,
`Lorentz.CoVector d = Tensor (realLorentz d) ![down]`. A vector transforms by `Λ *ᵥ v` and a
covector by `(Λ⁻¹)ᵀ *ᵥ ω`, and both enter index notation directly, as in `{v | μ ⊗ ω | μ}ᵀ` for
`v^μ ω_μ`. Their components and contractions are in
`Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct`.

## ii. Key results

- `realLorentz.coordPairing_rep` : the pairing `v^μ ω_μ` is Lorentz invariant.
- `realLorentz` : the species of real Lorentz tensors, with the colors `realLorentz.up` and
  `realLorentz.down` and the spaces of tensors `ℝT[d, up, down]` (scoped).
- `realLorentz.minkowskiBilin` and the instances `(realLorentz d).HasForm κ` and
  `(realLorentz d).IsSymmetricForm κ` : the Minkowski metric `η`.
- `realLorentz.tensorBasis_repr_formTensor` : the components of `η^μν` and `η_μν` are the
  Minkowski matrix.
- `realLorentz.basis_repr_toDual` and `realLorentz.tensorBasis_repr_toDualAt` : lowering or raising
  an index multiplies its component by `η_νν`.

## iii. Table of contents

- A. The species
- B. The Minkowski metric
- C. Components of the metric

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

/-- The basis `e_μ` of the components `Fin 1 ⊕ Fin d → ℝ` of a vector at an upper real Lorentz
index. -/
noncomputable abbrev indexBasis (d : ℕ) : Module.Basis (Fin 1 ⊕ Fin d) ℝ (Fin 1 ⊕ Fin d → ℝ) :=
  Pi.basisFun ℝ _

/-- The action of the Lorentz group on the components of a vector at an upper index, `Λ *ᵥ v`. -/
noncomputable def indexRep (d : ℕ) : Representation ℝ (LorentzGroup d) (Fin 1 ⊕ Fin d → ℝ) where
  toFun Λ := Matrix.toLinAlgEquiv (Pi.basisFun ℝ _) Λ
  map_one' := EmbeddingLike.map_eq_one_iff.mpr rfl
  map_mul' x y := by simp only [lorentzGroupIsGroup_mul_coe, _root_.map_mul]

lemma indexRep_toMatrix (d : ℕ) (Λ : LorentzGroup d) :
    LinearMap.toMatrix (indexBasis d) (indexBasis d) (indexRep d Λ) = Λ.1 :=
  (LinearEquiv.eq_symm_apply (LinearMap.toMatrix _ _)).mp rfl

/-- The action at an upper index is `Λ *ᵥ v`. -/
lemma indexRep_apply (d : ℕ) (Λ : LorentzGroup d) (x : Fin 1 ⊕ Fin d → ℝ) :
    indexRep d Λ x = Λ.1 *ᵥ x := by
  funext μ
  rw [← Pi.basisFun_repr ℝ _ (indexRep d Λ x) μ,
    ← LinearMap.toMatrix_mulVec_repr (indexBasis d) (indexBasis d), indexRep_toMatrix]
  simp [Matrix.mulVec, dotProduct]

end realLorentz

open realLorentz in
/-- Real Lorentz tensors in `d + 1` dimensions, on the components `Fin 1 ⊕ Fin d → ℝ` with the
action `Λ *ᵥ v`. A lower index is a linear form on these, built by the framework. The labels
`Fin 1 ⊕ Fin d` put time first. -/
noncomputable def realLorentz (d : ℕ) : Species ℝ (LorentzGroup d) Kind where
  W _ := Fin 1 ⊕ Fin d → ℝ
  repW _ := indexRep d

/-- The standard basis `e_μ` of real Lorentz tensors, labelled by `Fin 1 ⊕ Fin d`. -/
noncomputable instance (d : ℕ) : (realLorentz d).HasBasis fun _ => Fin 1 ⊕ Fin d :=
  ⟨fun _ => realLorentz.indexBasis d⟩

namespace realLorentz

/-- The matrix of `Λ` at an upper index is `Λ`. -/
lemma rep_toMatrix_up (d : ℕ) (κ : Kind) (Λ : LorentzGroup d) :
    LinearMap.toMatrix ((realLorentz d).basis ⟨κ, .up⟩) ((realLorentz d).basis ⟨κ, .up⟩)
      ((realLorentz d).rep ⟨κ, .up⟩ Λ) = Λ.1 := by
  ext μ ν
  rw [LinearMap.toMatrix_apply]
  exact (LinearMap.toMatrix_apply _ _ _ _ _).symm.trans (congrFun₂ (indexRep_toMatrix d Λ) μ ν)

/-- The matrix of `Λ` at a lower index is `(Λ⁻¹)ᵀ`, from Mathlib's `LinearMap.toMatrix_transpose`
for the dual representation. -/
lemma rep_toMatrix_down (d : ℕ) (κ : Kind) (Λ : LorentzGroup d) :
    LinearMap.toMatrix ((realLorentz d).basis ⟨κ, .down⟩) ((realLorentz d).basis ⟨κ, .down⟩)
      ((realLorentz d).rep ⟨κ, .down⟩ Λ) = Λ.1⁻¹ᵀ := by
  rw [Species.toMatrix_rep_down, rep_toMatrix_up, LorentzGroup.coe_inv]

/-- The components of `x` in the basis of a kind are its entries. `realLorentz` is a def, so
`Pi.basisFun_repr` does not see `(realLorentz d).W κ` as `Fin 1 ⊕ Fin d → ℝ`. -/
@[simp] lemma basisW_repr (d : ℕ) (κ : Kind) (x : (realLorentz d).W κ) (μ : Fin 1 ⊕ Fin d) :
    ((realLorentz d).basisW κ).repr x μ = x μ := rfl

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

-- The components of a vector and of a covector at a written-out color by `simp`.
example (d : ℕ) (v : (realLorentz d).V up) (μ : Fin 1 ⊕ Fin d) :
    ((realLorentz d).basis up).repr v μ = v μ := by simp

example (d : ℕ) (w : (realLorentz d).V down) (μ : Fin 1 ⊕ Fin d) :
    ((realLorentz d).basis down).repr w μ = w ((realLorentz d).basis up μ) := by simp

end realLorentz

/-!

## B. The Minkowski metric

-/

namespace realLorentz

/-- The Minkowski form `g(u, v) = u^μ η_μν v^ν` on upper vectors, with `η = diag(1, -1, …, -1)`. -/
noncomputable def minkowskiBilin (d : ℕ) (κ : Kind) :
    LinearMap.BilinForm ℝ ((realLorentz d).V ⟨κ, .up⟩) :=
  Matrix.toBilin ((realLorentz d).basis ⟨κ, .up⟩) minkowskiMatrix

/-- The Minkowski form is Lorentz invariant, `Λᵀ η Λ = η`. -/
lemma minkowskiBilin_invariant (d : ℕ) (κ : Kind) (Λ : LorentzGroup d)
    (u v : (realLorentz d).V ⟨κ, .up⟩) :
    minkowskiBilin d κ ((realLorentz d).rep ⟨κ, .up⟩ Λ u) ((realLorentz d).rep ⟨κ, .up⟩ Λ v) =
      minkowskiBilin d κ u v := by
  let b := (realLorentz d).basis ⟨κ, .up⟩
  let ρ := (realLorentz d).rep ⟨κ, .up⟩ Λ
  refine LinearMap.congr_fun₂ (f := (minkowskiBilin d κ).comp ρ ρ)
    ((LinearMap.BilinForm.toMatrix b).injective ?_) u v
  rw [LinearMap.BilinForm.toMatrix_comp b b, rep_toMatrix_up, minkowskiBilin,
    LinearMap.BilinForm.toMatrix_toBilin, LorentzGroup.transpose_mul_minkowskiMatrix_mul_self]

/-- The Minkowski form is nondegenerate, `det η = ±1`. -/
lemma minkowskiBilin_nondegenerate (d : ℕ) (κ : Kind) : (minkowskiBilin d κ).Nondegenerate :=
  (Matrix.nondegenerate_toBilin_iff _).2 <| Matrix.nondegenerate_of_det_ne_zero <| by
    rw [minkowskiMatrix.det_eq_neg_one_pow_d]
    exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)

end realLorentz

/-- The Minkowski metric `η`, `diag(1, -1, …, -1)` on the upper vectors of every kind. The signature
is mostly minus. -/
noncomputable instance (d : ℕ) (κ : realLorentz.Kind) : (realLorentz d).HasForm κ where
  bilin := realLorentz.minkowskiBilin d κ
  bilin_invariant := realLorentz.minkowskiBilin_invariant d κ
  bilin_nondegenerate := realLorentz.minkowskiBilin_nondegenerate d κ

namespace realLorentz

/-- The components of the metric are the Minkowski matrix, `η_μν` at a lower color and `η^μν` at an
upper one. -/
lemma formMatrix_apply (d : ℕ) (c : Color Kind) (μ ν : Fin 1 ⊕ Fin d) :
    (realLorentz d).formMatrix c μ ν = minkowskiMatrix μ ν := by
  match c with
  | ⟨κ, .down⟩ =>
    rw [Species.formMatrix_down]
    exact congrFun₂ (LinearMap.BilinForm.toMatrix_toBilin _ _) μ ν
  | ⟨κ, .up⟩ =>
    rw [Species.formMatrix_up]
    change (LinearMap.BilinForm.toMatrix _ (minkowskiBilin d κ))⁻¹ μ ν = _
    rw [minkowskiBilin, LinearMap.BilinForm.toMatrix_toBilin,
      Matrix.inv_eq_left_inv minkowskiMatrix.sq]

end realLorentz

/-- The Minkowski metric is symmetric. -/
instance (d : ℕ) (κ : realLorentz.Kind) : (realLorentz d).IsSymmetricForm κ where
  isSymm := (Matrix.isSymm_toBilin_iff_isSymm _).2 minkowskiMatrix.eq_transpose

/-!

## C. Components of the metric

-/

namespace realLorentz

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
