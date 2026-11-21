/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Schouten
public import Physlib.Mathematics.Tensors.Conjugation
public import Physlib.Relativity.SL2C.Basic
/-!

# The species of complex Lorentz tensors

Weyl spinors and complex Lorentz vectors as one conjugate species of `SL(2, ℂ)`, with the invariant
forms `ε` and `η`.

## i. Overview

Complex Lorentz tensors are built from two kinds of index, the Weyl kind `weyl`, as in `ψ_α`, with
the labels `Fin 2`, and the vector kind `vec`, as in `v^μ`, with the labels `Fin 1 ⊕ Fin 3`, so the
space dimension is fixed at `d = 3`. The model `complexLorentz.base` gives only these two:
the components `Fin 2 → ℂ` with `M` acting by `M`, and `Fin 1 ⊕ Fin 3 → ℂ` with the Lorentz
transformation of `M`. The species `complexLorentz` is `base.withConj`, so the framework adds the
conjugate of each kind. The right-handed index `α̇` of `ψ̄_α̇` is the barred Weyl kind, with the
conjugate module `ConjModule (Fin 2 → ℂ)`, the conjugate representation and the conjugate basis.
The six colors `upL`, `downL`, `upR`, `downR`, `up` and `down` are the four Weyl colors and the two
plain vector colors. Under `open scoped Tensor.complexLorentz`, `ℂT[upL, downR]` is the space of
the tensors `T^α_β̇`.

`M ∈ SL(2, ℂ)` acts on components by `repMatrix c M`. It is `M` on `upL`, its conjugate `M̄` on
`upR`, the Lorentz transformation of `M` on `up`, and `(U M⁻¹)ᵀ` on a lower color with upper
matrix `U`. Conjugation of vectors and tensors, and its compatibility with `SL(2, ℂ)` and with the
contraction, are the framework's. The vector kind is self-conjugate, since the Lorentz
transformations are real, and it is a real kind.

The invariant form is `ε` on the Weyl kind and `η` on the vector kind. The forms on the conjugate
kinds are the conjugate forms, built by the framework, and have the same entries since `ε` and `η`
are real. The form `ε` is antisymmetric and `η` symmetric (`IsAntisymmetricForm`,
`IsSymmetricForm`). The form `ε^αβ` has the matrix `!![0, 1; -1, 0]` and `ε_αβ` the matrix
`!![0, -1; 1, 0]`, so `ε^12 = 1` and `ε_12 = -1`, and the same at the dotted indices. Lowering
contracts the second index of the form, `ψ_α = ε_αβ ψ^β`, as in Wess and Bagger. The forms are
written `εL`, `εL'`, `εR`, `εR'`, `η` and `η'`, and the deltas `δL`, `δL'`, `δR`, `δR'`, `δ` and
`δ'`. Their components are stated through `tensorBasis`, and the antisymmetry of `ε` and the
symmetry of `η` are stated in index notation.

A Weyl spinor or a complex Lorentz vector is a tensor with one index, `Tensor complexLorentz ![c]`,
with components `toComponents c`. `Fermion.LeftHandedWeyl` and the other spinor and vector types are
these tensors, so a spinor `ψ` enters index notation directly, as in `{ψ | α ⊗ φ | α}ᵀ`.

## ii. Key results

- `complexLorentz.base` : the Weyl and vector kinds, and `complexLorentz` : the species of complex
  Lorentz tensors, `base.withConj`.
- the instances `complexLorentz.base.HasForm κ` : the forms `ε` and `η`, with
  `IsAntisymmetricForm` at the Weyl kind and `IsSymmetricForm` at the vector kind, which the
  framework carries to the conjugate kinds.
- the instance `complexLorentz.base.IsSelfConjugate vec` and `complexLorentz.isRealKind_vec` : the
  vector kind is real.
- `complexLorentz.formMatrix_apply` : the components `Species.formMatrix` of the form at any color
  are `complexLorentz.formEntries`, for lowering in components.
- `complexLorentz.tensorBasis_repr_formTensor` : the components of `ε` and `η` at any color.
- `complexLorentz.formTensor_upL_antisymm`, `complexLorentz.formTensor_up_symm` : `ε` is
  antisymmetric and `η` symmetric, and `complexLorentz.deltaTensor_swap` : `δ^μ_ν = δ_ν^μ`.
- `complexLorentz.schouten_downL` and `complexLorentz.schouten_downR` : the Schouten identity of
  `ε` in index notation, from `Species.schouten_formTensor_deltaTensor` and
  `Species.schouten_formTensor_deltaTensor_dual`.
- `complexLorentz.toComponents` and `complexLorentz.toComponents_smul` : the components of a tensor
  with one index, on which `M` acts by `repMatrix c M`.

## iii. Table of contents

- A. The matrix `ε` of the Weyl forms
- B. The species
- C. The invariant forms
- D. Conjugation
- E. Components of the forms
- F. Symmetry of the forms
- G. Tensors with one index
- H. Examples

## iv. References

- J. Wess and J. Bagger, Supersymmetry and Supergravity, Appendix A.

-/

@[expose] public section

open TensorProduct Lorentz MatrixGroups Matrix

namespace Fermion

open Matrix MatrixGroups

/-!

## A. The matrix `ε` of the Weyl forms

-/

/-- The raw `2x2` matrix corresponding to the metric for fermions. -/
def metricRaw : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The metric is antisymmetric, `εᵀ = -ε`. -/
lemma transpose_metricRaw : metricRawᵀ = -metricRaw := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [metricRaw]

/-- The metric with its indices raised is the inverse of the metric, `(-ε) ε = 1`. -/
lemma neg_metricRaw_mul_metricRaw : -metricRaw * metricRaw = 1 := by
  simpa [metricRaw] using Matrix.one_fin_two.symm

/-- The metric is the inverse of its negative, `ε (-ε) = 1`. -/
lemma metricRaw_mul_neg_metricRaw : metricRaw * -metricRaw = 1 := by
  simpa [metricRaw] using Matrix.one_fin_two.symm

/-- Multiplying an element of `SL(2, ℂ)` on the left with the metric `𝓔` is equivalent
  to multiplying the inverse-transpose of that element on the right with the metric. -/
lemma comm_metricRaw (M : SL(2,ℂ)) : M.1 * metricRaw = metricRaw * (M.1⁻¹)ᵀ := by
  rw [metricRaw]
  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
  simp only [Fin.isValue, mul_zero, mul_neg, mul_one, zero_add, add_zero, transpose_apply, of_apply,
    cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, cons_mul,
    Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, zero_smul, tail_cons, one_smul,
    empty_vecMul, neg_smul, neg_cons, neg_neg, neg_empty, empty_mul, Equiv.symm_apply_apply]

lemma metricRaw_comm (M : SL(2,ℂ)) : metricRaw * M.1 = (M.1⁻¹)ᵀ * metricRaw := by
  rw [metricRaw]
  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
  simp only [Fin.isValue, zero_mul, one_mul, zero_add, neg_mul, add_zero, transpose_apply, of_apply,
    cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, cons_mul,
    Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, smul_cons, smul_eq_mul, mul_zero,
    mul_one, smul_empty, tail_cons, neg_smul, mul_neg, neg_cons, neg_neg, neg_zero, neg_empty,
    empty_vecMul, add_cons, empty_add_empty, empty_mul, Equiv.symm_apply_apply]

lemma star_comm_metricRaw (M : SL(2,ℂ)) : M.1.map star * metricRaw = metricRaw * ((M.1)⁻¹)ᴴ := by
  rw [metricRaw]
  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᴴ]
  rw [eta_fin_two (!![M.1 0 0, M.1 0 1; M.1 1 0, M.1 1 1].map star)]
  simp

lemma metricRaw_comm_star (M : SL(2,ℂ)) : metricRaw * M.1.map star = ((M.1)⁻¹)ᴴ * metricRaw := by
  rw [metricRaw]
  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᴴ]
  rw [eta_fin_two (!![M.1 0 0, M.1 0 1; M.1 1 0, M.1 1 1].map star)]
  simp

/-- Lowering both indices of a `2 × 2` matrix with the metric `ε_ab = -metricRaw a b` gives its
adjugate, transposed: `∑ x y, ε_{bx} ε_{ay} M^{yx} = (adj M)_{ba}`. -/
lemma sum_metricRaw_mul_sum_metricRaw_mul (M : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) :
    ∑ x, (-metricRaw) b x * ∑ y, (-metricRaw) a y * M y x = adjugate M b a := by
  fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two, metricRaw, adjugate_fin_two]

end Fermion

open Fermion

namespace Tensor

/-!

## B. The species

-/

namespace complexLorentz

/-- The kinds of complex Lorentz index before conjugation. The conjugates are adjoined by
`Species.withConj`. -/
inductive Kind
  /-- The Weyl spinor kind, as the left-handed index of `ψ_α`. Its conjugate is the right-handed
  index of `ψ̄_α̇`. -/
  | weyl
  /-- The vector kind, as the index of `v^μ`. -/
  | vec
deriving DecidableEq

export Kind (weyl vec)

/-- The basis labels of a kind, `Fin 2` for Weyl spinors and `Fin 1 ⊕ Fin 3` for vectors. -/
abbrev baseIdx : Kind → Type
  | weyl => Fin 2
  | vec => Fin 1 ⊕ Fin 3

instance : ∀ κ, Fintype (baseIdx κ)
  | weyl => inferInstanceAs (Fintype (Fin 2))
  | vec => inferInstanceAs (Fintype (Fin 1 ⊕ Fin 3))

instance : ∀ κ, DecidableEq (baseIdx κ)
  | weyl => inferInstanceAs (DecidableEq (Fin 2))
  | vec => inferInstanceAs (DecidableEq (Fin 1 ⊕ Fin 3))

/-- The basis labels of a kind and of its conjugate, those of the kind. -/
abbrev Idx (κ : Kind × Conjugacy) : Type := baseIdx κ.1

/-- The matrix of `M` at an upper index of each kind, `M` at the Weyl kind and the Lorentz
transformation of `M`, as a complex matrix, at the vector kind. -/
noncomputable def indexMatrix : (κ : Kind) → SL(2, ℂ) →* Matrix (baseIdx κ) (baseIdx κ) ℂ
  | weyl => { toFun M := M.1, map_one' := rfl, map_mul' _ _ := rfl }
  | vec => LorentzGroup.toComplex.comp SL2C.toLorentzGroup

/-- The matrix of `M` at an upper index of a kind and of its conjugate: `indexMatrix κ M` plain and
its conjugate barred, so `M` left-handed and `M̄` right-handed. -/
noncomputable def upMatrix : (κ : Kind × Conjugacy) → SL(2, ℂ) →* Matrix (Idx κ) (Idx κ) ℂ
  | (κ, .plain) => indexMatrix κ
  | (κ, .barred) => (starRingEnd ℂ).mapMatrix.toMonoidHom.comp (indexMatrix κ)

/-- The matrix of `M` at a lower index, `(U M⁻¹)ᵀ` for the matrix `U M` at the upper index. -/
noncomputable def downMatrix (κ : Kind × Conjugacy) : SL(2, ℂ) →* Matrix (Idx κ) (Idx κ) ℂ where
  toFun M := (upMatrix κ M⁻¹)ᵀ
  map_one' := by simp
  map_mul' M N := by simp [Matrix.transpose_mul]

/-- The matrix of `M` at a color. -/
noncomputable def repMatrix : (c : Color (Kind × Conjugacy)) → SL(2, ℂ) →*
    Matrix (Idx c.kind) (Idx c.kind) ℂ
  | ⟨κ, .up⟩ => upMatrix κ
  | ⟨κ, .down⟩ => downMatrix κ

/-- The representation of `SL(2, ℂ)` on the components `baseIdx κ → ℂ` of an upper index of kind
`κ`, by the matrix `indexMatrix κ M`. -/
noncomputable def indexRep (κ : Kind) : Representation ℂ SL(2, ℂ) (baseIdx κ → ℂ) :=
  (Matrix.toLinAlgEquiv (Pi.basisFun ℂ (baseIdx κ)) :
    Matrix _ _ ℂ →* Module.End ℂ (baseIdx κ → ℂ)).comp (indexMatrix κ)

/-- The species of left-handed Weyl spinors and complex Lorentz vectors, before conjugation: the
components `baseIdx κ → ℂ` with `M` acting by `indexMatrix κ M`. -/
noncomputable def base : Species ℂ SL(2, ℂ) Kind where
  W κ := baseIdx κ → ℂ
  repW := indexRep

/-- The standard basis of components of `base`. -/
noncomputable instance : base.HasBasis baseIdx := ⟨fun κ => Pi.basisFun ℂ (baseIdx κ)⟩

end complexLorentz

/-- Complex Lorentz tensors: Weyl spinors and complex Lorentz vectors with the action of
`SL(2, ℂ)`, and their conjugates. An upper left-handed index has the space `Fin 2 → ℂ` with `M`
acting by `M`, an upper right-handed index its conjugate module with the conjugate representation,
and an upper vector index the space `Fin 1 ⊕ Fin 3 → ℂ` with the Lorentz transformation of `M`. The
conjugate kinds and the lower indices are built by the framework. -/
noncomputable abbrev complexLorentz : Species ℂ SL(2, ℂ) (complexLorentz.Kind × Conjugacy) :=
  complexLorentz.base.withConj

namespace complexLorentz

/-- The matrix of `M` at an upper index of `base` is `indexMatrix κ M`. -/
lemma base_rep_toMatrix (κ : Kind) (M : SL(2, ℂ)) :
    LinearMap.toMatrix (base.basis ⟨κ, .up⟩) (base.basis ⟨κ, .up⟩) (base.rep ⟨κ, .up⟩ M) =
      indexMatrix κ M :=
  (LinearEquiv.eq_symm_apply (LinearMap.toMatrix _ _)).mp rfl

/-- The matrix of `M` at an upper index of kind `κ` is `upMatrix κ M`. At a barred kind the
conjugate basis gives the conjugate matrix, `Representation.toMatrix_conj`. -/
lemma rep_toMatrix_up : ∀ (κ : Kind × Conjugacy) (M : SL(2, ℂ)),
    LinearMap.toMatrix (complexLorentz.basis ⟨κ, .up⟩) (complexLorentz.basis ⟨κ, .up⟩)
      (complexLorentz.rep ⟨κ, .up⟩ M) = upMatrix κ M
  | (κ, .plain), M => base_rep_toMatrix κ M
  | (κ, .barred), M => (Representation.toMatrix_conj (indexRep κ) _ M).trans
      (congrArg (Matrix.map · star) (base_rep_toMatrix κ M))

/-- The matrix of `M` at every color is `repMatrix c M`. At a lower color this is Mathlib's
`LinearMap.toMatrix_transpose` for the dual representation. -/
lemma rep_toMatrix : ∀ (c : Color (Kind × Conjugacy)) (M : SL(2, ℂ)),
    LinearMap.toMatrix (complexLorentz.basis c) (complexLorentz.basis c) (complexLorentz.rep c M) =
      repMatrix c M
  | ⟨κ, .up⟩, M => rep_toMatrix_up κ M
  | ⟨κ, .down⟩, M => by
    rw [Species.toMatrix_rep_down, rep_toMatrix_up]
    rfl

/-- The components of `M` applied to a basis vector are a column of `repMatrix c M`. -/
lemma basis_repr_rep_basis (c : Color (Kind × Conjugacy)) (M : SL(2, ℂ)) (μ ν : Idx c.kind) :
    (complexLorentz.basis c).repr (complexLorentz.rep c M (complexLorentz.basis c μ)) ν =
      repMatrix c M ν μ := by
  rw [← LinearMap.toMatrix_apply, rep_toMatrix]

/-- On components the action is `repMatrix c M *ᵥ x`. -/
lemma basis_repr_rep (c : Color (Kind × Conjugacy)) (M : SL(2, ℂ)) (x : complexLorentz.V c) :
    (complexLorentz.basis c).repr (complexLorentz.rep c M x) =
      repMatrix c M *ᵥ (complexLorentz.basis c).repr x := by
  rw [← rep_toMatrix, LinearMap.toMatrix_mulVec_repr]

/-- An upper left-handed index, `ψ^α`. -/
abbrev upL : Color (Kind × Conjugacy) := ⟨(weyl, .plain), .up⟩

/-- A lower left-handed index, `ψ_α`. -/
abbrev downL : Color (Kind × Conjugacy) := ⟨(weyl, .plain), .down⟩

/-- An upper right-handed index, `ψ̄^α̇`. -/
abbrev upR : Color (Kind × Conjugacy) := ⟨(weyl, .barred), .up⟩

/-- A lower right-handed index, `ψ̄_α̇`. -/
abbrev downR : Color (Kind × Conjugacy) := ⟨(weyl, .barred), .down⟩

/-- An upper vector index, `v^μ`. -/
abbrev up : Color (Kind × Conjugacy) := ⟨(vec, .plain), .up⟩

/-- A lower vector index, `w_μ`. -/
abbrev down : Color (Kind × Conjugacy) := ⟨(vec, .plain), .down⟩

/-- Conjugation swaps `upL` and `upR`. The conjugate of `up` is the barred vector index, identified
with `up` by `IsSelfConjugate`. -/
example : upL.bar = upR ∧ downR.bar = downL ∧ up.bar = ⟨(vec, .barred), .up⟩ := ⟨rfl, rfl, rfl⟩

/-- The complex Lorentz tensors with the colors listed, as `ℂT[upL, downR]` for `T^α_β̇`. The colors
are read in the namespace `complexLorentz`. The notation is active under
`open scoped Tensor.complexLorentz`. -/
scoped syntax (name := complexLorentzSyntax) "ℂT[" term,* "]" : term

macro_rules (kind := complexLorentzSyntax)
  | `(ℂT[$cs,*]) => `(Tensor Tensor.complexLorentz (open Tensor.complexLorentz in ![$cs,*]))

/-- `ℂT[upL, downR]` is the space of tensors `T^α_β̇`. -/
example : ℂT[upL, downR] = Tensor complexLorentz ![upL, downR] := rfl

/-- At an upper right-handed index, the matrix of `M` in the conjugate basis is `M̄`. -/
lemma rep_toMatrix_upR (M : SL(2, ℂ)) :
    LinearMap.toMatrix (complexLorentz.basis upR) (complexLorentz.basis upR)
      (complexLorentz.rep upR M) = M.1.map star :=
  rep_toMatrix_up (weyl, .barred) M

/-- At a lower right-handed index, the matrix of `M` is `(M̄⁻¹)ᵀ = (M⁻¹)†`. -/
lemma rep_toMatrix_downR (M : SL(2, ℂ)) :
    LinearMap.toMatrix (complexLorentz.basis downR) (complexLorentz.basis downR)
      (complexLorentz.rep downR M) = (M.1⁻¹)ᴴ := by
  rw [rep_toMatrix, Lorentz.SL2C.inverse_coe]
  rfl

end complexLorentz

/-!

## C. The invariant forms

-/

namespace complexLorentz

/-- The entries of the form at each color, `ε^αβ = !![0, 1; -1, 0]` at the upper Weyl colors,
`ε_αβ = !![0, -1; 1, 0]` at the lower ones, and `η` at the vector colors. -/
noncomputable def formEntries : (c : Color (Kind × Conjugacy)) → Idx c.kind → Idx c.kind → ℂ
  | ⟨(weyl, _), .up⟩ => metricRaw
  | ⟨(weyl, _), .down⟩ => -metricRaw
  | ⟨(vec, _), _⟩ => fun μ ν => minkowskiMatrix μ ν

/-- The entries of the forms are real, so the conjugate form has the same entries. -/
lemma star_formEntries : ∀ (c : Color (Kind × Conjugacy)) (μ ν : Idx c.kind),
    star (formEntries c μ ν) = formEntries c.bar μ ν
  | ⟨(weyl, _), .up⟩, μ, ν | ⟨(weyl, _), .down⟩, μ, ν => by
    fin_cases μ <;> fin_cases ν <;> simp [formEntries, metricRaw]
  | ⟨(vec, _), _⟩, _, _ => Complex.conj_ofReal _

/-- The forms on upper vectors are invariant on matrices, `Mᵀ ε M = ε` and `Λᵀ η Λ = η`. -/
lemma transpose_mul_formEntries_mul : ∀ (κ : Kind) (g : SL(2, ℂ)),
    (indexMatrix κ g)ᵀ * Matrix.of (formEntries ⟨(κ, .plain), .down⟩) * indexMatrix κ g =
      Matrix.of (formEntries ⟨(κ, .plain), .down⟩)
  | weyl, g => by
    change g.1ᵀ * -metricRaw * g.1 = -metricRaw
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, metricRaw_comm, ← Matrix.mul_assoc,
      ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (by simp), Matrix.transpose_one,
      Matrix.one_mul]
  | vec, g => LorentzGroup.toComplex_transpose_mul_minkowskiMatrix_mul_self _

/-- The matrices of the forms at `c.dual` and at `c` are inverse, `(-ε) ε = 1` and `η η = 1`. -/
lemma formEntries_dual_mul : ∀ c : Color (Kind × Conjugacy),
    Matrix.of (formEntries c.dual) * Matrix.of (formEntries c) = 1
  | ⟨(weyl, _), .up⟩ => neg_metricRaw_mul_metricRaw
  | ⟨(weyl, _), .down⟩ => metricRaw_mul_neg_metricRaw
  | ⟨(vec, _), _⟩ => show (@minkowskiMatrix 3).map Complex.ofRealHom *
      (@minkowskiMatrix 3).map Complex.ofRealHom = 1 by
    rw [← Matrix.map_mul, minkowskiMatrix.sq, Matrix.map_one _ (map_zero _) (map_one _)]

/-- The invariant form on the upper vectors of the kind `κ`, with the matrix
`formEntries ⟨(κ, plain), down⟩`: `ε_αβ` at the Weyl kind and `η_μν` at the vector kind. -/
noncomputable def invariantBilin (κ : Kind) : LinearMap.BilinForm ℂ (base.V ⟨κ, .up⟩) :=
  Matrix.toBilin (base.basis ⟨κ, .up⟩) (Matrix.of (formEntries ⟨(κ, .plain), .down⟩))

/-- The forms are invariant under `SL(2, ℂ)`. -/
lemma invariantBilin_invariant (κ : Kind) (g : SL(2, ℂ)) (u v : base.V ⟨κ, .up⟩) :
    invariantBilin κ (base.rep ⟨κ, .up⟩ g u) (base.rep ⟨κ, .up⟩ g v) = invariantBilin κ u v := by
  let b := base.basis ⟨κ, .up⟩
  let ρ := base.rep ⟨κ, .up⟩ g
  refine LinearMap.congr_fun₂ (f := (invariantBilin κ).comp ρ ρ)
    ((LinearMap.BilinForm.toMatrix b).injective ?_) u v
  rw [LinearMap.BilinForm.toMatrix_comp b b, base_rep_toMatrix, invariantBilin,
    LinearMap.BilinForm.toMatrix_toBilin, transpose_mul_formEntries_mul]

/-- The forms are nondegenerate, their matrices being invertible. -/
lemma invariantBilin_nondegenerate (κ : Kind) : (invariantBilin κ).Nondegenerate :=
  (Matrix.nondegenerate_toBilin_iff _).2 <| Matrix.nondegenerate_of_det_ne_zero <|
    (Matrix.isUnit_det_of_left_inverse (formEntries_dual_mul ⟨(κ, .plain), .down⟩)).ne_zero

end complexLorentz

/-- The invariant forms, `ε` at the Weyl kind and `η` at the vector kind. The forms at the
conjugate kinds are the conjugate forms, built by the framework. -/
noncomputable instance (κ : complexLorentz.Kind) : complexLorentz.base.HasForm κ where
  bilin := complexLorentz.invariantBilin κ
  bilin_invariant := complexLorentz.invariantBilin_invariant κ
  bilin_nondegenerate := complexLorentz.invariantBilin_nondegenerate κ

namespace complexLorentz

/-- The form `ε^αβ` on two upper left-handed indices. -/
scoped notation "εL" => Species.formTensor Tensor.complexLorentz Tensor.complexLorentz.upL

/-- The form `ε_αβ` on two lower left-handed indices. -/
scoped notation "εL'" => Species.formTensor Tensor.complexLorentz Tensor.complexLorentz.downL

/-- The form `ε^α̇β̇` on two upper right-handed indices. -/
scoped notation "εR" => Species.formTensor Tensor.complexLorentz Tensor.complexLorentz.upR

/-- The form `ε_α̇β̇` on two lower right-handed indices. -/
scoped notation "εR'" => Species.formTensor Tensor.complexLorentz Tensor.complexLorentz.downR

/-- The metric `η^μν` on two upper vector indices. -/
scoped notation "η" => Species.formTensor Tensor.complexLorentz Tensor.complexLorentz.up

/-- The metric `η_μν` on two lower vector indices. -/
scoped notation "η'" => Species.formTensor Tensor.complexLorentz Tensor.complexLorentz.down

/-- The delta `δ^μ_ν`, on the colors `![up, down]`. -/
scoped notation "δ" => Species.deltaTensor Tensor.complexLorentz Tensor.complexLorentz.down

/-- The delta `δ_μ^ν`, on the colors `![down, up]`. -/
scoped notation "δ'" => Species.deltaTensor Tensor.complexLorentz Tensor.complexLorentz.up

/-- The delta `δ^α_β`, on the colors `![upL, downL]`. -/
scoped notation "δL" => Species.deltaTensor Tensor.complexLorentz Tensor.complexLorentz.downL

/-- The delta `δ_α^β`, on the colors `![downL, upL]`. -/
scoped notation "δL'" => Species.deltaTensor Tensor.complexLorentz Tensor.complexLorentz.upL

/-- The delta `δ^α̇_β̇`, on the colors `![upR, downR]`. -/
scoped notation "δR" => Species.deltaTensor Tensor.complexLorentz Tensor.complexLorentz.downR

/-- The delta `δ_α̇^β̇`, on the colors `![downR, upR]`. -/
scoped notation "δR'" => Species.deltaTensor Tensor.complexLorentz Tensor.complexLorentz.upR

end complexLorentz

/-!

## D. Conjugation

Conjugation of vectors and tensors is the framework's, on `base.withConj`. The model says only that
the vector kind is self-conjugate, since the Lorentz transformations are real.

-/

namespace complexLorentz

/-- The vector kind is self-conjugate: the conjugate `v̄` of a vector is identified with the vector
of conjugate components `v*`. This commutes with `SL(2, ℂ)` because the Lorentz transformations are
real. -/
noncomputable instance : base.IsSelfConjugate vec where
  equiv := .mk ((conjEquiv (k := ℂ) (M := baseIdx vec → ℂ)).symm.trans
      (starLinearEquiv ℂ)) fun g => LinearMap.ext fun v => funext fun i => by
    change star (indexMatrix vec g *ᵥ v.ofConj) i = (indexMatrix vec g *ᵥ star v.ofConj) i
    simp only [Matrix.mulVec, dotProduct, Pi.star_apply, star_sum, star_mul']
    exact Finset.sum_congr rfl fun j _ =>
      congrArg (· * _) (LorentzGroup.star_toComplex_apply (SL2C.toLorentzGroup g) i j)

/-- The vector kind is real: its antilinear map `v ↦ v*` squares to the identity. -/
lemma isRealKind_vec : base.IsRealKind vec := fun v => star_star (R := baseIdx vec → ℂ) v

end complexLorentz

/-!

## E. Components of the forms

-/

namespace complexLorentz

/-- The matrix of the form on the upper vectors of a kind is `formEntries` at the lower color. At a
barred kind the form is the conjugate form, whose matrix is the conjugate of the real matrix. -/
lemma toMatrix_bilin : ∀ κ : Kind × Conjugacy,
    LinearMap.BilinForm.toMatrix (complexLorentz.basis ⟨κ, .up⟩) (complexLorentz.bilin κ) =
      Matrix.of (formEntries ⟨κ, .down⟩)
  | (_, .plain) => LinearMap.BilinForm.toMatrix_toBilin _ _
  | (κ, .barred) =>
    (LinearMap.BilinForm.toMatrix_conj (invariantBilin κ) (base.basis ⟨κ, .up⟩)).trans <|
      (congrArg (Matrix.map · star) (LinearMap.BilinForm.toMatrix_toBilin _ _)).trans <|
        Matrix.ext fun μ ν => star_formEntries ⟨(κ, .plain), .down⟩ μ ν

/-- The components of the form at any color are `formEntries`. -/
lemma formMatrix_apply (c : Color (Kind × Conjugacy)) (μ ν : Idx c.kind) :
    Species.formMatrix complexLorentz c μ ν = formEntries c μ ν := by
  match c with
  | ⟨κ, .down⟩ =>
    rw [Species.formMatrix_down, toMatrix_bilin]
    rfl
  | ⟨κ, .up⟩ =>
    rw [Species.formMatrix_up, toMatrix_bilin]
    exact congrFun₂ (Matrix.inv_eq_left_inv (formEntries_dual_mul ⟨κ, .down⟩)) μ ν

/-- The components of the form tensor at any color are `formEntries`, at the pair of labels
`(μ 0, μ 1)`. The labels `μ` form a dependent family, since the basis labels of an index depend on
its color. -/
lemma tensorBasis_repr_formTensor (c : Color (Kind × Conjugacy)) (μ : Π i, Idx (![c, c] i).kind) :
    (complexLorentz.tensorBasis ![c, c]).repr (complexLorentz.formTensor c) μ =
      formEntries c (μ 0) (μ 1) :=
  (Species.tensorBasis_repr_formTensor c μ).trans (formMatrix_apply c _ _)

/-- The components of `η^μν` and `η_μν` are the Minkowski matrix `diag(1, -1, -1, -1)`. -/
lemma tensorBasis_repr_formTensor_vec (v : Variance)
    (μ : Π i, Idx (![⟨(vec, .plain), v⟩, ⟨(vec, .plain), v⟩] i : Color (Kind × Conjugacy)).kind) :
    (complexLorentz.tensorBasis ![⟨(vec, .plain), v⟩, ⟨(vec, .plain), v⟩]).repr
      (complexLorentz.formTensor ⟨(vec, .plain), v⟩) μ = minkowskiMatrix (μ 0) (μ 1) :=
  tensorBasis_repr_formTensor ⟨(vec, .plain), v⟩ μ

/-- `η^00 = 1` and `η^11 = -1`: the signature is mostly minus. -/
example : (complexLorentz.tensorBasis ![up, up]).repr η
      (Fin.cons (Sum.inl 0 : Fin 1 ⊕ Fin 3) (Fin.cons (Sum.inl 0 : Fin 1 ⊕ Fin 3) (·.elim0))) =
        1 ∧
    (complexLorentz.tensorBasis ![up, up]).repr η
      (Fin.cons (Sum.inr 0 : Fin 1 ⊕ Fin 3) (Fin.cons (Sum.inr 0 : Fin 1 ⊕ Fin 3) (·.elim0))) =
        -1 := by
  rw [tensorBasis_repr_formTensor_vec .up, tensorBasis_repr_formTensor_vec .up]
  change ((minkowskiMatrix (Sum.inl 0) (Sum.inl 0) : ℝ) : ℂ) = 1 ∧
    ((minkowskiMatrix (Sum.inr 0) (Sum.inr 0) : ℝ) : ℂ) = -1
  simp

end complexLorentz

/-!

## F. Symmetry of the forms

-/

namespace complexLorentz

/-- The form on two basis vectors of a kind is an entry of `formEntries`, `g(e_μ, e_ν) = g_μν`. -/
lemma base_bilin_basis (κ : Kind) (μ ν : baseIdx κ) :
    base.bilin κ (base.basis ⟨κ, .up⟩ μ) (base.basis ⟨κ, .up⟩ ν) =
      formEntries ⟨(κ, .plain), .down⟩ μ ν :=
  (LinearMap.BilinForm.toMatrix_apply _ _ μ ν).symm.trans
    (congrFun₂ (toMatrix_bilin (κ, .plain)) μ ν)

/-- The Minkowski metric `η` on the vector kind is symmetric, `η_νμ = η_μν`. The framework derives
the symmetry of `η^μν` and of the conjugate kind. -/
instance : base.IsSymmetricForm vec where
  isSymm := (Matrix.isSymm_toBilin_iff_isSymm _).2 <| Matrix.IsSymm.ext fun μ ν =>
    congrArg Complex.ofReal (congrFun₂ minkowskiMatrix.eq_transpose μ ν)

/-- The form `ε` on the Weyl kind is antisymmetric, `ε_βα = -ε_αβ`. The framework derives the
antisymmetry of `ε^αβ` and of the dotted `ε`. -/
instance : base.IsAntisymmetricForm weyl where
  isAlt := LinearMap.isAlt_iff_eq_neg_flip.2 <|
    LinearMap.BilinForm.ext_basis (base.basis ⟨weyl, .up⟩) fun μ ν => by
      rw [LinearMap.neg_apply, LinearMap.neg_apply, LinearMap.flip_apply, base_bilin_basis,
        base_bilin_basis]
      change -metricRaw μ ν = -(-metricRaw ν μ)
      rw [neg_neg, ← Matrix.transpose_apply metricRaw μ ν, transpose_metricRaw, Matrix.neg_apply]

/-- `ε^αβ` is antisymmetric, `ε^αβ = -ε^βα`. -/
lemma formTensor_upL_antisymm : {εL | α β = -εL | β α}ᵀ := by
  tensor_regroup

/-- `ε_αβ` is antisymmetric, `ε_αβ = -ε_βα`. -/
lemma formTensor_downL_antisymm : {εL' | α β = -εL' | β α}ᵀ := by
  tensor_regroup

/-- `ε^α̇β̇` is antisymmetric, `ε^α̇β̇ = -ε^β̇α̇`. -/
lemma formTensor_upR_antisymm : {εR | α β = -εR | β α}ᵀ := by
  tensor_regroup

/-- `ε_α̇β̇` is antisymmetric, `ε_α̇β̇ = -ε_β̇α̇`. -/
lemma formTensor_downR_antisymm : {εR' | α β = -εR' | β α}ᵀ := by
  tensor_regroup

/-- `η^μν` is symmetric, `η^μν = η^νμ`. -/
lemma formTensor_up_symm : {η | μ ν = η | ν μ}ᵀ := by
  tensor_regroup

/-- `η_μν` is symmetric, `η_μν = η_νμ`. -/
lemma formTensor_down_symm : {η' | μ ν = η' | ν μ}ᵀ := by
  tensor_regroup

/-- The Schouten identity for left-handed indices, `ε_γρ δ^α_α' = ε_α'ρ δ_γ^α - ε_α'γ δ_ρ^α`. The
free lower index `α'` is the first index of each `ε`. -/
lemma schouten_downL :
    {εL' | γ ρ ⊗ δL | α α' = εL' | α' ρ ⊗ δL' | γ α + -{εL' | α' γ ⊗ δL' | ρ α}ᵀ | α' γ ρ α}ᵀ := by
  tensor_regroup using Species.schouten_formTensor_deltaTensor (S := complexLorentz) downL
    (Fintype.card_fin 2)

/-- The Schouten identity for right-handed indices,
`ε_γ̇ρ̇ δ_α̇^α̇' = ε_α̇ρ̇ δ_γ̇^α̇' - ε_α̇γ̇ δ_ρ̇^α̇'`. The free lower index `α̇` is the first
index of each `ε`. -/
lemma schouten_downR :
    {εR' | γ ρ ⊗ δR' | α α' = εR' | α ρ ⊗ δR' | γ α' + -{εR' | α γ ⊗ δR' | ρ α'}ᵀ | α γ ρ α'}ᵀ := by
  tensor_regroup using Species.schouten_formTensor_deltaTensor_dual (S := complexLorentz) downR
    (Fintype.card_fin 2)

/-- Swapping the indices of the delta at `c` gives the delta at `c.dual`, as `δ^μ_ν = δ_ν^μ`. -/
lemma deltaTensor_swap (c : Color (Kind × Conjugacy)) :
    {complexLorentz.deltaTensor c | μ ν = complexLorentz.deltaTensor c.dual | ν μ}ᵀ := by
  tensor_regroup

end complexLorentz

/-!

## G. Tensors with one index

A Weyl spinor or a complex Lorentz vector is a tensor with one index, `Tensor complexLorentz ![c]`.
Its components are `toComponents c`, and the group acts on them by the matrix `repMatrix c M`.

-/

namespace complexLorentz

/-- The components of a tensor with one index of color `c`, as `ψ^α` or `v^μ`. -/
noncomputable def toComponents (c : Color (Kind × Conjugacy)) :
    Tensor complexLorentz ![c] ≃ₗ[ℂ] (Idx c.kind → ℂ) :=
  (complexLorentz.oneIndexEquiv c).toLinearEquiv.symm ≪≫ₗ (complexLorentz.basis c).equivFun

/-- The basis of the tensors with one index, the tensor with the component `1` at `μ`. -/
noncomputable def oneIndexBasis (c : Color (Kind × Conjugacy)) :
    Module.Basis (Idx c.kind) ℂ (Tensor complexLorentz ![c]) :=
  (Pi.basisFun ℂ _).map (toComponents c).symm

@[simp]
lemma oneIndexBasis_repr (c : Color (Kind × Conjugacy)) (t : Tensor complexLorentz ![c])
    (μ : Idx c.kind) :
    (oneIndexBasis c).repr t μ = toComponents c t μ := by
  simp [oneIndexBasis]

@[simp]
lemma toComponents_oneIndexBasis (c : Color (Kind × Conjugacy)) (μ : Idx c.kind) :
    toComponents c (oneIndexBasis c μ) = Pi.single μ 1 := by
  simp [oneIndexBasis]

/-- The components of a tensor with one index in `tensorBasis` are its components, at the label of
its one index. -/
lemma tensorBasis_repr_oneIndex (c : Color (Kind × Conjugacy)) (t : Tensor complexLorentz ![c])
    (μ : Π i, Idx (![c] i).kind) :
    (complexLorentz.tensorBasis ![c]).repr t μ = toComponents c t (μ 0) := by
  conv_lhs => rw [← (complexLorentz.oneIndexEquiv c).apply_symm_apply t]
  exact Species.tensorBasis_repr_oneIndexEquiv c _ μ

/-- The group acts on the components by `repMatrix c M`. -/
lemma toComponents_smul (c : Color (Kind × Conjugacy)) (M : SL(2, ℂ))
    (t : Tensor complexLorentz ![c]) :
    toComponents c (M • t) = repMatrix c M *ᵥ toComponents c t := by
  have h := Representation.IntertwiningMap.isIntertwining _ _
    (complexLorentz.oneIndexEquiv c).symm.toIntertwiningMap M t
  change ⇑((complexLorentz.basis c).repr ((complexLorentz.oneIndexEquiv c).symm (M • t))) = _
  rw [show (complexLorentz.oneIndexEquiv c).symm (M • t) = _ from h, basis_repr_rep]
  rfl

end complexLorentz

/-!

## H. Examples

-/

namespace complexLorentz

/-- Lowering a left-handed spinor, `ψ_α = ε_αβ ψ^β` with `ε_01 = -1`: `ψ_0 = -ψ^1` and
`ψ_1 = ψ^0`. -/
example (ψ : complexLorentz.V upL) :
    (complexLorentz.basis downL).repr (complexLorentz.toDual upL ψ) 0 =
        -(complexLorentz.basis upL).repr ψ 1 ∧
      (complexLorentz.basis downL).repr (complexLorentz.toDual upL ψ) 1 =
        (complexLorentz.basis upL).repr ψ 0 := by
  refine ⟨(Species.basis_repr_toDual upL ψ 0).trans ?_,
    (Species.basis_repr_toDual upL ψ 1).trans ?_⟩ <;>
  simp [formMatrix_apply, formEntries, metricRaw, Fin.sum_univ_two]

/-- `ε^αβ ε_βγ = δ^α_γ`, by `tensor_regroup` through `contr_formTensor_formTensor`. -/
example : {εL | α β ⊗ εL' | β γ = δL | α γ}ᵀ := by
  tensor_regroup

/-- `g^αβ g_βγ = δ^α_γ` at every color: `ε`, `ε'` and `η` with their duals. -/
example (c : Color (Kind × Conjugacy)) : {complexLorentz.formTensor c | α β ⊗
    complexLorentz.formTensor c.dual | β γ = complexLorentz.deltaTensor c.dual | α γ}ᵀ := by
  tensor_regroup

/-- The components of `ε^αβ ⊗ ε^α̇β̇` are the products of the components of `εL` and `εR`. -/
example (μ : Π i, Idx (![upL, upL, upR, upR] i).kind) :
    (complexLorentz.tensorBasis _).repr {εL | α β ⊗ εR | α' β'}ᵀ μ =
      metricRaw (μ 0) (μ 1) * metricRaw (μ 2) (μ 3) := by
  rw [Species.tensorBasis_repr_reindex, Species.tensorBasis_repr_tmulEquiv,
    tensorBasis_repr_formTensor upL, tensorBasis_repr_formTensor upR]
  rfl

/-- `(ε^αβ ε_βγ)` at `α = γ = 0` is `1`, from the components of `εL` and `εL'`. -/
example : (complexLorentz.tensorBasis _).repr {εL | α β ⊗ εL' | β γ}ᵀ
    (Fin.cons (0 : Fin 2) (Fin.cons (0 : Fin 2) fun i => i.elim0)) = 1 := by
  rw [Tensor.tensorBasis_repr_contr_one_pair]
  simp only [Species.tensorBasis_repr_reindex, Species.tensorBasis_repr_tmulEquiv,
    tensorBasis_repr_formTensor upL, tensorBasis_repr_formTensor downL]
  change ∑ β : Fin 2, metricRaw 0 β * (-metricRaw) β 0 = 1
  simp [metricRaw, Fin.sum_univ_two]

/-- The conjugate of `ε^αβ` is `ε^α̇β̇`. The conjugate lands on `![upR, upR]` directly. -/
example : Tensor.conj εL = εR := by
  refine (complexLorentz.tensorBasis _).repr.injective (Finsupp.ext fun μ => ?_)
  rw [Tensor.tensorBasis_repr_conj, tensorBasis_repr_formTensor upL,
    tensorBasis_repr_formTensor upR]
  -- The labels are read along `rfl`, so they are `μ 0` and `μ 1`.
  exact star_formEntries upL _ _

-- The right-handed space is the conjugate module `ConjModule (Fin 2 → ℂ)`, a structure, so a
-- left-handed spinor is rejected as a right-handed one and the other way round, also when all
-- definitions unfold: at a single vector and covector, inside `pure`, on `![…]` and on
-- `fun _ => c`. A vector is rejected as a covector.
example (v : complexLorentz.V upL) (u : complexLorentz.V upR) (w : complexLorentz.V downL)
    (t : ℂT[upL]) (s : ℂT[downL]) (t' : Tensor complexLorentz fun _ : Fin 2 => upL)
    (s' : Tensor complexLorentz fun _ : Fin 2 => downL) :
    complexLorentz.V upL × complexLorentz.V upR × complexLorentz.V downL × ℂT[upL] × ℂT[downL] ×
      (Tensor complexLorentz fun _ : Fin 2 => upL) ×
      Tensor complexLorentz fun _ : Fin 2 => downL := by
  fail_if_success have : complexLorentz.V upR := v
  fail_if_success have : complexLorentz.V upR := by with_unfolding_all exact v
  fail_if_success have : complexLorentz.V upL := u
  fail_if_success have : complexLorentz.V upL := by with_unfolding_all exact u
  fail_if_success have : complexLorentz.V downR := w
  fail_if_success have : complexLorentz.V downR := by with_unfolding_all exact w
  fail_if_success have : ℂT[upR] := complexLorentz.pure fun | 0 => v
  fail_if_success have : ℂT[upR] := by with_unfolding_all exact complexLorentz.pure fun | 0 => v
  fail_if_success have : ℂT[downR] := complexLorentz.pure fun | 0 => w
  fail_if_success have : ℂT[downR] := by with_unfolding_all exact complexLorentz.pure fun | 0 => w
  fail_if_success have : ℂT[upR] := t
  fail_if_success have : ℂT[upR] := by with_unfolding_all exact t
  fail_if_success have : ℂT[downR] := s
  fail_if_success have : ℂT[downR] := by with_unfolding_all exact s
  fail_if_success have : Tensor complexLorentz fun _ : Fin 2 => upR := t'
  fail_if_success
    have : Tensor complexLorentz fun _ : Fin 2 => upR := by with_unfolding_all exact t'
  fail_if_success have : Tensor complexLorentz fun _ : Fin 2 => downR := s'
  fail_if_success
    have : Tensor complexLorentz fun _ : Fin 2 => downR := by with_unfolding_all exact s'
  fail_if_success have : complexLorentz.V downL := v
  fail_if_success have : complexLorentz.V downL := by with_unfolding_all exact v
  exact (v, u, w, t, s, t', s')

-- Bare components `Fin 2 → ℂ` are a left-handed spinor at the space of one index and are rejected
-- as a right-handed one, also when all definitions unfold. The spinor types with one index,
-- `Tensor complexLorentz ![upL]` and `Tensor complexLorentz ![upR]`, are rejected for each other.
example (f : Fin 2 → ℂ) (ψ : Tensor complexLorentz ![upL]) (χ : Tensor complexLorentz ![upR]) :
    complexLorentz.V upL × Tensor complexLorentz ![upL] × Tensor complexLorentz ![upR] := by
  fail_if_success have : complexLorentz.V upR := f
  fail_if_success have : complexLorentz.V upR := by with_unfolding_all exact f
  fail_if_success have : Tensor complexLorentz ![upR] := ψ
  fail_if_success have : Tensor complexLorentz ![upR] := by with_unfolding_all exact ψ
  fail_if_success have : Tensor complexLorentz ![upL] := χ
  fail_if_success have : Tensor complexLorentz ![upL] := by with_unfolding_all exact χ
  exact (f, ψ, χ)

/-- The conjugate of a left-handed spinor is the spinor read in the conjugate module, `conjEquiv`,
and the conjugate of a right-handed spinor is its inverse, both by definition. -/
example (v : complexLorentz.V upL) (u : complexLorentz.V upR) :
    (Species.bar v : complexLorentz.V upR) = conjEquiv (k := ℂ) v ∧
      (Species.bar u : complexLorentz.V upL) = (conjEquiv (k := ℂ)).symm u :=
  ⟨rfl, rfl⟩

/-- The conjugate of a left-handed spinor is a right-handed spinor, and conjugating twice gives it
back. -/
example (v : complexLorentz.V upL) : Species.bar (Species.bar v : complexLorentz.V upR) = v := by
  simp

/-- The conjugate of a spinor is rejected at the wrong color and accepted at `upR`. -/
noncomputable example (v : complexLorentz.V upL) : complexLorentz.V upR := by
  fail_if_success have : complexLorentz.V upL := Species.bar v
  fail_if_success have : complexLorentz.V downR := Species.bar v
  exact Species.bar v

/-- The same for a spinor as a tensor with one index. -/
example (ψ : ℂT[upL]) :
    (Tensor.conj (Tensor.conj ψ : ℂT[upR]) : ℂT[upL]) = ψ := by
  simp

/-- `(M ψ)‾ = M̄ ψ̄`: the components of the conjugate of `M ψ` are those of `ψ̄` acted on by
`M̄`. -/
example (M : SL(2, ℂ)) (v : complexLorentz.V upL) :
    (complexLorentz.basis upR).repr (Species.bar (complexLorentz.rep upL M v)) =
      M.1.map star *ᵥ (complexLorentz.basis upR).repr (Species.bar v) := by
  rw [Species.bar_rep, basis_repr_rep]
  rfl

/-- `(M ψ)‾ = M ψ̄` for a spinor as a tensor with one index. -/
example (M : SL(2, ℂ)) (ψ : ℂT[upL]) :
    (Tensor.conj (M • ψ) : ℂT[upR]) = M • (Tensor.conj ψ : ℂT[upR]) :=
  Tensor.conj_smul _ M ψ

end complexLorentz

end Tensor
