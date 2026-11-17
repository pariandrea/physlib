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

Complex Lorentz tensors have three kinds of index. The left-handed kind `left`, as in `ψ_α`, and
the right-handed kind `right`, as in `ψ̄_α̇`, have the labels `Fin 2`. The vector kind `vec`, as in
`v^μ`, has the labels `Fin 1 ⊕ Fin 3`, so the space dimension is fixed at `d = 3`. Conjugation
`star` swaps `left` and `right` and fixes `vec`. With the two variances this gives six colors,
`upL`, `downL`, `upR`, `downR`, `up` and `down`. Under `open scoped Tensor.complexLorentz`,
`ℂT[upL, downR]` is the space of the tensors `T^α_β̇`.

The space of an index of color `c` is `IndexSpace c`, the components `Idx c.kind → ℂ`. The
tensors of the six colors are six different types, since they are built on `Species.colored`. `M ∈ SL(2, ℂ)` acts on components by
`repMatrix c M`: `M` on `upL`, its conjugate `M̄` on `upR`, the Lorentz transformation of `M` on
`up`, and `(U M⁻¹)ᵀ` on a lower color with upper matrix `U`. An index contracts with its dual by the
coordinate pairing, which is `SL(2, ℂ)`-invariant.
Conjugation conjugates the components, and a label of a kind is the same label of its
conjugate (`idxBar`), a conjugation of the species (`HasConjugation.ofBasis`). The
right-handed representation is the conjugate of the left-handed one, `M ↦ M̄`, and the vector
representation is real, so this conjugation commutes with `SL(2, ℂ)`
(`IsEquivariantConjugation`).

The invariant form is `ε` at the Weyl colors and `η` at the vector colors. The form `ε` is
antisymmetric and `η` symmetric (`IsAntisymmetricForm`, `IsSymmetricForm`). The form `ε^αβ` has
the matrix `!![0, 1; -1, 0]` and `ε_αβ` the matrix `!![0, -1; 1, 0]`, so `ε^12 = 1` and
`ε_12 = -1`. Lowering contracts the second index of the form, `ψ_α = ε_αβ ψ^β`, as in Wess and
Bagger. The forms are written `εL`, `εL'`, `εR`, `εR'`, `η` and `η'`, and the deltas `δL`, `δL'`,
`δR`, `δR'`, `δ` and `δ'`. Their components are stated through `tensorBasis`, and the
antisymmetry of `ε` and the symmetry of `η` are stated in index notation.

A Weyl spinor or a complex Lorentz vector is a tensor with one index, `Tensor complexLorentz ![c]`,
with components `toComponents c`. `Fermion.LeftHandedWeyl` and the other spinor and vector types are
these tensors, so a spinor `ψ` enters index notation directly, as in `{ψ | α ⊗ φ | α}ᵀ`.

## ii. Key results

- `complexLorentz` : the species of complex Lorentz tensors.
- the instances `complexLorentz.HasForm κ` : the forms `ε` and `η`, with `IsAntisymmetricForm`
  at the Weyl kinds and `IsSymmetricForm` at the vector kind.
- the instances `complexLorentz.HasConjugation` and `complexLorentz.IsEquivariantConjugation` :
  conjugation swaps left- and right-handed indices and commutes with `SL(2, ℂ)`,
  and `complexLorentz.tensorBasis_repr_conj` : the components of a conjugate tensor are the
  conjugates of the components.
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

- A. The species
- B. The invariant forms
- C. Conjugation
- D. Components of the forms
- E. Symmetry of the forms
- F. Tensors with one index
- G. Examples

## iv. References

- J. Wess and J. Bagger, Supersymmetry and Supergravity, Appendix A.

-/

@[expose] public section

open TensorProduct Lorentz MatrixGroups Matrix

namespace Fermion

open Matrix MatrixGroups

/-!

## The matrix `ε` of the Weyl forms

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

## A. The species

-/

namespace complexLorentz

/-- The kinds of complex Lorentz index. -/
inductive Kind
  /-- The left-handed kind, as the index of `ψ_α`. -/
  | left
  /-- The right-handed kind, as the index of `ψ̄_α̇`. -/
  | right
  /-- The vector kind, its own conjugate. -/
  | vec
deriving DecidableEq

export Kind (left right vec)

/-- Conjugation swaps the left- and right-handed kinds and fixes the vector kind. -/
instance : InvolutiveStar Kind where
  star
    | left => right
    | right => left
    | vec => vec
  star_involutive κ := by cases κ <;> rfl

/-- The basis labels of a kind, `Fin 2` for Weyl spinors and `Fin 1 ⊕ Fin 3` for vectors. -/
abbrev Idx : Kind → Type
  | left | right => Fin 2
  | vec => Fin 1 ⊕ Fin 3

instance : ∀ κ, Fintype (Idx κ)
  | left | right => inferInstanceAs (Fintype (Fin 2))
  | vec => inferInstanceAs (Fintype (Fin 1 ⊕ Fin 3))

instance : ∀ κ, DecidableEq (Idx κ)
  | left | right => inferInstanceAs (DecidableEq (Fin 2))
  | vec => inferInstanceAs (DecidableEq (Fin 1 ⊕ Fin 3))

/-- The components `Idx c.kind → ℂ` of a vector at a complex Lorentz index of color `c`: a Weyl
spinor at the Weyl colors and a complex Lorentz vector at the vector colors. Colors of the same
kind have the same type. The tensors keep them apart, since they are built on `Species.colored`. -/
abbrev IndexSpace (c : Color Kind) : Type := Idx c.kind → ℂ

/-- The basis of an index: the vector with the component `1` at `μ`. -/
noncomputable abbrev IndexSpace.basis (c : Color Kind) :
    Module.Basis (Idx c.kind) ℂ (IndexSpace c) :=
  Pi.basisFun ℂ _

/-- The matrix of `M` at an upper index of each kind: `M` left-handed, its conjugate `M̄`
right-handed, and the Lorentz transformation of `M`, as a complex matrix, at the vector kind. -/
noncomputable def upMatrix : (κ : Kind) → SL(2, ℂ) →* Matrix (Idx κ) (Idx κ) ℂ
  | left => { toFun M := M.1, map_one' := rfl, map_mul' _ _ := rfl }
  | right => (starRingEnd ℂ).mapMatrix.toMonoidHom.comp
      { toFun M := M.1, map_one' := rfl, map_mul' _ _ := rfl }
  | vec => LorentzGroup.toComplex.comp SL2C.toLorentzGroup

/-- The matrix of `M` at a lower index, `(U M⁻¹)ᵀ` for the matrix `U M` at the upper index. -/
noncomputable def downMatrix (κ : Kind) : SL(2, ℂ) →* Matrix (Idx κ) (Idx κ) ℂ where
  toFun M := (upMatrix κ M⁻¹)ᵀ
  map_one' := by simp
  map_mul' M N := by simp [Matrix.transpose_mul]

/-- The matrix of `M` at a color. -/
noncomputable def repMatrix : (c : Color Kind) → SL(2, ℂ) →* Matrix (Idx c.kind) (Idx c.kind) ℂ
  | ⟨κ, .up⟩ => upMatrix κ
  | ⟨κ, .down⟩ => downMatrix κ

/-- The representation of `SL(2, ℂ)` on an index, by the matrix `repMatrix c M` on components. -/
noncomputable def indexRep (c : Color Kind) : Representation ℂ SL(2, ℂ) (IndexSpace c) :=
  (Matrix.toLinAlgEquiv (IndexSpace.basis c) : Matrix _ _ ℂ →* Module.End ℂ (IndexSpace c)).comp
    (repMatrix c)

lemma indexRep_toMatrix (c : Color Kind) (M : SL(2, ℂ)) :
    LinearMap.toMatrix (IndexSpace.basis c) (IndexSpace.basis c) (indexRep c M) =
      repMatrix c M :=
  (LinearEquiv.eq_symm_apply (LinearMap.toMatrix _ _)).mp rfl

/-- On components the action is `repMatrix c M *ᵥ x`. -/
lemma components_indexRep (c : Color Kind) (M : SL(2, ℂ)) (x : IndexSpace c) :
    indexRep c M x = repMatrix c M *ᵥ x := by
  funext μ
  rw [← Pi.basisFun_repr ℂ _ (indexRep c M x) μ, ← LinearMap.toMatrix_mulVec_repr
    (IndexSpace.basis c) (IndexSpace.basis c), indexRep_toMatrix]
  simp [Matrix.mulVec, dotProduct]

/-- The components of `M` applied to a basis vector are a column of `repMatrix c M`. -/
lemma basis_repr_indexRep_basis (c : Color Kind) (M : SL(2, ℂ)) (μ ν : Idx c.kind) :
    (IndexSpace.basis c).repr (indexRep c M (IndexSpace.basis c μ)) ν = repMatrix c M ν μ := by
  rw [← LinearMap.toMatrix_apply, indexRep_toMatrix]

/-- The coordinate pairing of a color and its dual is invariant under `SL(2, ℂ)`. At a lower color
it is the pairing at the upper color with its factors swapped (`Species.invariant_of_up`). -/
lemma coordPairing_rep : ∀ (c : Color Kind) (g : SL(2, ℂ)) (x : IndexSpace c)
    (y : IndexSpace c.dual),
    (IndexSpace.basis c).coordPairing (IndexSpace.basis c.dual)
        (indexRep c g x ⊗ₜ indexRep c.dual g y) =
      (IndexSpace.basis c).coordPairing (IndexSpace.basis c.dual) (x ⊗ₜ y) :=
  Species.invariant_of_up indexRep IndexSpace.basis fun κ g x y => by
    simp only [Module.Basis.coordPairing_tmul, Module.Basis.equivFun_apply]
    change (upMatrix κ g *ᵥ x) ⬝ᵥ ((upMatrix κ g⁻¹)ᵀ *ᵥ y) = x ⬝ᵥ y
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, ← map_mul,
      inv_mul_cancel, map_one, Matrix.one_mulVec]

end complexLorentz

open complexLorentz in
/-- Complex Lorentz tensors: Weyl spinors and complex Lorentz vectors with the action of
`SL(2, ℂ)`, on the spaces, representations and bases of `Fermion` and `Lorentz`. -/
noncomputable def complexLorentz : Species ℂ SL(2, ℂ) Kind Idx where
  V := IndexSpace
  rep := indexRep
  basis := IndexSpace.basis
  invariant := coordPairing_rep

namespace complexLorentz

/-- An upper left-handed index, `ψ^α`. -/
abbrev upL : Color Kind := ⟨left, .up⟩

/-- A lower left-handed index, `ψ_α`. -/
abbrev downL : Color Kind := ⟨left, .down⟩

/-- An upper right-handed index, `ψ̄^α̇`. -/
abbrev upR : Color Kind := ⟨right, .up⟩

/-- A lower right-handed index, `ψ̄_α̇`. -/
abbrev downR : Color Kind := ⟨right, .down⟩

/-- An upper vector index, `v^μ`. -/
abbrev up : Color Kind := ⟨vec, .up⟩

/-- A lower vector index, `w_μ`. -/
abbrev down : Color Kind := ⟨vec, .down⟩

/-- Conjugation swaps `upL` and `upR` and fixes `up`. -/
example : upL.bar = upR ∧ downR.bar = downL ∧ up.bar = up := ⟨rfl, rfl, rfl⟩

/-- The complex Lorentz tensors with the colors listed, as `ℂT[upL, downR]` for `T^α_β̇`. The colors
are read in the namespace `complexLorentz`. The notation is active under
`open scoped Tensor.complexLorentz`. -/
scoped syntax (name := complexLorentzSyntax) "ℂT[" term,* "]" : term

macro_rules (kind := complexLorentzSyntax)
  | `(ℂT[$cs,*]) => `(Tensor Tensor.complexLorentz (open Tensor.complexLorentz in ![$cs,*]))

/-- `ℂT[upL, downR]` is the space of tensors `T^α_β̇`. -/
example : ℂT[upL, downR] = Tensor complexLorentz ![upL, downR] := rfl

end complexLorentz

/-!

## B. The invariant forms

-/

namespace complexLorentz

/-- The entries of the form at each color, `ε^αβ = !![0, 1; -1, 0]` at the upper Weyl colors,
`ε_αβ = !![0, -1; 1, 0]` at the lower ones, and `η` at the vector colors. -/
noncomputable def formEntries : (c : Color Kind) → Idx c.kind → Idx c.kind → ℂ
  | ⟨left, .up⟩ => metricRaw
  | ⟨left, .down⟩ => -metricRaw
  | ⟨right, .up⟩ => metricRaw
  | ⟨right, .down⟩ => -metricRaw
  | ⟨vec, _⟩ => fun μ ν => minkowskiMatrix μ ν

/-- The invariant form at a color, the tensor with the components `formEntries c`: `ε` at the Weyl
colors and `η` at the vector colors. -/
noncomputable def form (c : Color Kind) : complexLorentz.V c ⊗[ℂ] complexLorentz.V c :=
  ((IndexSpace.basis c).tensorProductToMatrix (IndexSpace.basis c)).symm (Matrix.of (formEntries c))

/-- The coordinates of the form in Mathlib's product basis are `formEntries`: each form is defined
by its matrix. -/
lemma basis_tensorProduct_repr_form (c : Color Kind) (μ ν : Idx c.kind) :
    ((complexLorentz.basis c).tensorProduct (complexLorentz.basis c)).repr (form c) (μ, ν) =
      formEntries c μ ν :=
  congrFun₂ (((IndexSpace.basis c).tensorProductToMatrix (IndexSpace.basis c)).apply_symm_apply
    (Matrix.of (formEntries c))) μ ν

/-- The upper forms are invariant on matrices, `U ε Uᵀ = ε` and `Λ η Λᵀ = η`. -/
lemma upMatrix_mul_formEntries_mul_transpose : ∀ (κ : Kind) (g : SL(2, ℂ)),
    upMatrix κ g * Matrix.of (formEntries ⟨κ, .up⟩) * (upMatrix κ g)ᵀ =
      Matrix.of (formEntries ⟨κ, .up⟩)
  | left, g => by
    change g.1 * metricRaw * g.1ᵀ = metricRaw
    rw [comm_metricRaw, Matrix.mul_assoc, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv _ (by simp), Matrix.transpose_one, Matrix.mul_one]
  | right, g => by
    change g.1.map star * metricRaw * g.1ᴴ = metricRaw
    rw [star_comm_metricRaw, Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ (by simp),
      Matrix.conjTranspose_one, Matrix.mul_one]
  | vec, g => LorentzGroup.toComplex_mul_minkowskiMatrix_mul_transpose _

/-- A form invariant under `U` has its inverse invariant under the inverse transpose `V` of `U`,
`Vᵀ E' V = E'`. -/
lemma transpose_mul_mul_of_mul_mul_transpose {n : Type} [Fintype n] [DecidableEq n]
    {U V E E' : Matrix n n ℂ} (hUV : U * V = 1) (hVU : V * U = 1) (hE : U * E * Uᵀ = E)
    (hEE' : E * E' = 1) (hE'E : E' * E = 1) : Vᵀ * E' * V = E' :=
  calc Vᵀ * E' * V = Vᵀ * E' * V * (U * E * Uᵀ * E') := by rw [hE, hEE', Matrix.mul_one]
    _ = Vᵀ * E' * (V * U) * E * Uᵀ * E' := by simp only [Matrix.mul_assoc]
    _ = Vᵀ * (E' * E) * Uᵀ * E' := by rw [hVU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (U * V)ᵀ * E' := by rw [hE'E, Matrix.mul_one, Matrix.transpose_mul]
    _ = E' := by rw [hUV, Matrix.transpose_one, Matrix.one_mul]

/-- The matrices of the forms at `c.dual` and at `c` are inverse, `(-ε) ε = 1` and `η η = 1`. -/
lemma formEntries_dual_mul : ∀ c : Color Kind,
    Matrix.of (formEntries c.dual) * Matrix.of (formEntries c) = 1
  | ⟨left, .up⟩ | ⟨right, .up⟩ => neg_metricRaw_mul_metricRaw
  | ⟨left, .down⟩ | ⟨right, .down⟩ => metricRaw_mul_neg_metricRaw
  | ⟨vec, _⟩ => show (@minkowskiMatrix 3).map Complex.ofRealHom *
      (@minkowskiMatrix 3).map Complex.ofRealHom = 1 by
    rw [← Matrix.map_mul, minkowskiMatrix.sq, Matrix.map_one _ (map_zero _) (map_one _)]

/-- The forms at `c` and at `c.dual` are inverse to each other. -/
lemma form_inverse (c : Color Kind) :
    complexLorentz.toLin (form c) ∘ₗ complexLorentz.toLin (form c.dual) = LinearMap.id :=
  Module.Basis.coordTensorHomEquiv_comp_of_mul_eq_one _ _ _ _ <| by
    simpa only [basis_tensorProduct_repr_form] using formEntries_dual_mul c

/-- The forms are invariant under `SL(2, ℂ)`. -/
lemma form_invariant (c : Color Kind) (g : SL(2, ℂ)) :
    TensorProduct.map (complexLorentz.rep c g) (complexLorentz.rep c g) (form c) = form c := by
  let e := (IndexSpace.basis c).tensorProductToMatrix (IndexSpace.basis c)
  refine e.injective ((Module.Basis.tensorProductToMatrix_map _ _ _ _ _).trans ?_)
  change LinearMap.toMatrix _ _ (indexRep c g) * e (form c) *
    (LinearMap.toMatrix _ _ (indexRep c g))ᵀ = e (form c)
  rw [indexRep_toMatrix, show e (form c) = Matrix.of (formEntries c) from e.apply_symm_apply _]
  match c with
  | ⟨κ, .up⟩ => exact upMatrix_mul_formEntries_mul_transpose κ g
  | ⟨κ, .down⟩ =>
    change (upMatrix κ g⁻¹)ᵀ * _ * (upMatrix κ g⁻¹)ᵀᵀ = _
    rw [Matrix.transpose_transpose]
    exact transpose_mul_mul_of_mul_mul_transpose (U := upMatrix κ g)
      (by rw [← map_mul, mul_inv_cancel, map_one]) (by rw [← map_mul, inv_mul_cancel, map_one])
      (upMatrix_mul_formEntries_mul_transpose κ g) (formEntries_dual_mul ⟨κ, .down⟩)
      (formEntries_dual_mul ⟨κ, .up⟩)

end complexLorentz

/-- The invariant forms, `ε` at the Weyl kinds and `η` at the vector kind. -/
noncomputable instance (κ : complexLorentz.Kind) : complexLorentz.HasForm κ where
  formAt v := complexLorentz.form ⟨κ, v⟩
  formAt_invariant v := complexLorentz.form_invariant ⟨κ, v⟩
  formAt_inverse v := complexLorentz.form_inverse ⟨κ, v⟩

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

## C. Conjugation

-/

namespace complexLorentz

/-- A label of a kind read as a label of its conjugate `κ'`, the same element of `Fin 2` or of
`Fin 1 ⊕ Fin 3`. -/
def idxBar {κ κ' : Kind} (h : κ' = star κ) : Idx κ ≃ Idx κ' :=
  match κ, κ', h with
  | left, _, rfl | right, _, rfl | vec, _, rfl => Equiv.refl _

/-- Reading a label as a label of the conjugate kind and back gives the label. -/
lemma idxBar_idxBar {κ κ' : Kind} (h : κ' = star κ) (h' : κ = star κ') (μ : Idx κ) :
    idxBar h' (idxBar h μ) = μ := by
  subst h
  cases κ <;> rfl

/-- Conjugation swaps left- and right-handed indices and fixes vector indices, conjugating the
components. -/
noncomputable instance : complexLorentz.HasConjugation :=
  .ofBasis complexLorentz ⟨idxBar, idxBar_idxBar⟩

/-- Conjugation commutes with the action of `SL(2, ℂ)`. The right-handed representation is the
conjugate of the left-handed one, and the vector representation is real. -/
instance : complexLorentz.IsEquivariantConjugation :=
  Species.HasConjugation.isEquivariantConjugation_ofBasis ⟨idxBar, idxBar_idxBar⟩ fun κ g μ ν => by
    refine (basis_repr_indexRep_basis ⟨star κ, .up⟩ g _ _).trans
      (Eq.trans ?_ (congrArg star (basis_repr_indexRep_basis ⟨κ, .up⟩ g μ ν)).symm)
    match κ with
    | left => rfl
    | right => exact (star_star _).symm
    | vec => exact (LorentzGroup.star_toComplex_apply _ _ _).symm

/-- The components of the conjugate of a tensor are the conjugates of its components, at the same
labels read through `idxBar`. -/
lemma tensorBasis_repr_conj {ι : Type} [Fintype ι] {c c' : ι → Color Kind}
    (h : ∀ i, c' i = (c i).bar) (t : Tensor complexLorentz c) (μ : Π i, Idx (c' i).kind) :
    (complexLorentz.tensorBasis c').repr (Tensor.conj h t) μ =
      star ((complexLorentz.tensorBasis c).repr t
        fun i => (idxBar (congrArg Color.kind (h i))).symm (μ i)) :=
  Tensor.tensorBasis_repr_conj_of_basis h _
    (fun i => Species.HasConjugation.ofBasis_conjEquiv_basis _ (h i)) t μ

end complexLorentz

/-!

## D. Components of the forms

-/

namespace complexLorentz

/-- The components of the form at any color are `formEntries`. -/
lemma formMatrix_apply (c : Color Kind) (μ ν : Idx c.kind) :
    Species.formMatrix complexLorentz c μ ν = formEntries c μ ν :=
  basis_tensorProduct_repr_form c μ ν

/-- The components of the form tensor at any color are `formEntries`, at the pair of labels
`(μ 0, μ 1)`. The labels `μ` form a dependent family, since the basis labels of an index depend on
its color. -/
lemma tensorBasis_repr_formTensor (c : Color Kind) (μ : Π i, Idx (![c, c] i).kind) :
    (complexLorentz.tensorBasis ![c, c]).repr (complexLorentz.formTensor c) μ =
      formEntries c (μ 0) (μ 1) :=
  (Species.tensorBasis_repr_formTensor c μ).trans (formMatrix_apply c _ _)

/-- The components of `η^μν` and `η_μν` are the Minkowski matrix `diag(1, -1, -1, -1)`. -/
lemma tensorBasis_repr_formTensor_vec (v : Variance)
    (μ : Π i, Idx (![⟨vec, v⟩, ⟨vec, v⟩] i : Color Kind).kind) :
    (complexLorentz.tensorBasis ![⟨vec, v⟩, ⟨vec, v⟩]).repr (complexLorentz.formTensor ⟨vec, v⟩)
      μ = minkowskiMatrix (μ 0) (μ 1) :=
  tensorBasis_repr_formTensor ⟨vec, v⟩ μ

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

## E. Symmetry of the forms

-/

namespace complexLorentz

/-- The Minkowski metric `η` on the vector kind is symmetric, `η^νμ = η^μν`. -/
instance : complexLorentz.IsSymmetricForm vec where
  comm_form v := (Species.comm_form_eq_smul _ 1 fun μ ν => by
    rw [formMatrix_apply, formMatrix_apply, one_mul]
    exact congrArg Complex.ofReal (congrFun (congrFun minkowskiMatrix.eq_transpose μ) ν)).trans
    (one_smul _ _)

/-- The entries of `ε` are antisymmetric, `ε^βα = -ε^αβ`. -/
lemma formEntries_antisymm : ∀ c : Color Kind, c.kind ≠ vec → ∀ μ ν,
    formEntries c ν μ = -1 * formEntries c μ ν
  | ⟨left, .up⟩, _ | ⟨left, .down⟩, _ | ⟨right, .up⟩, _ | ⟨right, .down⟩, _ => fun μ ν => by
    have h : metricRaw ν μ = -metricRaw μ ν := congrFun₂ transpose_metricRaw μ ν
    simp [formEntries, h]
  | ⟨vec, _⟩, h => absurd rfl h

/-- The form `ε` is antisymmetric at the Weyl colors. -/
lemma comm_form_weyl (c : Color Kind) (h : c.kind ≠ vec) :
    TensorProduct.comm ℂ _ _ (Species.form (S := complexLorentz) c) = -Species.form c :=
  (Species.comm_form_eq_smul c (-1) fun μ ν => by
    rw [formMatrix_apply, formMatrix_apply]
    exact formEntries_antisymm c h μ ν).trans (neg_one_smul _ _)

/-- The form `ε` on the left-handed Weyl kind is antisymmetric. -/
instance : complexLorentz.IsAntisymmetricForm left where
  comm_form v := comm_form_weyl ⟨left, v⟩ nofun

/-- The form `ε` on the right-handed Weyl kind is antisymmetric. -/
instance : complexLorentz.IsAntisymmetricForm right where
  comm_form v := comm_form_weyl ⟨right, v⟩ nofun

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
lemma deltaTensor_swap (c : Color Kind) :
    {complexLorentz.deltaTensor c | μ ν = complexLorentz.deltaTensor c.dual | ν μ}ᵀ := by
  tensor_regroup

end complexLorentz

/-!

## F. Tensors with one index

A Weyl spinor or a complex Lorentz vector is a tensor with one index, `Tensor complexLorentz ![c]`.
Its components are `toComponents c`, and the group acts on them by the matrix `repMatrix c M`.

-/

namespace complexLorentz

/-- The components of a tensor with one index of color `c`, as `ψ^α` or `v^μ`. -/
noncomputable def toComponents (c : Color Kind) :
    Tensor complexLorentz ![c] ≃ₗ[ℂ] (Idx c.kind → ℂ) :=
  (complexLorentz.oneIndexEquiv c).toLinearEquiv.symm ≪≫ₗ
    ((complexLorentz.coloredEquiv c).toLinearEquiv).symm

/-- The basis of the tensors with one index, the tensor with the component `1` at `μ`. -/
noncomputable def oneIndexBasis (c : Color Kind) :
    Module.Basis (Idx c.kind) ℂ (Tensor complexLorentz ![c]) :=
  (Pi.basisFun ℂ _).map (toComponents c).symm

@[simp]
lemma oneIndexBasis_repr (c : Color Kind) (t : Tensor complexLorentz ![c]) (μ : Idx c.kind) :
    (oneIndexBasis c).repr t μ = toComponents c t μ := by
  simp [oneIndexBasis]

@[simp]
lemma toComponents_oneIndexBasis (c : Color Kind) (μ : Idx c.kind) :
    toComponents c (oneIndexBasis c μ) = Pi.single μ 1 := by
  simp [oneIndexBasis]

/-- The components of a tensor with one index in `tensorBasis` are its components, at the label of
its one index. -/
lemma tensorBasis_repr_oneIndex (c : Color Kind) (t : Tensor complexLorentz ![c])
    (μ : Π i, Idx (![c] i).kind) :
    (complexLorentz.tensorBasis ![c]).repr t μ = toComponents c t (μ 0) := by
  conv_lhs => rw [← (complexLorentz.oneIndexEquiv c).apply_symm_apply t]
  exact Species.tensorBasis_repr_oneIndexEquiv c _ μ

/-- The group acts on the components by `repMatrix c M`. -/
lemma toComponents_smul (c : Color Kind) (M : SL(2, ℂ)) (t : Tensor complexLorentz ![c]) :
    toComponents c (M • t) = repMatrix c M *ᵥ toComponents c t := by
  have h := Representation.IntertwiningMap.isIntertwining _ _
    (complexLorentz.oneIndexEquiv c).symm.toIntertwiningMap M t
  exact (congrArg Species.ColoredSpace.toV h).trans (components_indexRep c M _)

end complexLorentz

/-!

## G. Examples

-/

namespace complexLorentz

/-- `ε^αβ ε_βγ = δ^α_γ`, by `tensor_regroup` through `contr_formTensor_formTensor`. -/
example : {εL | α β ⊗ εL' | β γ = δL | α γ}ᵀ := by
  tensor_regroup

/-- `g^αβ g_βγ = δ^α_γ` at every color: `ε`, `ε'` and `η` with their duals. -/
example (c : Color Kind) : {complexLorentz.formTensor c | α β ⊗
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
example : Tensor.conj (fun i => by fin_cases i <;> rfl) εL = εR := by
  refine (complexLorentz.tensorBasis _).repr.injective (Finsupp.ext fun μ => ?_)
  rw [tensorBasis_repr_conj, tensorBasis_repr_formTensor upL, tensorBasis_repr_formTensor upR]
  -- The labels are `idxBar` along `rfl` of `μ 0` and `μ 1`, the identity.
  have h (a b : Fin 2) : star (metricRaw a b) = metricRaw a b := by
    fin_cases a <;> fin_cases b <;> simp [metricRaw]
  exact h _ _

end complexLorentz

end Tensor
