/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Species
/-!

## Modules associated with complex Lorentz vectors

We define the modules underlying complex Lorentz vectors.
These definitions are preludes to the definitions of
`Lorentz.complexContr` and `Lorentz.complexCo`.

-/

@[expose] public section

namespace Lorentz

noncomputable section
open Matrix
open MatrixGroups
open Complex

open Tensor in
/-- The upper complex Lorentz vectors, the complex Lorentz tensors with one upper vector
index. -/
abbrev ComplexVector := Tensor complexLorentz ![Tensor.complexLorentz.up]

namespace ComplexVector

open Tensor Tensor.complexLorentz

/-- The linear equivalence between `ComplexVector` and `(Fin 1 ⊕ Fin 3 → ℂ)`, its components. -/
def toFin13ℂEquiv : ComplexVector ≃ₗ[ℂ] (Fin 1 ⊕ Fin 3 → ℂ) := toComponents up

/-- The underlying element of `Fin 1 ⊕ Fin 3 → ℂ` of a element in `ComplexVector` defined
  through the linear equivalence `toFin13ℂEquiv`. -/
abbrev toFin13ℂ (ψ : ComplexVector) := toFin13ℂEquiv ψ

/-- The components of the vector, `Fin 1 ⊕ Fin 3 → ℂ`. -/
def val (ψ : ComplexVector) : Fin 1 ⊕ Fin 3 → ℂ := toFin13ℂEquiv ψ

@[simp]
lemma toFin13ℂEquiv_apply (ψ : ComplexVector) : toFin13ℂEquiv ψ = ψ.val := rfl

@[simp]
lemma val_toFin13ℂEquiv_symm (f : Fin 1 ⊕ Fin 3 → ℂ) :
    (toFin13ℂEquiv.symm f : ComplexVector).val = f :=
  toFin13ℂEquiv.apply_symm_apply f

@[ext]
lemma ext (ψ ψ' : ComplexVector) (h : ψ.val = ψ'.val) : ψ = ψ' := toFin13ℂEquiv.injective h

@[simp]
lemma val_add (ψ ψ' : ComplexVector) : (ψ + ψ').val = ψ.val + ψ'.val := map_add toFin13ℂEquiv ψ ψ'

@[simp]
lemma val_smul (r : ℂ) (ψ : ComplexVector) : (r • ψ).val = r • ψ.val := map_smul toFin13ℂEquiv r ψ

/-- The representation of the Lorentz group on `ComplexVector`, `v ↦ Λ *ᵥ v` on components. -/
def lorentzGroupRep : Representation ℂ (LorentzGroup 3) ComplexVector where
  toFun M := {
      toFun := fun v => toFin13ℂEquiv.symm (LorentzGroup.toComplex M *ᵥ v.toFin13ℂ),
      map_add' := by
        intro ψ ψ'
        simp [mulVec_add]
      map_smul' := by
        intro r ψ
        simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' M N := by
    ext i
    simp []

/-- The representation of `SL(2, ℂ)` on `ComplexVector`, the action on tensors. It is the
representation of the Lorentz group through `SL2C.toLorentzGroup` (`val_SL2CRep`). -/
def SL2CRep : Representation ℂ SL(2, ℂ) ComplexVector := complexLorentz.tensorRep ![up]

@[simp]
lemma val_SL2CRep (M : SL(2, ℂ)) (v : ComplexVector) :
    (SL2CRep M v).val = LorentzGroup.toComplex (SL2C.toLorentzGroup M) *ᵥ v.val :=
  (toComponents_smul up M v).trans (by rfl)

end ComplexVector

open Tensor in
/-- The lower complex Lorentz vectors, the complex Lorentz tensors with one lower vector
index. -/
abbrev ComplexCoVector := Tensor complexLorentz ![Tensor.complexLorentz.down]

namespace ComplexCoVector

open Tensor Tensor.complexLorentz

/-- The linear equivalence between `ComplexCoVector` and `(Fin 1 ⊕ Fin 3 → ℂ)`, its components. -/
def toFin13ℂEquiv : ComplexCoVector ≃ₗ[ℂ] (Fin 1 ⊕ Fin 3 → ℂ) := toComponents down

/-- The underlying element of `Fin 1 ⊕ Fin 3 → ℂ` of a element in `ComplexCoVector` defined
  through the linear equivalence `toFin13ℂEquiv`. -/
abbrev toFin13ℂ (ψ : ComplexCoVector) := toFin13ℂEquiv ψ

/-- The components of the vector, `Fin 1 ⊕ Fin 3 → ℂ`. -/
def val (ψ : ComplexCoVector) : Fin 1 ⊕ Fin 3 → ℂ := toFin13ℂEquiv ψ

@[simp]
lemma toFin13ℂEquiv_apply (ψ : ComplexCoVector) : toFin13ℂEquiv ψ = ψ.val := rfl

@[simp]
lemma val_toFin13ℂEquiv_symm (f : Fin 1 ⊕ Fin 3 → ℂ) :
    (toFin13ℂEquiv.symm f : ComplexCoVector).val = f :=
  toFin13ℂEquiv.apply_symm_apply f

@[ext]
lemma ext (ψ ψ' : ComplexCoVector) (h : ψ.val = ψ'.val) : ψ = ψ' := toFin13ℂEquiv.injective h

@[simp]
lemma val_add (ψ ψ' : ComplexCoVector) : (ψ + ψ').val = ψ.val + ψ'.val := map_add toFin13ℂEquiv ψ ψ'

@[simp]
lemma val_smul (r : ℂ) (ψ : ComplexCoVector) : (r • ψ).val = r • ψ.val := map_smul toFin13ℂEquiv r ψ

/-- The representation of the Lorentz group on `ComplexCoVector`, `v ↦ (Λ⁻¹)ᵀ *ᵥ v` on
components. -/
def lorentzGroupRep : Representation ℂ (LorentzGroup 3) ComplexCoVector where
  toFun M := {
      toFun := fun v => toFin13ℂEquiv.symm ((LorentzGroup.toComplex M)⁻¹ᵀ *ᵥ v.toFin13ℂ),
      map_add' := by
        intro ψ ψ'
        simp [mulVec_add]
      map_smul' := by
        intro r ψ
        simp only [toFin13ℂ, toFin13ℂEquiv_apply, mulVec_smul, map_smul,
          RingHom.id_apply]}
  map_one' := LinearMap.ext fun ψ => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_one, inv_one, transpose_one, one_mulVec,
      toFin13ℂ, LinearEquiv.symm_apply_apply, one_apply_eq_self]
  map_mul' M N := LinearMap.ext fun ψ => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, Matrix.mul_inv_rev, transpose_mul,
      toFin13ℂ, LinearEquiv.apply_symm_apply, mul_apply_eq_comp, mulVec_mulVec]

/-- The representation of `SL(2, ℂ)` on `ComplexCoVector`, the action on tensors. It is the
representation of the Lorentz group through `SL2C.toLorentzGroup` (`val_SL2CRep`). -/
def SL2CRep : Representation ℂ SL(2, ℂ) ComplexCoVector := complexLorentz.tensorRep ![down]

@[simp]
lemma val_SL2CRep (M : SL(2, ℂ)) (v : ComplexCoVector) :
    (SL2CRep M v).val = (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ v.val :=
  (toComponents_smul down M v).trans (by rw [LorentzGroup.toComplex_inv, ← map_inv]; rfl)

end ComplexCoVector

end
end Lorentz
