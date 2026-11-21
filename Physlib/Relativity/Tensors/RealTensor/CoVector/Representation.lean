/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Physlib.Relativity.LorentzGroup.Basic
public import Physlib.Relativity.Tensors.RealTensor.CoVector.Basic
/-!

# Representation of the Lorentz group on Lorentz vectors

In this module we define the representation of the Lorentz group on Lorentz covectors.
This does not define the MulAction on `Lorentz.CoVector`, which is induced
by its tensor structure.

-/

@[expose] public section


open Module Matrix MatrixGroups Complex TensorProduct

noncomputable section

namespace Lorentz

namespace CoVector
attribute [-simp] Fintype.sum_sum_type

/-- The representation of the Lorentz group on Lorentz covectors, the action on tensors with one
lower index. -/
def rep {d : ℕ} : Representation ℝ (LorentzGroup d) (CoVector d) :=
  (Tensor.realLorentz d).tensorRep _

/-!

## Properties of the representation.

-/

lemma rep_apply_eq_mulVec (d : ℕ) (Λ : LorentzGroup d) (v : CoVector d) :
    ⇑(rep Λ v) = (LorentzGroup.transpose Λ⁻¹) *ᵥ ⇑v := by
  rw [toCoord_eq_equivFun, toCoord_eq_equivFun]
  have h := Representation.IntertwiningMap.isIntertwining _ _
    ((Tensor.realLorentz d).oneIndexEquiv Tensor.realLorentz.down).symm.toIntertwiningMap Λ v
  change ((Tensor.realLorentz d).basis Tensor.realLorentz.down).equivFun
    (((Tensor.realLorentz d).oneIndexEquiv Tensor.realLorentz.down).symm (Λ • v)) = _
  rw [show ((Tensor.realLorentz d).oneIndexEquiv Tensor.realLorentz.down).symm (Λ • v) = _ from h,
    Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    ← LinearMap.toMatrix_mulVec_repr ((Tensor.realLorentz d).basis Tensor.realLorentz.down)
      ((Tensor.realLorentz d).basis Tensor.realLorentz.down), Tensor.realLorentz.rep_toMatrix_down]
  rw [LorentzGroup.transpose_val, LorentzGroup.coe_inv]
  rfl

lemma rep_apply_eq_sum (d : ℕ) (Λ : LorentzGroup d) (v : CoVector d) (k : Fin 1 ⊕ Fin d) :
    rep Λ v k = ∑ j, (Λ⁻¹).1 j k • v j := by
  rw [rep_apply_eq_mulVec]; rfl

/-- The Lorentz group acts on covectors as on tensors with one lower index, `Λ • ω = rep Λ ω`. The
priority is above the generic action `TensorSpecies.Tensorial.smulAction` of the older tensor
library, so that `Λ • ω` is this action. -/
instance (priority := high + 1) {d : ℕ} : DistribMulAction (LorentzGroup d) (CoVector d) :=
  Tensor.distribMulAction

instance (priority := high + 1) {d : ℕ} : MulAction (LorentzGroup d) (CoVector d) :=
  DistribMulAction.toMulAction

instance (priority := high + 1) {d : ℕ} : SMul (LorentzGroup d) (CoVector d) :=
  Tensor.smul

lemma smul_eq_rep {d : ℕ} (Λ : LorentzGroup d) (v : CoVector d) : Λ • v = rep Λ v := rfl

lemma rep_apply_eq_sum_coe (d : ℕ) (Λ : LorentzGroup d) (v : CoVector d) (k : Fin 1 ⊕ Fin d) :
    rep Λ v k = ∑ j, Λ.1⁻¹ j k • v j := by
  rw [rep_apply_eq_sum, LorentzGroup.coe_inv]

lemma rep_apply_basis {d} (μ : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) :
    rep Λ (basis μ) = ∑ j, Λ.1⁻¹ μ j • basis j := by
  ext k
  simp [rep_apply_eq_sum_coe, apply_sum]

lemma rep_toMatrix (d : ℕ) (Λ : LorentzGroup d) :
    LinearMap.toMatrix basis basis (rep Λ) = Λ.1⁻¹ᵀ := by
  ext μ ν
  simp [LinearMap.toMatrix_apply, basis_repr_apply, rep_apply_eq_sum_coe, basis_apply]

lemma rep_injective (d : ℕ) (Λ : LorentzGroup d) : Function.Injective (rep Λ) := by
  intro v1 v2 h
  have h := congrArg toCoord h
  change ⇑(rep Λ v1) = ⇑(rep Λ v2) at h
  rw [rep_apply_eq_mulVec, rep_apply_eq_mulVec] at h
  exact toCoord.injective (Matrix.mulVec_injective_of_isUnit (isUnit_of_invertible _) h)

lemma rep_surjective (d : ℕ) (Λ : LorentzGroup d) : Function.Surjective (rep Λ) := by
  intro v
  use toCoord.symm ((LorentzGroup.transpose Λ) *ᵥ ⇑v)
  refine toCoord.injective ?_
  change ⇑(rep Λ _) = _
  rw [rep_apply_eq_mulVec]
  simp [← LorentzGroup.transpose_inv, LorentzGroup.coe_inv]

lemma rep_bijective (d : ℕ) (Λ : LorentzGroup d) : Function.Bijective (rep Λ) :=
  ⟨rep_injective d Λ, rep_surjective d Λ⟩

end CoVector

end Lorentz
