/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Physlib.Relativity.LorentzGroup.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
/-!

# Representation of the Lorentz group on Lorentz vectors

In this module we define the representation of the Lorentz group on Lorentz vectors.
This does not define the MulAction on `Lorentz.Vector`, which is induced
by its tensor structure.

-/

@[expose] public section


open Module Matrix MatrixGroups Complex TensorProduct

noncomputable section

namespace Lorentz

namespace Vector
attribute [-simp] Fintype.sum_sum_type

/-- The representation of the Lorentz group on Lorentz vectors, the action on tensors with one
upper index. -/
def rep {d : ℕ} : Representation ℝ (LorentzGroup d) (Vector d) :=
  (Tensor.realLorentz d).tensorRep _

/-!

## Properties of the representation.

-/

lemma rep_apply_eq_mulVec (d : ℕ) (Λ : LorentzGroup d) (v : Vector d) :
    ⇑(rep Λ v) = Λ *ᵥ ⇑v := by
  rw [toCoord_apply, toCoord_apply]
  have h := Representation.IntertwiningMap.isIntertwining _ _
    ((Tensor.realLorentz d).oneIndexEquiv Tensor.realLorentz.up).symm.toIntertwiningMap Λ v
  exact (congrArg Tensor.Species.ColoredSpace.toV h).trans
    (Tensor.realLorentz.indexRep_up_apply d .vec Λ _)

lemma rep_apply_eq_sum (d : ℕ) (Λ : LorentzGroup d) (v : Vector d) (k : Fin 1 ⊕ Fin d) :
    rep Λ v k = ∑ j, Λ.1 k j • v j := by
  rw [rep_apply_eq_mulVec]; rfl

/-- The Lorentz group acts on vectors as on tensors with one upper index, `Λ • v = rep Λ v`. The
priority is above the generic action `TensorSpecies.Tensorial.smulAction` of the older tensor
library, so that `Λ • v` is this action. -/
instance (priority := high + 1) {d : ℕ} : DistribMulAction (LorentzGroup d) (Vector d) :=
  Tensor.distribMulAction

instance (priority := high + 1) {d : ℕ} : MulAction (LorentzGroup d) (Vector d) :=
  DistribMulAction.toMulAction

instance (priority := high + 1) {d : ℕ} : SMul (LorentzGroup d) (Vector d) :=
  Tensor.smul

lemma smul_eq_rep {d : ℕ} (Λ : LorentzGroup d) (v : Vector d) : Λ • v = rep Λ v := rfl

lemma rep_apply_basis {d} (μ : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) :
    rep Λ (basis μ) = ∑ j, Λ.1 j μ • basis j := by
  ext k
  simp [rep_apply_eq_sum, apply_sum]

lemma rep_toMatrix (d : ℕ) (Λ : LorentzGroup d) :
    LinearMap.toMatrix basis basis (rep Λ) = Λ.1 := by
  ext μ ν
  simp [LinearMap.toMatrix_apply, basis_repr_apply, rep_apply_eq_sum, basis_apply]

lemma rep_injective (d : ℕ) (Λ : LorentzGroup d) : Function.Injective (rep Λ) :=
  fun _ _ h => toCoord.injective <| Matrix.mulVec_injective_of_isUnit (isUnit_of_invertible Λ.1)
    (by simpa [rep_apply_eq_mulVec] using congrArg toCoord h)

lemma rep_surjective (d : ℕ) (Λ : LorentzGroup d) : Function.Surjective (rep Λ) :=
  fun v => ⟨toCoord.symm (Λ⁻¹ *ᵥ ⇑v), toCoord.injective <| by
    change ⇑(rep Λ _) = _
    simp [rep_apply_eq_mulVec]⟩

lemma rep_bijective (d : ℕ) (Λ : LorentzGroup d) : Function.Bijective (rep Λ) :=
  ⟨rep_injective d Λ, rep_surjective d Λ⟩

@[fun_prop]
lemma rep_contDiff (d : ℕ) {n} (Λ : LorentzGroup d) : ContDiff ℝ n (rep Λ) := by
  refine (contDiff_apply _).mp fun μ => ?_
  simp only [rep_apply_eq_sum, smul_eq_mul]
  fun_prop

lemma rep_left_injective (d : ℕ) : Function.Injective (rep (d := d)) :=
  fun _ _ h => LorentzGroup.eq_of_mulVec_eq fun v => by
    simpa [rep_apply_eq_mulVec] using congrArg toCoord (LinearMap.congr_fun h (toCoord.symm v))

end Vector

end Lorentz
