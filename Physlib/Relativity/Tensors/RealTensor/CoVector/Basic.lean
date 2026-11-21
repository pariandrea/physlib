/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Physlib.Relativity.Tensors.RealTensor.Species
/-!

# Lorentz co vectors

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

/-- Real covariant Lorentz vector, the real Lorentz tensor `w_μ` with one lower index. -/
abbrev CoVector (d : ℕ := 3) := Tensor (Tensor.realLorentz d) ![Tensor.realLorentz.down]

namespace CoVector

open Tensor

/-- The components `w_μ` of a Lorentz covector. -/
noncomputable def toCoord {d : ℕ} : CoVector d ≃ₗ[ℝ] (Fin 1 ⊕ Fin d → ℝ) :=
  ((realLorentz d).oneIndexEquiv realLorentz.down).toLinearEquiv.symm ≪≫ₗ
    ((realLorentz d).basis realLorentz.down).equivFun

/-- The components of the tensor of a vector `x` of the index space are its components. -/
lemma toCoord_oneIndexEquiv {d : ℕ} (x : (realLorentz d).V realLorentz.down) :
    toCoord ((realLorentz d).oneIndexEquiv realLorentz.down x) =
      fun μ => x ((realLorentz d).basis realLorentz.up μ) := by
  change ((realLorentz d).basis realLorentz.down).equivFun
    (((realLorentz d).oneIndexEquiv realLorentz.down).toLinearEquiv.symm
      (((realLorentz d).oneIndexEquiv realLorentz.down).toLinearEquiv x)) = _
  rw [LinearEquiv.symm_apply_apply]
  funext μ
  simp

/-- The components of `v` are the components of its vector of the index space. -/
lemma toCoord_apply {d : ℕ} (v : CoVector d) :
    toCoord v =
      fun μ => ((realLorentz d).oneIndexEquiv realLorentz.down).symm v
        ((realLorentz d).basis realLorentz.up μ) := by
  conv_lhs => rw [← ((realLorentz d).oneIndexEquiv realLorentz.down).apply_symm_apply v]
  exact toCoord_oneIndexEquiv _

/-- The components of `v` in the basis of the color of its index. -/
lemma toCoord_eq_equivFun {d : ℕ} (v : CoVector d) :
    toCoord v = ((realLorentz d).basis realLorentz.down).equivFun
      (((realLorentz d).oneIndexEquiv realLorentz.down).symm v) :=
  rfl

-- `toCoord` goes through `PiTensorProduct`. Unfolding it in `whnf` is expensive (it made a
-- `fun_prop` call cost 136k heartbeats instead of 1k), so it is irreducible from here on.
attribute [irreducible] toCoord

/-- `w μ` is the component `w_μ`. -/
instance {d} : CoeFun (CoVector d) (fun _ => Fin 1 ⊕ Fin d → ℝ) where
  coe := fun v => toCoord v

/-- The equivalence between `CoVector d` and `EuclideanSpace ℝ (Fin 1 ⊕ Fin d)`. -/
def equivEuclid (d : ℕ) :
    CoVector d ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1 ⊕ Fin d) :=
  toCoord ≪≫ₗ (WithLp.linearEquiv _ _ _).symm

@[ext]
lemma eq_of_apply_eq {d : ℕ} {v w : CoVector d} (h : ∀ i, v i = w i) : v = w := by
  apply (equivEuclid d).injective
  ext i
  exact h i

instance (d : ℕ) : Norm (CoVector d) where
  norm := fun v => ‖equivEuclid d v‖

lemma norm_eq_equivEuclid (d : ℕ) (v : CoVector d) :
    ‖v‖ = ‖equivEuclid d v‖ := rfl

instance isNormedAddCommGroup (d : ℕ) : NormedAddCommGroup (CoVector d) :=
  NormedAddCommGroup.induced _ _ (equivEuclid d) (equivEuclid d).injective

instance isNormedSpace (d : ℕ) : NormedSpace ℝ (CoVector d) where
  norm_smul_le c v := by
    simp only [norm_eq_equivEuclid, map_smul]
    exact norm_smul_le c (equivEuclid d v)

open InnerProductSpace

instance (d : ℕ) : Inner ℝ (CoVector d) where
  inner := fun v w => ⟪equivEuclid d v, equivEuclid d w⟫_ℝ

lemma inner_eq_equivEuclid (d : ℕ) (v w : CoVector d) :
    ⟪v, w⟫_ℝ = ⟪equivEuclid d v, equivEuclid d w⟫_ℝ := rfl

/-- The Euclidean inner product structure on `CoVector`. -/
instance innerProductSpace (d : ℕ) : InnerProductSpace ℝ (CoVector d) where
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

/-- The instance of a `ChartedSpace` on `Vector d`. -/
instance : ChartedSpace (CoVector d) (CoVector d) := chartedSpaceSelf (CoVector d)

@[simp]
lemma apply_smul {d : ℕ} (c : ℝ) (v : CoVector d) (i : Fin 1 ⊕ Fin d) :
    (c • v) i = c * v i := by simp

@[simp]
lemma apply_add {d : ℕ} (v w : CoVector d) (i : Fin 1 ⊕ Fin d) :
    (v + w) i = v i + w i := by simp

@[simp]
lemma apply_sub {d : ℕ} (v w : CoVector d) (i : Fin 1 ⊕ Fin d) :
    (v - w) i = v i - w i := by simp

@[simp]
lemma apply_sum {d : ℕ} {ι : Type} [Fintype ι] (f : ι → CoVector d) (i : Fin 1 ⊕ Fin d) :
    (∑ j, f j) i = ∑ j, f j i := by simp [map_sum]

@[simp]
lemma neg_apply {d : ℕ} (v : CoVector d) (i : Fin 1 ⊕ Fin d) :
    (-v) i = - v i := by simp

@[simp]
lemma zero_apply {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    (0 : CoVector d) i = 0 := by simp

/-!

## Basis

-/

/-- The basis on `Vector d` indexed by `Fin 1 ⊕ Fin d`. -/
def basis {d : ℕ} : Basis (Fin 1 ⊕ Fin d) ℝ (CoVector d) :=
  (Pi.basisFun ℝ _).map toCoord.symm

@[simp]
lemma basis_apply {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) :
    basis μ ν = if μ = ν then 1 else 0 := by
  simp [basis, Pi.single_apply, eq_comm]

lemma basis_repr_apply {d : ℕ} (p : CoVector d) (μ : Fin 1 ⊕ Fin d) :
    basis.repr p μ = p μ := by
  simp [basis]

lemma map_apply_eq_basis_mulVec {d : ℕ} (f : CoVector d →ₗ[ℝ] CoVector d) (p : CoVector d) :
    ⇑(f p) = (LinearMap.toMatrix basis basis) f *ᵥ ⇑p := by
  simpa only [funext (basis_repr_apply _)] using
    (LinearMap.toMatrix_mulVec_repr basis basis f p).symm

end CoVector

end Lorentz
