/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.RepresentationTheory.Invariants
public import Physlib.Mathematics.ForMathlib.Contraction
public import Physlib.Mathematics.ForMathlib.TensorProductMatrix

/-!

# Tensors as linear maps through the coordinate pairing

Two bases with the same labels read a tensor of `M ⊗ U` as a linear map `N → U`.

## i. Overview

Mathlib reads a tensor of `Module.Dual R N ⊗ U` as a linear map `N → U`
(`dualTensorHomEquivOfBasis`). When `M` is paired with `N` by the coordinate pairing of two bases
`b` and `b'` with the same labels (`Module.Basis.coordPairing`), `M` plays the role of the dual of
`N`, so a tensor of `M ⊗ U` is a linear map `N → U`. For a covector index this reads a metric
`g_μν` as the map `v^μ ↦ v^μ g_μν`.

The delta `∑ I, b I ⊗ b' I` of the two bases is the tensor of the identity map. When the
coordinate pairing is invariant under representations of a group, the linear map of `Λz` is
`Λ ∘ z ∘ Λ⁻¹`.

## ii. Key results

- `Module.Basis.coordTensorHomEquiv` : a tensor of `M ⊗ U` as a linear map `N → U`.
- `Module.Basis.coordDelta` : the delta `∑ I, b I ⊗ b' I`, and
  `Module.Basis.coordTensorHomEquiv_coordDelta` : it is the identity map.
- `Module.Basis.repr_coordTensorHomEquiv` : the linear map in components.
- `Module.Basis.coordTensorHomEquiv_map_rep` : the linear map of `(Λ ⊗ f) z` is
  `f ∘ z ∘ Λ⁻¹`.

## iii. Table of contents

- A. Tensors as linear maps through the coordinate pairing
- B. Equivariance

## iv. References

* None.

-/

@[expose] public section

namespace Module.Basis

open TensorProduct

/-!

## A. Tensors as linear maps through the coordinate pairing

-/

variable {R ι M N U U' : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup U] [Module R U] [AddCommGroup U']
    [Module R U']

/-- `M ⊗ U` as the linear maps `N → U`, reading `M` as the dual of `N` through the coordinate
pairing. It sends `x ⊗ y` to `v ↦ b'.coordPairing b (v ⊗ x) • y`. -/
noncomputable def coordTensorHomEquiv (b : Module.Basis ι R M) (b' : Module.Basis ι R N) :
    M ⊗[R] U ≃ₗ[R] (N →ₗ[R] U) :=
  (TensorProduct.congr (TensorProduct.curry (b'.coordPairing b)).flip.toPerfPair
    (LinearEquiv.refl R U)).trans (dualTensorHomEquivOfBasis b')

/-- A pure tensor `x ⊗ y` acts as `v ↦ b'.coordPairing b (v ⊗ x) • y`. -/
@[simp]
lemma coordTensorHomEquiv_tmul (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (x : M) (y : U)
    (v : N) : b.coordTensorHomEquiv b' (x ⊗ₜ[R] y) v = b'.coordPairing b (v ⊗ₜ[R] x) • y :=
  rfl

/-- The delta `∑ I, b I ⊗ b' I` of two bases with the same labels. -/
noncomputable def coordDelta (b : Module.Basis ι R M) (b' : Module.Basis ι R N) : M ⊗[R] N :=
  ∑ I, b I ⊗ₜ b' I

/-- The delta read as a linear map is the identity. -/
lemma coordTensorHomEquiv_coordDelta (b : Module.Basis ι R M) (b' : Module.Basis ι R N) :
    b.coordTensorHomEquiv b' (b.coordDelta b') = LinearMap.id :=
  b'.ext fun J => by
    simp [coordDelta, coordPairing_basis_basis, Finset.sum_ite_eq]

/-- The components of the delta form the identity matrix. -/
lemma tensorProduct_repr_coordDelta (b : Module.Basis ι R M) (b' : Module.Basis ι R N)
    (I J : ι) : (b.tensorProduct b').repr (b.coordDelta b') (I, J) = if I = J then 1 else 0 := by
  simp [coordDelta, Finsupp.single_apply]

/-- `coordTensorHomEquiv` in components, `(z v)_J = ∑ I, v_I z_{IJ}`. -/
lemma repr_coordTensorHomEquiv {κ N' : Type*} [AddCommGroup N'] [Module R N']
    (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (d : Module.Basis κ R N')
    (z : M ⊗[R] N') (v : N) (J : κ) :
    d.repr (b.coordTensorHomEquiv b' z v) J =
      ∑ I, b'.repr v I * (b.tensorProduct d).repr z (I, J) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy, mul_add, Finset.sum_add_distrib]
  | tmul x y => simp [coordPairing_tmul, Finset.sum_mul, mul_assoc, mul_comm (d.repr y J)]

/-!

## B. Equivariance

When the coordinate pairing of `b` and `b'` is invariant under representations `ρ` on `M` and `ρ'`
on `N`, the group acts on a tensor of `M ⊗ U` as `Λ ∘ z ∘ Λ⁻¹` on its linear map.

-/

section

variable {G : Type*} [Group G] {ρ : Representation R G M} {ρ' : Representation R G N}
  {b : Module.Basis ι R M} {b' : Module.Basis ι R N}

/-- The linear map of `(Λ ⊗ f) z` is `f ∘ z ∘ Λ⁻¹` when the coordinate pairing is invariant. -/
lemma coordTensorHomEquiv_map_rep
    (hρ : ∀ g x y, b.coordPairing b' (ρ g x ⊗ₜ ρ' g y) = b.coordPairing b' (x ⊗ₜ y))
    (f : U →ₗ[R] U') (z : M ⊗[R] U) (g : G) :
    b.coordTensorHomEquiv b' (TensorProduct.map (ρ g) f z) =
      f ∘ₗ b.coordTensorHomEquiv b' z ∘ₗ ρ' g⁻¹ := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz', LinearMap.add_comp, LinearMap.comp_add]
  | tmul x y =>
    ext v
    simpa [coordPairing_comm b' b] using
      congrArg (· • f y) (hρ g x (ρ' g⁻¹ v))

end

end Module.Basis
