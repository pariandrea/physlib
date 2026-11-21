/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-!

# Swapping the factors of a tensor in coordinates

Swapping the factors of a tensor transposes its coefficients.

## i. Overview

A tensor `v` in `M ⊗ N` has the coefficients `(b₁.tensorProduct b₂).repr v (i, j)`. Swapping the
factors transposes them, so a tensor of `M ⊗ M` is symmetric or antisymmetric exactly when its
coefficients are.

## ii. Key results

- `Module.Basis.tensorProduct_repr_comm` : swapping the factors of a tensor transposes its
  coefficients.
- `Module.Basis.comm_eq_smul_iff` : swapping the factors scales a tensor of `M ⊗ M` by `r` exactly
  when its coefficient matrix satisfies `Xᵀ = r X`, symmetric for `r = 1` and antisymmetric for
  `r = -1`.

## iii. Table of contents

- A. Swapping the factors

## iv. References

* None.

-/

@[expose] public section

/-!

## A. Swapping the factors

-/

namespace Module.Basis

open TensorProduct

variable {R M N ι κ : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N]

/-- Swapping the factors of `v` transposes its coefficients, as `(Tᵀ)^νμ = T^μν`. -/
lemma tensorProduct_repr_comm (b₁ : Basis ι R M) (b₂ : Basis κ R N) (v : M ⊗[R] N) (i : ι)
    (j : κ) :
    (b₂.tensorProduct b₁).repr (TensorProduct.comm R M N v) (j, i) =
      (b₁.tensorProduct b₂).repr v (i, j) := by
  induction v using TensorProduct.inductionOn with
  | tmul x y => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

/-- Swapping the factors scales `v` by `r` exactly when its coefficients do, `X j i = r X i j`. -/
lemma comm_eq_smul_iff (b : Basis ι R M) (v : M ⊗[R] M) (r : R) :
    TensorProduct.comm R M M v = r • v ↔
      ∀ i j, (b.tensorProduct b).repr v (j, i) = r * (b.tensorProduct b).repr v (i, j) := by
  rw [← (b.tensorProduct b).repr.injective.eq_iff, Finsupp.ext_iff, Prod.forall]
  simp only [tensorProduct_repr_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

end Module.Basis
