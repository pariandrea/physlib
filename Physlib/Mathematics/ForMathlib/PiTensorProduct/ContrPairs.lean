/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Physlib.Mathematics.ForMathlib.Representation
/-!

# Contraction of pairs of factors of a tensor product

This file contracts chosen pairs of factors of `⨂[R] i, P i` and keeps the others.

## i. Overview

Contraction pairs some indices of a tensor, turns each pair into a scalar, and keeps the other
indices. The index type `κ ⊕ (J ⊕ J)` says which indices are paired, with Mathlib's tags `Sum.inl`
and `Sum.inr` for the left and the right side of `⊕`. The indices `inl x`, for `x` in `κ`, are kept.
Each `j` in `J` is a pair, with first index `inr (inl j)` and second index `inr (inr j)`, contracted
by the pairing `p j`. On a pure tensor, `contrPairs p` multiplies the kept vectors by the product of
the pairings (`contrPairs_tprod`). Mathlib's `PiTensorProduct.tmulEquivDep` splits a tensor product
over `A ⊕ B` into the tensor product over `A` times the tensor product over `B`. Splitting at the
outer `⊕` separates the kept factors from the paired ones. Splitting at the inner `⊕` separates the
first factor of each pair from the second, so that `p j` can contract them. `contrPairs` takes only
this arrangement. A tensor whose indices are in another order is reordered into it first, with
`PiTensorProduct.reindex`.

For example, the Ricci tensor `R_μν = R^ρ_μρν` pairs the first and third indices and keeps the
second and fourth. Reordering takes `u ⊗ α ⊗ β ⊗ γ` to `α ⊗ γ ⊗ u ⊗ β`, with `α ⊗ γ` at the kept
indices and `u`, `β` the pair. The contraction then gives `(β_ρ u^ρ) α ⊗ γ`. The Ricci scalar
`R = R^μν_μν` has two pairs and no kept index, so the result is the scalar `(α_μ u^μ) (β_ν v^ν)` on
`u ⊗ v ⊗ α ⊗ β`.

When each pairing is invariant, the contraction is a map of representations (B).

## ii. Key results

- `PiTensorProduct.contrPairs` : the contraction of pairs of factors by a family of pairings,
  with `PiTensorProduct.contrPairs_tprod` : its value on a pure tensor.
- `Representation.IsIntertwiningMap.contrPairs` : the contraction by invariant pairings commutes
  with the action on tensors.

## iii. Table of contents

- A. Contraction of pairs of factors
- B. Invariance of the contraction

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct

/-!

## A. Contraction of pairs of factors

-/

section

open PiTensorProduct

variable {R : Type*} [CommSemiring R] {κ J : Type*} [Fintype J] {P : κ ⊕ (J ⊕ J) → Type*}
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]

/-- The contraction of `⨂ i, P i` on `κ ⊕ (J ⊕ J)` that pairs the factors at `inr (inl j)` and
`inr (inr j)` by `p j` and keeps the factors at `inl x`. -/
noncomputable def PiTensorProduct.contrPairs
    (p : Π j, P (.inr (.inl j)) ⊗[R] P (.inr (.inr j)) →ₗ[R] R) :
    (⨂[R] i, P i) →ₗ[R] ⨂[R] x, P (.inl x) :=
  -- The factors of each pair are split into two tensor products, and the second is read as a
  -- linear form on the first through the `p j` and Mathlib's `PiTensorProduct.dualDistrib`.
  (TensorProduct.rid R _).toLinearMap ∘ₗ
    (TensorProduct.lift (PiTensorProduct.dualDistrib ∘ₗ
      PiTensorProduct.map fun j => (TensorProduct.curry (p j)).flip).flip ∘ₗ
      (tmulEquivDep R fun i => P (.inr i)).symm.toLinearMap).lTensor _ ∘ₗ
    (tmulEquivDep R P).symm.toLinearMap

/-- On a pure tensor the contraction multiplies the kept factors by the pairings of each pair. -/
@[simp]
lemma PiTensorProduct.contrPairs_tprod
    (p : Π j, P (.inr (.inl j)) ⊗[R] P (.inr (.inr j)) →ₗ[R] R) (f : Π i, P i) :
    contrPairs p (⨂ₜ[R] i, f i) =
      (∏ j, p j (f (.inr (.inl j)) ⊗ₜ f (.inr (.inr j)))) • ⨂ₜ[R] x, f (.inl x) := by
  simp [contrPairs, tmulEquivDep_symm_apply]

end

/-!

## B. Invariance of the contraction

-/

section

variable {k G : Type*} [CommSemiring k] [Monoid G]

/-- `PiTensorProduct.contrPairs p` intertwines `piTprod ρ` and `piTprod` of the kept factors when
every pairing `p j` is invariant. -/
lemma Representation.IsIntertwiningMap.contrPairs {κ J : Type*} [Fintype J]
    {M : κ ⊕ (J ⊕ J) → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]
    {ρ : Π i, Representation k G (M i)}
    {p : Π j, M (.inr (.inl j)) ⊗[k] M (.inr (.inr j)) →ₗ[k] k}
    (hp : ∀ j g x y, p j (ρ _ g x ⊗ₜ ρ _ g y) = p j (x ⊗ₜ y)) :
    (Representation.piTprod ρ).IsIntertwiningMap (Representation.piTprod fun x => ρ (.inl x))
      (PiTensorProduct.contrPairs p) where
  isIntertwining g v := by
    induction v using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      simp only [map_smul, Representation.piTprod_tprod, PiTensorProduct.contrPairs_tprod, hp,
        smul_comm r]
    | add x y hx hy => simp only [map_add, hx, hy]

end
