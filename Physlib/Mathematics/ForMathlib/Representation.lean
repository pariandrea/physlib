/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.ForMathlib.PiTensorProduct
public import Mathlib.RepresentationTheory.Intertwining

/-!

# Tensor products of representations

This file gives the representation on the tensor product of a family of representations.

## i. Overview

A tensor such as `T^μ_ν` lies in the tensor product `⨂[k] i, M i` of a family of spaces. Each
index `i` transforms by its own representation `ρ i`, as `Λ` at the up index and `(Λ⁻¹)ᵀ` at the
down index. Mathlib has the representation `ρ.tprod τ` for two factors only.

We define the representation of a family (A). `piTprod ρ` acts by `ρ i g` at each index `i`. A map
out of `⨂[k] i, M i` that commutes with `piTprod ρ` on pure tensors commutes with it on all tensors
(`map_piTprod_of_tprod`).

## ii. Key results

- `Representation.piTprod` : the representation on `⨂[k] i, M i` of a family of representations.
- `Representation.map_piTprod_of_tprod` : a map that commutes with `piTprod ρ` on pure tensors
  commutes with it on all tensors.
- `Representation.IntertwiningMap.piTprod`, `Representation.Equiv.piTprodCongr`,
  `Representation.Equiv.tprodCongr`, `Representation.Equiv.piTprodReindex`,
  `Representation.Equiv.piTprodSum`, `Representation.Equiv.piTprodOfSubsingleton` and
  `Representation.IsIntertwiningMap.contrPairs` : Mathlib's maps of tensor products as maps of
  representations.

## iii. Table of contents

- A. The representation on a tensor product of a family
- B. Invariant vectors
- C. Maps of representations

## iv. References

* None.

-/

@[expose] public section

open TensorProduct

variable {k l G U : Type*} [CommSemiring k] [CommSemiring l] [Monoid G] [AddCommMonoid U]
  [Module l U] {τ : Representation l G U}

/-!

## A. The representation on a tensor product of a family

`piTprod ρ` transforms each index by its own representation. For `T^μ_ν` it sends the pure tensor
`u ⊗ α` to `Λu ⊗ (Λ⁻¹)ᵀα` (`piTprod_tprod`).

-/

namespace Representation

variable {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]

/-- The tensor product of a family of representations, `g ↦ ⨂ i, ρ i g` on `⨂[k] i, M i`. It is
the n-ary `Representation.tprod`. -/
noncomputable def piTprod (ρ : Π i, Representation k G (M i)) : Representation k G (⨂[k] i, M i) :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi ρ)

/-- On a pure tensor, `piTprod ρ g` acts by `ρ i g` on the vector at each index `i`. -/
@[simp]
lemma piTprod_tprod (ρ : Π i, Representation k G (M i)) (g : G) (m : Π i, M i) :
    piTprod ρ g (⨂ₜ[k] i, m i) = ⨂ₜ[k] i, ρ i g (m i) :=
  PiTensorProduct.map_tprod _ _

/-- A semilinear map out of `⨂ i, M i` that commutes with `piTprod ρ g` on pure tensors commutes
with it on all tensors. The ring map `σ : k →+* l` can be complex conjugation. -/
lemma map_piTprod_of_tprod {σ : k →+* l} {ρ : Π i, Representation k G (M i)}
    (f : (⨂[k] i, M i) →ₛₗ[σ] U) (g : G)
    (h : ∀ m : Π i, M i, f (piTprod ρ g (⨂ₜ[k] i, m i)) = τ g (f (⨂ₜ[k] i, m i)))
    (t : ⨂[k] i, M i) : f (piTprod ρ g t) = τ g (f t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r m => rw [map_smul, map_smulₛₗ, h, map_smulₛₗ, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Representation

/-!

## B. Invariant vectors

An intertwining map sends invariant vectors to invariant vectors (`map_invariant`). An intertwining
map from the trivial representation on `k` picks out the invariant vector `φ 1`
(`map_one_invariant`).

-/

section

variable {V W U X : Type*} [AddCommMonoid V] [Module k V]
  [AddCommMonoid W] [Module k W] [AddCommMonoid U] [Module k U] [AddCommMonoid X] [Module k X]
  {ρ : Representation k G V} {σ : Representation k G W} {τ : Representation k G U}
  {π : Representation k G X}

/-- An intertwining map sends an invariant vector to an invariant vector,
`ρ g v = v → σ g (φ v) = φ v`. -/
lemma Representation.IntertwiningMap.map_invariant (φ : ρ.IntertwiningMap σ) {v : V} {g : G}
    (hv : ρ g v = v) : σ g (φ v) = φ v := by
  rw [← Representation.IntertwiningMap.isIntertwining, hv]

/-- An intertwining map `φ` from the trivial representation on `k` picks out an invariant vector,
`φ 1`. -/
lemma Representation.IntertwiningMap.map_one_invariant
    (φ : (Representation.trivial k G k).IntertwiningMap ρ) {v : V} (hv : φ 1 = v) (g : G) :
    ρ g v = v :=
  hv ▸ φ.map_invariant rfl

/-!

## C. Maps of representations

-/

/-- The tensor product of two equivalences of representations, `v ⊗ u ↦ φ v ⊗ ψ u`, Mathlib's
`TensorProduct.congr` with the actions `ρ ⊗ τ` and `σ ⊗ π`. -/
noncomputable def Representation.Equiv.tprodCongr (φ : ρ.Equiv σ) (ψ : τ.Equiv π) :
    (ρ.tprod τ).Equiv (σ.tprod π) :=
  .mk (TensorProduct.congr φ.toLinearEquiv ψ.toLinearEquiv)
    (φ.toIntertwiningMap.tensor ψ.toIntertwiningMap).isIntertwining'

@[simp]
lemma Representation.Equiv.tprodCongr_tmul (φ : ρ.Equiv σ) (ψ : τ.Equiv π) (v : V) (u : U) :
    φ.tprodCongr ψ (v ⊗ₜ u) = φ v ⊗ₜ ψ u := rfl

end

section

variable {ι : Type*} {M N : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module k (N i)]

namespace Representation

/-- `piTprod ρ g` is Mathlib's `PiTensorProduct.map` of the `ρ i g`. -/
lemma piTprod_apply (ρ : Π i, Representation k G (M i)) (g : G) :
    piTprod ρ g = PiTensorProduct.map fun i => ρ i g := rfl

namespace IntertwiningMap

/-- The tensor product of a family of intertwining maps, `⨂ i, v i ↦ ⨂ i, f i (v i)`, Mathlib's
`PiTensorProduct.map` as an intertwining map. It is the n-ary `IntertwiningMap.tensor`. -/
noncomputable def piTprod {ρ : Π i, Representation k G (M i)} {σ : Π i, Representation k G (N i)}
    (f : Π i, (ρ i).IntertwiningMap (σ i)) :
    (Representation.piTprod ρ).IntertwiningMap (Representation.piTprod σ) where
  toLinearMap := PiTensorProduct.map fun i => (f i).toLinearMap
  isIntertwining' g := by
    rw [piTprod_apply, piTprod_apply, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
    exact congrArg PiTensorProduct.map (funext fun i => (f i).isIntertwining' g)

/-- On a pure tensor, `piTprod f` applies `f i` to the vector at each index `i`. -/
@[simp]
lemma piTprod_tprod {ρ : Π i, Representation k G (M i)} {σ : Π i, Representation k G (N i)}
    (f : Π i, (ρ i).IntertwiningMap (σ i)) (m : Π i, M i) :
    piTprod f (⨂ₜ[k] i, m i) = ⨂ₜ[k] i, f i (m i) :=
  PiTensorProduct.map_tprod _ _

/-- The linear map of `piTprod f` is `PiTensorProduct.map` of the linear maps of the `f i`. -/
@[simp]
lemma toLinearMap_piTprod {ρ : Π i, Representation k G (M i)} {σ : Π i, Representation k G (N i)}
    (f : Π i, (ρ i).IntertwiningMap (σ i)) :
    (piTprod f).toLinearMap = PiTensorProduct.map fun i => (f i).toLinearMap := rfl

/-- The tensor product of composites is the composite of the tensor products. -/
lemma piTprod_comp {P : ι → Type*} [∀ i, AddCommMonoid (P i)] [∀ i, Module k (P i)]
    {ρ : Π i, Representation k G (M i)} {σ : Π i, Representation k G (N i)}
    {υ : Π i, Representation k G (P i)} (f : Π i, (ρ i).IntertwiningMap (σ i))
    (g : Π i, (σ i).IntertwiningMap (υ i)) :
    piTprod (fun i => (g i).comp (f i)) = (piTprod g).comp (piTprod f) :=
  ext (PiTensorProduct.map_comp _ _)

/-- The tensor product of identities is the identity. -/
lemma piTprod_id {ρ : Π i, Representation k G (M i)} :
    piTprod (fun i => id (ρ i)) = id (Representation.piTprod ρ) :=
  ext PiTensorProduct.map_id

end IntertwiningMap

namespace Equiv

/-- The tensor product of a family of equivalences of representations, `⨂ i, v i ↦ ⨂ i, φ i (v i)`,
Mathlib's `PiTensorProduct.congr` as an equivalence of representations. -/
noncomputable def piTprodCongr {ρ : Π i, Representation k G (M i)}
    {σ : Π i, Representation k G (N i)} (φ : Π i, (ρ i).Equiv (σ i)) :
    (Representation.piTprod ρ).Equiv (Representation.piTprod σ) :=
  .mk (PiTensorProduct.congr fun i => (φ i).toLinearEquiv)
    (IntertwiningMap.piTprod fun i => (φ i).toIntertwiningMap).isIntertwining'

/-- On a pure tensor, `piTprodCongr φ` applies `φ i` to the vector at each index `i`. -/
@[simp]
lemma piTprodCongr_tprod {ρ : Π i, Representation k G (M i)}
    {σ : Π i, Representation k G (N i)} (φ : Π i, (ρ i).Equiv (σ i)) (m : Π i, M i) :
    piTprodCongr φ (⨂ₜ[k] i, m i) = ⨂ₜ[k] i, φ i (m i) :=
  PiTensorProduct.congr_tprod _ _

/-- The intertwining map of `piTprodCongr φ` is `IntertwiningMap.piTprod` of those of the `φ i`. -/
@[simp]
lemma toIntertwiningMap_piTprodCongr {ρ : Π i, Representation k G (M i)}
    {σ : Π i, Representation k G (N i)} (φ : Π i, (ρ i).Equiv (σ i)) :
    (piTprodCongr φ).toIntertwiningMap = IntertwiningMap.piTprod fun i => (φ i).toIntertwiningMap :=
  rfl

/-- The linear equivalence of `piTprodCongr φ` is `PiTensorProduct.congr` of those of the `φ i`. -/
@[simp]
lemma toLinearEquiv_piTprodCongr {ρ : Π i, Representation k G (M i)}
    {σ : Π i, Representation k G (N i)} (φ : Π i, (ρ i).Equiv (σ i)) :
    (piTprodCongr φ).toLinearEquiv = PiTensorProduct.congr fun i => (φ i).toLinearEquiv :=
  rfl

/-- The inverse of `piTprodCongr φ` applies the inverses `(φ i).symm` index by index. -/
@[simp]
lemma piTprodCongr_symm_tprod {ρ : Π i, Representation k G (M i)}
    {σ : Π i, Representation k G (N i)} (φ : Π i, (ρ i).Equiv (σ i)) (m : Π i, N i) :
    (piTprodCongr φ).symm (⨂ₜ[k] i, m i) = ⨂ₜ[k] i, (φ i).symm (m i) :=
  PiTensorProduct.congr_symm_tprod _ _


end Equiv

end Representation

/-- Reindexing the factors of a tensor product of representations along `e : ι ≃ ι'`,
`⨂ i, v i ↦ ⨂ j, v (e.symm j)`. It is Mathlib's `PiTensorProduct.reindex` with the actions
`piTprod ρ` and `piTprod (ρ ∘ e.symm)`. -/
noncomputable def Representation.Equiv.piTprodReindex {ι' : Type*}
    (ρ : Π i, Representation k G (M i)) (e : ι ≃ ι') :
    (Representation.piTprod ρ).Equiv (Representation.piTprod fun j => ρ (e.symm j)) :=
  .mk (PiTensorProduct.reindex k M e) fun g => PiTensorProduct.ext <| MultilinearMap.ext fun m => by
    simp [PiTensorProduct.reindex_tprod]

@[simp]
lemma Representation.Equiv.piTprodReindex_tprod {ι' : Type*} (ρ : Π i, Representation k G (M i))
    (e : ι ≃ ι') (m : Π i, M i) :
    Representation.Equiv.piTprodReindex ρ e (⨂ₜ[k] i, m i) = ⨂ₜ[k] j, m (e.symm j) :=
  PiTensorProduct.reindex_tprod _ _

/-- The inverse of `piTprodReindex ρ e` moves the factors back, `⨂ j, m (e.symm j) ↦ ⨂ i, m i`. -/
@[simp]
lemma Representation.Equiv.piTprodReindex_symm_tprod {ι' : Type*}
    (ρ : Π i, Representation k G (M i)) (e : ι ≃ ι') (m : Π i, M i) :
    (Representation.Equiv.piTprodReindex ρ e).symm (⨂ₜ[k] j, m (e.symm j)) = ⨂ₜ[k] i, m i :=
  (LinearEquiv.symm_apply_eq _).2 (PiTensorProduct.reindex_tprod _ _).symm

/-- The tensor product of the two halves of a family of representations indexed by `ι₁ ⊕ ι₂`,
`(⨂ i, v i) ⊗ (⨂ j, w j) ↦ ⨂ s, Sum.rec v w s`. It is Mathlib's `PiTensorProduct.tmulEquivDep`
with the actions. -/
noncomputable def Representation.Equiv.piTprodSum {ι₁ ι₂ : Type*} {M : ι₁ ⊕ ι₂ → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)] (ρ : Π i, Representation k G (M i)) :
    ((Representation.piTprod fun i => ρ (.inl i)).tprod
      (Representation.piTprod fun j => ρ (.inr j))).Equiv (Representation.piTprod ρ) :=
  .mk (PiTensorProduct.tmulEquivDep k M) fun g => by
    ext f₁ f₂
    simp only [Representation.tprod_apply, LinearMap.compMultilinearMap_apply,
      TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
      TensorProduct.curry_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      TensorProduct.map_tmul, Representation.piTprod_tprod, PiTensorProduct.tmulEquivDep_apply]
    exact congrArg (PiTensorProduct.tprod k) (funext fun s => by rcases s with _ | _ <;> rfl)

@[simp]
lemma Representation.Equiv.piTprodSum_tmul {ι₁ ι₂ : Type*} {M : ι₁ ⊕ ι₂ → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)] (ρ : Π i, Representation k G (M i))
    (f₁ : Π i, M (.inl i)) (f₂ : Π j, M (.inr j)) :
    Representation.Equiv.piTprodSum ρ ((⨂ₜ[k] i, f₁ i) ⊗ₜ (⨂ₜ[k] j, f₂ j)) =
      ⨂ₜ[k] s, Sum.rec f₁ f₂ s :=
  PiTensorProduct.tmulEquivDep_apply k M f₁ f₂

/-- A representation `ρ i₀` as the tensor product of a family `ρ` over a subsingleton index type,
`v ↦ ⨂ i, v`. It is Mathlib's `PiTensorProduct.subsingletonEquiv` with the actions. -/
noncomputable def Representation.Equiv.piTprodOfSubsingleton [Subsingleton ι]
    (ρ : Π i, Representation k G (M i)) (i₀ : ι) :
    (ρ i₀).Equiv (Representation.piTprod ρ) :=
  .mk (PiTensorProduct.subsingletonEquiv i₀).symm fun g => LinearMap.ext fun v => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      PiTensorProduct.subsingletonEquiv_symm_apply, Representation.piTprod_tprod]
    congr 1
    ext i
    obtain rfl := Subsingleton.elim i i₀
    simp

/-- The inverse of `piTprodOfSubsingleton ρ i₀` takes a pure tensor to its vector at `i₀`. -/
@[simp]
lemma Representation.Equiv.piTprodOfSubsingleton_symm_tprod [Subsingleton ι]
    (ρ : Π i, Representation k G (M i)) (i₀ : ι) (m : Π i, M i) :
    (Representation.Equiv.piTprodOfSubsingleton ρ i₀).symm (⨂ₜ[k] i, m i) = m i₀ :=
  PiTensorProduct.subsingletonEquiv_apply_tprod _ _

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
