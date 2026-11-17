/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.ForMathlib.CoordTensorHom
public import Physlib.Mathematics.Tensors.Contraction
public import Physlib.Mathematics.Tensors.IndexMaps
/-!

# Tensors of two factors as linear maps

A tensor in `V a ⊗ U` is read as a linear map `V a.dual → U`. The delta is the identity map, and
contracting an index with a tensor of two factors applies its linear map.

## i. Overview

A tensor `z` in `V a ⊗ U`, for a color `a` of a species `S` and any module `U`, is read as the
linear map `S.toLin z : V a.dual → U` that contracts its input with the first factor of `z`. On a
pure tensor `z = x ⊗ y` it is `v ↦ (v^μ x_μ) y`. Every linear map `V a.dual → U` is `toLin z` for
exactly one `z`. `toLin` is `Module.Basis.coordTensorHomEquiv` for the bases of `a` and `a.dual`,
which is Mathlib's `dualTensorHomEquivOfBasis` once the contraction identifies `V a` with the dual
of `V a.dual`. The results that need only the bases and the invariance of the contraction, such as
the matrix of `toLin z` and its equivariance, are stated there.

This is how two-index tensors act as maps. A metric `g_μν` is the map `v^μ ↦ v^μ g_μν`, and the
inverse metric `g^μν` is the tensor of the inverse map. The map of `Λz` is `Λ ∘ z ∘ Λ⁻¹`, so `z` is
invariant exactly when its linear map commutes with the group action
(`Module.Basis.coordTensorHomEquiv_map_rep`). This is Mathlib's
`Representation.mem_linHom_invariants_iff_isIntertwining`, read through `toLin`.

The delta `S.delta c = ∑ μ, e^μ ⊗ e_μ` is the tensor of the identity map, `u^μ δ_μ^ν = u^ν`. The
identity commutes with every group element, so the delta is invariant. `S.deltaTensor c` is the
delta as a tensor on two indices, and its components form the identity matrix.

Contracting the inner indices of two tensors on two indices, `M^μ_ν N^ν_ρ`, applies the linear map
of `N` to the second factor of `M`, and the result is the delta exactly when the two linear maps
are inverse. More generally, contracting an index of any tensor with the first index of a tensor
`F` on two indices applies the linear map of `F` at that index, and for the delta this is the
identity.

## ii. Key results

- `Species.toLin` : `V a ⊗ U` as the linear maps `V a.dual → U`, with
  `Species.isIntertwiningMap_toLin_iff` : `z` is invariant exactly when its linear map commutes
  with the group action.
- `Species.delta` : the delta `δ_μ^ν`, with `Species.delta_invariant` : it is invariant.
- `Species.deltaTensor` : the delta as a tensor on two indices, with
  `Species.tensorBasis_repr_deltaTensor_eq_one` : its components form the identity matrix.
- `Tensor.contr_matMul` : the contraction `M^μ_ν N^ν_ρ`, the case `i = 1` of `contr_matMulAt`, and
  `Tensor.contr_matMul_eq_deltaTensor_iff` : it is the delta exactly when the linear maps
  of `M` and `N` are inverse.
- `Tensor.contr_matMulAt` : contracting the index `i` with the first index of `F` applies
  `F` at `i`, and `Tensor.contr_deltaTensor` : for the delta this is
  `T^…μ… δ_μ^ν = T^…ν…`.

## iii. Table of contents

- A. Choices of pairs for products with a tensor on two indices
- B. Tensors of two factors as linear maps
- C. The delta
- D. Products with a tensor on two indices

## iv. References

* None.

-/

@[expose] public section

open TensorProduct

namespace Tensor

/-!

## A. Choices of pairs for products with a tensor on two indices

-/

namespace ColorEquiv

variable {K ι₁ : Type}

/-- The reindexing of `T^…μ… F_μ^ν`, which contracts the index `i` of `T` with the first index of a
tensor `F` on two indices and puts the second index of `F` in the place of `i`. -/
def matMulAt [DecidableEq ι₁] {c c' : ι₁ → Color K} (i : ι₁)
    (a b : Color K) (ha : c i = a) (hi : c' i = b) (h : ∀ x, x ≠ i → c x = c' x) :
    ColorEquiv (prodColors c ![a.dual, b]) (contrColors c' fun _ : Unit => a) where
  toEquiv :=
    { toFun := Sum.elim (fun x => if x = i then .inr (.inl ()) else .inl x)
        (fun j => if j = 0 then .inr (.inr ()) else .inl i)
      invFun := Sum.elim (fun x => if x = i then .inr 1 else .inl x)
        (Sum.elim (fun _ => .inl i) fun _ => .inr 0)
      left_inv := by
        rintro (x | j)
        · by_cases hx : x = i <;> simp [hx]
        · fin_cases j <;> simp
      right_inv := by
        rintro (x | (⟨⟩ | ⟨⟩))
        · by_cases hx : x = i <;> simp [hx]
        · simp
        · simp }
  color_eq := by
    rintro (x | (⟨⟩ | ⟨⟩))
    · by_cases hx : x = i
      · subst hx
        simp [hi]
      · simp [hx, h x hx]
    · simp [ha]
    · simp

/-- The reindexing of the product `M^μ_ν N^ν_ρ` of two tensors on two indices that contracts the
second index of `M`, of color `c`, with the first index of `N`. The free indices `μ` and `ρ` are
`0` and `1`. It is `matMulAt` at the index `1`. -/
def matMul (a c b : Color K) :
    ColorEquiv (prodColors ![a, c] ![c.dual, b]) (contrColors ![a, b] fun _ : Unit => c) :=
  matMulAt (c := ![a, c]) (c' := ![a, b]) 1 c b rfl rfl fun x hx => by fin_cases x <;> simp_all

end ColorEquiv

variable {k : Type} [RCLike k] {G : Type} [Group G] {K : Type} {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] (S : Species k G K basisIdx)

namespace Species

/-!

## B. Tensors of two factors as linear maps

-/

/-- An element `z` of `V a ⊗ U` as the linear map `V a.dual → U` that contracts a vector with the
first factor of `z`. For a lower color `a` and `z = g` in `V a ⊗ V a` it is `v^μ ↦ v^μ g_μν`.
Every linear map arises so. -/
noncomputable abbrev toLin {a : Color K} {U : Type} [AddCommGroup U] [Module k U] :
    S.V a ⊗[k] U ≃ₗ[k] (S.V a.dual →ₗ[k] U) :=
  (S.basis a).coordTensorHomEquiv (S.basis a.dual)

/-- The coordinate pairing of the bases of `c` and `c.dual` is the contraction. -/
@[simp]
lemma coordPairing_basis (c : Color K) {x : S.V c} {y : S.V c.dual} :
    (S.basis c).coordPairing (S.basis c.dual) (x ⊗ₜ y) = S.contr c (x ⊗ₜ y) :=
  rfl

/-- The coordinate pairing of the bases of `c.dual` and `c` is the contraction at `c.dual`. -/
@[simp]
lemma coordPairing_basis_dual (c : Color K) {x : S.V c.dual} {y : S.V c} :
    (S.basis c.dual).coordPairing (S.basis c) (x ⊗ₜ y) = S.contr c.dual (x ⊗ₜ y) :=
  rfl

/-- A tensor is invariant exactly when its linear map commutes with the group action. -/
lemma isIntertwiningMap_toLin_iff {a b : Color K} (z : S.V a ⊗[k] S.V b) :
    (S.rep a.dual).IsIntertwiningMap (S.rep b) (S.toLin z) ↔
      ∀ g, TensorProduct.map (S.rep a g) (S.rep b g) z = z :=
  Module.Basis.isIntertwiningMap_coordTensorHomEquiv_iff (S.invariant a) z

variable {S} in
/-- The coordinate pairing of the bases of the spaces of `c.dual` and `c` is that of the bases of
`S`. -/
lemma coordPairing_spaceBasis_dual (c : Color K) (x : S.colored.V c.dual) (y : S.colored.V c) :
    (S.colored.basis c.dual).coordPairing (S.colored.basis c) (x ⊗ₜ y) =
      (S.basis c.dual).coordPairing (S.basis c) (x.toV ⊗ₜ y.toV) := by
  simp only [Module.Basis.coordPairing_tmul, Module.Basis.equivFun_apply, colored_basis_repr]

/-- The linear map of an element of `V a ⊗ V b` moved to the spaces is its linear map on the
underlying vectors. -/
lemma colored_toLin_tprodCongr {a b : Color K} (z : S.V a ⊗[k] S.V b) :
    S.colored.toLin ((S.coloredEquiv a).tprodCongr (S.coloredEquiv b) z) =
      (S.coloredEquiv b).toLinearMap ∘ₗ S.toLin z ∘ₗ
        (S.coloredEquiv a.dual).symm.toLinearMap := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, LinearMap.add_comp, LinearMap.comp_add]
  | tmul x y =>
    refine LinearMap.ext fun v => ColoredSpace.toV_injective ?_
    simp only [Representation.Equiv.tprodCongr_tmul, Module.Basis.coordTensorHomEquiv_tmul,
      coordPairing_spaceBasis_dual]
    rfl

/-!

## C. The delta

-/

/-- The Kronecker delta `∑ μ, e^μ ⊗ e_μ ∈ V c.dual ⊗ V c`, with components `δ_μ^ν`. The factor of
the dual color is first. -/
noncomputable abbrev delta (c : Color K) : S.V c.dual ⊗[k] S.V c :=
  (S.basis c.dual).coordDelta (S.basis c)

/-- The delta is invariant, `Λ δ = δ`, with `Λ` acting on both factors. -/
lemma delta_invariant (c : Color K) (g : G) :
    TensorProduct.map (S.rep c.dual g) (S.rep c g) (S.delta c) = S.delta c :=
  Module.Basis.coordDelta_invariant (S.invariant c.dual) g

variable {S}

variable (S) in
/-- The delta `S.delta c` as a tensor with colors `![c.dual, c]`. It is `δ_μ^ν` for an upper
color `c` and `δ^μ_ν` for a lower one. -/
noncomputable def deltaTensor (c : Color K) : Tensor S ![c.dual, c] :=
  S.twoIndexEquiv c.dual c (S.colored.delta c)

/-- The delta tensor is invariant, `Λ δ = δ`. -/
lemma deltaTensor_invariant (c : Color K) (Λ : G) : Λ • S.deltaTensor c = S.deltaTensor c :=
  (S.twoIndexEquiv _ c).toIntertwiningMap.map_invariant (S.colored.delta_invariant c Λ)

/-- The components of the delta tensor are the coordinates of `S.delta c` in Mathlib's product
basis, at the pair of labels `(μ 0, μ 1)`. -/
lemma tensorBasis_repr_deltaTensor (c : Color K) (μ : Π j, basisIdx (![c.dual, c] j).kind) :
    (S.tensorBasis ![c.dual, c]).repr (S.deltaTensor c) μ =
      ((S.colored.basis c.dual).tensorProduct (S.colored.basis c)).repr (S.colored.delta c) (μ 0, μ 1) :=
  tensorBasis_repr_twoIndexEquiv _ _ _ μ

/-- The components of the delta tensor form the identity matrix, `δ_μ^ν = 1` for `μ = ν` and `0`
otherwise. -/
lemma tensorBasis_repr_deltaTensor_eq_one (c : Color K)
    (μ : Π j, basisIdx (![c.dual, c] j).kind) :
    (S.tensorBasis ![c.dual, c]).repr (S.deltaTensor c) μ =
      (1 : Matrix (basisIdx c.kind) (basisIdx c.kind) k) (μ 0) (μ 1) :=
  (tensorBasis_repr_deltaTensor c μ).trans
    ((Module.Basis.tensorProduct_repr_coordDelta _ _ _ _).trans Matrix.one_apply.symm)

end Species

open Species PiTensorProduct

variable {S}

variable {ι₁ κ : Type} {c : ι₁ → Color K} {c' : κ → Color K}

/-!

## D. Products with a tensor on two indices

Contracting an index with a tensor `F` on two indices applies the linear map of `F` at that index.
This map commutes with the group only when `F` is invariant, so it is the linear map
`linearMapAt`, Mathlib's `PiTensorProduct.map` of `indexMapsAt`. For an intertwining map `f`,
`(intertwiningMapAt i f h).toLinearMap` is `linearMapAt i f.toLinearMap h` by `rfl`.

-/

namespace Species

variable [DecidableEq ι₁]

variable (S) in
/-- The linear map `f` at the index `i` and `S.colored.cast (h x _)` at every other index `x`,
`u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. -/
noncomputable def linearMapAt {c c' : ι₁ → Color K} (i : ι₁)
    (f : S.colored.V (c i) →ₗ[k] S.colored.V (c' i)) (h : ∀ x, x ≠ i → c x = c' x) :
    Tensor S c →ₗ[k] Tensor S c' :=
  PiTensorProduct.map (S.indexMapsAt i f h)

/-- The linear map of `intertwiningMapAt` is `linearMapAt`. -/
lemma toLinearMap_intertwiningMapAt {c c' : ι₁ → Color K} (i : ι₁)
    (f : (S.colored.rep (c i)).IntertwiningMap (S.colored.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) :
    (S.intertwiningMapAt i f h).toLinearMap = S.linearMapAt i f.toLinearMap h := rfl

/-- On a pure tensor, `linearMapAt` applies `f` to the vector at `i` and keeps the others. -/
lemma linearMapAt_pure {c c' : ι₁ → Color K} (i : ι₁)
    (f : S.colored.V (c i) →ₗ[k] S.colored.V (c' i)) (h : ∀ x, x ≠ i → c x = c' x)
    (p : Π x, S.colored.V (c x)) (q : Π x, S.colored.V (c' x)) (hqi : q i = f (p i))
    (hq : ∀ x (hx : x ≠ i), q x = S.colored.cast (h x hx) (p x)) :
    S.linearMapAt i f h (S.pure p) = S.pure q := by
  refine (map_pure (S.indexMapsAt i f h) p).trans (congrArg S.pure (funext fun x => ?_))
  by_cases hx : x = i
  · subst hx
    rw [indexMapsAt_apply_self, hqi]
  · rw [indexMapsAt_apply_ne _ _ _ hx, hq x hx]
    rfl

/-- `linearMapAt` of the identity is the identity. -/
lemma linearMapAt_id {c : ι₁ → Color K} (i : ι₁) (h : ∀ x, x ≠ i → c x = c x) :
    S.linearMapAt i LinearMap.id h = LinearMap.id :=
  ext_pure fun p => linearMapAt_pure i _ h p p rfl fun _ _ => rfl

/-- A linear map `f` at the index `1` of the tensor of `M` in `V a ⊗ V c` is `f` on the second
factor of `M`, `M^μν ↦ M^μρ f_ρ^ν`. -/
lemma linearMapAt_one_twoIndexEquiv (a c b : Color K) (f : S.colored.V c →ₗ[k] S.colored.V b) (M : S.colored.V a ⊗[k] S.colored.V c)
    (h : ∀ x, x ≠ (1 : Fin 2) → (![a, c] : Fin 2 → Color K) x = (![a, b] : Fin 2 → Color K) x) :
    S.linearMapAt (c := ![a, c]) (c' := ![a, b]) 1 f h (S.twoIndexEquiv a c M) =
      S.twoIndexEquiv a b (f.lTensor _ M) := by
  induction M using TensorProduct.inductionOn with
  | add M M' hM hM' => simp only [map_add, hM, hM']
  | tmul m₁ m₂ =>
    rw [twoIndexEquiv_tmul, LinearMap.lTensor_tmul, twoIndexEquiv_tmul]
    refine linearMapAt_pure (c := ![a, c]) (c' := ![a, b]) 1 f h _ _ rfl fun x hx => ?_
    fin_cases x
    · rfl
    · exact absurd rfl hx

end Species

/-- On a pure tensor, contracting the index `i` with the first index of `F` applies `F`, read as a
linear map by `Species.toLin`, to the vector at `i`. The vectors `q` at the other indices are
those of `p`, moved along `h`. -/
lemma contr_matMulAt_pure [DecidableEq ι₁] {c c' : ι₁ → Color K} (i : ι₁) (a b : Color K)
    (ha : c i = a) (hi : c' i = b) (h : ∀ x, x ≠ i → c x = c' x) (F : S.colored.V a.dual ⊗[k] S.colored.V b)
    (p : Π x, S.colored.V (c x)) (q : Π x, S.colored.V (c' x))
    (hq : ∀ x (hx : x ≠ i), q x = S.colored.cast (h x hx) (p x)) :
    contr (ColorEquiv.matMulAt i a b ha hi h)
        (S.tmulEquiv c ![a.dual, b] (S.pure p ⊗ₜ S.twoIndexEquiv a.dual b F)) =
      S.pure (Function.update q i (S.colored.cast hi.symm (S.colored.toLin F (S.colored.cast ha (p i))))) := by
  induction F using TensorProduct.inductionOn with
  | add F F' hF hF' =>
    simp only [map_add, LinearMap.add_apply, tmul_add, hF, hF']
    exact ((PiTensorProduct.tprod k).map_update_add q i _ _).symm
  | tmul x y =>
    rw [Module.Basis.coordTensorHomEquiv_tmul, S.colored.coordPairing_basis, map_smul]
    conv_rhs => rw [Species.pure, MultilinearMap.map_update_smul, ← Species.pure]
    rw [twoIndexEquiv_tmul, tmulEquiv_pure, contr_pure, Fintype.prod_unique]
    congr 2
    funext z
    by_cases hz : z = i
    · subst hz
      rw [Function.update_self, cast_apply_congr _ (show
        (ColorEquiv.matMulAt z a b ha hi h).toEquiv.symm (.inl z) = .inr 1 by
          simp [ColorEquiv.matMulAt])]
      rfl
    · rw [Function.update_of_ne hz, cast_apply_congr _ (show
        (ColorEquiv.matMulAt i a b ha hi h).toEquiv.symm (.inl z) = .inl z by
          simp [ColorEquiv.matMulAt, hz]), hq z hz]

/-- Contracting the index `i` of `t` with the first index of a tensor `F` on two indices applies
`F`, read as a linear map by `Species.toLin`, at `i`, as in `T^…μ… F_μ^ν`. -/
lemma contr_matMulAt [DecidableEq ι₁] {c c' : ι₁ → Color K} (i : ι₁) (a b : Color K)
    (ha : c i = a) (hi : c' i = b) (h : ∀ x, x ≠ i → c x = c' x) (F : S.colored.V a.dual ⊗[k] S.colored.V b)
    (t : Tensor S c) :
    contr (ColorEquiv.matMulAt i a b ha hi h)
        (S.tmulEquiv c ![a.dual, b] (t ⊗ₜ S.twoIndexEquiv a.dual b F)) =
      S.linearMapAt i ((S.colored.cast hi.symm).toLinearMap ∘ₗ S.colored.toLin F ∘ₗ (S.colored.cast ha).toLinearMap) h t := by
  refine LinearMap.congr_fun (f := (contr _).toLinearMap ∘ₗ (S.tmulEquiv c ![a.dual, b]).toLinearMap
    ∘ₗ (TensorProduct.mk k _ _).flip (S.twoIndexEquiv a.dual b F)) (ext_pure fun p => ?_) t
  -- The vectors of `p` moved along `h` away from `i`. The vector at `i` is replaced below.
  let q : Π x, S.colored.V (c' x) := fun x => if hx : x = i then 0 else S.colored.cast (h x hx) (p x)
  exact (contr_matMulAt_pure i a b ha hi h F p q (fun x hx => by simp [q, hx])).trans
    (linearMapAt_pure i _ h p (Function.update q i (S.colored.cast hi.symm (S.colored.toLin F (S.colored.cast ha (p i)))))
      (Function.update_self _ _ _) (fun x hx => by simp [q, hx])).symm

/-- The contraction `M^μ_ν N^ν_ρ` of two tensors on two indices is `M` with its second factor mapped
by `S.toLin N`, the linear map `v_ν ↦ v_ν N^ν_ρ`. -/
lemma contr_matMul (a c b : Color K) (M : S.colored.V a ⊗[k] S.colored.V c) (N : S.colored.V c.dual ⊗[k] S.colored.V b) :
    contr (ColorEquiv.matMul a c b)
        (S.tmulEquiv _ _ (S.twoIndexEquiv a c M ⊗ₜ S.twoIndexEquiv _ b N)) =
      S.twoIndexEquiv a b ((S.colored.toLin N).lTensor _ M) :=
  (contr_matMulAt (S := S) (c := ![a, c]) (c' := ![a, b]) 1 c b rfl rfl
    (fun x hx => by fin_cases x <;> simp_all) N (S.twoIndexEquiv a c M)).trans
    (linearMapAt_one_twoIndexEquiv a c b (S.colored.toLin N) M _)

/-- Two tensors on two indices contract to the delta, `X_μν Y^νρ = δ_μ^ρ`, exactly when their linear
maps compose to the identity, `Y ∘ X = id`. -/
lemma contr_matMul_eq_deltaTensor_iff {x y : Color K} (X : S.colored.V x ⊗[k] S.colored.V y)
    (Y : S.colored.V y.dual ⊗[k] S.colored.V x.dual) :
    contr (ColorEquiv.matMul x y x.dual)
        (S.tmulEquiv _ _ (S.twoIndexEquiv x y X ⊗ₜ S.twoIndexEquiv _ _ Y)) = S.deltaTensor x.dual ↔
      S.colored.toLin Y ∘ₗ S.colored.toLin X = LinearMap.id := by
  rw [deltaTensor, contr_matMul, (EquivLike.injective (S.twoIndexEquiv _ _)).eq_iff,
    ← (S.colored.toLin (a := x)).injective.eq_iff, Module.Basis.coordTensorHomEquiv_lTensor,
    Module.Basis.coordTensorHomEquiv_coordDelta]

/-- Contracting the index `i` with the first index of the delta is the identity,
`T^…μ… δ_μ^ν = T^…ν…`. -/
lemma contr_deltaTensor [DecidableEq ι₁] {c : ι₁ → Color K} (i : ι₁) (a : Color K) (ha : c i = a)
    (t : Tensor S c) :
    contr (ColorEquiv.matMulAt i a a ha ha fun _ _ => rfl)
      (S.tmulEquiv c ![a.dual, a] (t ⊗ₜ S.deltaTensor a)) = t := by
  subst ha
  rw [deltaTensor, contr_matMulAt, Module.Basis.coordTensorHomEquiv_coordDelta]
  exact LinearMap.congr_fun (linearMapAt_id i _) t

/-- Contracting the index `i` with the second index of the delta is the identity,
`δ^ν_μ T^…μ… = T^…ν…`. -/
lemma contr_deltaTensor_swap [DecidableEq ι₁] {c : ι₁ → Color K} (i : ι₁) (a : Color K)
    (ha : c i = a) (t : Tensor S c) :
    contr (ColorEquiv.matMulAt i a a ha ha fun _ _ => rfl)
      (S.tmulEquiv c ![a.dual, a]
        (t ⊗ₜ S.reindex (ColorEquiv.swapTwo a a.dual) (S.deltaTensor a.dual))) = t := by
  rw [deltaTensor, reindex_swapTwo_twoIndexEquiv,
    show TensorProduct.comm k _ _ (S.colored.delta a.dual) = S.colored.delta a from
      Module.Basis.comm_coordDelta _ _]
  exact contr_deltaTensor i a ha t

end Tensor
