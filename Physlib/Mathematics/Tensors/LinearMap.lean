/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.RepresentationTheory.Invariants
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
exactly one `z`. `toLin` is Mathlib's `dualTensorHomEquiv` once the contraction identifies `V a`
with the dual of `V a.dual`. In a basis `toLin z` has the components
`(z v)^ν = ∑ μ, v_μ z^μν` (`Species.repr_toLin`).

This is how two-index tensors act as maps. A metric `g_μν` is the map `v^μ ↦ v^μ g_μν`, and the
inverse metric `g^μν` is the tensor of the inverse map. The map of `Λz` is `Λ ∘ z ∘ Λ⁻¹`, so `z` is
invariant exactly when its linear map commutes with the group action
(`Species.toLin_map_rep`). This is Mathlib's
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
- `Species.mapIndices` and `Species.linearMapAt` : linear maps at every index and at one index.
- `Tensor.contr_matMulAt` : contracting the index `i` with the first index of `F` applies
  `F` at `i`, and `Tensor.contr_deltaTensor` : for the delta this is
  `T^…μ… δ_μ^ν = T^…ν…`.

## iii. Table of contents

- A. Choices of pairs for products with a tensor on two indices
- B. Tensors of two factors as linear maps
- C. The delta
  - C.1. In coordinates
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

variable {k : Type} [RCLike k] {G : Type} [Group G] {K : Type} (S : Species k G K)

namespace Species

/-!

## B. Tensors of two factors as linear maps

-/

/-- An element `z` of `V a ⊗ U` as the linear map `V a.dual → U` that contracts a vector with the
first factor of `z`. For a lower color `a` and `z = g` in `V a ⊗ V a` it is `v^μ ↦ v^μ g_μν`.
Every linear map arises so. It is Mathlib's `dualTensorHomEquiv`, after the contraction identifies
`V a` with the dual of `V a.dual`. -/
noncomputable def toLin {a : Color K} {U : Type} [AddCommGroup U] [Module k U] :
    S.V a ⊗[k] U ≃ₗ[k] (S.V a.dual →ₗ[k] U) :=
  (TensorProduct.congr (S.dualEquiv a.dual).toLinearEquiv (LinearEquiv.refl k U)).trans
    (dualTensorHomEquiv k (S.V a.dual) U)

/-- A pure tensor `x ⊗ y` acts as `v ↦ (v^μ x_μ) y`. -/
@[simp]
lemma toLin_tmul {a : Color K} {U : Type} [AddCommGroup U] [Module k U] (x : S.V a) (y : U)
    (v : S.V a.dual) :
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _
      (@DFunLike.coe (no_index _) (no_index _) (no_index _) _ S.toLin (no_index (x ⊗ₜ y))) v =
        S.contr a.dual (v ⊗ₜ x) • y :=
  rfl

/-- Applying `f` to the second factor composes with `f`, `(id ⊗ f) z = f ∘ z`. -/
lemma toLin_lTensor {a : Color K} {U U' : Type} [AddCommGroup U] [Module k U] [AddCommGroup U']
    [Module k U'] (f : U →ₗ[k] U') (z : S.V a ⊗[k] U) :
    S.toLin (f.lTensor _ z) = f ∘ₗ S.toLin z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => ext v; simp
  | add z z' hz hz' => simp only [map_add, hz, hz', LinearMap.comp_add]

/-- The linear map of `(Λ ⊗ f) z` is `f ∘ z ∘ Λ⁻¹`. -/
lemma toLin_map_rep {a : Color K} {U U' : Type} [AddCommGroup U] [Module k U] [AddCommGroup U']
    [Module k U'] (f : U →ₗ[k] U') (z : S.V a ⊗[k] U) (g : G) :
    S.toLin (TensorProduct.map (S.rep a g) f z) = f ∘ₗ S.toLin z ∘ₗ S.rep a.dual g⁻¹ := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz', LinearMap.add_comp, LinearMap.comp_add]
  | tmul x y =>
    ext v
    simp only [TensorProduct.map_tmul, toLin_tmul, LinearMap.comp_apply, map_smul]
    rw [S.contr_tmul_rep a.dual g v x]

/-- A tensor is invariant exactly when its linear map commutes with the group action. -/
lemma isIntertwiningMap_toLin_iff {a b : Color K} (z : S.V a ⊗[k] S.V b) :
    (S.rep a.dual).IsIntertwiningMap (S.rep b) (S.toLin z) ↔
      ∀ g, TensorProduct.map (S.rep a g) (S.rep b g) z = z := by
  rw [← Representation.mem_linHom_invariants_iff_isIntertwining]
  exact forall_congr' fun g => by
    rw [← S.toLin.injective.eq_iff, toLin_map_rep]

/-- Swapping the factors of `z` transposes its linear map,
`v_μ (comm z)^μ_ν u^ν = u^ν z_ν^μ v_μ`. -/
lemma contr_toLin_comm {a b : Color K} (z : S.V a ⊗[k] S.V b) (u : S.V b.dual)
    (v : S.V a.dual) :
    S.contr a.dual (v ⊗ₜ S.toLin (TensorProduct.comm k _ _ z) u) =
      S.contr b.dual (u ⊗ₜ S.toLin z v) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, tmul_add, hz, hz']
  | tmul x y =>
    simp only [TensorProduct.comm_tmul, toLin_tmul, tmul_smul, map_smul, smul_eq_mul]
    exact mul_comm _ _

/-!

## C. The delta

-/

/-- The Kronecker delta `δ_μ^ν ∈ V c.dual ⊗ V c`, the tensor of the identity map. The factor of
the dual color is first. -/
noncomputable abbrev delta (c : Color K) : S.V c.dual ⊗[k] S.V c :=
  S.toLin.symm LinearMap.id

/-- The delta read as a linear map is the identity, `u^μ δ_μ^ν = u^ν`. -/
@[simp]
lemma toLin_delta (c : Color K) :
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.toLin (U := no_index _))
      (no_index (S.delta c)) = LinearMap.id :=
  S.toLin.apply_symm_apply _

/-- The delta is invariant, `Λ δ = δ`, with `Λ` acting on both factors. -/
lemma delta_invariant (c : Color K) (g : G) :
    TensorProduct.map (S.rep c.dual g) (S.rep c g) (S.delta c) = S.delta c :=
  (S.isIntertwiningMap_toLin_iff (S.delta c)).1
    (by rw [toLin_delta]; exact ⟨fun _ _ => rfl⟩) g

/-- Swapping the factors of the delta at `c.dual` gives the delta at `c`. -/
lemma comm_delta (c : Color K) :
    TensorProduct.comm k _ _ (S.delta c.dual) = S.delta c := by
  refine S.toLin.injective (LinearMap.ext fun u => ext_contr (c := c.dual) fun v => ?_)
  rw [contr_toLin_comm, toLin_delta, LinearMap.id_apply]
  -- `toLin` of the delta at `c.dual` is the identity, with `c.dual.dual` read as `c`.
  exact (congrArg (fun w => S.contr c (u ⊗ₜ w))
    (LinearMap.congr_fun (S.toLin_delta c.dual) v)).trans
    (S.contr_tmul_symm c u v)

variable {S}

variable (S) in
/-- The delta `S.delta c` as a tensor with colors `![c.dual, c]`. It is `δ_μ^ν` for an upper
color `c` and `δ^μ_ν` for a lower one. -/
noncomputable def deltaTensor (c : Color K) : Tensor S ![c.dual, c] :=
  S.twoIndexEquiv c.dual c (S.delta c)

/-- The delta tensor is invariant, `Λ δ = δ`. -/
lemma deltaTensor_invariant (c : Color K) (Λ : G) : Λ • S.deltaTensor c = S.deltaTensor c :=
  (S.twoIndexEquiv _ c).toIntertwiningMap.map_invariant (S.delta_invariant c Λ)

/-!

### C.1. In coordinates

-/

variable {basisIdx : K → Type} [B : S.HasBasis basisIdx] [∀ κ, Fintype (basisIdx κ)]
  [∀ κ, DecidableEq (basisIdx κ)]

variable (S) in
/-- The linear map of `z` in components, `(z v)^ν = ∑ μ, v_μ z^μν`, with `d` a basis of `U`. -/
lemma repr_toLin {a : Color K} {U ι : Type} [AddCommGroup U] [Module k U]
    (d : Module.Basis ι k U) (z : S.V a ⊗[k] U) (v : S.V a.dual) (ν : ι) :
    d.repr (S.toLin z v) ν =
      ∑ μ, (S.basis a.dual).repr v μ * ((S.basis a).tensorProduct d).repr z (μ, ν) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [hz, hz', mul_add, Finset.sum_add_distrib]
  | tmul x y =>
    rw [toLin_tmul, ← S.contr_tmul_symm a x v, contr_tmul_eq_sum_basis, map_smul,
      Finsupp.smul_apply, smul_eq_mul, Finset.sum_mul]
    simp only [Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun μ _ => by ring

/-- In a basis the delta is `∑ μ, e^μ ⊗ e_μ`. -/
lemma delta_eq_sum_basis (c : Color K) :
    S.delta c = ∑ μ, S.basis c.dual μ ⊗ₜ S.basis c μ :=
  S.toLin.injective <| by
    rw [toLin_delta]
    refine (S.basis c).ext fun ν => ?_
    have h (μ) : S.contr c.dual.dual (S.basis c ν ⊗ₜ S.basis c.dual μ) = if ν = μ then 1 else 0 :=
      S.contr_basis c ν μ
    simp only [map_sum, LinearMap.sum_apply, toLin_tmul, LinearMap.id_apply, h,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The components of the delta tensor are the coordinates of `S.delta c` in Mathlib's product
basis, at the pair of labels `(μ 0, μ 1)`. -/
lemma tensorBasis_repr_deltaTensor (c : Color K) (μ : Π j, basisIdx (![c.dual, c] j).kind) :
    (S.tensorBasis ![c.dual, c]).repr (S.deltaTensor c) μ =
      ((S.basis c.dual).tensorProduct (S.basis c)).repr (S.delta c)
        (μ 0, μ 1) :=
  tensorBasis_repr_twoIndexEquiv _ _ _ μ

/-- The components of the delta tensor form the identity matrix, `δ_μ^ν = 1` for `μ = ν` and `0`
otherwise. -/
lemma tensorBasis_repr_deltaTensor_eq_one (c : Color K)
    (μ : Π j, basisIdx (![c.dual, c] j).kind) :
    (S.tensorBasis ![c.dual, c]).repr (S.deltaTensor c) μ =
      (1 : Matrix (basisIdx c.kind) (basisIdx c.kind) k) (μ 0) (μ 1) := by
  rw [tensorBasis_repr_deltaTensor, delta_eq_sum_basis]
  have h (ν ρ : basisIdx c.kind) : ((S.basis c.dual).tensorProduct (S.basis c)).repr
      (∑ μ, S.basis c.dual μ ⊗ₜ S.basis c μ) (ν, ρ) = (1 : Matrix _ _ k) ν ρ := by
    simp [Finsupp.single_apply, Matrix.one_apply]
  exact h (μ 0) (μ 1)

end Species

open Species PiTensorProduct

variable {S}

variable {ι₁ κ : Type} {c : ι₁ → Color K} {c' : κ → Color K}

/-!

## D. Products with a tensor on two indices

Contracting an index with a tensor `F` on two indices applies the linear map of `F` at that index.
This map commutes with the group only when `F` is invariant, so it is the linear map
`linearMapAt`, `mapIndices` of `indexMapsAt`. For an intertwining map `f`,
`(intertwiningMapAt i f h).toLinearMap` is `linearMapAt i f.toLinearMap h` by `rfl`.

-/

namespace Species

variable (S) in
/-- A linear map `f x` at every index `x`, `u ⊗ v ↦ f₀ u ⊗ f₁ v`, Mathlib's
`PiTensorProduct.map`. -/
noncomputable def mapIndices {c c' : ι₁ → Color K}
    (f : Π x, S.V (c x) →ₗ[k] S.V (c' x)) : Tensor S c →ₗ[k] Tensor S c' :=
  PiTensorProduct.map f

/-- Two index-wise maps in sequence are the index-wise map of the composites. -/
lemma mapIndices_mapIndices {c c' c'' : ι₁ → Color K}
    (f : Π x, S.V (c x) →ₗ[k] S.V (c' x))
    (g : Π x, S.V (c' x) →ₗ[k] S.V (c'' x)) (t : Tensor S c) :
    S.mapIndices g (S.mapIndices f t) = S.mapIndices (fun x => g x ∘ₗ f x) t :=
  LinearMap.congr_fun (PiTensorProduct.map_comp g f).symm t

/-- The index-wise map of the identities is the identity. -/
lemma mapIndices_id_apply {c : ι₁ → Color K} (t : Tensor S c) :
    S.mapIndices (fun _ => LinearMap.id) t = t :=
  LinearMap.congr_fun PiTensorProduct.map_id t

variable [DecidableEq ι₁]

variable (S) in
/-- The linear map `f` at the index `i` and `S.cast (h x _)` at every other index `x`,
`u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. -/
noncomputable def linearMapAt {c c' : ι₁ → Color K} (i : ι₁)
    (f : S.V (c i) →ₗ[k] S.V (c' i)) (h : ∀ x, x ≠ i → c x = c' x) :
    Tensor S c →ₗ[k] Tensor S c' :=
  S.mapIndices (S.indexMapsAt i f h)

/-- The linear map of `intertwiningMapAt` is `linearMapAt`. -/
lemma toLinearMap_intertwiningMapAt {c c' : ι₁ → Color K} (i : ι₁)
    (f : (S.rep (c i)).IntertwiningMap (S.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) :
    (S.intertwiningMapAt i f h).toLinearMap = S.linearMapAt i f.toLinearMap h := rfl

/-- On a pure tensor, `linearMapAt` applies `f` to the vector at `i` and keeps the others. -/
lemma linearMapAt_pure {c c' : ι₁ → Color K} (i : ι₁)
    (f : S.V (c i) →ₗ[k] S.V (c' i)) (h : ∀ x, x ≠ i → c x = c' x)
    (p : Π x, S.V (c x)) (q : Π x, S.V (c' x)) (hqi : q i = f (p i))
    (hq : ∀ x (hx : x ≠ i), q x = S.cast (h x hx) (p x)) :
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
lemma linearMapAt_one_twoIndexEquiv (a c b : Color K) (f : S.V c →ₗ[k] S.V b)
    (M : S.V a ⊗[k] S.V c)
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
    (ha : c i = a) (hi : c' i = b) (h : ∀ x, x ≠ i → c x = c' x)
    (F : S.V a.dual ⊗[k] S.V b)
    (p : Π x, S.V (c x)) (q : Π x, S.V (c' x))
    (hq : ∀ x (hx : x ≠ i), q x = S.cast (h x hx) (p x)) :
    contr (ColorEquiv.matMulAt i a b ha hi h)
        (S.tmulEquiv c ![a.dual, b] (S.pure p ⊗ₜ S.twoIndexEquiv a.dual b F)) =
      S.pure (Function.update q i
        (S.cast hi.symm (S.toLin F (S.cast ha (p i))))) := by
  induction F using TensorProduct.inductionOn with
  | add F F' hF hF' =>
    simp only [map_add, LinearMap.add_apply, tmul_add, hF, hF']
    exact ((PiTensorProduct.tprod k).map_update_add q i _ _).symm
  | tmul x y =>
    rw [toLin_tmul, map_smul]
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
    (ha : c i = a) (hi : c' i = b) (h : ∀ x, x ≠ i → c x = c' x)
    (F : S.V a.dual ⊗[k] S.V b)
    (t : Tensor S c) :
    contr (ColorEquiv.matMulAt i a b ha hi h)
        (S.tmulEquiv c ![a.dual, b] (t ⊗ₜ S.twoIndexEquiv a.dual b F)) =
      S.linearMapAt i ((S.cast hi.symm).toLinearMap ∘ₗ S.toLin F ∘ₗ
        (S.cast ha).toLinearMap) h t := by
  refine LinearMap.congr_fun (f := (contr _).toLinearMap ∘ₗ (S.tmulEquiv c ![a.dual, b]).toLinearMap
    ∘ₗ (TensorProduct.mk k _ _).flip (S.twoIndexEquiv a.dual b F)) (ext_pure fun p => ?_) t
  -- The vectors of `p` moved along `h` away from `i`. The vector at `i` is replaced below.
  let q : Π x, S.V (c' x) := fun x =>
    if hx : x = i then 0 else S.cast (h x hx) (p x)
  exact (contr_matMulAt_pure i a b ha hi h F p q (fun x hx => by simp [q, hx])).trans
    (linearMapAt_pure i _ h p (Function.update q i
      (S.cast hi.symm (S.toLin F (S.cast ha (p i)))))
      (Function.update_self _ _ _) (fun x hx => by simp [q, hx])).symm

/-- The contraction `M^μ_ν N^ν_ρ` of two tensors on two indices is `M` with its second factor mapped
by `S.toLin N`, the linear map `v_ν ↦ v_ν N^ν_ρ`. -/
lemma contr_matMul (a c b : Color K) (M : S.V a ⊗[k] S.V c)
    (N : S.V c.dual ⊗[k] S.V b) :
    contr (ColorEquiv.matMul a c b)
        (S.tmulEquiv _ _ (S.twoIndexEquiv a c M ⊗ₜ S.twoIndexEquiv _ b N)) =
      S.twoIndexEquiv a b ((S.toLin N).lTensor _ M) :=
  (contr_matMulAt (S := S) (c := ![a, c]) (c' := ![a, b]) 1 c b rfl rfl
    (fun x hx => by fin_cases x <;> simp_all) N (S.twoIndexEquiv a c M)).trans
    (linearMapAt_one_twoIndexEquiv a c b (S.toLin N) M _)

/-- Two tensors on two indices contract to the delta, `X_μν Y^νρ = δ_μ^ρ`, exactly when their linear
maps compose to the identity, `Y ∘ X = id`. -/
lemma contr_matMul_eq_deltaTensor_iff {x y : Color K} (X : S.V x ⊗[k] S.V y)
    (Y : S.V y.dual ⊗[k] S.V x.dual) :
    contr (ColorEquiv.matMul x y x.dual)
        (S.tmulEquiv _ _ (S.twoIndexEquiv x y X ⊗ₜ S.twoIndexEquiv _ _ Y)) = S.deltaTensor x.dual ↔
      S.toLin Y ∘ₗ S.toLin X = LinearMap.id := by
  rw [deltaTensor, contr_matMul, (EquivLike.injective (S.twoIndexEquiv _ _)).eq_iff,
    ← (S.toLin (a := x)).injective.eq_iff, toLin_lTensor,
    show S.toLin (a := x) (S.delta x.dual) = LinearMap.id from S.toLin_delta x.dual]

/-- Contracting the index `i` with the first index of the delta is the identity,
`T^…μ… δ_μ^ν = T^…ν…`. -/
lemma contr_deltaTensor [DecidableEq ι₁] {c : ι₁ → Color K} (i : ι₁) (a : Color K) (ha : c i = a)
    (t : Tensor S c) :
    contr (ColorEquiv.matMulAt i a a ha ha fun _ _ => rfl)
      (S.tmulEquiv c ![a.dual, a] (t ⊗ₜ S.deltaTensor a)) = t := by
  subst ha
  rw [deltaTensor, contr_matMulAt, toLin_delta]
  exact LinearMap.congr_fun (linearMapAt_id i _) t

/-- Contracting the index `i` with the second index of the delta is the identity,
`δ^ν_μ T^…μ… = T^…ν…`. -/
lemma contr_deltaTensor_swap [DecidableEq ι₁] {c : ι₁ → Color K} (i : ι₁) (a : Color K)
    (ha : c i = a) (t : Tensor S c) :
    contr (ColorEquiv.matMulAt i a a ha ha fun _ _ => rfl)
      (S.tmulEquiv c ![a.dual, a]
        (t ⊗ₜ S.reindex (ColorEquiv.swapTwo a a.dual) (S.deltaTensor a.dual))) = t := by
  rw [deltaTensor, reindex_swapTwo_twoIndexEquiv,
    S.comm_delta a]
  exact contr_deltaTensor i a ha t

end Tensor
