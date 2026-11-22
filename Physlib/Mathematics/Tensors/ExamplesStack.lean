/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Conjugation
public import Physlib.Mathematics.Tensors.Examples
public import Mathlib.Analysis.Complex.Basic

/-!

# Examples of the tensor operations

Tests of contraction, lowering and raising, and conjugation of colored tensors.

## i. Overview

Each test fails if its guarantee breaks. The colors `up` and `down` are those of `Examples.lean`.
The tests are:
- A. A species of an abstract representation, with no basis, has tensors, contraction, and
  lowering and raising with a form.
- B. Two bases of one species give the same contraction.
- C. `simp` and Mathlib's lemmas work on vectors and covectors of the operations at a written-out
  color, on a generic and on a concrete species.
- D. A self-conjugate kind whose antilinear map squares to `-1` is accepted.
- E. Lowering, raising and conjugation close by `simp` at each written-out color.

## ii. Key results

- `ofRep` : the species of an abstract finite-dimensional representation, with no basis.
- `piDef` : a species with the space `Fin 2 → ℝ`, as a def.
- `pseudoreal` : a species with one pseudoreal kind, `j x = ε x̄` with `j² = -1`.

## iii. Table of contents

- A. A species with no basis
  - A.1. Lowering and raising with no basis
- B. Two bases of one species
- C. A transparent space of a color
  - C.1. Automation on a generic species
  - C.2. Automation on a concrete species
- D. A pseudoreal kind
- E. `simp` at written-out colors
  - E.1. Lowering and raising
  - E.2. Conjugation, at the four colors of a kind and its conjugate

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

namespace Tensor.Examples

open Species TensorProduct

/-!

## A. A species with no basis

`ofRep ρ` is the species of an abstract finite-dimensional representation `ρ`, with no basis. Its
tensors, the group action on them and the contraction are defined. Its components are not.

-/

section ofRep

variable {k G W : Type} [RCLike k] [Group G] [AddCommGroup W] [Module k W] [Module.Finite k W]

/-- The species with one kind, the space `W` and the representation `ρ`, with no basis. -/
noncomputable def ofRep (ρ : Representation k G W) : Species k G Unit where
  W _ := W
  repW _ := ρ

variable (ρ : Representation k G W)

-- A tensor `T^μ_ν` of `ofRep ρ`, the group acting on it, and the contraction of a vector with a
-- covector, which is invariant.
noncomputable example (T : Tensor (ofRep ρ) ![up, down]) (g : G) (v : (ofRep ρ).V up)
    (α : (ofRep ρ).V down) :
    Tensor (ofRep ρ) ![up, down] × k × k :=
  (g • T, (ofRep ρ).contr up (v ⊗ₜ α), (ofRep ρ).contr up ((ofRep ρ).rep up g v ⊗ₜ α))

example (g : G) (v : (ofRep ρ).V up) (α : (ofRep ρ).V down) :
    (ofRep ρ).contr up ((ofRep ρ).rep up g v ⊗ₜ (ofRep ρ).rep down g α) =
      (ofRep ρ).contr up (v ⊗ₜ α) :=
  (ofRep ρ).contr_invariant up g v α

-- The contraction is a perfect pairing with no basis.
example (α α' : (ofRep ρ).V down) (h : ∀ u, (ofRep ρ).contr up (u ⊗ₜ α) =
    (ofRep ρ).contr up (u ⊗ₜ α')) : α = α' :=
  ext_contr h

-- `ofRep ρ` has no basis, so it has no components.
example (T : Tensor (ofRep ρ) ![up]) : Tensor (ofRep ρ) ![up] := by
  fail_if_success have := (ofRep ρ).tensorBasis ![up]
  exact T

/-- error: failed to synthesize instance of type class
  (ofRep ρ).HasBasis ?m -/
#guard_msgs (substring := true) in
noncomputable example : Module.Basis _ k (Tensor (ofRep ρ) ![up]) := (ofRep ρ).tensorBasis ![up]

/-!

### A.1. Lowering and raising with no basis

An invariant nondegenerate bilinear form `B` on `W` is a form on `ofRep ρ`, and lowers and raises
its indices. No basis is named.

-/

section form

variable (B : LinearMap.BilinForm k W) (hB : B.Nondegenerate)
  (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v)

/-- The form `B` on the upper space of `ofRep ρ`. -/
noncomputable abbrev ofRepForm : (ofRep ρ).HasForm () where
  bilin := B
  bilin_invariant g _ _ := hinv g _ _
  bilin_nondegenerate := hB

-- The form of `ofRepForm` is `B`, read on the upper space.
example : (ofRepForm ρ B hB hinv).bilin = B := rfl

variable [(ofRep ρ).HasForm ()]

-- Lowering `v ↦ g(·, v)` and raising, its inverse, as equivalences of representations.
noncomputable example : ((ofRep ρ).rep up).Equiv ((ofRep ρ).rep down) := (ofRep ρ).toDual up
noncomputable example : ((ofRep ρ).rep down).Equiv ((ofRep ρ).rep up) := (ofRep ρ).toDual down

-- The lowered vector `v_μ` applied to `u` is `g(u, v)`.
example (u v : (ofRep ρ).V up) : (ofRep ρ).toDual up v u = (ofRep ρ).bilin () u v :=
  lower_apply () u v

-- Raising undoes lowering, `(v_μ)^μ = v^μ`.
example (v : (ofRep ρ).V up) : (ofRep ρ).toDual down ((ofRep ρ).toDual up v) = v :=
  toDual_toDual up v

example (v : (ofRep ρ).V up) : (ofRep ρ).toDual down ((ofRep ρ).toDual up v) = v := by simp

-- Lowering commutes with the group, `(g v)_μ = g (v_μ)`.
example (g : G) (v : (ofRep ρ).V up) :
    (ofRep ρ).toDual up ((ofRep ρ).rep up g v) = (ofRep ρ).rep down g ((ofRep ρ).toDual up v) :=
  Representation.IntertwiningMap.isIntertwining _ _ ((ofRep ρ).toDual up).toIntertwiningMap g v

-- In any basis `b` of `W`, the components of the lowered vector are the matrix of `B` applied to
-- the components of the vector, `v_ν = B_νμ v^μ`.
open Matrix in
example (hBf : (ofRep ρ).bilin () = B) {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι k ((ofRep ρ).V up)) (v : (ofRep ρ).V up) :
    ⇑(b.dualBasis.repr ((ofRep ρ).toDual up v)) = B.toMatrix b *ᵥ ⇑(b.repr v) := by
  rw [dualBasis_repr_toDual_up, hBf]

end form

end ofRep

/-!

## B. Two bases of one species

A statement for any basis takes the basis as a hypothesis. Two bases, with different labels, give
the same contraction, since the contraction is defined with no basis.

-/

example {k G K : Type} [RCLike k] [Group G] (S : Species k G K) {ι₁ ι₂ : K → Type}
    [∀ κ, Fintype (ι₁ κ)] [∀ κ, DecidableEq (ι₁ κ)] [∀ κ, Fintype (ι₂ κ)]
    [∀ κ, DecidableEq (ι₂ κ)] (B₁ : S.HasBasis ι₁) (B₂ : S.HasBasis ι₂) (c : Color K)
    (x : S.V c) (y : S.V c.dual) :
    (letI := B₁; ∑ μ, (S.basis c).repr x μ * (S.basis c.dual).repr y μ) =
      (letI := B₂; ∑ μ, (S.basis c).repr x μ * (S.basis c.dual).repr y μ) :=
  (letI := B₁; S.contr_tmul_eq_sum_basis c x y).symm.trans
    (letI := B₂; S.contr_tmul_eq_sum_basis c x y)

/-!

## C. A transparent space of a color

`S.V` is reducible. The colors are still told apart, and at a written-out color `simp` and
Mathlib's lemmas work on vectors and covectors.

-/

/-! ### C.1. Automation on a generic species -/

section Generic

variable {k G K : Type} [RCLike k] [Group G] {basisIdx : K → Type} [∀ κ, Fintype (basisIdx κ)]
  [∀ κ, DecidableEq (basisIdx κ)] (S : Species k G K) [S.HasBasis basisIdx] (κ : K)

example (v : S.V ⟨κ, .up⟩) (μ : basisIdx κ) :
    (S.basis ⟨κ, .up⟩).repr v μ = (S.basisW κ).repr v μ := by simp

example (w : S.V ⟨κ, .down⟩) (v v' : S.V ⟨κ, .up⟩) : w (v + v') = w v + w v' := map_add w v v'

example (w : S.V ⟨κ, .down⟩) (v v' : S.V ⟨κ, .up⟩) : w (v + v') = w v + w v' := by simp

example (w w' : S.V ⟨κ, .down⟩) (v : S.V ⟨κ, .up⟩) : (w + w') v = w v + w' v := by simp

-- The components of a covector, `w_μ = w(e_μ)`, by Mathlib's `dualBasis_repr`.
example (w : S.V ⟨κ, .down⟩) (μ : basisIdx κ) :
    (S.basis ⟨κ, .down⟩).repr w μ = w (S.basis ⟨κ, .up⟩ μ) := by simp

-- The instances on `S.V c` at a written-out color are those of the unfolded space.
example : S.instAddCommGroupV ⟨κ, .up⟩ = (inferInstance : AddCommGroup (S.W κ)) := by
  with_reducible_and_instances rfl
example : S.instModuleV ⟨κ, .up⟩ = (inferInstance : Module k (S.W κ)) := by
  with_reducible_and_instances rfl
example : S.instAddCommGroupV ⟨κ, .down⟩ =
    (inferInstance : AddCommGroup (Module.Dual k (S.W κ))) := by
  with_reducible_and_instances rfl
example : S.instModuleV ⟨κ, .down⟩ =
    (inferInstance : Module k (Module.Dual k (S.W κ))) := by
  with_reducible_and_instances rfl

-- A general-color lemma on tensors, `smul_pure`, at a written-out color by `simp`.
example (g : G) (f : Π i : Fin 1, S.V ((fun _ => ⟨κ, .up⟩) i)) :
    g • S.pure (c := fun _ => ⟨κ, .up⟩) f = S.pure fun i => S.repW κ g (f i) := by
  simp [rep_up]

-- Lemmas on maps between spaces `S.V c`, whose coercion types are `no_index`, fire by `simp` at a
-- written-out color and at a variable one.
example (a : Color K) (p : a = ⟨κ, .up⟩) (x : S.V a) : S.cast p x = cast (congrArg S.V p) x := by
  simp only [cast_apply]

example (a b : Color K) (p : a = b) (x : S.V a) : S.cast p x = cast (congrArg S.V p) x := by
  simp only [cast_apply]

example (α : S.V ⟨κ, .down⟩) (u : S.V ⟨κ, .up⟩) :
    S.dualEquiv ⟨κ, .up⟩ α u = S.contr ⟨κ, .up⟩ (u ⊗ₜ α) := by
  simp only [dualEquiv_apply]

example (v : S.V ⟨κ, .up⟩) :
    S.oneIndexEquiv ⟨κ, .up⟩ v = S.pure (c := ![⟨κ, .up⟩]) (Fin.cons v finZeroElim) := by
  simp only [oneIndexEquiv_apply]

example (x : S.V ⟨κ, .up⟩) (y : S.V ⟨κ, .down⟩) :
    S.twoIndexEquiv ⟨κ, .up⟩ ⟨κ, .down⟩ (x ⊗ₜ y) =
      S.pure (c := ![⟨κ, .up⟩, ⟨κ, .down⟩]) (Fin.cons x (Fin.cons y finZeroElim)) := by
  simp only [twoIndexEquiv_tmul]

example (x : S.V ⟨κ, .up⟩) (y : S.V ⟨κ, .down⟩) :
    (S.basis ⟨κ, .up⟩).coordPairing (S.basis (⟨κ, .up⟩ : Color K).dual) (x ⊗ₜ y) =
      S.contr ⟨κ, .up⟩ (x ⊗ₜ y) := by
  simp only [coordPairing_basis]

-- The contraction of a vector and a covector at a written-out color, by `simp`.
example (x : S.V ⟨κ, .up⟩) (y : S.V ⟨κ, .down⟩) : S.contr ⟨κ, .up⟩ (x ⊗ₜ y) = y x := by
  simp

example [S.HasForm κ] (v : S.V ⟨κ, .up⟩) :
    S.toDual (⟨κ, .up⟩ : Color K).dual (S.toDual ⟨κ, .up⟩ v) = v := by
  simp only [toDual_toDual]

example (c : Color K) [S.HasForm c.kind] (v : S.V c) : S.toDual c.dual (S.toDual c v) = v := by
  simp only [toDual_toDual]

-- The vector-level lemmas of `Metric` and `LinearMap`, at a written-out color.
example [S.HasForm κ] (u v : S.V ⟨κ, .up⟩) : S.lower κ v u = S.bilin κ u v := by
  simp only [lower_apply]

example [S.HasForm κ] (u v : S.V ⟨κ, .up⟩) : S.bilinEquiv κ u v = S.bilin κ u v := by
  simp only [bilinEquiv_apply]

example : S.toLin (S.delta ⟨κ, .up⟩) = LinearMap.id := by
  simp only [toLin_delta]

example (x y : S.V ⟨κ, .up⟩) (v : S.V ⟨κ, .down⟩) :
    S.toLin (x ⊗ₜ y) v = S.contr ⟨κ, .down⟩ (v ⊗ₜ x) • y := by
  simp only [toLin_tmul]

-- At the dual of a written-out color, `S.V ⟨κ, up⟩.dual`, `simp` first rewrites the color to
-- `⟨κ, down⟩` (`Color.dual_mk`, `Variance.dual_up`, proved by `rfl`), also inside the types of a
-- coercion. Then Mathlib's lemmas on linear forms, as `LinearMap.add_apply`, `LinearMap.smul_apply`
-- and `contractRight_apply`, fire.
example (w w' : S.V (⟨κ, .up⟩ : Color K).dual) (v : S.V ⟨κ, .up⟩) :
    (w + w') v = w v + w' v := by
  simp

example [S.HasForm κ] (v v' u : S.V ⟨κ, .up⟩) :
    S.toDual ⟨κ, .up⟩ (v + v') u = S.toDual ⟨κ, .up⟩ v u + S.toDual ⟨κ, .up⟩ v' u := by
  simp

example [S.HasForm κ] (r : k) (v u : S.V ⟨κ, .up⟩) :
    S.toDual ⟨κ, .up⟩ (r • v) u = r * S.toDual ⟨κ, .up⟩ v u := by
  simp

-- Raising undoes lowering at written-out colors, by plain `simp`, through `toDual_down_toDual_up`
-- and `toDual_up_toDual_down`, whichever way the dual color is written.
example [S.HasForm κ] (v : S.V ⟨κ, .up⟩) : S.toDual ⟨κ, .down⟩ (S.toDual ⟨κ, .up⟩ v) = v := by
  simp

example [S.HasForm κ] (w : S.V ⟨κ, .down⟩) : S.toDual ⟨κ, .up⟩ (S.toDual ⟨κ, .down⟩ w) = w := by
  simp

example [S.HasForm κ] (v : S.V ⟨κ, .up⟩) :
    S.toDual (⟨κ, .up⟩ : Color K).dual (S.toDual ⟨κ, .up⟩ v) = v := by
  simp

-- A lemma stated at `c.dual` does not unify `?c.dual` with a written-out `⟨κ, down⟩`. `rw` finds
-- `coordPairing_basis`, which meets `c` first in `S.basis c` (`simp only` does not). For
-- `basis_repr_toDual` the color must be given.
example (x : S.V ⟨κ, .up⟩) (y : S.V ⟨κ, .down⟩) :
    (S.basis ⟨κ, .up⟩).coordPairing (S.basis ⟨κ, .down⟩) (x ⊗ₜ y) = S.contr ⟨κ, .up⟩ (x ⊗ₜ y) := by
  rw [coordPairing_basis]

example [S.HasForm κ] (v : S.V ⟨κ, .up⟩) (ν : basisIdx κ) :
    (S.basis ⟨κ, .down⟩).repr (S.toDual ⟨κ, .up⟩ v) ν =
      ∑ μ, (S.basis ⟨κ, .up⟩).repr v μ * S.formMatrix ⟨κ, .down⟩ ν μ := by
  fail_if_success rw [basis_repr_toDual]
  rw [basis_repr_toDual ⟨κ, .up⟩]

end Generic

/-! ### C.2. Automation on a concrete species -/

/-- A species with the space `Fin 2 → ℝ`, as a def. Compare `plane`, an abbrev. -/
noncomputable def piDef : Species ℝ Unit Unit where
  W _ := Fin 2 → ℝ
  repW _ := Representation.trivial ℝ Unit (Fin 2 → ℝ)

/-- Mathlib's basis `Pi.basisFun` on `piDef`. -/
noncomputable instance : piDef.HasBasis (fun _ => Fin 2) := ⟨fun _ => Pi.basisFun ℝ (Fin 2)⟩

-- As a def the components must be stated, as `realLorentz.basisW_repr` does:
-- `Pi.basisFun_repr` misses, since `piDef.W ()` does not unfold to `Fin 2 → ℝ`.
example (v : piDef.V ⟨(), .up⟩) (i : Fin 2) : (piDef.basis ⟨(), .up⟩).repr v i = v i := by
  fail_if_success (simp; done)
  simp
  rfl

/-!

## D. A pseudoreal kind

`pseudoreal` has one kind with the space `ℂ²` and the trivial action. It is self-conjugate through
`x̄ ↦ ε x̄`, whose antilinear map `j x = ε x̄` squares to `-1`. The class `IsSelfConjugate` accepts
it, and it is not a real kind.

-/

/-- The species with the space `Fin 2 → ℂ` at its one kind and the trivial action of `Unit`. -/
noncomputable def pseudoreal : Species ℂ Unit Unit where
  W _ := Fin 2 → ℂ
  repW _ := Representation.trivial ℂ Unit (Fin 2 → ℂ)

/-- The matrix `ε = !![0, 1; -1, 0]`. -/
def epsilon : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- `ε` is invertible, with inverse `-ε`. -/
instance : Invertible epsilon where
  invOf := -epsilon
  invOf_mul_self := by ext i j; fin_cases i <;> fin_cases j <;> simp [epsilon]
  mul_invOf_self := by ext i j; fin_cases i <;> fin_cases j <;> simp [epsilon]

/-- The kind of `pseudoreal` is self-conjugate through `x̄ ↦ ε x̄`. -/
noncomputable instance : pseudoreal.IsSelfConjugate () where
  equiv := .mk ((conjEquiv (k := ℂ) (M := Fin 2 → ℂ)).symm.trans
    ((starLinearEquiv ℂ).trans (Matrix.toLinearEquiv' epsilon inferInstance)))
    fun _ => LinearMap.ext fun _ => rfl

open Matrix in
-- The antilinear map is `j x = ε x̄`, and `j² = -1`.
example (x : Fin 2 → ℂ) : pseudoreal.selfConjMap () (pseudoreal.selfConjMap () x) = -x := by
  change epsilon *ᵥ star (epsilon *ᵥ star x) = -x
  ext i
  fin_cases i <;> simp [epsilon, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

open Matrix in
-- The kind is not real.
example : ¬ pseudoreal.IsRealKind () := fun h => by
  have h1 := congrFun (h fun _ => 1) 0
  change (epsilon *ᵥ star (epsilon *ᵥ star fun _ => (1 : ℂ))) 0 = 1 at h1
  norm_num [epsilon, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1

/-!

## E. `simp` at written-out colors

Each color-indexed operation at each written-out color, closed by plain `simp`. A lemma on a map
between spaces `S.V c` that lacks its `no_index` (`Species` §A.1) makes one of these fail.

-/

section WrittenOut

variable {k G K : Type} [RCLike k] [Group G] {basisIdx : K → Type} [∀ κ, Fintype (basisIdx κ)]
  [∀ κ, DecidableEq (basisIdx κ)] (S : Species k G K) [S.HasBasis basisIdx] (κ : K)

/-! ### E.1. Lowering and raising -/

example [S.HasForm κ] (u v : S.V ⟨κ, .up⟩) : S.toDual ⟨κ, .up⟩ v u = S.bilin κ u v := by simp

example [S.HasForm κ] (u : S.V ⟨κ, .up⟩) (w : S.V ⟨κ, .down⟩) :
    S.bilin κ u (S.toDual ⟨κ, .down⟩ w) = w u := by simp

example [S.HasForm κ] (v : S.V ⟨κ, .up⟩) : S.toDual ⟨κ, .down⟩ (S.toDual ⟨κ, .up⟩ v) = v := by
  simp

example [S.HasForm κ] (w : S.V ⟨κ, .down⟩) : S.toDual ⟨κ, .up⟩ (S.toDual ⟨κ, .down⟩ w) = w := by
  simp

/-! ### E.2. Conjugation, at the four colors of a kind and its conjugate -/

example (v : S.withConj.V ⟨(κ, .plain), .up⟩) :
    bar (bar v : S.withConj.V ⟨(κ, .barred), .up⟩) = v := by simp

example (v : S.withConj.V ⟨(κ, .barred), .up⟩) :
    bar (bar v : S.withConj.V ⟨(κ, .plain), .up⟩) = v := by simp

example (w : S.withConj.V ⟨(κ, .plain), .down⟩) :
    bar (bar w : S.withConj.V ⟨(κ, .barred), .down⟩) = w := by simp

example (w : S.withConj.V ⟨(κ, .barred), .down⟩) :
    bar (bar w : S.withConj.V ⟨(κ, .plain), .down⟩) = w := by simp

example (v v' : S.withConj.V ⟨(κ, .plain), .up⟩) :
    (bar (v + v') : S.withConj.V ⟨(κ, .barred), .up⟩) = bar v + bar v' := by simp

example (w w' : S.withConj.V ⟨(κ, .barred), .down⟩) :
    (bar (w + w') : S.withConj.V ⟨(κ, .plain), .down⟩) = bar w + bar w' := by simp

example (r : k) (v : S.withConj.V ⟨(κ, .plain), .up⟩) :
    (bar (r • v) : S.withConj.V ⟨(κ, .barred), .up⟩) = star r • bar v := by simp

example (r : k) (w : S.withConj.V ⟨(κ, .barred), .down⟩) :
    (bar (r • w) : S.withConj.V ⟨(κ, .plain), .down⟩) = star r • bar w := by simp

-- The conjugate covector on a vector, `ᾱ(ū) = (α u)*`, at both conjugacies.
example (w : S.withConj.V ⟨(κ, .plain), .down⟩) (u : S.withConj.V ⟨(κ, .barred), .up⟩) :
    (bar w : S.withConj.V ⟨(κ, .barred), .down⟩) u = star (w (ConjModule.ofConj u)) := by simp

example (w : S.withConj.V ⟨(κ, .barred), .down⟩) (u : S.withConj.V ⟨(κ, .plain), .up⟩) :
    (bar w : S.withConj.V ⟨(κ, .plain), .down⟩) u = star (w (ConjModule.toConj u)) := by simp

-- The equivalence `barEquiv` is normalised to `bar`.
example (v : S.withConj.V ⟨(κ, .plain), .up⟩) :
    Species.barEquiv (c := ⟨(κ, .plain), .up⟩) (c' := ⟨(κ, .barred), .up⟩) rfl v = bar v := by
  simp

-- A wrong target color is rejected, the conjugate color accepted.
noncomputable example (v : S.withConj.V ⟨(κ, .plain), .up⟩) :
    S.withConj.V ⟨(κ, .barred), .up⟩ := by
  fail_if_success have : S.withConj.V ⟨(κ, .plain), .up⟩ := bar v
  fail_if_success have : S.withConj.V ⟨(κ, .barred), .down⟩ := bar v
  exact bar v

-- The components of a plain and of a barred vector.
example (v : S.withConj.V ⟨(κ, .plain), .up⟩) (μ : basisIdx κ) :
    (S.withConj.basis ⟨(κ, .plain), .up⟩).repr v μ = (S.basisW κ).repr v μ := by simp

example (v : S.withConj.V ⟨(κ, .barred), .up⟩) (μ : basisIdx κ) :
    (S.withConj.basis ⟨(κ, .barred), .up⟩).repr v μ =
      star ((S.basisW κ).repr (ConjModule.ofConj v) μ) := by simp

-- The conjugate form at a barred kind, and sums in the conjugate module.
example [S.HasForm κ] (x y : S.withConj.V ⟨(κ, .barred), .up⟩) :
    S.withConj.bilin (κ, .barred) x y =
      star (S.bilin κ (ConjModule.ofConj x) (ConjModule.ofConj y)) := by simp

example (a b : S.W κ) :
    (ConjModule.toConj a + ConjModule.toConj b : ConjModule (S.W κ)) =
      ConjModule.toConj (a + b) := by simp

end WrittenOut

end Tensor.Examples
