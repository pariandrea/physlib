/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.ForMathlib.SemilinearMaps
public import Physlib.Mathematics.Modules.ConjModule
public import Physlib.Mathematics.Tensors.Contraction
public import Physlib.Mathematics.Tensors.Metric
/-!

# Conjugation of tensors

A species with its complex conjugates, the conjugation of a vector built once from the conjugate
module, and the conjugate of a tensor.

## i. Overview

A species with complex conjugation has the kinds `(κ, β)`, a kind `κ` and a conjugacy `β`, plain or
barred. The conjugate of `⟨(κ, β), v⟩` is `⟨(κ, β.swap), v⟩`, as the left-handed index `α` of
`ψ_α` and the right-handed index `α̇` of `ψ̄_α̇`. Conjugation and duality commute, and both are
involutive by definition.

`S.withConj` is the species `S` with the complex conjugate of each of its kinds adjoined. Its kinds
are the pairs `(κ, β)` of a kind of `S` and a conjugacy `β`, plain or barred. The space of a plain
kind is `S.W κ` with `S.repW κ`. The space of a barred kind is the conjugate module
`ConjModule (S.W κ)` with the conjugate representation, as the right-handed Weyl spinors are the
conjugate of the left-handed ones. A basis of `S` gives the basis of `S.withConj`, conjugated at a
barred kind (`Basis.conj`), with the same labels.

The conjugate `bar v` of a vector `v` of color `c` is a vector of the conjugate color
`c' = c.bar`, given with an equation `h` that `bar` finds by `rfl` at concrete colors. As a
conjugate-linear equivalence it is `barEquiv h : V c ≃ V c'`. At an upper color
it is `conjEquiv` of the conjugate module, or its inverse at a barred kind. At a lower color it is
the conjugate transpose `α ↦ star ∘ α ∘ conj⁻¹`. Conjugating twice gives back the vector,
conjugation preserves the contraction and commutes with the group action, all from these two
definitions.

A form on a kind gives the conjugate form `B̄(x̄, ȳ) = (B(x, y))*` on its conjugate, so that a
species gives a form only on its plain kinds. A kind is self-conjugate (`Species.IsSelfConjugate`)
when its conjugate representation is equivalent to it, as for the Lorentz vector. The antilinear map
`selfConjMap` it induces squares to `1` on a real kind and to `-1` on a pseudoreal one.

The conjugate `Tensor.conj T` of a tensor conjugates every index, and its components are the
conjugates of the components. As a conjugate-linear equivalence it is `Tensor.conjLinearEquiv`.

## ii. Key results

- `Conjugacy` : whether an index is plain or barred, with `Conjugacy.swap`.
- `Color.bar` : the conjugate color of a kind `(κ, β)`, with `Color.bar_bar` : `c.bar.bar = c` and
  `Color.bar_dual` : `c.bar.dual = c.dual.bar`, both by `rfl`.
- `Species.withConj` : the species with the conjugate of each kind, and its basis.
- `Species.bar` : the conjugate of a vector, and `Species.barEquiv` as an equivalence, with
  `Species.bar_bar`, `Species.star_contr_bar` and `Species.bar_rep`.
- the instance `Species.withConj.HasForm` : the conjugate form at a barred kind, symmetric or
  antisymmetric when the form is (`Species.isSymm_bilin_withConj`, `Species.isAlt_bilin_withConj`).
- `Species.IsSelfConjugate`, `Species.selfConjMap` and `Species.IsRealKind` : self-conjugate kinds.
- `Tensor.conj` is the conjugate of a tensor, and `Tensor.conjLinearEquiv` as an equivalence, with
  `Tensor.conj_conj`, `Tensor.conj_smul`, `Tensor.conj_contr` and `Tensor.tensorBasis_repr_conj`.

## iii. Table of contents

- A. Conjugate colors
- B. The species with its conjugates
- C. The conjugate of a vector
- D. The conjugate form
- E. Self-conjugate kinds
- F. Conjugation of tensors
  - F.1. The group action and contraction
  - F.2. Components

## iv. References

* None.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensor

/-!

## A. Conjugate colors

`Conjugacy` is two booleans, as `Variance`, so that `swap` is involutive by definition and
`c.bar.bar` is `c` also for a variable color `c`.

-/

/-- Whether an index is plain, as `α` in `ψ_α`, or barred, as `α̇` in `ψ̄_α̇`. -/
structure Conjugacy where
  /-- Whether the index is plain. -/
  isPlain : Bool
  /-- Whether the index is barred. -/
  isBarred : Bool
  /-- An index is either plain or barred. -/
  ne : isPlain ≠ isBarred
deriving DecidableEq

namespace Conjugacy

/-- A plain index, as `α` in `ψ_α`. -/
@[match_pattern]
abbrev plain : Conjugacy := ⟨true, false, by decide⟩

/-- A barred index, as `α̇` in `ψ̄_α̇`. -/
@[match_pattern]
abbrev barred : Conjugacy := ⟨false, true, by decide⟩

/-- The other conjugacy, exchanging plain and barred. -/
abbrev swap (β : Conjugacy) : Conjugacy := ⟨β.isBarred, β.isPlain, β.ne.symm⟩

/-- The conjugate of a plain index is barred. -/
@[simp] lemma swap_plain : plain.swap = barred := rfl

/-- The conjugate of a barred index is plain. -/
@[simp] lemma swap_barred : barred.swap = plain := rfl

end Conjugacy

/-- The conjugate color: the same kind `κ` and variance, with the other conjugacy, as
`ψ_α ↦ ψ̄_α̇`. -/
abbrev Color.bar {K : Type} (c : Color (K × Conjugacy)) : Color (K × Conjugacy) :=
  ⟨(c.kind.1, c.kind.2.swap), c.variance⟩

/-- Conjugating twice gives back the color. -/
lemma Color.bar_bar {K : Type} (c : Color (K × Conjugacy)) : c.bar.bar = c := rfl

/-- Conjugation and duality commute. -/
lemma Color.bar_dual {K : Type} (c : Color (K × Conjugacy)) : c.bar.dual = c.dual.bar := rfl

/-- If `b` is the conjugate of `a`, then `a.dual` is the conjugate of `b.dual`. This is the color
equation of the inverse of a form in `V a ⊗ V b`. -/
lemma Color.dual_eq_bar_dual {K : Type} {a b : Color (K × Conjugacy)} (hb : b = a.bar) :
    a.dual = b.dual.bar := by
  subst hb
  rfl

/-- The conjugate of `⟨(κ, β), v⟩` is `⟨(κ, β.swap), v⟩`. With `swap_plain` and `swap_barred` it
normalises a conjugate written-out color, as `Color.dual_mk` does for the dual. -/
@[simp]
lemma Color.bar_mk {K : Type} (κ : K) (β : Conjugacy) (v : Variance) :
    (⟨(κ, β), v⟩ : Color (K × Conjugacy)).bar = ⟨(κ, β.swap), v⟩ := rfl

/-- The pairs `σ` of `T`, as pairs of its conjugate `T̄`, with the same bijection of indices. -/
def ColorEquiv.barContr {K ι κ J : Type} {c : ι → Color (K × Conjugacy)}
    {b : κ → Color (K × Conjugacy)} {a : J → Color (K × Conjugacy)}
    (σ : ColorEquiv c (contrColors b a)) :
    ColorEquiv (fun i => (c i).bar) (contrColors (fun x => (b x).bar) fun j => (a j).bar) :=
  ⟨σ.toEquiv, fun j => by rcases j with _ | _ | _ <;> exact congrArg Color.bar (σ.color_eq _)⟩

namespace Species

variable {k : Type} [RCLike k] {G : Type} [Group G] {K : Type}

/-!

## B. The species with its conjugates

-/

/-- The species `S.withConj` of `S` with the conjugate of each kind. The kind `(κ, plain)` has the
space `S.W κ` and the representation `S.repW κ`, the kind `(κ, barred)` the conjugate module
`ConjModule (S.W κ)` and the conjugate representation. -/
noncomputable def withConj (S : Species k G K) : Species k G (K × Conjugacy) where
  W
    | (κ, .plain) => S.W κ
    | (κ, .barred) => ConjModule (S.W κ)
  addCommGroup
    | (κ, .plain) => S.addCommGroup κ
    | (κ, .barred) => inferInstanceAs (AddCommGroup (ConjModule (S.W κ)))
  module
    | (κ, .plain) => S.module κ
    | (_, .barred) => ConjModule.instModule
  finite
    | (κ, .plain) => S.finite κ
    | (κ, .barred) => .of_basis (Basis.conj (Module.finBasis k (S.W κ)))
  repW
    | (κ, .plain) => S.repW κ
    | (κ, .barred) => (S.repW κ).conj

variable (S : Species k G K)

/-- The basis of `S.withConj`, with the labels of `S`: the basis of `S` at a plain kind and its
conjugate `Basis.conj` at a barred kind. -/
noncomputable instance instHasBasisWithConj {basisIdx : K → Type} [S.HasBasis basisIdx] :
    S.withConj.HasBasis (fun κ => basisIdx κ.1) where
  basisW
    | (κ, .plain) => S.basisW κ
    | (κ, .barred) => Basis.conj (S.basisW κ)

/-! The action and the components at a written-out kind, for `simp`. `withConj` is not reducible,
so `simp` does not see `S.withConj.W (κ, plain)` as `S.W κ` without them. -/

@[simp] lemma withConj_repW_plain_apply (κ : K) (g : G) (v : S.withConj.W (κ, .plain)) :
    S.withConj.repW (κ, .plain) g v = S.repW κ g v := rfl

@[simp] lemma withConj_repW_barred_apply (κ : K) (g : G) (v : S.withConj.W (κ, .barred)) :
    S.withConj.repW (κ, .barred) g v = ConjModule.toConj (S.repW κ g (ConjModule.ofConj v)) := rfl

variable {basisIdx : K → Type} [S.HasBasis basisIdx] in
@[simp] lemma withConj_basisW_plain_repr (κ : K) (v : S.withConj.W (κ, .plain))
    (μ : basisIdx κ) :
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.withConj.basisW (κ, .plain)).repr v
      μ = (S.basisW κ).repr v μ := rfl

variable {basisIdx : K → Type} [S.HasBasis basisIdx] in
/-- The components of a barred vector are the conjugates of those of the plain vector. -/
@[simp] lemma withConj_basisW_barred_repr (κ : K) (v : S.withConj.W (κ, .barred))
    (μ : basisIdx κ) :
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.withConj.basisW (κ, .barred)).repr v
      μ = star ((S.basisW κ).repr (ConjModule.ofConj v) μ) := rfl

/-!

## C. The conjugate of a vector

-/

/-- The conjugate `v̄` of an upper vector of the kind `κ`, an upper vector of the conjugate kind:
`conjEquiv` of the conjugate module at a plain kind and its inverse at a barred kind. -/
noncomputable def conjW : (κ : K × Conjugacy) → S.withConj.W κ ≃ₗ⋆[k] S.withConj.W (κ.1, κ.2.swap)
  | (κ, .plain) => conjEquiv (M := S.W κ)
  | (κ, .barred) => (conjEquiv (M := S.W κ)).symm

/-- Conjugating an upper vector twice gives back the vector. -/
lemma conjW_conjW : ∀ (κ : K × Conjugacy) (v : S.withConj.W κ),
    S.conjW (κ.1, κ.2.swap) (S.conjW κ v) = v
  | (_, .plain), _ | (_, .barred), _ => rfl

/-- Conjugating an upper vector commutes with the group action, since the representation of the
conjugate kind is the conjugate representation. -/
lemma conjW_repW : ∀ (κ : K × Conjugacy) (g : G) (v : S.withConj.W κ),
    S.conjW κ (S.withConj.repW κ g v) = S.withConj.repW (κ.1, κ.2.swap) g (S.conjW κ v)
  | (_, .plain), _, _ | (_, .barred), _, _ => rfl

variable {basisIdx : K → Type} [S.HasBasis basisIdx] in
/-- Conjugation sends the basis vector `e_μ` of a kind to the basis vector `e_μ` of its
conjugate. -/
lemma conjW_basisW : ∀ (κ : K × Conjugacy) (μ : basisIdx κ.1),
    S.conjW κ (S.withConj.basisW κ μ) = S.withConj.basisW (κ.1, κ.2.swap) μ
  | (κ, .plain), μ => (Basis.conj_apply (S.basisW κ) μ).symm
  | (κ, .barred), μ => congrArg (conjEquiv (M := S.W κ)).symm (Basis.conj_apply (S.basisW κ) μ)

variable {S} in
/-- The conjugation `barEquiv h : V c ≃ V c'` of the vectors of color `c` onto those of the
conjugate color `c'`, given with the equation `h : c' = c.bar` that holds by `rfl` at concrete
colors. It is `conjW` at an upper color and its conjugate transpose `α ↦ star ∘ α ∘ conjW⁻¹` at a
lower one. -/
noncomputable def barEquiv : {c c' : Color (K × Conjugacy)} → (h : c' = c.bar) →
    S.withConj.V c ≃ₗ⋆[k] S.withConj.V c'
  | ⟨κ, .up⟩, _, rfl => S.conjW κ
  | ⟨κ, .down⟩, _, rfl => (S.conjW κ).conjDual

variable {S} in
/-- `bar v` is the conjugate `v̄` of a vector `v` of color `c`, a vector of the conjugate color
`c'`. The equation `h : c' = c.bar` is found by `rfl` at concrete colors. It is
`barEquiv h v`. -/
noncomputable def bar {c c' : Color (K × Conjugacy)} (v : S.withConj.V c)
    (h : c' = c.bar := by rfl) : S.withConj.V c' :=
  barEquiv h v

variable {S}
variable {c c' : Color (K × Conjugacy)}

/-- `barEquiv h v` is `bar v h`, the simp normal form. The coercion types are `no_index`
(`Species` §A.1). -/
@[simp]
lemma barEquiv_apply (h : c' = c.bar) (v : S.withConj.V c) :
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _ (barEquiv h) v = bar v h :=
  rfl

/-- Conjugating twice gives back the vector, `v̄̄ = v`. -/
@[simp]
lemma bar_bar (h : c' = c.bar) (h' : c = c'.bar) (v : S.withConj.V c) : bar (bar v h) h' = v := by
  subst h
  match c with
  | ⟨κ, .up⟩ => exact S.conjW_conjW κ v
  | ⟨κ, .down⟩ => exact LinearEquiv.conjDual_conjDual _ _ (S.conjW_conjW κ) v

/-- Conjugation is additive. The sum is `no_index`, since its type `S.V c` reduces at a written-out
color (`Species` §A.1). -/
@[simp] lemma bar_add (h : c' = c.bar) (v v' : S.withConj.V c) :
    bar (no_index (v + v')) h = bar v h + bar v' h :=
  map_add (barEquiv h) v v'

/-- Conjugation is conjugate-linear, `(r v)‾ = r* v̄`. -/
@[simp] lemma bar_smul (h : c' = c.bar) (r : k) (v : S.withConj.V c) :
    bar (no_index (r • v)) h = star r • bar v h :=
  LinearEquiv.map_smulₛₗ (barEquiv h) r v

/-- Conjugation preserves the contraction, `(u^μ α_μ)* = ū^μ ᾱ_μ`, for `u` of color `c` and `α` of
color `c.dual`. -/
lemma star_contr_bar (h : c' = c.bar) (u : S.withConj.V c) (α : S.withConj.V c.dual) :
    star (S.withConj.contr c (u ⊗ₜ[k] α)) =
      S.withConj.contr c' (bar u h ⊗ₜ[k] bar (c' := c'.dual) α (congrArg Color.dual h)) := by
  subst h
  match c with
  | ⟨κ, .up⟩ =>
    exact congrArg (star ∘ α) ((S.conjW κ).symm_apply_apply u).symm
  | ⟨κ, .down⟩ =>
    exact congrArg (star ∘ u) ((S.conjW κ).symm_apply_apply α).symm

/-- Conjugation commutes with the group action, `(Λv)‾ = Λ v̄`. -/
lemma bar_rep (h : c' = c.bar) (g : G) (v : S.withConj.V c) :
    bar (S.withConj.rep c g v) h = S.withConj.rep c' g (bar v h) := by
  subst h
  match c with
  | ⟨κ, .up⟩ => exact S.conjW_repW κ g v
  | ⟨κ, .down⟩ =>
    refine LinearMap.ext fun u => congrArg (star ∘ v) ?_
    exact (S.conjW κ).eq_symm_apply.2 ((S.conjW_repW κ g⁻¹ _).trans
      (congrArg _ ((S.conjW κ).apply_symm_apply u)))

/-- Moving the conjugate along an equality of colors conjugates to the new color. -/
lemma cast_bar {c'' : Color (K × Conjugacy)} (q : c' = c'') (h : c' = c.bar)
    (x : S.withConj.V c) :
    S.withConj.cast q (bar x h) = bar x (q.symm.trans h) := by
  subst q
  rfl

/-- Conjugating a vector moved along an equality of colors conjugates the vector. -/
lemma bar_cast {b b' : Color (K × Conjugacy)} (p : b = b') (h : c' = b'.bar)
    (x : S.withConj.V b) :
    bar (S.withConj.cast p x) h = bar x (h.trans (congrArg Color.bar p.symm)) := by
  subst p
  rfl

/-- The conjugate `ᾱ` of a plain covector on a barred vector `ū` is `(α u)*`. The coercion types
are `no_index` (`Species` §A.1). -/
@[simp] lemma bar_down_plain_apply (κ : K) (w : S.withConj.V ⟨(κ, .plain), .down⟩)
    (h : (⟨(κ, .barred), .down⟩ : Color (K × Conjugacy)) = (⟨(κ, .plain), .down⟩ : Color _).bar)
    (u : S.withConj.V ⟨(κ, .barred), .up⟩) :
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _ (bar w h) u =
      star (w (ConjModule.ofConj u)) := rfl

/-- The conjugate of a barred covector on a plain vector `u` is `(α ū)*`. -/
@[simp] lemma bar_down_barred_apply (κ : K) (w : S.withConj.V ⟨(κ, .barred), .down⟩)
    (h : (⟨(κ, .plain), .down⟩ : Color (K × Conjugacy)) = (⟨(κ, .barred), .down⟩ : Color _).bar)
    (u : S.withConj.V ⟨(κ, .plain), .up⟩) :
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _ (bar w h) u =
      star (w (ConjModule.toConj u)) := rfl

variable {basisIdx : K → Type} [S.HasBasis basisIdx] [∀ κ, Fintype (basisIdx κ)]
  [∀ κ, DecidableEq (basisIdx κ)]

/-- Conjugation sends the basis vector `e_μ` of `c` to the basis vector `e_μ` of `c'`, the label
read at `c'` along `h`. -/
lemma bar_basis (h : c' = c.bar) (μ : basisIdx c.kind.1) :
    bar (S.withConj.basis c μ) h =
      S.withConj.basis c' (Equiv.cast (congrArg (fun c => basisIdx c.kind.1) h.symm) μ) := by
  subst h
  match c with
  | ⟨κ, .up⟩ => exact S.conjW_basisW κ μ
  | ⟨κ, .down⟩ => exact LinearEquiv.conjDual_dualBasis _ _ _ (S.conjW_basisW κ) μ

/-!

## D. The conjugate form

-/

variable (S) in
/-- The form of `S.withConj` at the kind `(κ, β)`: the form of `S` at a plain kind and its
conjugate `B̄(x̄, ȳ) = (B(x, y))*` at a barred kind. -/
@[instance_reducible]
noncomputable def hasFormWithConj (κ : K) [S.HasForm κ] :
    (β : Conjugacy) → S.withConj.HasForm (κ, β)
  | .plain => ⟨S.bilin κ, HasForm.bilin_invariant (S := S), HasForm.bilin_nondegenerate (S := S)⟩
  | .barred => ⟨(S.bilin κ).conj, fun g u v => congrArg star
      (HasForm.bilin_invariant (S := S) g u.ofConj v.ofConj),
      (HasForm.bilin_nondegenerate (S := S)).conj⟩

/-- A form on a kind of `S` gives the form of `S.withConj` on the kind and on its conjugate. -/
noncomputable instance (κ : K × Conjugacy) [S.HasForm κ.1] : S.withConj.HasForm κ :=
  S.hasFormWithConj κ.1 κ.2

/-- The conjugate form at a barred kind, `B̄(x̄, ȳ) = (B(x, y))*`. The coercion types are
`no_index` (`Species` §A.1). -/
@[simp] lemma withConj_bilin_barred_apply (κ : K) [S.HasForm κ]
    (x y : S.withConj.V ⟨(κ, .barred), .up⟩) :
    @DFunLike.coe (no_index _) (no_index _) (no_index _) _
      (@DFunLike.coe (no_index _) (no_index _) (no_index _) _ (S.withConj.bilin (κ, .barred)) x) y =
      star (S.bilin κ (ConjModule.ofConj x) (ConjModule.ofConj y)) := rfl

/-- The conjugate of a symmetric form is symmetric, `B̄(ȳ, x̄) = (B(y, x))* = (B(x, y))*`. -/
lemma isSymm_bilin_withConj (κ : K) [S.HasForm κ] [S.IsSymmetricForm κ] :
    ∀ β : Conjugacy, (S.withConj.bilin (κ, β)).IsSymm
  | .plain => IsSymmetricForm.isSymm (S := S)
  | .barred => ⟨fun x y =>
      congrArg star ((IsSymmetricForm.isSymm (S := S) (κ := κ)).eq x.ofConj y.ofConj)⟩

/-- The conjugate of an alternating form is alternating, `B̄(x̄, x̄) = (B(x, x))* = 0`. -/
lemma isAlt_bilin_withConj (κ : K) [S.HasForm κ] [S.IsAntisymmetricForm κ] :
    ∀ β : Conjugacy, LinearMap.IsAlt (S.withConj.bilin (κ, β))
  | .plain => IsAntisymmetricForm.isAlt (S := S)
  | .barred => fun x =>
      (congrArg star (IsAntisymmetricForm.isAlt (S := S) (κ := κ) x.ofConj)).trans (star_zero k)

/-- A symmetric form on a kind gives symmetric forms on the kind and on its conjugate. -/
instance (κ : K × Conjugacy) [S.HasForm κ.1] [S.IsSymmetricForm κ.1] :
    S.withConj.IsSymmetricForm κ :=
  ⟨S.isSymm_bilin_withConj κ.1 κ.2⟩

/-- An antisymmetric form on a kind gives antisymmetric forms on the kind and on its conjugate. -/
instance (κ : K × Conjugacy) [S.HasForm κ.1] [S.IsAntisymmetricForm κ.1] :
    S.withConj.IsAntisymmetricForm κ :=
  ⟨S.isAlt_bilin_withConj κ.1 κ.2⟩

/-!

## E. Self-conjugate kinds

-/

variable (S) in
/-- A self-conjugate kind `κ`, whose conjugate representation is equivalent to it by the chosen
`equiv`, as `V̄^μ ≅ V^μ` for the Lorentz vector. -/
class IsSelfConjugate (κ : K) where
  /-- The equivalence of the conjugate representation of the kind `κ` with its representation. -/
  equiv : (S.repW κ).conj.Equiv (S.repW κ)

variable (S) in
/-- The antilinear map `j v = equiv v̄` of a self-conjugate kind. It squares to `1` on a real kind
and to `-1` on a pseudoreal one. -/
noncomputable def selfConjMap (κ : K) [S.IsSelfConjugate κ] : S.W κ ≃ₗ⋆[k] S.W κ :=
  conjEquiv.trans (IsSelfConjugate.equiv (S := S) (κ := κ)).toLinearEquiv

/-- The antilinear map of a self-conjugate kind commutes with the group action. -/
lemma selfConjMap_rep (κ : K) [S.IsSelfConjugate κ] (g : G) (v : S.W κ) :
    S.selfConjMap κ (S.repW κ g v) = S.repW κ g (S.selfConjMap κ v) :=
  Representation.IntertwiningMap.isIntertwining _ _
    (IsSelfConjugate.equiv (S := S) (κ := κ)).toIntertwiningMap g (ConjModule.toConj v)

variable (S) in
/-- A self-conjugate kind is real when its antilinear map squares to `1`, `j² = 1`. -/
def IsRealKind (κ : K) [S.IsSelfConjugate κ] : Prop :=
  ∀ v, S.selfConjMap κ (S.selfConjMap κ v) = v

end Species

open Species

/-!

## F. Conjugation of tensors

-/

variable {k : Type} [RCLike k] {G : Type} [Group G] {K : Type} {S : Species k G K}
  {ι : Type} {c c' : ι → Color (K × Conjugacy)}

/-- The conjugation `conjLinearEquiv h` of the tensors of colors `c` onto those of the conjugate
colors `c'`, every index conjugated. The colors `c'` are the conjugates of `c` by `h`. It is
conjugate-linear. -/
noncomputable def conjLinearEquiv (h : ∀ i, c' i = (c i).bar) :
    Tensor S.withConj c ≃ₗ⋆[k] Tensor S.withConj c' :=
  PiTensorProduct.congrₛₗ fun i => barEquiv (h i)

/-- The conjugate `T̄` of a tensor `T`, with every index conjugated and moved to the conjugate
color. The colors `c'` of the result are the conjugates of `c` by `h`, found for a literal family
of colors on `Fin n` by `fin_cases`. It is `conjLinearEquiv h T`. -/
noncomputable def conj (t : Tensor S.withConj c)
    (h : ∀ i, c' i = (c i).bar := by intro i; fin_cases i <;> rfl) : Tensor S.withConj c' :=
  conjLinearEquiv h t

/-- `conjLinearEquiv h t` is `conj t h`, the simp normal form. -/
@[simp]
lemma conjLinearEquiv_apply (h : ∀ i, c' i = (c i).bar) (t : Tensor S.withConj c) :
    conjLinearEquiv h t = conj t h :=
  rfl

/-- The conjugate of a pure tensor conjugates each factor, `(u ⊗ α)‾ = ū ⊗ ᾱ`. -/
@[simp]
lemma conj_pure (h : ∀ i, c' i = (c i).bar) (f : Π i, S.withConj.V (c i)) :
    conj (S.withConj.pure f) h = S.withConj.pure fun i => bar (f i) (h i) :=
  congrₛₗ_tprod _ f

/-- Conjugating twice gives back the tensor. -/
@[simp]
lemma conj_conj (h : ∀ i, c' i = (c i).bar) (h' : ∀ i, c i = (c' i).bar)
    (t : Tensor S.withConj c) : conj (conj t h) h' = t :=
  PiTensorProduct.congrₛₗ_congrₛₗ _ _ (fun i => bar_bar (h i) (h' i)) t

/-!

### F.1. The group action and contraction

-/

/-- Conjugation commutes with the action `Λ` of `g : G`, `(ΛT)‾ = Λ T̄`. -/
lemma conj_smul (h : ∀ i, c' i = (c i).bar) (g : G) (t : Tensor S.withConj c) :
    conj (g • t) h = g • conj t h :=
  map_smul_of_pure (conjLinearEquiv h) g (fun f => by simp [bar_rep]) t

variable {κ J : Type} [Fintype J] {b : κ → Color (K × Conjugacy)} {a : J → Color (K × Conjugacy)}

/-- Conjugating a contraction is contracting the conjugate along the same pairs of indices,
`(T^ρμ_μ)‾ = T̄^ρμ_μ`. -/
lemma conj_contr (σ : ColorEquiv c (contrColors b a)) (t : Tensor S.withConj c) :
    conj (contr σ t) (fun _ => rfl) = contr σ.barContr (conj t fun _ => rfl) := by
  change conjLinearEquiv _ (contr σ t) = contr σ.barContr (conjLinearEquiv _ t)
  induction t using induction_on_pure with
  | hsmul r t ht => rw [map_smul, LinearEquiv.map_smulₛₗ, ht, LinearEquiv.map_smulₛₗ, map_smul]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | h f =>
    simp only [contr_pure, conjLinearEquiv_apply, conj_pure, LinearEquiv.map_smulₛₗ,
      starRingEnd_apply, star_prod, star_contr_bar rfl, bar_cast, cast_bar]
    rfl

/-!

### F.2. Components

-/

variable {basisIdx : K → Type} [S.HasBasis basisIdx] [∀ κ, Fintype (basisIdx κ)]
  [∀ κ, DecidableEq (basisIdx κ)]

/-- The components of the conjugate are the conjugates of the components, `(T̄)^μν = (T^μν)*`,
with the labels read at `c` along `h`. -/
lemma tensorBasis_repr_conj [Fintype ι] (h : ∀ i, c' i = (c i).bar) (t : Tensor S.withConj c)
    (μ : Π i, basisIdx (c' i).kind.1) :
    (S.withConj.tensorBasis c').repr (conj t h) μ =
      star ((S.withConj.tensorBasis c).repr t fun i =>
        (Equiv.cast (congrArg (fun c => basisIdx c.kind.1) (h i).symm)).symm (μ i)) := by
  rw [conj, Module.Basis.eq_starEquiv (S.withConj.tensorBasis c) (S.withConj.tensorBasis c')
    (Equiv.piCongrRight fun i => Equiv.cast (congrArg (fun c => basisIdx c.kind.1) (h i).symm))
    (conjLinearEquiv h) (fun ν => by
      simp only [tensorBasis_apply, conjLinearEquiv_apply, conj_pure]
      exact congrArg S.withConj.pure (funext fun i => bar_basis (h i) (ν i))) t,
    Module.Basis.repr_starEquiv]
  rfl

end Tensor
