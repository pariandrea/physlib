/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!

# The conjugate module

Over a commutative star-ring `k`, the *conjugate module* `ConjModule M` of a `k`-module `M` is the
same additive group with the scalar action twisted by conjugation: `r • v := star r • v`. It turns a
sesquilinear pairing into a bilinear one: a map conjugate-linear in a slot `M` is linear in the slot
`ConjModule M`.

`ConjModule M` is a one-field structure, as Mathlib's `WithLp`, so that `M` and `ConjModule M` are
different types even when every definition unfolds. A vector `v : M` is `toConj v` in the conjugate
module, and `ofConj` reads it back. The additive group is that of `M`, and the `Module k` instance
is the one of `M` along `starRingEnd k` (`Module.compHom`), so the twisted action does not leak onto
`M` and vice versa. The canonical conjugate-linear identity
`conjEquiv : M ≃ₛₗ[starRingEnd k] ConjModule M`, the involution `ConjModule (ConjModule M) ≃ₗ[k] M`,
and the transported basis `Basis.conj` are provided.

## Key results

- `ConjModule` : the conjugate module, a structure with its twisted `Module` instance.
- `conjEquiv` : the canonical conjugate-linear equivalence `M ≃ₛₗ[starRingEnd k] ConjModule M`.
- `ConjModule.involution` : the involution `ConjModule (ConjModule M) ≃ₗ[k] M`.
- `Basis.conj` : a basis of `M` transported to a basis of `ConjModule M` (coordinates by `star`).
- `Representation.conj` : the conjugate of a representation, on `ConjModule M`, with
  `Representation.toMatrix_conj` : its matrix in `Basis.conj b` is the conjugate matrix.
- `LinearMap.BilinForm.conj` : the conjugate `B̄(x̄, ȳ) = (B(x, y))*` of a bilinear form, a bilinear
  form on `ConjModule M`, nondegenerate when `B` is, with the conjugate matrix in `Basis.conj b`.

-/

@[expose] public section

open Module

variable {k : Type*} [CommRing k] [StarRing k]
variable {M : Type*} [AddCommGroup M] [Module k M]

/-- The conjugate module of `M`: the same additive group with the scalar action twisted by
conjugation, `r • v = star r • v`. A structure, so that it is a different type from `M`. -/
structure ConjModule (M : Type*) where
  /-- A vector of `M` read in the conjugate module. -/
  toConj ::
  /-- The vector of `M` underlying a vector of the conjugate module. -/
  ofConj : M

namespace ConjModule

/-- `ofConj` and `toConj` as an equivalence `ConjModule M ≃ M`. -/
def equiv (M : Type*) : ConjModule M ≃ M := ⟨ofConj, toConj, fun _ => rfl, fun _ => rfl⟩

instance : AddCommGroup (ConjModule M) := (equiv M).addCommGroup

/-- `ofConj` as an additive equivalence `ConjModule M ≃+ M`. -/
def addEquiv (M : Type*) [AddCommGroup M] : ConjModule M ≃+ M :=
  { equiv M with map_add' _ _ := rfl }

/-- The twisted action `r • v = star r • v`, the action of `M` along the conjugation ring
endomorphism `starRingEnd k`. -/
instance instModule : Module k (ConjModule M) :=
  letI := Module.compHom M (starRingEnd k)
  (addEquiv M).module k

@[simp] lemma toConj_add (x y : M) : toConj (x + y) = toConj x + toConj y := rfl

@[simp] lemma ofConj_add (x y : ConjModule M) : (x + y).ofConj = x.ofConj + y.ofConj := rfl

@[simp] lemma ofConj_smul (r : k) (x : ConjModule M) : (r • x).ofConj = star r • x.ofConj := rfl

@[simp] lemma toConj_smul (r : k) (x : M) :
    (toConj (r • x) : ConjModule M) = star r • toConj x := by
  show toConj (r • x) = toConj (star (star r) • x)
  rw [star_star]

end ConjModule

/-- The canonical conjugate-linear equivalence `M ≃ₛₗ[starRingEnd k] ConjModule M`, `toConj`, the
identity on the underlying additive group. -/
def conjEquiv : M ≃ₛₗ[starRingEnd k] ConjModule M where
  toFun := ConjModule.toConj
  map_add' _ _ := rfl
  map_smul' r v := by
    show ConjModule.toConj (r • v) = ConjModule.toConj (star (star r) • v); rw [star_star]
  invFun := ConjModule.ofConj
  left_inv _ := rfl
  right_inv _ := rfl

namespace ConjModule

/-- Conjugating twice returns the original module: the `k`-linear isomorphism
`ConjModule (ConjModule M) ≃ₗ[k] M`. It is `k`-linear, not merely semilinear, because
`starRingEnd k` composed with itself is the identity. -/
def involution : ConjModule (ConjModule M) ≃ₗ[k] M :=
  ((conjEquiv (k := k) (M := M)).trans (conjEquiv (k := k) (M := ConjModule M))).symm

variable {ι : Type*}

/-- Coordinate-wise conjugation on `ι →₀ k`, a conjugate-linear self-equivalence. -/
noncomputable def starFinsupp : (ι →₀ k) ≃ₛₗ[starRingEnd k] (ι →₀ k) where
  toFun f := f.mapRange star (star_zero k)
  invFun f := f.mapRange star (star_zero k)
  map_add' f g := by ext i; simp [Finsupp.mapRange_apply, star_add]
  map_smul' r f := by
    ext i
    simp only [Finsupp.mapRange_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      starRingEnd_apply, star_mul']
  left_inv f := by ext i; simp [Finsupp.mapRange_apply]
  right_inv f := by ext i; simp [Finsupp.mapRange_apply]

/-- A basis of `M` transported to a basis of `ConjModule M`: the same basis vectors, with
coordinates conjugated (`(Basis.conj b).repr v = star ∘ b.repr v`). -/
noncomputable def _root_.Basis.conj (b : Basis ι k M) : Basis ι k (ConjModule M) :=
  Basis.ofRepr
    (((conjEquiv (k := k) (M := M)).symm.trans b.repr).trans starFinsupp)

/-- Coordinates in `Basis.conj b` are the `star` of the coordinates in `b`. -/
@[simp] lemma _root_.Basis.conj_repr_apply (b : Basis ι k M) (v : ConjModule M) (i : ι) :
    (Basis.conj b).repr v i = star (b.repr ((conjEquiv (k := k) (M := M)).symm v) i) := rfl

/-- The basis vectors of `Basis.conj b` are those of `b`, viewed through `conjEquiv`. -/
@[simp] lemma _root_.Basis.conj_apply (b : Basis ι k M) (i : ι) :
    Basis.conj b i = conjEquiv (k := k) (M := M) (b i) := by
  apply (Basis.conj b).repr.injective
  ext j
  rcases eq_or_ne j i with h | h
  · subst h; simp [Basis.conj_repr_apply]
  · simp [Basis.conj_repr_apply, Finsupp.single_eq_of_ne, h]

/-- The conjugate of a representation `ρ` of `G` on `M`: the same maps `ρ g`, acting on
`ConjModule M` through `conjEquiv`. -/
def _root_.Representation.conj {G} [Group G] (ρ : Representation k G M) :
    Representation k G (ConjModule M) where
  toFun g := {
    toFun := conjEquiv (k := k) (M := M) ∘ ρ g ∘ (conjEquiv (k := k) (M := M)).symm
    map_add' x y := congrArg ConjModule.toConj ((ρ g).map_add x.ofConj y.ofConj)
    map_smul' a m := congrArg ConjModule.toConj ((ρ g).map_smul (star a) m.ofConj) }
  map_one' := LinearMap.ext fun _ =>
    congrArg (conjEquiv (k := k)) (LinearMap.congr_fun (map_one ρ) _)
  map_mul' g h := LinearMap.ext fun _ =>
    congrArg (conjEquiv (k := k)) (LinearMap.congr_fun (map_mul ρ g h) _)

lemma _root_.Representation.conj_apply {G} [Group G] (ρ : Representation k G M) (g : G)
    (m : ConjModule M) :
    ρ.conj g m = conjEquiv (k := k) (M := M) (ρ g ((conjEquiv (k := k) (M := M)).symm m)) := rfl

/-- The matrix of `ρ.conj g` in the conjugate basis is the conjugate of the matrix of `ρ g`. -/
lemma _root_.Representation.toMatrix_conj {G} [Group G] [Fintype ι] [DecidableEq ι]
    (ρ : Representation k G M) (b : Basis ι k M) (g : G) :
    LinearMap.toMatrix (Basis.conj b) (Basis.conj b) (ρ.conj g) =
      (LinearMap.toMatrix b b (ρ g)).map star := by
  ext μ ν
  rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, Basis.conj_apply,
    Basis.conj_repr_apply, Representation.conj_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

/-- The conjugate `B̄` of a bilinear form `B` on `M`, the bilinear form
`B̄(x̄, ȳ) = (B(x, y))*` on the conjugate module. -/
def _root_.LinearMap.BilinForm.conj (B : LinearMap.BilinForm k M) :
    LinearMap.BilinForm k (ConjModule M) :=
  LinearMap.mk₂ k (fun x y => star (B x.ofConj y.ofConj))
    (fun x x' y => by
      change star (B (x.ofConj + x'.ofConj) y.ofConj) = _
      rw [map_add, LinearMap.add_apply, star_add])
    (fun r x y => by
      change star (B (star r • x.ofConj) y.ofConj) = _
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, star_mul', star_star, smul_eq_mul])
    (fun x y y' => by
      change star (B x.ofConj (y.ofConj + y'.ofConj)) = _
      rw [map_add, star_add])
    (fun r x y => by
      change star (B x.ofConj (star r • y.ofConj)) = _
      rw [map_smul, smul_eq_mul, star_mul', star_star, smul_eq_mul])

@[simp]
lemma _root_.LinearMap.BilinForm.conj_apply (B : LinearMap.BilinForm k M) (x y : ConjModule M) :
    B.conj x y = star (B x.ofConj y.ofConj) := rfl

/-- The conjugate of a nondegenerate form is nondegenerate. -/
lemma _root_.LinearMap.BilinForm.Nondegenerate.conj {B : LinearMap.BilinForm k M}
    (hB : B.Nondegenerate) : B.conj.Nondegenerate :=
  ⟨fun x hx => congrArg toConj (hB.1 x.ofConj fun y => star_eq_zero.1 (hx (toConj y))),
    fun y hy => congrArg toConj (hB.2 y.ofConj fun x => star_eq_zero.1 (hy (toConj x)))⟩

/-- The matrix of `B̄` in the conjugate basis is the conjugate of the matrix of `B`. -/
lemma _root_.LinearMap.BilinForm.toMatrix_conj [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm k M) (b : Basis ι k M) :
    LinearMap.BilinForm.toMatrix (Basis.conj b) B.conj =
      (LinearMap.BilinForm.toMatrix b B).map star := by
  ext μ ν
  rw [LinearMap.BilinForm.toMatrix_apply, Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply,
    Basis.conj_apply, Basis.conj_apply]
  rfl

end ConjModule

end
