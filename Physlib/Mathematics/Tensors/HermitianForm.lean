/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Conjugation
public import Physlib.Mathematics.Tensors.Inverse
/-!

# Hermitian forms

A tensor `g_{IJ̄}` in `V a ⊗ V b` with `b = a.bar` read as a sesquilinear form, and its inverse.

## i. Overview

A tensor `g_{IJ̄}` whose second color is the conjugate of the first is a sesquilinear form on the
vectors (`sesqForm`), so that Hermiticity is Mathlib's `LinearMap.IsSymm` and
positive-definiteness is `LinearMap.IsPosDef` from `ForMathlib.SesquilinearForm`. The inverse
`g^{J̄I}` in `V b.dual ⊗ V a.dual` is again such a form, since `a.dual = b.dual.bar`
(`Color.dual_eq_bar_dual`). The colors are those of a species with its conjugates,
`S.withConj`. The inverse of an invertible Hermitian or positive-definite `g_{IJ̄}`
is again Hermitian or positive-definite, and a positive-definite `g_{IJ̄}` is invertible.

## ii. Key results

- `Species.sesqForm` reads a tensor `g_{IJ̄}` as the sesquilinear form `x, y ↦ g_{IJ̄} y^I x̄^J̄`.
- `Species.isSymm_sesqForm_inverse` and `Species.isPosDef_sesqForm_inverse` prove that the inverse
  of an invertible Hermitian or positive-definite `g_{IJ̄}` is Hermitian or positive-definite, from
  `LinearMap.IsSymm.of_comp_star` and `LinearMap.IsPosDef.of_comp_star`.
- `Species.toLin_injective_of_isPosDef` proves that the linear map of a positive-definite `g_{IJ̄}`
  is injective, and `Species.toLin_bijective_of_isPosDef` that it is bijective.

## iii. Table of contents

- A. Hermitian forms and their inverses
- B. Positive-definite forms are invertible

## iv. References

* None.

-/

@[expose] public section

open TensorProduct
open scoped ComplexOrder

namespace Tensor

namespace Species

variable {K : Type} {k : Type} [RCLike k] {G : Type} [Group G]
    {S : Species k G K} {a b : Color (K × Conjugacy)}

/-!

## A. Hermitian forms and their inverses

-/

variable (S) in
/-- A tensor `g_{IJ̄}` in `V a ⊗ V b` as the sesquilinear form `x, y ↦ g_{IJ̄} y^I x̄^J̄` on the
vectors of color `a.dual`. The color `b` is the conjugate of `a` by `hb`, which holds by `rfl` at
concrete colors. The form is conjugate-linear in its first argument, Mathlib's convention, so it is
the physicist's `g(y, x) = g_{IJ̄} y^I x̄^J̄` with the arguments swapped. -/
noncomputable def sesqForm (g : S.withConj.V a ⊗[k] S.withConj.V b) (hb : b = a.bar) :
    S.withConj.V a.dual →ₗ⋆[k] S.withConj.V a.dual →ₗ[k] k :=
  (((TensorProduct.mk k _ _).compr₂ (S.withConj.contr b.dual).toLinearMap).compl₂
    (S.withConj.toLin g)).comp (barEquiv (congrArg Color.dual hb)).toLinearMap

/-- The form on `x, y` contracts `x̄` with `g y`, where `g y` is the contraction of `g` with `y`. -/
lemma sesqForm_apply (g : S.withConj.V a ⊗[k] S.withConj.V b) (hb : b = a.bar)
    (x y : S.withConj.V a.dual) :
    S.sesqForm g hb x y =
      S.withConj.contr b.dual (bar (c' := b.dual) x (congrArg Color.dual hb) ⊗ₜ
        S.withConj.toLin g y) :=
  rfl

/-- The form of the inverse on `g x` and `g y` is the conjugate of the form of `g` on `y` and `x`,
`g^{J̄I} (g y)_J̄ (g x)‾_I = (g_{IJ̄} x^I ȳ^J̄)*`. The inverse `g^{J̄I}` acts on barred
covectors, so its form is the conjugate of the usual `g^{IJ̄} w_I w̄'_J̄`. -/
lemma sesqForm_inverse_toLin (g : S.withConj.V a ⊗[k] S.withConj.V b)
    (h : Function.Bijective (S.withConj.toLin g)) (hb : b = a.bar) (x y : S.withConj.V a.dual) :
    S.sesqForm (S.withConj.inverse g) (Color.dual_eq_bar_dual hb) (S.withConj.toLin g x)
      (S.withConj.toLin g y) =
      star (S.sesqForm g hb y x) := by
  rw [sesqForm_apply, sesqForm_apply, toLin_inverse g h, LinearEquiv.coe_coe,
    LinearEquiv.ofBijective_symm_apply_apply, ← S.withConj.contr_tmul_symm,
    star_contr_bar (Color.dual_eq_bar_dual hb), bar_bar]

/-- The inverse of a Hermitian `g_{IJ̄}` is Hermitian. -/
lemma isSymm_sesqForm_inverse (g : S.withConj.V a ⊗[k] S.withConj.V b) (hb : b = a.bar)
    (h : Function.Bijective (S.withConj.toLin g)) (hg : (S.sesqForm g hb).IsSymm) :
    (S.sesqForm (S.withConj.inverse g) (Color.dual_eq_bar_dual hb)).IsSymm :=
  hg.of_comp_star h.2 (sesqForm_inverse_toLin g h hb)

/-!

## B. Positive-definite forms are invertible

-/

/-- The linear map `y ↦ g y` of a positive-definite `g_{IJ̄}` is injective. -/
lemma toLin_injective_of_isPosDef (g : S.withConj.V a ⊗[k] S.withConj.V b) {hb : b = a.bar}
    (hg : (S.sesqForm g hb).IsPosDef) : Function.Injective (S.withConj.toLin g) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  exact fun y hy => hg.nondegenerate.2 y fun x => by simp [sesqForm_apply, hy]

/-- A positive-definite `g_{IJ̄}` is invertible. Its linear map `y ↦ g y` is bijective. -/
lemma toLin_bijective_of_isPosDef (g : S.withConj.V a ⊗[k] S.withConj.V b) {hb : b = a.bar}
    (hg : (S.sesqForm g hb).IsPosDef) : Function.Bijective (S.withConj.toLin g) := by
  -- Surjective since the dimensions agree, through the conjugation `V a.dual ≃ V b.dual`.
  have hi := toLin_injective_of_isPosDef g hg
  refine ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hi⟩
  rw [(barEquiv (S := S) (congrArg Color.dual hb)).finrank_eqₛₗ,
    (S.withConj.dualEquiv b).toLinearEquiv.finrank_eq, Subspace.dual_finrank_eq]

/-- The inverse of a positive-definite `g_{IJ̄}` is positive-definite. -/
lemma isPosDef_sesqForm_inverse (g : S.withConj.V a ⊗[k] S.withConj.V b) (hb : b = a.bar)
    (hg : (S.sesqForm g hb).IsPosDef) :
    (S.sesqForm (S.withConj.inverse g) (Color.dual_eq_bar_dual hb)).IsPosDef :=
  have h := toLin_bijective_of_isPosDef g hg
  hg.of_comp_star h.2 (sesqForm_inverse_toLin g h hb)

end Species

end Tensor
