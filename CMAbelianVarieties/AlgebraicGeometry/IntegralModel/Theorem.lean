/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.AbelianVarieties.BaseFieldChange
public import Mathlib.NumberTheory.NumberField.Basic

/-!
## Goal

The goal of this file is to show that an abelian variety `A` over `AlgebraicClosure ℚ`
has a model over a number field. That is, there is a number field `E` and an abelian
variety `A₀` over `E`, such that `A₀ _ (AlgebraicClosure ℚ) ≅ A` as group objects.

-/

@[expose] public section
/-
Note written by AI (Claude Code), from a search of the local Mathlib checkout.

Question: is there anything in Mathlib which says that a nice scheme (finite type and all)
over `Q̄` has a model over a number field?

Answer: not as a ready-made theorem. Mathlib has the morphism half of spreading out, but not
the half that produces the model itself.

## What exists

- Morphisms from a limit factor through some stage:
  `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
  in `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`.
  - Setup: a cofiltered diagram `Dᵢ` of qcqs `S`-schemes with affine transition maps, and `X`
    locally of finite presentation over `S`.
  - Conclusion: every `S`-morphism `lim Dᵢ ⟶ X` factors through some `Dⱼ`.
- Packaged as a colimit statement: `AlgebraicGeometry.Scheme.preservesColimit_yoneda`
  (same file). It says `Hom_S(-, X)` sends such limits to filtered colimits.
  This is EGA IV 8 / Stacks 01ZC-style, for morphisms only.
- The same file has more limit lemmas:
  - `Scheme.exists_isAffine_of_isLimit`
  - `Scheme.exists_isOpenCover_and_isAffine`
  - `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`
  - `Scheme.nonempty_of_isLimit`
- The ring-level version: `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` and
  `CommRingCat.preservesFilteredColimits_coyoneda`, in
  `Mathlib/Algebra/Category/Ring/FinitePresentation.lean`.

## What is missing

EGA IV 8.8.2 (ii), the existence of a model: if `X` is of finite presentation over `lim Sᵢ`,
then `X ≅ Xᵢ ×_{Sᵢ} lim S` for some `Xᵢ` of finite presentation over some `Sᵢ`.
Nothing for this was found at the scheme level. At the algebra level there was also no lemma
saying "a finitely presented `R`-algebra over a filtered colimit `R = colim Rᵢ` comes from
some `Rᵢ`".

## Practical consequences for this project

- With `Q̄ = colim E` over number fields `E ⊆ Q̄`, the object-level step ("`A` comes from some
  `A_E`") would have to be proved by hand.
  - Affine case: take the finitely many coefficients of a presentation and adjoin them to `ℚ`.
    Glue over a finite affine cover for the general case.
  - Mathlib's `Spec ↧Q̄` is a limit of `Spec ↧E`, so the setup above fits.
- The morphism-level results above should already handle descending isomorphisms,
  endomorphisms, the group law and the CM action (`F →+* End⁰`) to some `E`, since
  `Hom(A_{Q̄}, B_{Q̄}) = colim_E Hom(A_E, B_E)` follows from `preservesColimit_yoneda` plus
  base change.
- Descending properties like properness and geometric integrality would also be extra work.
  No limit results for those were found either.

Only the local Mathlib checkout was searched, so a newer Mathlib or an open PR might have the
object-level result. `AffineTransitionLimit.lean` (Andrew Yang, Christian Merten) is actively
being extended.
-/

open CategoryTheory AlgebraicGeometry

variable {A : Over (Spec ↧(AlgebraicClosure ℚ))}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

/-
Hey cladue, Maybe i should consider moving this specific file to the abelian varieties folder, and
call it IntegralModel.lean
-/
variable (A) in
theorem AbelianVarieties.exists_numberField_model_of__over_algClosureRat : ∃ (E : Type)
    (_ : Field E) (_ : NumberField E) (_ : Algebra E (AlgebraicClosure ℚ)) (A₀ : Over (Spec ↧E))
    (_ : IsProper A₀.hom) (_ : GeometricallyIntegral A₀.hom) (_ : AddGrpObj A₀),
    Nonempty (AddGrp.mk (A₀ _ (AlgebraicClosure ℚ)) ≅ AddGrp.mk A) := sorry
