/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.RationalModel.Affine

/-!
## Goal

The goal of this file is to show that a seperated scheme `X` of finite type over
`AlgebraicClosure ℚ` has a model over a number field that is also separated and of
finite type. That is, there is a number field `E` and a seperated scheme of finite
type `X₀` over `E`, such that `X₀ _ (AlgebraicClosure ℚ) ≅ X`.

-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {K : Type u} [Field K]
variable {X : Over (Spec ↧(AlgebraicClosure K))} [IsSeparated X.hom]

lemma nameless (𝒰 : X.left.OpenCover)
    [∀ i : 𝒰.I₀, IsAffine (𝒰.X i)]:
    ∀ i j : 𝒰.I₀, IsAffine ((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange : X.left.Opens) := by
  intro i j
  #check Limits.pullback (𝒰.f i) (𝒰.f j)
  #check ((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange : X.left.Opens)
  sorry

-- aided by claude
variable (X) in
theorem exists_model_of_isSeparated_of_locallyOfFiniteType [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧
    ∃ X₀ : Over (Spec ↧E), IsAffine X₀.left ∧ LocallyOfFiniteType X₀.hom ∧
    Nonempty ((X₀ _ (AlgebraicClosure K)) ≅ X) := by
  let 𝒰 : X.left.OpenCover := X.left.affineCover.finiteSubcover
  have (i : 𝒰.I₀) : IsAffine (Over.mk (𝒰.f i ≫ X.hom)).left := inferInstanceAs (IsAffine (𝒰.X i))
  have (i : 𝒰.I₀) : LocallyOfFiniteType (Over.mk (𝒰.f i ≫ X.hom)).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝒰.f i ≫ X.hom))
  let model (i : 𝒰.I₀) :=
    exists_model_of_isAffine_of_locallyOfFiniteType (Over.mk (𝒰.f i ≫ X.hom))
  let E' (i : 𝒰.I₀) : IntermediateField K (AlgebraicClosure K) := (model i).choose
  let E := ⨆ i : 𝒰.I₀, E' i
  have (i : 𝒰.I₀) : Algebra (E' i) E := sorry
  have : FiniteDimensional K E :=
    have (i : 𝒰.I₀) : FiniteDimensional K (model i).choose := (model i).choose_spec.1
    IntermediateField.finiteDimensional_iSup_of_finite
  let U (i : 𝒰.I₀) : Over (Spec ↧E) :=
    ((model i).choose_spec.2.choose : Over (Spec ↧(E' i))) _ E
  /- (Written by AI.) Gluing the `U i`.

  Structure: `AlgebraicGeometry.Scheme.GlueData` (Mathlib/AlgebraicGeometry/Gluing.lean).
  To build `D : Scheme.GlueData` we need:
  - `J := 𝒰.I₀` and `U i := (U i).left`.
  - `V (i, j)`: a scheme with an open immersion `f i j : V (i, j) ⟶ U i`. This should be a
    model over `E` of the intersection `(𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange`, seen inside
    `U i`. (`X` separated + `𝒰.X i` affine ⇒ these intersections are affine.)
  - `t i j : V (i, j) ⟶ V (j, i)`: the transition isomorphisms. Over `AlgebraicClosure K`
    these are `pullbackSymmetry`, as in `Scheme.OpenCover.gluedCover`.
  - `t' i j k`: the maps on triple overlaps
    `pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)`.
  - Axioms: `f_id : IsIso (f i i)`, `t_id : t i i = 𝟙 _`, `t_fac : t' i j k ≫ pullback.snd _ _ =
    pullback.fst _ _ ≫ t i j`, `cocycle : t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`,
    and `f_open : IsOpenImmersion (f i j)`.

  What we get from it:
  - `D.glued : Scheme`, with open immersions `D.ι i : D.U i ⟶ D.glued` and the open cover
    `D.openCover`.
  - The structure map `D.glued ⟶ Spec ↧E`: glue the `(U i).hom` with
    `Scheme.Cover.glueMorphisms D.openCover (fun i ↦ (U i).hom) _` (compatibility on the `V`s).
  - Comparison with `X`: Mathlib glues `X`'s own cover via `𝒰.gluedCover` and has
    `IsIso 𝒰.fromGlued : 𝒰.gluedCover.glued ⟶ X.left`. So one shows `D` base changed to
    `AlgebraicClosure K` is `𝒰.gluedCover` (base change commutes with gluing along an open
    cover; this is not in Mathlib) and then composes with `𝒰.fromGlued`.

  Warning: `E := ⨆ i, E' i` is not enough. The `V (i, j)`, `t i j`, `t' i j k` exist over
  `AlgebraicClosure K` but must be descended to a finite extension, which may be bigger:
  - Opens: each intersection is a finite union of basic opens `D(g)` with
    `g ∈ Γ(U i _ (AlgebraicClosure K))`; enlarge `E` by the finitely many coefficients of the `g`s.
  - Morphisms (`t`, `t'`) and the equalities (`t_id`, `t_fac`, `cocycle`) descend to some finite
    extension: `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`,
    `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
    (Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean), using
    `Spec ↧(AlgebraicClosure K) = lim Spec ↧E'` over finite `E'`.
  The index is finite, so finitely many enlargements still give a finite extension. So it is
  easier to first collect all the data over `AlgebraicClosure K`, then take one compositum. -/
  sorry
