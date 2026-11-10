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


















/-
_This file is being replaced by `Separated_.lean`_
-/
















open CategoryTheory AlgebraicGeometry
open scoped BaseChange

universe u

variable {K : Type u} [Field K]
variable {X : Over (Spec ↧(AlgebraicClosure K))} [IsSeparated X.hom]

lemma isAffine_opensRange_inf_opensRange (𝒰 : X.left.OpenCover)
    [∀ i : 𝒰.I₀, IsAffine (𝒰.X i)]:
    ∀ i j : 𝒰.I₀, IsAffine ((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange : X.left.Opens) := by
  intro i j
  #check Limits.pullback (𝒰.f i) (𝒰.f j)
  #check ((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange : X.left.Opens)
  sorry

/- Hey claude, the results about affine schemes should be moved to the file `Affine.lean`-/

-- written by AI (Claude)
/-- Every element of the bottom right corner `P` of a pushout square in `CommRingCat` is a sum
of products `inl x * inr y` (since `P ≅ B ⊗[A] C`). -/
lemma CommRingCat.isPushout_induction {A B C P : CommRingCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr) {Q : P → Prop}
    (mul : ∀ x y, Q (inl x * inr y)) (add : ∀ p q, Q p → Q q → Q (p + q)) (p : P) : Q p := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  have ht := CommRingCat.isPushout_tensorProduct A B C
  obtain ⟨t, rfl⟩ : ∃ t, (ht.isoIsPushout _ _ h).hom t = p :=
    ⟨(ht.isoIsPushout _ _ h).inv p, by simp⟩
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    have hl := ConcreteCategory.congr_hom (IsPushout.inl_isoIsPushout_hom (h := ht) (h' := h)) x
    have hr := ConcreteCategory.congr_hom (IsPushout.inr_isoIsPushout_hom (h := ht) (h' := h)) y
    rw [← mul_one x, ← one_mul y, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul]
    convert mul x y
    · exact hl
    · exact hr
  | add s t hs ht => simpa using add _ _ hs ht

-- statement and proof written by AI (Claude)
open Limits in
/-- A quasi-compact open of `U _ L` already comes from `U _ F'` for some finite subextension
`F'` of `L/F`. Idea: write it as a finite union of basic opens `D(g)`, and adjoin to `F`
the finitely many coefficients of the `g`s in `Γ(U) ⊗[F] L`. Alternatively, it is
`exists_preimage_eq` (Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean), once `U _ L` is
the limit of the `U _ F'`. -/
lemma exists_opens_basechange_of_isCompact {F L : Type u} [Field F] [Field L] [Algebra F L]
    [Algebra.IsAlgebraic F L] (U : Over (Spec ↧F)) [IsAffine U.left]
    (W : (U _ L).left.Opens) (hW : IsCompact (W : Set (U _ L).left)) :
    ∃ F' : IntermediateField F L, FiniteDimensional F F' ∧
      ∃ W₀ : (U _ F').left.Opens, basechange_over_Field.proj U F' L ⁻¹ᵁ W₀ = W := by
  classical
  -- every global section of `U _ L` comes from `U _ F'` once `F'` contains a finite set `s`
  have key : ∀ g : Γ((U _ L).left, ⊤), ∃ s : Finset L, ∀ F' : IntermediateField F L,
      (s : Set L) ⊆ F' →
        ∃ g' : Γ((U _ F').left, ⊤), (basechange_over_Field.proj U F' L).appTop g' = g := by
    refine CommRingCat.isPushout_induction
      (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback _ _)) (fun x y ↦ ?_)
      fun p q ⟨s, hs⟩ ⟨t, ht⟩ ↦ ?_
    · refine ⟨{(Scheme.ΓSpecIso _).hom y}, fun F' hF' ↦ ⟨Scheme.Hom.appTop
        (pullback.fst U.hom (Spec.map (CommRingCat.ofHom (algebraMap F F')))) x *
        Scheme.Hom.appTop (pullback.snd U.hom (Spec.map (CommRingCat.ofHom (algebraMap F F'))))
          ((Scheme.ΓSpecIso (.of F')).inv
            ⟨_, hF' (Finset.mem_coe.2 (Finset.mem_singleton_self _))⟩), ?_⟩⟩
      rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← Scheme.Hom.comp_appTop]
      simp only [basechange_over_Field.proj, pullback.lift_fst, pullback.lift_snd,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      congr 2
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      exact (Scheme.ΓSpecIso _).hom_inv_id_apply y
    · refine ⟨s ∪ t, fun F' hF' ↦ ?_⟩
      rw [Finset.coe_union, Set.union_subset_iff] at hF'
      obtain ⟨p', rfl⟩ := hs F' hF'.1
      obtain ⟨q', rfl⟩ := ht F' hF'.2
      exact ⟨p' + q', map_add _ _ _⟩
  -- write `W` as a finite union of basic opens and descend each of them
  have : IsAffine (U _ L).left := inferInstanceAs (IsAffine (pullback _ _))
  obtain ⟨Us, hUs, hUsf, rfl⟩ := (isBasis_basicOpen _).exists_finite_of_isCompact hW
  have := hUsf.to_subtype
  choose g hg using fun V : Us ↦ hUs V.2
  choose s hs using fun V : Us ↦ key (g V)
  let S : Set L := ⋃ V, (s V : Set L)
  have : Finite S := Set.finite_iUnion (fun V ↦ (s V).finite_toSet) |>.to_subtype
  let F' := IntermediateField.adjoin F S
  choose g' hg' using fun V : Us ↦ hs V F'
    ((Set.subset_iUnion (fun V ↦ (s V : Set L)) V).trans (IntermediateField.subset_adjoin F S))
  refine ⟨F', IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x,
    ⨆ V, (U _ F').left.basicOpen (g' V), ?_⟩
  simp only [Scheme.Hom.preimage_iSup, Scheme.preimage_basicOpen_top, hg', hg, sSup_eq_iSup']

-- aided by claude
variable (X) in
theorem exists_model_of_isSeparated_of_locallyOfFiniteType [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧
    ∃ X₀ : Over (Spec ↧E), IsSeparated X₀.hom ∧ LocallyOfFiniteType X₀.hom ∧
    Nonempty ((X₀ _ (AlgebraicClosure K)) ≅ X) := by
  let 𝒰 : X.left.OpenCover := X.left.affineCover.finiteSubcover
  have h𝒰_aff (i : 𝒰.I₀) : IsAffine (Over.mk (𝒰.f i ≫ X.hom)).left :=
    inferInstanceAs (IsAffine (𝒰.X i))
  have h𝒰_fty (i : 𝒰.I₀) : LocallyOfFiniteType (Over.mk (𝒰.f i ≫ X.hom)).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝒰.f i ≫ X.hom))
  let model (i : 𝒰.I₀) :=
    exists_model_of_isAffine_of_locallyOfFiniteType (Over.mk (𝒰.f i ≫ X.hom))
  let E₀' (i : 𝒰.I₀) : IntermediateField K (AlgebraicClosure K) := (model i).choose
  let E₀ := ⨆ i : 𝒰.I₀, E₀' i
  let (i : 𝒰.I₀) : Algebra (E₀' i) E₀ :=
    (IntermediateField.inclusion (le_iSup E₀' i)).toRingHom.toAlgebra
  have : FiniteDimensional K E₀ :=
    have (i : 𝒰.I₀) : FiniteDimensional K (model i).choose := (model i).choose_spec.1
    IntermediateField.finiteDimensional_iSup_of_finite
  let U' (i : 𝒰.I₀) : Over (Spec ↧E₀) :=
    ((model i).choose_spec.2.choose : Over (Spec ↧(E₀' i))) _ E₀
  let W (i j : 𝒰.I₀) : X.left.Opens := (𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange
  have hW_aff (i j : 𝒰.I₀) : IsAffine (Over.mk ((W i j).ι ≫ X.hom)).left :=
    have : IsAffine (𝒰.f i).opensRange := isAffineOpen_opensRange (𝒰.f i)
    have : IsAffine (𝒰.f j).opensRange := isAffineOpen_opensRange (𝒰.f j)
    -- note by AI (Claude): commented out, since `intersectionOpens_ofSeparated` changed its
    -- statement (it is now about `finiteAffineCover`) and no longer fits here.
    -- intersectionOpens_ofSeparated _ _
    sorry
  have (i : 𝒰.I₀) : IsScalarTower (E₀' i) E₀ (AlgebraicClosure K) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have hU'_aff (i : 𝒰.I₀) : IsAffine (U' i).left :=
    have := (model i).choose_spec.2.choose_spec.1
    inferInstanceAs (IsAffine (Limits.pullback _ _))
  let eU' (i : 𝒰.I₀) : (U' i) _ (AlgebraicClosure K) ≅ Over.mk (𝒰.f i ≫ X.hom) :=
    basechange_over_Field.trans _ E₀ (AlgebraicClosure K) ≪≫
      (model i).choose_spec.2.choose_spec.2.2.some
  -- `W i j`, seen inside `U' i _ (AlgebraicClosure K)`
  let W' (i j : 𝒰.I₀) : ((U' i) _ (AlgebraicClosure K)).left.Opens :=
    (eU' i).hom.left ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ W i j
  have hW' (i j : 𝒰.I₀) : IsCompact (W' i j : Set ((U' i) _ (AlgebraicClosure K)).left) := by
    refine (eU' i).hom.left.isOpenEmbedding.isInducing.isCompact_preimage' ?_ ?_
    · refine (𝒰.f i).isOpenEmbedding.isInducing.isCompact_preimage' ?_ fun x hx ↦ hx.1
      exact IsAffineOpen.isCompact (hW_aff i j)
    · exact fun x _ ↦ ⟨(eU' i).inv.left x, by
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Iso.inv_hom_id, Over.id_left]; rfl⟩
  have desc (i j : 𝒰.I₀) := exists_opens_basechange_of_isCompact (U' i) (W' i j) (hW' i j)
  let F (i j : 𝒰.I₀) : IntermediateField E₀ (AlgebraicClosure K) := (desc i j).choose
  let E := E₀ ⊔ ⨆ (i : 𝒰.I₀) (j : 𝒰.I₀), (F i j).restrictScalars K
  have : FiniteDimensional K E :=
    have (i j : 𝒰.I₀) : FiniteDimensional K ((F i j).restrictScalars K) :=
      have : FiniteDimensional E₀ (F i j) := (desc i j).choose_spec.1
      FiniteDimensional.trans K E₀ (F i j)
    IntermediateField.finiteDimensional_sup _ _
  let : Algebra E₀ E := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
  let (i j : 𝒰.I₀) : Algebra (F i j) E :=
    (IntermediateField.inclusion (E := (F i j).restrictScalars K)
      ((le_iSup₂ (f := fun i j ↦ (F i j).restrictScalars K) i j).trans
        le_sup_right)).toRingHom.toAlgebra
  have : IsScalarTower E₀ E (AlgebraicClosure K) := .of_algebraMap_eq fun _ ↦ rfl
  have (i j : 𝒰.I₀) : IsScalarTower E₀ (F i j) E := .of_algebraMap_eq fun _ ↦ rfl
  let U (i : 𝒰.I₀) : Over (Spec ↧E) := (U' i) _ E
  let V (i j : 𝒰.I₀) : (U i).left.Opens :=
    basechange_over_Field.proj (U' i) (F i j) E ⁻¹ᵁ (desc i j).choose_spec.2.choose
  let eU (i : 𝒰.I₀) : (U i) _ (AlgebraicClosure K) ≅ Over.mk (𝒰.f i ≫ X.hom) :=
    basechange_over_Field.trans (U' i) E (AlgebraicClosure K) ≪≫ eU' i
  sorry




/- (Written by AI.) Steps to finish `exists_model_of_isSeparated_of_locallyOfFiniteType`.
Notation as in the proof; `K̄ := AlgebraicClosure K`. Done so far: the finite affine cover `𝒰`,
the models `U i` over `E`, the opens `V i j ⊆ U i` descending `W i j`, and the isos `eU i`.


Step 1 (lemma: descending ring maps). For finitely generated `E`-algebras `A`, `B` and a
`K̄`-algebra map `φ : K̄ ⊗[E] A → K̄ ⊗[E] B`, there is a finite `E ⊆ E' ⊆ K̄` and an
`E'`-algebra map `E' ⊗[E] A → E' ⊗[E] B` whose base change is `φ`. Proof: adjoin the
coefficients of the images of the generators of `A` (as for `key` in
`exists_opens_basechange_of_isCompact`); relations hold over `E'` by Step 2.


Step 2 (lemma: equalities descend for free). For `E' ⊆ K̄`, the map `E' ⊗[E] B → K̄ ⊗[E] B`
is injective (`K̄` is flat over `E'`). So two morphisms of affine `E'`-schemes that agree
after base change to `K̄` are equal.


Step 3 (affine overlaps). Make `V i j` (and `V i j ⊓ V i k`) affine over a finite extension.
Over `K̄` they are affine (`X` separated, `intersectionOpens_ofSeparated`). Options: descend
affineness (`Y → Spec Γ(Y)` is an iso after base change, and isomorphisms descend,
`FlatDescent.lean`; needs `Γ` commuting with flat base change), or
`Scheme.exists_isAffine_of_isLimit`.


Step 4 (transition maps). Descend `t i j : V i j ≅ V j i`; over `K̄` it is
`eU i`, then the identity of `W i j`, then `(eU j).symm`. Descend the map and its inverse by
Step 1; both composites are the identity by Step 2.


Step 5 (triple overlaps). Show that `t i j` maps `V i j ⊓ V i k` into `V j k ⊓ V j i` (check
after base change; the projection to `U i` is surjective), giving `t' i j k`.


Step 6 (gluing axioms). `f_id`, `t_id`, `t_fac`, `cocycle`: by Step 2 it suffices to check
them over `K̄`, where they are the axioms of `𝒰.gluedCover`.


Step 7 (one field). Replace `E` by the compositum of the finitely many fields from Steps 3–6
(finite, as `𝒰.I₀` is finite) and base change all data to it (`basechange_over_Field.trans`).


Step 8 (glue). Build `D : Scheme.GlueData` and set `X₀ := Over.mk (D.openCover.glueMorphisms
(fun i ↦ (U i).hom) _)` (compatible on the `V i j` since the `t i j` are over `E`).


Step 9 (`LocallyOfFiniteType X₀.hom`). Local on the source; each `U i` is of finite type.


Step 10 (`X₀ _ K̄ ≅ X`; base change commutes with gluing, not in Mathlib). The pullback of
`D.openCover` covers `X₀ _ K̄` by the `U i _ K̄`. Glue `eU i ≫ 𝒰.f i` to a map
`X₀ _ K̄ ⟶ X` and the inverses to `X ⟶ X₀ _ K̄` (compatible on overlaps by Step 4); check
both composites are identities on the covers.


Step 11 (`IsSeparated X₀.hom`). Criterion: glued from affines `U i` with `V i j` affine and
`Γ(U i) ⊗[E] Γ(U j) → Γ(V i j)` surjective ⇒ separated (find in Mathlib or prove, e.g. via
`isSeparated_iff_isClosedImmersion_prod_lift`). Surjectivity holds after `⊗[E] K̄` (`X`
separated), hence over `E` (`K̄` faithfully flat over `E`).


Step 12 (assemble). `refine ⟨E, _, X₀, _, _, ⟨_⟩⟩` with Steps 7, 11, 9, 10. -/
