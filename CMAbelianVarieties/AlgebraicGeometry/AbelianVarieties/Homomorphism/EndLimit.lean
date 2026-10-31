/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.AbelianVarieties.Homomorphism.EndomorphismRing
public import Mathlib.Algebra.Colimit.DirectLimit

/-!
## Goal

In this file, we will show that `End (A _ K)` is the colimit of the endomorphism rings
`End (A _ L)`, where `L : IntermediateField K₀ K`.

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry RationalEnd
open scoped BaseChange AddGrp.End

universe u

variable {K₀ K : Type u} [Field K₀] [Field K] [Algebra K₀ K]
variable {A : Over (Spec ↧K₀)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

variable (A K) in
open AddGrp in
def R₀ : (IntermediateField K₀ K) ⥤ RingCat.{u} where
  obj L := ↧(End⁰ (A _ L))
  map f := by
    rename_i L₁ L₂
    algebraize [((IntermediateField.inclusion (leOfHom f) : L₁ →ₐ[K₀] L₂) : L₁ →+* L₂)]
    have : IsScalarTower K₀ L₁ L₂ := {
      smul_assoc x y z:= by
        ext
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc]
    }
    exact RingCat.ofHom ((conjAlgEquiv (basechange_over_Field.trans_addGrpObj A L₁
      L₂)).toRingHom.comp (rational_end_morphism (A _ L₁) L₂))
  -- proof written by Claude
  map_id L := by
    ext1
    simp only [rational_end_morphism, AlgHom.toRingHom_eq_coe, conjAlgEquiv]
    ext
    · simp
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
          Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.map_tmul, eq_ratCast, Rat.cast_one,
          Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom, AlgEquiv.coe_toAlgHom,
          RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingCat.hom_ofHom,
          RingCat.hom_id, RingHom.id_apply]
      congr 1
      ext : 3
      simp only [Iso.conjAlgEquiv, Iso.conjRingEquiv, MulEquiv.toEquiv_eq_coe,
        RingEquiv.coe_toIntAlgEquiv, RingEquiv.coe_mk, EquivLike.coe_coe, Iso.conj_apply_asHom]
      erw [AddGrp.comp_hom_hom, AddGrp.comp_hom_hom]
      simp only [Over.comp_left]
      have hm : Spec.map (CommRingCat.ofHom (algebraMap L L)) = 𝟙 _ := by
        rw [← Spec.map_id]
        rfl
      apply Limits.pullback.hom_ext
      · simp only [RationalEnd.End.algHom_ofBaseChange, AddGrp.End.algHom_ofBaseChange,
          basechange_over_Field.trans_addGrpObj, basechange_over_Field.trans]
        simp only [Over.pullback_obj_left, Over.pullback_obj_hom, mkIso'_inv_hom_hom,
          Over.isoMk_inv_left, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
          Over.pullback_map_left, mkIso'_hom_hom_hom, Over.isoMk_hom_left, Category.assoc,
          Limits.limit.lift_π, Limits.PullbackCone.mk_pt, Limits.PullbackCone.mk_π_app,
          Limits.limit.lift_π_assoc, Limits.cospan_left]
        convert Category.id_comp ?_ using 2
        apply Limits.pullback.hom_ext
        · simp
        · simp only [Limits.pullback.lift_snd, Category.id_comp]
          erw [hm]
          simp
      · simp only [Over.pullback_obj_left, Over.pullback_obj_hom,
          basechange_over_Field.trans_addGrpObj, basechange_over_Field.trans, mkIso'_inv_hom_hom,
          Over.isoMk_inv_left, RationalEnd.End.algHom_ofBaseChange,
          AddGrp.End.algHom_ofBaseChange, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
          OneHom.coe_mk, Over.pullback_map_left, mkIso'_hom_hom_hom, Over.isoMk_hom_left,
          Category.assoc, Limits.limit.lift_π, Limits.PullbackCone.mk_pt,
          Limits.PullbackCone.mk_π_app]
        rename_i f
        exact (Over.w f.asHom.hom.hom).symm
  -- proof written by Claude
  map_comp {L₁ L₂ L₃} f g := by
    ext1
    simp only [rational_end_morphism, AlgHom.toRingHom_eq_coe, conjAlgEquiv]
    ext
    · simp
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
          Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.map_tmul, eq_ratCast, Rat.cast_one,
          Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom, AlgEquiv.coe_toAlgHom,
          RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingCat.hom_ofHom,
          RingCat.hom_comp]
      congr 1
      ext : 3
      simp only [Iso.conjAlgEquiv, Iso.conjRingEquiv, MulEquiv.toEquiv_eq_coe,
        RingEquiv.coe_toIntAlgEquiv, RingEquiv.coe_mk, EquivLike.coe_coe, Iso.conj_apply_asHom]
      erw [AddGrp.comp_hom_hom, AddGrp.comp_hom_hom, AddGrp.comp_hom_hom, AddGrp.comp_hom_hom]
      simp only [Over.comp_left]
      rename_i e
      apply Limits.pullback.hom_ext
      · simp only [Over.pullback_obj_left, Over.pullback_obj_hom,
          basechange_over_Field.trans_addGrpObj, basechange_over_Field.trans, mkIso'_inv_hom_hom,
          Over.isoMk_inv_left, RationalEnd.End.algHom_ofBaseChange,
          AddGrp.End.algHom_ofBaseChange, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
          OneHom.coe_mk, Over.pullback_map_left, mkIso'_hom_hom_hom, Over.isoMk_hom_left,
          Category.assoc, Limits.limit.lift_π, Limits.PullbackCone.mk_pt,
          Limits.PullbackCone.mk_π_app, Limits.limit.lift_π_assoc,
          Limits.cospan_left, Iso.conj_apply_asHom, comp', AddMon.comp_hom', Functor.map_comp,
          Over.comp_left]
        erw [AddGrp.comp_hom_hom]
        simp only [mkIso'_hom_hom_hom, Over.comp_left, Over.pullback_obj_left,
          Over.pullback_obj_hom, Over.pullback_map_left, Over.isoMk_hom_left, Category.assoc,
          Limits.limit.lift_π, Limits.PullbackCone.mk_pt, Limits.PullbackCone.mk_π_app,
          Limits.limit.lift_π_assoc, Limits.cospan_left]
        simp only [← Category.assoc]
        congr 2
        apply Limits.pullback.hom_ext
        · simp
        · simp only [Limits.pullback.lift_snd, Category.assoc, Limits.pullback.lift_snd_assoc]
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          rfl
      · simp [RationalEnd.End.algHom_ofBaseChange, AddGrp.End.algHom_ofBaseChange,
          basechange_over_Field.trans_addGrpObj, basechange_over_Field.trans]

def R : Limits.Cocone (R₀ K A) where
  pt := ↧(End⁰ (A _ K))
  ι := {
    app L :=
    { hom' := (conjAlgEquiv (basechange_over_Field.trans_addGrpObj A L K)).toRingHom.comp
        (rational_end_morphism (A _ L) K) }
    naturality L₁ L₂ f := by
      sorry
  }

-- written by Claude: two ways to say that a ring `R` is a colimit of rings `R i`
-- 1. Category theory: a functor `F : J ⥤ RingCat` and a colimit cocone over it (or `R ≅ colimit F`)
#check fun {J : Type u} [SmallCategory J] (F : J ⥤ RingCat.{u}) (c : Limits.Cocone F) =>
  Limits.IsColimit c
#check fun {J : Type u} [SmallCategory J] (F : J ⥤ RingCat.{u}) [Limits.HasColimit F]
  (R : RingCat.{u}) => R ≅ Limits.colimit F
-- 2. Direct limit of a directed system of rings `G i` with ring maps `f i j : G i →+* G j`
--    (`DirectLimit`, not `Ring.DirectLimit`, which needs commutative rings)
#check fun {ι : Type u} [Preorder ι] [IsDirectedOrder ι] (G : ι → Type u) [∀ i, Ring (G i)]
  (f : ∀ i j, i ≤ j → G i →+* G j) [DirectedSystem G fun i j h ↦ f i j h] (R : Type u) [Ring R] =>
  R ≃+* DirectLimit G f

/-
Suggestion written by Claude: lemmas that would shorten `R₀.map_id`, `R₀.map_comp`,
`R.ι.naturality`, `CMStructure.basechange.refl` / `basechange.trans` (Defn.lean) and the
base-change bookkeeping in Theorem.lean / Pottentially.lean.

All of these proofs prove the same kind of statement: an identity between composites of
`rational_end_morphism` and `conjAlgEquiv (trans_addGrpObj ..)`. Each time, they unfold
everything down to pullbacks. The unfolding boilerplate (tensor `ext`, `Iso.conjAlgEquiv`,
`erw [AddGrp.comp_hom_hom]`, long `simp only` lists, `pullback.hom_ext`) is repeated
verbatim. Proving the geometric fact once and the ring statements on top of it would
remove most of that.

1. Name the composite that keeps appearing (in `R₀.map`, `R.ι.app`, `basechange.trans`,
   `Pottentially`, and implicitly in `(ι.basechange K₂).ofIso (trans_addGrpObj ..)` in
   Theorem.lean):

     def RationalEnd.baseChangeHom (A : Over (Spec ↧K)) [..] (K₁ K₂ : Type u) [Field K₁]
         [Field K₂] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] :
         End⁰ (A _ K₁) →+* End⁰ (A _ K₂) :=
       (conjAlgEquiv (basechange_over_Field.trans_addGrpObj A K₁ K₂)).toRingHom.comp
         (rational_end_morphism (A _ K₁) K₂)

   (Possibly first at the level of `End (mk (A _ K₁)) →ₐ[ℤ] End (mk (A _ K₂))`, then
   tensored with `ℚ`, so that the ℚ-part is handled once by
   `Algebra.TensorProduct.ringHom_ext`.)

2. The geometric core: the projection `(A _ K₂).left ⟶ (A _ K₁).left`.

     def basechange_over_Field.proj (X : Over (Spec ↧K)) (K₁ K₂) [..] [IsScalarTower K K₁ K₂] :
         (X _ K₂).left ⟶ (X _ K₁).left :=
       pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (ofHom (algebraMap K₁ K₂)))
         (by ...)

   This is exactly the map that showed up in `map_id` and `map_comp`. With
     - `proj_self    : proj X K₁ K₁ = 𝟙 _`  (for any `[Algebra K₁ K₁]` with
                        `algebraMap K₁ K₁ = RingHom.id _`, to avoid the instance mismatch that
                        forced `erw [hm]` in `map_id`)
     - `proj_comp    : proj X K₂ K₃ ≫ proj X K₁ K₂ = proj X K₁ K₃`
                       (the `Spec.map_comp` step of `map_comp`)
     - `@[reassoc (attr := simp)] proj_fst : proj X K₁ K₂ ≫ pullback.fst _ _ = pullback.fst _ _`
     - `@[reassoc (attr := simp)]` lemmas for `(trans X K₁ K₂).hom.left ≫ pullback.fst/snd` and
       `(trans X K₁ K₂).inv.left ≫ pullback.fst/snd`, so that proofs never need
       `simp [basechange_over_Field.trans]` (which is what produces the huge `simp only`
       lists).

3. The characterising lemma for `baseChangeHom`: for `f : End (mk (A _ K₁))`, the
   endomorphism `g` it is sent to (on `A _ K₂`) is the unique endomorphism over `Spec K₂` with

     g.left ≫ proj A K₁ K₂ = proj A K₁ K₂ ≫ f.left

   i.e. one lemma `baseChangeHom_tmul_left_proj` plus an ext lemma "two endomorphisms of
   `A _ K₂` over `Spec K₂` are equal if they agree after `≫ pullback.fst`" (that is
   `pullback.hom_ext` with the `snd` component discharged once and for all by `Over.w`).

4. With 1–3, the ring-level statements are short and reusable:
     - `baseChangeHom_self : baseChangeHom A K₁ K₁ = RingHom.id _`              (`R₀.map_id`)
     - `baseChangeHom_comp : (baseChangeHom A K₂ K₃).comp (baseChangeHom A K₁ K₂) =
                             baseChangeHom A K₁ K₃`                              (`R₀.map_comp`,
       and `R.ι.naturality` is exactly this with `K₃ = K`, so `naturality` would be one line)
     - `rational_end_morphism A K₁ = (baseChangeHom A K K₁).comp (conjAlgEquiv refl-iso)`
       relating the two; then `CMStructure.basechange.refl` and `basechange.trans` in
       Defn.lean become `baseChangeHom_self` and `baseChangeHom_comp`.
     - In Theorem.lean, `(ι.basechange K₂).ofIso (trans_addGrpObj A K₁ K₂)` is the
       CM structure with `incl = (baseChangeHom A K₁ K₂).comp ι.incl`. A named
       `CMStructure.basechange'` with that `incl` (and `rfl` lemma), plus `baseChangeHom_comp`,
       would replace the repeated `⟨trans_addGrpObj .., rfl⟩` /
       `basechangeTrans` / `basechange.refl` chains in `P₁` and `P₂`.

5. Smaller: the `algebraize [...]` + `IsScalarTower K₀ L₁ L₂` boilerplate in `R₀.map` can be
   a definition `IntermediateField.algebraOfLE (h : L₁ ≤ L₂) : Algebra L₁ L₂` with instances /
   lemmas `IsScalarTower K₀ L₁ L₂` and `IsScalarTower L₁ L₂ K`. The latter is what
   `R.ι.naturality` needs, to apply `baseChangeHom_comp` to the tower `L₁ → L₂ → K`.

Order I would suggest: 2 (geometry, in Basic.lean next to `trans`), then 1 and 3
(EndomorphismRing.lean next to `rational_end_morphism`), then 4. None of this needs
`eqToIso` / `eqToHom`.
-/
