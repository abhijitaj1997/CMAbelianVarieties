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

variable {K₀ : Type u} [Field K₀]
variable {A : Over (Spec ↧K₀)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable {K : Type u} [Field K] [Algebra K₀ K]

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
    exact RingCat.ofHom (RationalEnd.baseChangeHom A L₁ L₂)
  -- proof written by Claude
  map_id L := by
    ext1
    simp only [RingCat.hom_id, RingCat.hom_ofHom]
    convert baseChangeHom_self A L
    exact Algebra.algebra_ext _ _ fun _ ↦ rfl
  -- proof written by Claude
  map_comp {L₁ L₂ L₃} f g := by
    ext1
    simp only [RingCat.hom_comp, RingCat.hom_ofHom]
    algebraize [((IntermediateField.inclusion (leOfHom f) : L₁ →ₐ[K₀] L₂) : L₁ →+* L₂),
      ((IntermediateField.inclusion (leOfHom g) : L₂ →ₐ[K₀] L₃) : L₂ →+* L₃),
      ((IntermediateField.inclusion (leOfHom (f ≫ g)) : L₁ →ₐ[K₀] L₃) : L₁ →+* L₃)]
    have : IsScalarTower K₀ L₁ L₂ := ⟨fun x y z ↦ by
      ext; simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc]⟩
    have : IsScalarTower K₀ L₂ L₃ := ⟨fun x y z ↦ by
      ext; simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc]⟩
    have : IsScalarTower K₀ L₁ L₃ := ⟨fun x y z ↦ by
      ext; simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc]⟩
    have : IsScalarTower L₁ L₂ L₃ := ⟨fun x y z ↦ by
      ext; simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc]⟩
    exact (baseChangeHom_comp A L₁ L₂ L₃).symm

variable (A K) in
def limitRatEnd : Limits.Cocone (R₀ A K) where
  pt := ↧(End⁰ (A _ K))
  ι := {
    app L := RingCat.ofHom (RationalEnd.baseChangeHom A L K)
    -- proof written by Claude
    naturality L₁ L₂ f := by
      ext1
      simp only [R₀, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
        RingCat.hom_comp, RingCat.hom_ofHom]
      algebraize [((IntermediateField.inclusion (leOfHom f) : L₁ →ₐ[K₀] L₂) : L₁ →+* L₂)]
      have : IsScalarTower K₀ L₁ L₂ := ⟨fun x y z ↦ by
        ext; simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc]⟩
      have : IsScalarTower L₁ L₂ K := ⟨fun x y z ↦ by
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc]⟩
      exact baseChangeHom_comp A L₁ L₂ K
  }

-- pick up from here : we need to use this to prove `RationalEnd.exists_finiteDimensional_model`
variable (A K) in
def limitRatEnd.isColimit : Limits.IsColimit (limitRatEnd A K) := sorry

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
Suggestion written by Claude: what is left to shorten the base-change bookkeeping.

1. Basic.lean, next to `basechange_over_Field.proj` and `trans`:
   - `proj_self : proj X K₁ K₁ = 𝟙 _`, for any `[Algebra K₁ K₁]` with
     `algebraMap K₁ K₁ = RingHom.id _` (so that it also applies to the `algebraize` instances
     in `R₀`). Currently only a local `have hproj` in `baseChangeHom_self`.
   - `proj_comp : proj X K₂ K₃ ≫ proj X K₁ K₂ = proj X K₁ K₃`.
     Currently only a local `have hproj` in `baseChangeHom_comp`.
   - `@[reassoc (attr := simp)] proj_fst : proj X K₁ K₂ ≫ pullback.fst _ _ = pullback.fst _ _`
   - `@[reassoc (attr := simp)]` lemmas for `(trans X K₁ K₂).hom.left ≫ pullback.fst/snd` and
     `(trans X K₁ K₂).inv.left ≫ pullback.fst/snd`, so that proofs never need
     `simp [basechange_over_Field.trans]`.
   - `refl_addGrpObj : mk G ≅ mk (G _ K)` (like `trans_addGrpObj`), so that
     `rational_end_morphism_eq_baseChangeHom_comp` can be stated without `have`/`let`
     and its uses do not need `dsimp only at`.

2. Defn.lean: `Iso` constructions for `CMStructure.basechange'`, e.g.
   `((ι.basechange' K₂).basechange' K₃).Iso (ι.basechange' K₃)` (`Iso.refl` plus
   `baseChangeHom_comp`), and one relating `basechange'` to `basechange`.

3. Theorem.lean: use 2 for `ι''` (line 67), `ι₀` (line 79), and the
   `⟨trans_addGrpObj .., rfl⟩` / `basechangeTrans` / `basechange.refl` chains in `P₁` and `P₂`.

4. Pottentially.lean (around lines 42-75) still unfolds `trans_addGrpObj` and
   `rational_end_morphism` by hand; shorten it with `baseChangeHom` and its lemmas.

5. `RationalEnd.baseChangeHom_eq_map` (EndomorphismRing.lean) is no longer used; delete it.

None of this needs `eqToIso` / `eqToHom`.
-/
