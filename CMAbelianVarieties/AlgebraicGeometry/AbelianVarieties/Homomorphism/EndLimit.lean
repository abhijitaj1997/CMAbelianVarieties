/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.AbelianVarieties.Homomorphism.EndomorphismRing

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

-- aided by claude
variable (A K) in
open AddGrp in
def RatEnd : (IntermediateField K₀ K) ⥤ RingCat.{u} where
  obj L := ↧(End⁰ (A _ L))
  map f := by
    rename_i L₁ L₂
    algebraize [((IntermediateField.inclusion (leOfHom f) : L₁ →ₐ[K₀] L₂) : L₁ →+* L₂)]
    have : IsScalarTower K₀ L₁ L₂ := {
      smul_assoc x y z:= by
        ext
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc]
    }
    exact RingCat.ofHom (baseChangeHom A L₁ L₂)
  map_id L := by
    ext1
    simp only [RingCat.hom_id, RingCat.hom_ofHom]
    convert baseChangeHom_self A L
    exact Algebra.algebra_ext _ _ fun _ ↦ rfl
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

-- aided by claude
variable (A K) in
def limitRatEnd : Limits.Cocone (RatEnd A K) where
  pt := ↧(End⁰ (A _ K))
  ι := {
    app L := RingCat.ofHom (baseChangeHom A L K)
    naturality L₁ L₂ f := by
      ext1
      simp only [RatEnd, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
        RingCat.hom_comp, RingCat.hom_ofHom]
      algebraize [((IntermediateField.inclusion (leOfHom f) : L₁ →ₐ[K₀] L₂) : L₁ →+* L₂)]
      have : IsScalarTower K₀ L₁ L₂ := ⟨fun x y z ↦ by
        ext; simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc]⟩
      have : IsScalarTower L₁ L₂ K := ⟨fun x y z ↦ by
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc]⟩
      exact baseChangeHom_comp A L₁ L₂ K
  }

-- written by Claude
variable (A K) in
/-- `RatEnd A K` restricted to the intermediate fields that are finite over `K₀`. -/
def RatEndFin : {L : IntermediateField K₀ K // FiniteDimensional K₀ L} ⥤ RingCat.{u} :=
  (Subtype.mono_coe _).functor ⋙ RatEnd A K

-- written by Claude
variable (A K) in
/-- The cocone `limitRatEnd A K` restricted to `RatEndFin A K`. -/
def limitRatEndFin : Limits.Cocone (RatEndFin A K) :=
  (limitRatEnd A K).whisker _

/- When I get down to solving this, I need to consider what assumption I need to pu on the extension
`K/K₀`. I do not think any assumption is needed, but claude suggested it might be easier if I added
`IsAlgebraic`.
-/
variable (A K) in
def limitRatEnd.isColimit : Limits.IsColimit (limitRatEndFin A K) := sorry
