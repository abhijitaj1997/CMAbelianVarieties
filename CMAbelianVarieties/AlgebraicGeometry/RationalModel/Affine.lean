/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Extension.Presentation.Core

/-!
## Goal

The goal of this file is to show that a affine scheme `X` of finite type over
`AlgebraicClosure K` has a model over a finite extension of `K` that is also
affine and of finite type. That is, there is a finite extension `E/K` and a
seperated scheme of finite type `X₀` over `E`, such that
`X₀ _ (AlgebraicClosure K) ≅ X`.

-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {K : Type u} [Field K]

-- written by Claude
open TensorProduct in
/-- A finite type algebra `A` over an algebraic extension `L/K` has a model `A₀` over a
finite extension `E/K` inside `L`, i.e. `L ⊗[E] A₀ ≃ₐ[L] A`. We take `E` to be generated over `K`
by the coefficients of the relations of a finite presentation of `A`. -/
lemma exists_model_of_finiteType {L A : Type u} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [CommRing A] [Algebra L A] [Algebra.FiniteType L A] :
    ∃ (E : IntermediateField K L) (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra E A₀),
      FiniteDimensional K E ∧ Algebra.FiniteType E A₀ ∧ Nonempty (L ⊗[E] A₀ ≃ₐ[L] A) := by
  have : Algebra.FinitePresentation L A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let P := Algebra.Presentation.ofFinitePresentation L A
  let E := IntermediateField.adjoin K P.coeffs
  have : Finite P.coeffs := P.finite_coeffs
  have : P.HasCoeffs E := ⟨fun x hx ↦ ⟨⟨x, IntermediateField.subset_adjoin K _ hx⟩, rfl⟩⟩
  exact ⟨E, P.ModelOfHasCoeffs E, inferInstance, inferInstance,
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x,
    inferInstance, ⟨P.tensorModelOfHasCoeffsEquiv E⟩⟩

-- written by Claude
theorem exists_model_of_isAffine_of_locallyOfFiniteType (X : Over (Spec ↧(AlgebraicClosure K)))
    [LocallyOfFiniteType X.hom] [IsAffine X.left] :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧
      ∃ X₀ : Over (Spec ↧E), IsAffine X₀.left ∧ LocallyOfFiniteType X₀.hom ∧
        Nonempty ((X₀ _ (AlgebraicClosure K)) ≅ X) := by
  algebraize [((Scheme.ΓSpecIso ↧(AlgebraicClosure K)).inv ≫ X.hom.appTop).hom]
  have : Algebra.FiniteType (AlgebraicClosure K) Γ(X.left, ⊤) :=
    (HasRingHomProperty.appTop @LocallyOfFiniteType X.hom ‹_›).comp
      (.of_surjective _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.surjective)
  obtain ⟨E, A₀, _, _, hE, hA₀, ⟨e⟩⟩ :=
    exists_model_of_finiteType (K := K) (L := AlgebraicClosure K) (A := Γ(X.left, ⊤))
  have h : X.hom = X.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure K) Γ(X.left, ⊤))) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_comp,
      ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Scheme.isoSpec_Spec_hom,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  let f : TensorProduct E A₀ (AlgebraicClosure K) ≃+* Γ(X.left, ⊤) :=
    (Algebra.TensorProduct.comm E A₀ (AlgebraicClosure K)).toRingEquiv.trans e.toRingEquiv
  refine ⟨E, hE, Over.mk (Spec.map (CommRingCat.ofHom (algebraMap E A₀))),
    inferInstanceAs (IsAffine (Spec _)),
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr hA₀), ⟨Over.isoMk
      (pullbackSpecIso E A₀ (AlgebraicClosure K) ≪≫ Scheme.Spec.mapIso f.symm.toCommRingCatIso.op ≪≫
        X.left.isoSpec.symm) ?_⟩⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, h, Iso.inv_hom_id_assoc]
  refine Eq.trans ?_ (pullbackSpecIso_hom_snd E A₀ (AlgebraicClosure K))
  rw [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, ← Spec.map_comp]
  congr 2
  ext x
  simp [f]
