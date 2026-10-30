/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.Pottentially
public import CMAbelianVarieties.AlgebraicGeometry.AbelianVarieties.RationalModel

/-!
## Goal

In this section we prove the main result of this probject, which
states the following:

>   If `A` is a CM abelian variety over an algebraically closed field `K` of
>   characteristic 0, then it, along with the CM structure, has a model `A₀` over
>   a number field `E`, such that `K` is an `E`-algebra, and `A₀ _ K ≅ A` along
>   with its CM Strucutre.

-/

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField RationalEnd

/-
I removed the universe because I need to move through `AlgebraicClosure ℚ`, which is of `Type 0`.
I need to consider if this is okay, or wheather I need to generalise this
-/
--universe u

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K]
variable {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable {F : Type*} [Field F] [NumberField F] [IsCMField F]

namespace CMStructure

theorem exists_algClosureRat_model (ι : CMStructure A F) :
    ∃ (_ : Algebra (AlgebraicClosure ℚ) K) (A₀ : Over (Spec ↧((AlgebraicClosure ℚ))))
    (_ : IsProper A₀.hom) (_ : GeometricallyIntegral A₀.hom) (_ : AddGrpObj A₀)
    (ι₀ : CMStructure A₀ F), Nonempty ((ι₀.basechange K).Iso ι) := by
  sorry

-- partly solved and cleaned up by claude
theorem exists_finiteDimensional_model {L : Type*} [Field L]
    {A : Over (Spec ↧(AlgebraicClosure L))} [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (ι : CMStructure A F) : ∃ (E : IntermediateField L (AlgebraicClosure L))
    (_ : FiniteDimensional L E) (A₀ : Over (Spec ↧E)) (_ : IsProper A₀.hom)
    (_ : GeometricallyIntegral A₀.hom) (_ : AddGrpObj A₀) (ι₀ : CMStructure A₀ F),
    Nonempty ((ι₀.basechange (AlgebraicClosure L)).Iso ι) := by
  obtain ⟨E₁, _, A₁, _, _, _, hφ⟩ := AbelianVarieties.exists_finiteDimensional_model A
  let ι' : CMStructure (A₁ _ (AlgebraicClosure L)) F := ι.ofIso hφ.some.symm
  have : IsAlgClosure E₁ (AlgebraicClosure L) := ⟨inferInstance, .tower_top (K := L) E₁⟩
  let σ : AlgebraicClosure L ≃ₐ[E₁] AlgebraicClosure E₁ :=
    IsAlgClosure.equiv E₁ (AlgebraicClosure L) (AlgebraicClosure E₁)
  let ι'' : CMStructure (A₁ _ (AlgebraicClosure E₁)) F :=
    letI : Algebra (AlgebraicClosure L) (AlgebraicClosure E₁) := σ.toRingHom.toAlgebra
    letI : Algebra E₁ (AlgebraicClosure E₁) := AlgebraicClosure.instAlgebra E₁
    letI : SMul E₁ (AlgebraicClosure E₁) := (AlgebraicClosure.instAlgebra E₁).toSMul
    haveI : IsScalarTower E₁ (AlgebraicClosure L) (AlgebraicClosure E₁) :=
      .of_algebraMap_eq fun x ↦ (σ.commutes x).symm
    (ι'.basechange (AlgebraicClosure E₁)).ofIso
      (basechange_over_Field.trans_addGrpObj A₁ (AlgebraicClosure L) (AlgebraicClosure E₁))
  obtain ⟨E', _, ι₀', h⟩ := potentiallyCMStructure.exists_cmStructure_basechange_iso
    (potentiallyCMStructure.of_CMStructure ι'')
  let E : IntermediateField L (AlgebraicClosure L) := (E'.map σ.symm.toAlgHom).restrictScalars L
  let e : E' ≃+* E := (E'.equivMap σ.symm.toAlgHom).toRingEquiv
  have : FiniteDimensional E₁ (E'.map σ.symm.toAlgHom) :=
    (E'.equivMap σ.symm.toAlgHom).toLinearEquiv.finiteDimensional
  have h_fin : FiniteDimensional L E :=
    (Module.Finite.trans E₁ (E'.map σ.symm.toAlgHom) : FiniteDimensional L _)
  algebraize [e.toRingHom]
  algebraize [e.toRingHom.comp (Algebra.algebraMap E₁ E')]
  let ι₀ : CMStructure (A₁ _ E) F :=
    (ι₀'.basechange E).ofIso (basechange_over_Field.trans_addGrpObj A₁ E' E)
  refine ⟨E, h_fin, A₁ _ E, inferInstance, inferInstance, inferInstance, ι₀, ?_⟩
  have hι : ι'.Iso ι := CMStructure.Iso.symm (ι_A := ι) ⟨hφ.some.symm, rfl⟩
  let : Algebra (AlgebraicClosure E₁) (AlgebraicClosure L) := σ.symm.toRingHom.toAlgebra
  have P₁ : (ι'.basechange (AlgebraicClosure L)).Iso (ι''.basechange (AlgebraicClosure L)) :=
    letI : Algebra (AlgebraicClosure L) (AlgebraicClosure E₁) := σ.toRingHom.toAlgebra
    letI : Algebra E₁ (AlgebraicClosure E₁) := AlgebraicClosure.instAlgebra E₁
    letI : SMul E₁ (AlgebraicClosure E₁) := (AlgebraicClosure.instAlgebra E₁).toSMul
    haveI : IsScalarTower E₁ (AlgebraicClosure L) (AlgebraicClosure E₁) :=
      .of_algebraMap_eq fun x ↦ (σ.commutes x).symm
    haveI : IsScalarTower (AlgebraicClosure L) (AlgebraicClosure E₁) (AlgebraicClosure L) :=
      .of_algebraMap_eq fun x ↦ (σ.symm_apply_apply x).symm
    CMStructure.Iso.basechangeTrans (K₁ := AlgebraicClosure E₁)
      ⟨basechange_over_Field.trans_addGrpObj A₁ (AlgebraicClosure L) (AlgebraicClosure E₁), rfl⟩
      (CMStructure.Iso.refl _)
  let : Algebra E (AlgebraicClosure E₁) :=
    ((algebraMap E' (AlgebraicClosure E₁)).comp e.symm.toRingHom).toAlgebra
  have : IsScalarTower E' E (AlgebraicClosure E₁) :=
    .of_algebraMap_eq fun x ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower E (AlgebraicClosure E₁) (AlgebraicClosure L) :=
    .of_algebraMap_eq fun x ↦ by
      obtain ⟨y, rfl⟩ := e.surjective x
      simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp, Function.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e.symm_apply_apply]
      rfl
  have P₂ : (ι₀.basechange (AlgebraicClosure E₁)).Iso ι'' :=
    CMStructure.Iso.trans (CMStructure.Iso.basechangeTrans (K₁ := E)
      (CMStructure.Iso.trans (basechange.refl ι₀)
        (CMStructure.Iso.symm (ι_A := ι₀'.basechange E)
          ⟨basechange_over_Field.trans_addGrpObj A₁ E' E, rfl⟩))
      (basechange.trans ι₀' E (AlgebraicClosure E₁)))
      (CMStructure.Iso.trans (ι_A := ι₀'.basechange (AlgebraicClosure E₁))
        ⟨basechange_over_Field.trans_addGrpObj A₁ E' (AlgebraicClosure E₁), rfl⟩ h.some)
  exact ⟨(CMStructure.Iso.basechangeTrans (K₁ := AlgebraicClosure E₁) P₂
    (CMStructure.Iso.refl _)).trans (P₁.symm.trans ((basechange.refl ι').trans hι))⟩

theorem exists_numberField_model (ι : CMStructure A F) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra E K)
    (A₀ : Over (Spec ↧E)) (_ : IsProper A₀.hom) (_ : GeometricallyIntegral A₀.hom)
    (_ : AddGrpObj A₀) (ι₀ : CMStructure A₀ F), Nonempty ((ι₀.basechange K).Iso ι) := by
  rcases exists_algClosureRat_model ι with ⟨_, A₁, _, _, _, ι₁, hψ⟩
  rcases exists_finiteDimensional_model ι₁ with ⟨E, _, A₀, _, _, _, ι₀, hφ⟩
  have : NumberField E := .of_module_finite ℚ E
  have : IsScalarTower E (AlgebraicClosure ℚ) K :={smul_assoc e r k := by simp}
  use E, (by infer_instance), (by infer_instance), (by infer_instance), A₀, (by infer_instance),
    (by infer_instance), (by infer_instance), ι₀
  exact ⟨hφ.some.basechangeTrans hψ.some⟩

end CMStructure
