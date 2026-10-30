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

theorem exists_finiteDimensional_model {L : Type*} [Field L]
    {A : Over (Spec ↧(AlgebraicClosure L))} [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (ι : CMStructure A F) : ∃ (E : IntermediateField L (AlgebraicClosure L))
    (_ : FiniteDimensional L E) (A₀ : Over (Spec ↧E)) (_ : IsProper A₀.hom)
    (_ : GeometricallyIntegral A₀.hom) (_ : AddGrpObj A₀) (ι₀ : CMStructure A₀ F),
    Nonempty ((ι₀.basechange (AlgebraicClosure L)).Iso ι) := by
  rcases AbelianVarieties.exists_finiteDimensional_model A with
    ⟨E₁, _, A₁, _, _, _, hφ⟩
  let ι' : CMStructure (A₁ _ (AlgebraicClosure L)) F := ι.ofIso hφ.some.symm
  have : IsAlgClosure E₁ (AlgebraicClosure L) := ⟨inferInstance, .tower_top (K := L) E₁⟩
  let ιₚ := potentiallyCMStructure.of_CMStructure ι'
  rcases potentiallyCMStructure.exists_cmStructure_basechange_iso ιₚ with ⟨E', _, ι₀', h⟩
  -- written by Claude
  let E : IntermediateField L (AlgebraicClosure L) := E'.restrictScalars L
  have h_fin : FiniteDimensional L E := (Module.Finite.trans E₁ E' : FiniteDimensional L E')
  let e : E' ≃+* E := RingEquiv.refl E'
  algebraize [e.toRingHom]
  algebraize [e.toRingHom.comp (Algebra.algebraMap E₁ E')]
  use E, h_fin
  let ι₀ : CMStructure (A₁ _ E) F :=
    (ι₀'.basechange E).ofIso (basechange_over_Field_trans_addGrpObj A₁ E' E)
  use A₁ _ E, by infer_instance, by infer_instance, by infer_instance, ι₀
  sorry

/-
(Written by Claude, 2026-10-30.) Definitions with a `sorry` that
`CMStructure.exists_finiteDimensional_model` depends on (found by walking its dependencies
in Lean):

- `AlgebraicGeometry/RationalModel/GroupStructure.lean`: `fieldOfDefintion`,
  `AddGroupObj_overFieldOfDefintion` (instance), `AddGroupObj_overFieldOfDefintion_Iso`.
- `Defn.lean`: `CMStructure.ofIso`.
- `Pottentially.lean`: `potentiallyCMStructure.of_CMStructure`.
-/

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
  exact ⟨Iso_trans hφ.some hψ.some⟩

end CMStructure
