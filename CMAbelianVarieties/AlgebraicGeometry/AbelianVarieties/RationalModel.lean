/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.RationalModel.GroupStructure
public import CMAbelianVarieties.AlgebraicGeometry.RationalModel.Morphism

/-!
## Goal

The goal of this file is to show that an abelian variety `A` over `AlgebraicClosure K`
has a model over a finite extension of `K`. That is, there is a finite extension `E/K`
inside `AlgebraicClosure K` and an abelian variety `A₀` over `E`, such that
`A₀ _ (AlgebraicClosure K) ≅ A` as group objects.

For `K = ℚ`, `E` is a number field.

-/

@[expose] public section

open CategoryTheory AlgebraicGeometry GroupStructure
open Algebra (IsAlgebraic)

universe u

variable {K : Type u} [Field K]
variable {A : Over (Spec ↧(AlgebraicClosure K))}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

-- aided by claude
variable (A) in
theorem AbelianVarieties.exists_finiteDimensional_model :
    ∃ (E : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K E)
    (A₀ : Over (Spec ↧E)) (_ : IsProper A₀.hom) (_ : GeometricallyIntegral A₀.hom)
    (_ : AddGrpObj A₀), Nonempty (AddGrp.mk (A₀ _ (AlgebraicClosure K)) ≅ AddGrp.mk A) := by
  let E₁ := (exists_model_of_isSeparated_of_locallyOfFiniteType A).choose
  let A₁ : Over (Spec ↧E₁) :=
    (exists_model_of_isSeparated_of_locallyOfFiniteType A).choose_spec.2.choose
  have : IsProper (A₁.hom) := isProper_model A
  have : GeometricallyIntegral A₁.hom := geometricallyIntegral_model A
  have : IsAlgebraic E₁ (AlgebraicClosure K) := .tower_top (K := K) E₁
  obtain ⟨ψ⟩ :=
    (exists_model_of_isSeparated_of_locallyOfFiniteType A).choose_spec.2.choose_spec.2.2
  let : AddGrpObj (A₁ _ (AlgebraicClosure K)) := .ofIso ψ.symm
  let φ : AddGrp.mk (A₁ _ (AlgebraicClosure K)) ≅ AddGrp.mk A := (AddGrp.mkIso' ψ.symm).symm
  let E := fieldOfDefintion A₁ (AlgebraicClosure K)
  let h_addGrp : AddGrpObj (A₁ _ E) := AddGroupObj_overFieldOfDefintion A₁ (AlgebraicClosure K)
  have : FiniteDimensional E₁ E := FiniteDimensional_ofFieldOfDefintion A₁ (AlgebraicClosure K)
  have : FiniteDimensional K E₁ :=
    (exists_model_of_isSeparated_of_locallyOfFiniteType A).choose_spec.1
  have : FiniteDimensional K E := Module.Finite.trans E₁ E
  have hP : IsProper (A₁ _ E).hom := inferInstance
  have hGI : GeometricallyIntegral (A₁ _ E).hom := inferInstance
  refine ⟨E.restrictScalars K, this, ?_⟩
  use (A₁ _ E), hP, hGI, h_addGrp
  exact ⟨(AddGroupObj_overFieldOfDefintion_Iso A₁ (AlgebraicClosure K)).trans φ⟩
