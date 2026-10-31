/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.Defn

/-!
## Goal

In this section, we will define pottentially CM, and show that every Potentially CM
Abelian variety is CM after a finite extension.

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry NumberField RationalEnd
open scoped BaseChange

universe u

variable {K : Type u} [Field K]
variable {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

variable (A) in
structure potentiallyCMStructure (F : Type*) [Field F] [NumberField F] [IsCMField F] extends
  CMStructure (A _ (AlgebraicClosure K)) F

def potentiallyCMStructure.of_CMStructure {F : Type*} [Field F] [NumberField F] [IsCMField F]
    (ι : CMStructure (A _ (AlgebraicClosure K)) F) : potentiallyCMStructure A F where
      incl := ι.incl
      finrank_of_CM_field := ι.finrank_of_CM_field

lemma potentiallyCMStructure.exists_cmStructure_basechange_iso {F : Type*} [Field F]
    [NumberField F] [IsCMField F] (ι : potentiallyCMStructure A F) :
    ∃ (E : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K E)
    (ι_E : CMStructure (A _ E) F),
    Nonempty (((ι_E.basechange (AlgebraicClosure K)).ofIso
    (basechange_over_Field.trans_addGrpObj A E (AlgebraicClosure K))).Iso ι.toCMStructure) := by
  rcases RationalEnd.exists_finiteDimensional_model A with ⟨E, _, hf⟩
  let f := rational_end_morphism (A _ E) (AlgebraicClosure K)
  let φ := (conjAlgEquiv (basechange_over_Field.trans_addGrpObj A E
    (AlgebraicClosure K))).symm.toRingEquiv.trans (RingEquiv.ofBijective f hf).symm
  let ψ : (A _ E) _ (AlgebraicClosure K) ≅ A _ (AlgebraicClosure K) :=
    basechange_over_Field.trans A (↥E) (AlgebraicClosure K)
  have : topologicalKrullDim ((A _ E) _ (AlgebraicClosure K)).left =
      topologicalKrullDim (A _ (AlgebraicClosure K)).left := by
    exact IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso ((Over.forget _).mapIso ψ)).isHomeomorph
  let ι_E : CMStructure (A _ E) F := {
    incl := by
      exact φ.toRingHom.comp ι.toCMStructure.incl
    finrank_of_CM_field := by
      rw [dimension_isStableUnderBasechange (A _ E) (AlgebraicClosure K), this]
      exact ι.toCMStructure.finrank_of_CM_field
  }
  use E, inferInstance, ι_E
  let π := (basechange_over_Field.trans_addGrpObj A E (AlgebraicClosure K))
  let σ : ((ι_E.basechange (AlgebraicClosure K)).ofIso π).Iso ι.toCMStructure := {
    val := by apply Iso.refl
    property := by
      have h : ((ι_E.basechange (AlgebraicClosure K)).ofIso π).incl =
        (conjAlgEquiv π).toRingHom.comp
        ((rational_end_morphism (A _ E) (AlgebraicClosure K)).comp (φ.toRingHom.comp
        ι.toCMStructure.incl)) := rfl
      simp only [conjAlgEquiv.refl, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
        AlgEquiv.refl_toRingHom, h, RingHomCompTriple.comp_eq]
      have hr (y : End⁰ ((A _ E) _ (AlgebraicClosure K))) :
          rational_end_morphism (A _ E) (AlgebraicClosure K)
            ((RingEquiv.ofBijective f hf).symm y) = y :=
        (RingEquiv.ofBijective f hf).apply_symm_apply y
      ext x
      simp [φ, π, hr]
  }
  exact ⟨σ⟩
