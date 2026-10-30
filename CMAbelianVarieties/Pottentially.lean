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
  sorry
