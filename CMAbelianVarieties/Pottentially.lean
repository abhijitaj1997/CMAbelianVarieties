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
variable {Kₐ : Type u} [Field Kₐ] [Algebra K Kₐ] [IsAlgClosure K Kₐ]

variable (A Kₐ) in
structure potentiallyCMStructure (F : Type*) [Field F] [NumberField F] [IsCMField F] extends
  CMStructure (A _ Kₐ) F

def potentiallyCMStructure.of_CMStructure {F : Type*} [Field F] [NumberField F] [IsCMField F]
    (ι : CMStructure (A _ Kₐ) F) : potentiallyCMStructure A Kₐ F := sorry

lemma potentiallyCMStructure.exists_cmStructure_basechange_iso {F : Type*} [Field F]
    [NumberField F] [IsCMField F] (ι : potentiallyCMStructure A Kₐ F) :
    ∃ (E : IntermediateField K Kₐ) (_ : FiniteDimensional K E) (ι_E : CMStructure (A _ E) F),
    Nonempty (((ι_E.basechange Kₐ).ofIso
    (basechange_over_Field_trans_addGrpObj A E Kₐ)).Iso ι.toCMStructure) := by
  sorry
