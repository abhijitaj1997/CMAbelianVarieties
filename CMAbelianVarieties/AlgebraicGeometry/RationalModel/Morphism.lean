/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.RationalModel.Separated

/-!
## Goal

The goal of this file is to show that properties of morphisms descend to
a Rational model

-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {K : Type u} [Field K]
variable {X : Over (Spec ↧(AlgebraicClosure K))}

variable (X) in
lemma isProper_model [IsProper X.hom] :
    IsProper (exists_model_of_isSeparated_of_locallyOfFiniteType X).choose_spec.2.choose.hom := by
  sorry

variable (X) in
lemma geometricallyIntegral_model [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] [GeometricallyIntegral X.hom] :
    GeometricallyIntegral
    (exists_model_of_isSeparated_of_locallyOfFiniteType X).choose_spec.2.choose.hom := by
  sorry
