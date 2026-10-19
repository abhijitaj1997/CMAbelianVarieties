/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AbelianVarieties.Commutativity
public import CMAbelianVarieties.AbstractNonsense.EndRingIso

/-!
## Main Goal

The goal of this file is to collect all the results of homomophism ring that
we have defined get these instance for the Endomorphisms ring. Additionally
we will define `(End A) ⊗[ℤ] ℚ`

-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AddGrp
open scoped TensorProduct End

variable {K : Type*} [Field K]
variable {A : Over (Spec ↧K)}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

abbrev RationalEnd (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
  := ℚ ⊗[ℤ] (End (mk A))

namespace RationalEnd

scoped notation "End⁰ " A:max => RationalEnd A

instance {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A] :
    Module.Finite ℚ (End⁰ A) := sorry

/-- An isomorphism `φ : A ≅ B` of abelian varieties over `K` (as additive group objects)
induces an isomorphism `End⁰ A ≃ₐ[ℤ] End⁰ B` of their rational endomorphism algebras, given by
conjugation `f ↦ φ.inv ≫ f ≫ φ.hom`. It is obtained by tensoring the `ℤ`-algebra isomorphism
`Iso.conjAlgEquiv φ : End A ≃ₐ[ℤ] End B` with `ℚ`. -/
noncomputable def conjAlgEquiv {A : Over (Spec ↧K)} [IsProper A.hom]
    [GeometricallyIntegral A.hom] [AddGrpObj A]
    {B : Over (Spec ↧K)} [IsProper B.hom] [GeometricallyIntegral B.hom] [AddGrpObj B]
    (φ : mk A ≅ mk B) : End⁰ A ≃ₐ[ℤ] End⁰ B :=
  Algebra.TensorProduct.congr AlgEquiv.refl (Iso.conjAlgEquiv φ)

end RationalEnd

#min_imports
