/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.Defn

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

universe u

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
variable {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable {F : Type*} [Field F] [NumberField F] [IsCMField F]

theorem CMStructure.exists_numberField_model (ι : CMStructure A F) :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (_ : Algebra E K)
    (A₀ : Over (Spec ↧E)) (_ : IsProper A₀.hom) (_ : GeometricallyIntegral A₀.hom)
    (_ : AddGrpObj A₀) (ι₀ : CMStructure A₀ F), Nonempty ((ι₀.basechange K).Iso ι) := by
  sorry
