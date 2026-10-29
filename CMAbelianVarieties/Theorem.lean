/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.Defn
public import CMAbelianVarieties.AlgebraicGeometry.IntegralModel.Theorem

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

theorem exists_numberField_model_of__over_algClosureRat
    {A : Over (Spec ↧(AlgebraicClosure ℚ))} [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (ι : CMStructure A F) : ∃ (E : Type) (_ : Field E) (_ : NumberField E)
    (_ : Algebra E (AlgebraicClosure ℚ)) (A₀ : Over (Spec ↧E)) (_ : IsProper A₀.hom)
    (_ : GeometricallyIntegral A₀.hom) (_ : AddGrpObj A₀) (ι₀ : CMStructure A₀ F),
    Nonempty ((ι₀.basechange (AlgebraicClosure ℚ)).Iso ι) := by
  rcases AbelianVarieties.exists_numberField_model_of__over_algClosureRat A with
    ⟨E₀, _, _, _, A₀, _, _, _, hφ⟩
  #check hφ.some
  sorry

theorem exists_numberField_model (ι : CMStructure A F) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra E K)
    (A₀ : Over (Spec ↧E)) (_ : IsProper A₀.hom) (_ : GeometricallyIntegral A₀.hom)
    (_ : AddGrpObj A₀) (ι₀ : CMStructure A₀ F), Nonempty ((ι₀.basechange K).Iso ι) := by
  rcases exists_algClosureRat_model ι with ⟨_, A₁, _, _, _, ι₁, hψ⟩
  rcases exists_numberField_model_of__over_algClosureRat ι₁ with
    ⟨E, _, _, _, A₀, _, _, _, ι₀, hφ⟩
  algebraize [(Algebra.algebraMap _ K).comp (Algebra.algebraMap E (AlgebraicClosure ℚ))]
  have : IsScalarTower E (AlgebraicClosure ℚ) K :={smul_assoc e r k := by simp}
  use E, (by infer_instance), (by infer_instance), (by infer_instance), A₀, (by infer_instance),
    (by infer_instance), (by infer_instance), ι₀
  exact ⟨Iso_trans hφ.some hψ.some⟩

end CMStructure
