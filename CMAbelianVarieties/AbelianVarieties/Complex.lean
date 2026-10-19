/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib
public import CMAbelianVarieties.AlgebraicGeometry.LieAlgebra.Defn
public import CMAbelianVarieties.AbelianVarieties.Commutativity

/-!
## Goal

In this section we shall catalogue results about complex abelian varieties.
Especially facts about uniforization, as far as need for this project.

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory AddMonObj AddGrp

variable {A : Over (Spec ↧ℂ)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

variable (A) in
/-- The exponential map `Lie A ⟶ A` for a complex abelian variety `A`. -/
def exponential : Lie A →+ (𝟙_ _  ⟶ A) := sorry

def AddMonoidHom_of_End (f : End (mk A)) : (𝟙_ _  ⟶ A) →+ (𝟙_ _  ⟶ A) :=
  IsAddMonHom.addMonoidHom f.asHom.hom.hom (𝟙_ _)

lemma end_comp_exponential (f : End (mk A)) :
    (AddMonoidHom_of_End f).comp (exponential A) =
    (exponential A).comp (lie_algebra_represenation A f).toAddMonoidHom := by
  sorry

variable (A) in
/-- The lattice associated to a complex abelian variety `A` in the lie algebra of `A`. -/
def lattice := (exponential A).ker

#check AddMonoidHom.toIntLinearMap

def lie_algebra_lattice_representation (f : End (mk A)) : lattice A →ₗ[ℤ] lattice A := by
  apply AddMonoidHom.toIntLinearMap
  let φ := (lie_algebra_represenation A f).toAddMonoidHom
  #check AddMonoidHom.codRestrict

  -- I need a lemma which says the the f ≫ exp = exp ≫ repn(f)
  sorry

/-- The lattice of a complex abelian variety `A` of dimension `g` is a free `ℤ`-module of
rank `2 * g`. -/
lemma lattice_addEquiv {g : ℕ} (hg : topologicalKrullDim A.left = g) :
    Nonempty (lattice A ≃+ (Fin (2 * g) → ℤ)) := sorry
