/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

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

/-
Hey clausde, remind me to create a local notation (I do not want to access this outside) for
`(𝟙_ (Over (Spec ↧ℂ)) ⟶ A)`. Maybe something like `A/ℂ/` or something.
-/

variable (A) in
/-- The exponential map `Lie A ⟶ A` for a complex abelian variety `A`. -/
def exponential : Lie A →+ (𝟙_ _  ⟶ A) := sorry

def AddMonoidHom_of_End (f : End (mk A)) : (𝟙_ _  ⟶ A) →+ (𝟙_ _  ⟶ A) :=
  IsAddMonHom.addMonoidHom f.asHom.hom.hom (𝟙_ _)

lemma end_comp_exponential (f : End (mk A)) (g : Lie A) :
    (AddMonoidHom_of_End f) ((exponential A) g) =
    (exponential A) ((lie_algebra_represenation A f) g) := by
  sorry

variable (A) in
/-- The lattice associated to a complex abelian variety `A` in the lie algebra of `A`. -/
abbrev lattice := (exponential A).ker

def lattice_representation' (f : End (mk A)) : lattice A →ₗ[ℤ] lattice A := by
  let φ := (lie_algebra_represenation A f).toAddMonoidHom
  have : ∀ g : lattice A, (φ.comp (lattice A).subtype) g ∈ lattice A := by
    intro g
    simp only [AddMonoidHom.coe_comp, AddSubgroup.coe_subtype, Function.comp_apply,
      AddMonoidHom.mem_ker, lattice, LinearMap.toAddMonoidHom_coe, φ]
    simp [← end_comp_exponential,
      (@AddMonoidHom.mem_ker _ _ _ _ (exponential A) g).1 (SetLike.coe_mem g)]
  exact AddMonoidHom.toIntLinearMap (AddMonoidHom.codRestrict (φ.comp (lattice A).subtype)
    (lattice A) this)

/-- The lattice of a complex abelian variety `A` of dimension `g` is a free `ℤ`-module of
rank `2 * g`. -/
lemma lattice_addEquiv {g : ℕ} (hg : topologicalKrullDim A.left = g) :
    Nonempty (lattice A ≃+ (Fin (2 * g) → ℤ)) := sorry
