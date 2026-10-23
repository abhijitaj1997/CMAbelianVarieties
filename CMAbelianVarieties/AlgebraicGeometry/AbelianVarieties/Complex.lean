/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.LieAlgebra.Dimension
public import CMAbelianVarieties.AlgebraicGeometry.AbelianVarieties.Commutativity

/-!
## Goal

In this section we shall catalogue results about complex abelian varieties.
Especially facts about uniforization, as far as need for this project.

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory AddMonObj AddGrp End

variable {A : Over (Spec ↧ℂ)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

/-- The complex points of `A`. -/
local notation "|" A " ℂ|" => (𝟙_ (Over (Spec ↧ℂ)) ⟶ A)

variable (A) in
/-- The exponential map `Lie A ⟶ A` for a complex abelian variety `A`. -/
def exponential : Lie A →+ |A ℂ| := sorry

def AddMonoidHom_of_End (f : End (mk A)) : |A ℂ| →+ |A ℂ| :=
  IsAddMonHom.addMonoidHom f.asHom.hom.hom (𝟙_ _)

lemma end_comp_exponential (f : End (mk A)) (g : Lie A) :
    (AddMonoidHom_of_End f) ((exponential A) g) =
    (exponential A) ((lie_algebra_represenation A f) g) := by
  sorry

variable (A) in
/-- The lattice associated to a complex abelian variety `A` in the lie algebra of `A`. -/
abbrev lattice := (exponential A).ker

open TensorProduct in
variable (A) in
lemma lattice_isLattice : Nonempty (ℝ ⊗[ℤ] (lattice A) ≃+ Lie A) := sorry

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

-- filled in using Claude
variable (A) in
def lattice_representation : End (mk A) →+* (lattice A →ₗ[ℤ] lattice A) where
  toFun f := lattice_representation' f
  map_one' := by
    refine LinearMap.ext fun g ↦ Subtype.ext ?_
    exact congrArg (· g.1) (map_one (lie_algebra_represenation A))
  map_mul' f f' := by
    refine LinearMap.ext fun g ↦ Subtype.ext ?_
    exact congrArg (· g.1) (map_mul (lie_algebra_represenation A) f f')
  map_zero' := by
    refine LinearMap.ext fun g ↦ Subtype.ext ?_
    exact congrArg (· g.1) (map_zero (lie_algebra_represenation A))
  map_add' f f' := by
    refine LinearMap.ext fun g ↦ Subtype.ext ?_
    exact congrArg (· g.1) (map_add (lie_algebra_represenation A) f f')

/-- The lattice of a complex abelian variety `A` of dimension `g` is a free `ℤ`-module of
rank `2 * g`. -/
lemma lattice_linearEquiv {g : ℕ} (hg : topologicalKrullDim A.left = g) :
    Nonempty (lattice A ≃ₗ[ℤ] (Fin (2 * g) → ℤ)) := sorry

-- proof written by Claude
variable (A) in
lemma lattice_freeModule : Module.Free ℤ (lattice A) := by
  obtain ⟨e⟩ := lattice_linearEquiv (topologicalKrullDim_eq_finrank_Lie A)
  exact Module.Free.of_equiv e.symm
