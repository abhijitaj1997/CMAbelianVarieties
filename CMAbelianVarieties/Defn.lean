/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.AbelianVarieties.BaseFieldChange
public import CMAbelianVarieties.AlgebraicGeometry.AbelianVarieties.Homomorphisms.EndomorphismRing
public import CMAbelianVarieties.AbstractNonsense.EndBaseChange
public import CMAbelianVarieties.preCMType.Defn
public import CMAbelianVarieties.AlgebraicGeometry.AbelianVarieties.Complex

/-!
## CM Abelian varieties

In this section, we will define CM Abelian varieties

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AddGrp NumberField
open scoped TensorProduct End RationalEnd

section CMStructure

universe u

variable {K : Type u} [Field K]
variable {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

variable (A) in
/-- A complex multiplication structure `ι : CMStructure A F` for an abelian variety `A` over a
field `K` and a CM field `F`, is made of an inclusion `F →+* End⁰ A` together with a proof
that `[F : ℚ] = 2 * dim A`, where `End⁰ A = ℚ ⊗[ℤ] End A` are all the rational endomorphisms of `A`.
Note that the endomorphisms are defined over the base field `K`. Alternative definitions that exist:
1. Some authors define `End A` over the algebraic closure of `K` (this is not equivalent to
our definition, in fact it is weaker).
2. Some authors only require that `F` is a product of CM fields (this is not equivalent to our
definition, in fact it is weaker).
3. In characteristic zero, some authors define a CM abelian variety of CM type `(F, Φ)`, where
`Φ` is read off of the action of `F` on the Lie algebra of `A` (this definition is equivalent
to our definition in characteristic zero). -/
structure CMStructure (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (F : Type*) [Field F] [NumberField F] [IsCMField F] where
  /-- The inclusion of the CM field into the algebra of rational endomorphisms -/
  incl : F →+* End⁰ A
  /-- The dimension of the CM field is twice the Krull dimension of the abelian variety -/
  finrank_of_CM_field : Module.finrank ℚ F = 2 * topologicalKrullDim A.left

attribute [coe] CMStructure.incl

/-- A CM structure `ι` can be used as its inclusion `F →+* End⁰ A`. -/
instance {F : Type*} [Field F] [NumberField F] [IsCMField F] :
    Coe (CMStructure A F) (F →+* End⁰ A) :=
  ⟨CMStructure.incl⟩

namespace CMStructure

section BaseChange

open CommRingCat Spec

variable {F : Type*} [Field F] [NumberField F] [IsCMField F]

def End.algHom_ofBaseChange (A : Over (Spec ↧K)) [AddGrpObj A] [IsCommAddMonObj A] (K₁ : Type u)
    [Field K₁] [Algebra K K₁] : End (AddGrp.mk A) →ₐ[ℤ] End (AddGrp.mk (A _ K₁)) :=
  AddGrp.End.algHom_ofBaseChange (Over.pullback (map (ofHom (Algebra.algebraMap K K₁))))

def rational_end_morphism (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (K₁ : Type u) [Field K₁] [Algebra K K₁] : End⁰ A →+* End⁰ ((A _ K₁)) :=
  (Algebra.TensorProduct.map (AlgHom.id ℤ ℚ) (End.algHom_ofBaseChange A K₁)).toRingHom


/-
Hey claude, remind me to move this to another file about dimenions.
-/
#check smoothOfRelativeDimension_isStableUnderBaseChange -- But I don't wanna just prove this
-- for AVs
lemma dimension_isStableUnderBasechange (X : Over (Spec ↧K)) [LocallyOfFiniteType X.hom]
    (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    topologicalKrullDim X.left = topologicalKrullDim (X _ K₁).left := sorry

def basechange (ι : CMStructure A F) (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    CMStructure (A _ K₁) F where
      incl := (rational_end_morphism A K₁).comp ι
      finrank_of_CM_field := by
        rw [ι.finrank_of_CM_field, dimension_isStableUnderBasechange A K₁]

end BaseChange

end CMStructure

section CMType

variable {K : Type} [Field K] [Algebra K ℂ]
variable {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

-- aided by Claude
def CMField_ringHom_rationalLattice {F : Type*} [Field F] [NumberField F]
    [IsCMField F] (ι : CMStructure A F) :
    F →+* Module.End ℚ (ℚ ⊗[ℤ] (lattice (A _ ℂ))) := by
  let L := lattice (A _ ℂ)
  let g₁ : ℚ →ₐ[ℤ] Module.End ℚ (ℚ ⊗[ℤ] L) := (algebraMap ℚ _).toIntAlgHom
  let g₂ : End (AddGrp.mk (A _ ℂ)) →ₐ[ℤ] Module.End ℚ (ℚ ⊗[ℤ] L) :=
    (Module.End.baseChangeHom ℤ ℚ L).comp (lattice_representation (A _ ℂ)).toIntAlgHom
  let ψ' := (Algebra.TensorProduct.lift g₁ g₂ fun x y ↦ Algebra.commutes x (g₂ y)).toRingHom
  exact (ψ' : End⁰ (A _ ℂ) →+* Module.End ℚ (ℚ ⊗[ℤ] L)).comp (ι.basechange ℂ).incl

@[instance_reducible]
def module_rational_lattice_of_CMStructure {F : Type*} [Field F] [NumberField F]
    [IsCMField F] (ι : CMStructure A F) :
    Module F (ℚ ⊗[ℤ] lattice (A _ ℂ)) :=
  Module.compHom (ℚ ⊗[ℤ] (lattice (A _ ℂ))) (CMField_ringHom_rationalLattice ι)

-- aided by Claude
/-- With the `F`-module structure `module_rational_lattice_of_CMStructure ι`, the rational
lattice `ℚ ⊗[ℤ] lattice (A _ ℂ)` is one-dimensional over `F`. -/
lemma finrank_rational_lattice_of_CMStructure {F : Type*} [Field F] [NumberField F]
    [IsCMField F] (ι : CMStructure A F) :
    letI := module_rational_lattice_of_CMStructure ι
    Module.finrank F (ℚ ⊗[ℤ] lattice (A _ ℂ)) = 1 := by
  let := module_rational_lattice_of_CMStructure ι
  set g := topologicalKrullDim (A _ ℂ).left with hg
  have : (Module.finrank ℚ (ℚ ⊗[ℤ] lattice (A _ ℂ))) = 2 * g := by
    have : (Module.finrank ℤ (lattice (A _ ℂ))) = 2 * g := by
      obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim (A _ ℂ).left = n := by
        use Module.finrank (κ_ (A _ ℂ)) (Lie (A _ ℂ))
        rw [ topologicalKrullDim_eq_finrank_Lie (A _ ℂ)]
      obtain ⟨φ⟩ := lattice_linearEquiv hn
      rw [φ.finrank_eq, Module.finrank_fin_fun, show g = n from hn]
      push_cast
      rfl
    have : (Module.finrank ℚ (ℚ ⊗[ℤ] lattice (A _ ℂ))) = (Module.finrank ℤ (lattice (A _ ℂ))) := by
      let := lattice_freeModule (A _ ℂ)
      rw [Module.finrank_baseChange]
    rwa [this]
  let E := Module.End ℚ (ℚ ⊗[ℤ] lattice (A _ ℂ))
  let L := lattice (A _ ℂ)
  let ψ : F →+* E := CMField_ringHom_rationalLattice ι
  have h : (Module.finrank ℚ F : WithBot ℕ∞) * Module.finrank F (ℚ ⊗[ℤ] lattice (A _ ℂ)) =
      Module.finrank ℚ (ℚ ⊗[ℤ] lattice (A _ ℂ)) := by
    exact_mod_cast Module.finrank_mul_finrank ℚ F (ℚ ⊗[ℤ] lattice (A _ ℂ))
  rw [this, hg, ← (ι.basechange ℂ).finrank_of_CM_field] at h
  norm_cast at h
  exact (Nat.mul_eq_left Module.finrank_pos.ne').mp h

-- proved by Claude
/-- With the `F`-module structure `module_rational_lattice_of_CMStructure ι`, the rational
lattice `ℚ ⊗[ℤ] lattice (A _ ℂ)` is isomorphic to `F` as an `F`-module. -/
lemma nonempty_linearEquiv_rational_lattice_of_CMStructure {F : Type*} [Field F] [NumberField F]
    [IsCMField F] (ι : CMStructure A F) : letI := module_rational_lattice_of_CMStructure ι
    Nonempty (F ≃ₗ[F] (ℚ ⊗[ℤ] lattice (A _ ℂ))) := by
  let := module_rational_lattice_of_CMStructure ι
  have h := finrank_rational_lattice_of_CMStructure ι
  have : FiniteDimensional F (ℚ ⊗[ℤ] lattice (A _ ℂ)) := Module.finite_of_finrank_eq_succ h
  exact ⟨LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_self, h])⟩

/- Not needed (just for the lemma and notation below)
def u {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    letI := module_rational_lattice_of_CMStructure ι
    F ≃ₗ[F] (ℚ ⊗[ℤ] lattice (A _ ℂ)) :=
  letI := module_rational_lattice_of_CMStructure ι
  (nonempty_linearEquiv_rational_lattice_of_CMStructure ι).some

lemma catalogue {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    1 = 1 := by
  let := module_rational_lattice_of_CMStructure ι
  #check u ι
  #check (u ι).toLinearMap
  #check (u ι).symm
  #check (u ι).symm.toLinearMap
  #check (u ι).bijective
  rfl-/

def u_ℚ {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    F ≃ₗ[ℚ] (ℚ ⊗[ℤ] lattice (A _ ℂ)) :=
  letI := module_rational_lattice_of_CMStructure ι
  (nonempty_linearEquiv_rational_lattice_of_CMStructure ι).some.restrictScalars ℚ

def u_ℝ {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    ℝ ⊗[ℚ] F ≃ₗ[ℝ] (Lie (A _ ℂ)) :=
  let ψ₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℝ ℝ ↥(lattice (A _ ℂ))
  let ψ₂ := LinearEquiv.baseChange ℚ ℝ F (ℚ ⊗[ℤ] ↥(lattice (A _ ℂ))) (u_ℚ ι)
  (ψ₂.trans ψ₁).trans (lattice_isLattice (A _ ℂ)).some

lemma u_ℝ_one_tmul_mul {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    ∀ x : F, ∀ y : ℝ ⊗[ℚ] F, (u_ℝ ι) (1 ⊗ₜ[ℚ] x * y) = rationalEnd_lie_algebra_represenation (A _ ℂ)
    ((ι.basechange ℂ).incl x) ((u_ℝ ι) y) := by
  intro x y
  sorry

def complex_I_mul (V : Type*) [AddCommGroup V] [Module ℂ V] : V →ₗ[ℂ] V :=
  DistribSMul.toLinearMap _ V Complex.I

def J {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    ℝ ⊗[ℚ] F →ₗ[ℝ] ℝ ⊗[ℚ] F :=
  ((u_ℝ ι).symm.toLinearMap.comp ((complex_I_mul (Lie (A _ ℂ))).restrictScalars ℝ)).comp
  (u_ℝ ι).toLinearMap

lemma J_one {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    J ι 1 * J ι 1 = -1 := by
  have hJ : ∀ v : ℝ ⊗[ℚ] F, (J ι) (J ι v) = - v := sorry
  let μ (x : F) : ℝ ⊗[ℚ] F →ₗ[ℝ] ℝ ⊗[ℚ] F :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
      ((DistribSMul.toLinearMap F F x).restrictScalars ℚ)
  have hμ : ∀ x : F, ∀ y : ℝ ⊗[ℚ] F, (u_ℝ ι) (μ x y) = rationalEnd_lie_algebra_represenation (A _ ℂ)
    ((ι.basechange ℂ).incl x) ((u_ℝ ι) y) := by
    intro x y
    have : μ x y = 1 ⊗ₜ x * y := by
      simp [μ]
      sorry
    rw [this]
    exact u_ℝ_one_tmul_mul ι x y
  have : ∀ x : F, (J ι).comp (μ x) = (μ x).comp (J ι) := by
    intro x
    sorry
  have : ∀ y : ℝ ⊗[ℚ] F, J ι y = (J ι 1) * y := sorry
  specialize this (J ι 1)
  rw [hJ 1] at this
  rw [this]

/-- Given a CM strucutre on an Abelian variety `A` over a field `K`, such that `K` is
a subfield of `ℂ`, and `F` is the CM Field in the CM Structure. The, we have a preCMType
on the field `F`. -/
def CMType {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    preCMType F := preCMType.ofComplexStructure (J_one ι)

end CMType

end CMStructure
