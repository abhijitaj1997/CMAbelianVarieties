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
public import CMAbelianVarieties.AlgebraicGeometry.Dimension

/-!
## CM Abelian varieties

In this section, we will define CM Abelian varieties

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AddGrp NumberField RationalEnd
open scoped TensorProduct End

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
structure CMStructure (F : Type*) [Field F] [NumberField F] [IsCMField F] where
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

def Iso {B : Over (Spec ↧K)} [IsProper B.hom] [GeometricallyIntegral B.hom] [AddGrpObj B]
    (ι_A : CMStructure A F) (ι_B : CMStructure B F) :=
  {φ : AddGrp.mk A ≅ AddGrp.mk B // (conjAlgEquiv φ).toRingHom.comp ι_A.incl = ι_B}

def End.algHom_ofBaseChange (A : Over (Spec ↧K)) [AddGrpObj A] [IsCommAddMonObj A] (K₁ : Type u)
    [Field K₁] [Algebra K K₁] : End (AddGrp.mk A) →ₐ[ℤ] End (AddGrp.mk (A _ K₁)) :=
  AddGrp.End.algHom_ofBaseChange (Over.pullback (map (ofHom (Algebra.algebraMap K K₁))))

def rational_end_morphism (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (K₁ : Type u) [Field K₁] [Algebra K K₁] : End⁰ A →+* End⁰ ((A _ K₁)) :=
  (Algebra.TensorProduct.map (AlgHom.id ℤ ℚ) (End.algHom_ofBaseChange A K₁)).toRingHom

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
variable (A) in
def rationalEnd_ringHom_rationalLattice : End⁰ (A _ ℂ) →+* Module.End ℚ (ℚ ⊗[ℤ]
    (lattice (A _ ℂ))) :=
  let L := lattice (A _ ℂ)
  let g₁ : ℚ →ₐ[ℤ] Module.End ℚ (ℚ ⊗[ℤ] L) := (algebraMap ℚ _).toIntAlgHom
  let g₂ : End (AddGrp.mk (A _ ℂ)) →ₐ[ℤ] Module.End ℚ (ℚ ⊗[ℤ] L) :=
    (Module.End.baseChangeHom ℤ ℚ L).comp (lattice_representation (A _ ℂ)).toIntAlgHom
  (Algebra.TensorProduct.lift g₁ g₂ fun x y ↦ Algebra.commutes x (g₂ y)).toRingHom

def CMField_ringHom_rationalLattice {F : Type*} [Field F] [NumberField F]
    [IsCMField F] (ι : CMStructure A F) :
    F →+* Module.End ℚ (ℚ ⊗[ℤ] (lattice (A _ ℂ))) :=
  (rationalEnd_ringHom_rationalLattice A).comp (ι.basechange ℂ)

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

/-- A fixed isomorphism `F ≃ₗ[F] (ℚ ⊗[ℤ] L)`, where `L` is the lattice of
the complex abelian variety. -/
def u {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    letI := module_rational_lattice_of_CMStructure ι
    F ≃ₗ[F] (ℚ ⊗[ℤ] lattice (A _ ℂ)) :=
  letI := module_rational_lattice_of_CMStructure ι
  (nonempty_linearEquiv_rational_lattice_of_CMStructure ι).some

lemma u_mul {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) (x y : F) :
    letI := module_rational_lattice_of_CMStructure ι
    u ι (x * y) =  x • (u ι y) := by
  let := module_rational_lattice_of_CMStructure ι
  exact map_smul (u ι) x y

def u_ℚ {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    F ≃ₗ[ℚ] (ℚ ⊗[ℤ] lattice (A _ ℂ)) :=
  letI := module_rational_lattice_of_CMStructure ι
  (u ι).restrictScalars ℚ

lemma u_ℚ_mul {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    letI := module_rational_lattice_of_CMStructure ι
    ∀ a b : F, u_ℚ ι (a * b) = a • u_ℚ ι b := by
  let := module_rational_lattice_of_CMStructure ι
  intro a b
  simp only [u_ℚ, LinearEquiv.restrictScalars_apply]
  exact map_smul ((nonempty_linearEquiv_rational_lattice_of_CMStructure ι).some) a b

/-- The isomorphism `ℝ ⊗[ℚ] F ≃ₗ ℝ ⊗[ℚ] (ℚ ⊗[ℤ] L)`, where `L` is the lattice of
the complex abelian variety. -/
def ψ₁ {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F)
  := LinearEquiv.baseChange ℚ ℝ F (ℚ ⊗[ℤ] (lattice (A _ ℂ))) (u_ℚ ι)

lemma ψ₁_tmul {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    ∀ x : ℝ, ∀ y : F, ψ₁ ι (x ⊗ₜ[ℚ] y) = (x ⊗ₜ[ℚ] u ι y) :=
  fun x y ↦ by simp [ψ₁, u_ℚ]

variable (A) in
/-- The isomorphism `ℝ ⊗[ℚ] (ℚ ⊗[ℤ] L) ≃ₗ[ℝ] ℝ ⊗[ℤ] L`, where `L` is the lattice of
the complex abelian variety. -/
def ψ₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℝ ℝ (lattice (A _ ℂ))

variable (A) in
omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
/-- The natural linear map `(ℚ ⊗[ℤ] L) →ₗ[ℤ] (ℝ ⊗[ℤ] L)` -/
def incl : (ℚ ⊗[ℤ] (lattice (A _ ℂ))) →ₗ[ℤ] (ℝ ⊗[ℤ] (lattice (A _ ℂ))) :=
  TensorProduct.map (algebraMap ℚ ℝ).toAddMonoidHom.toIntLinearMap LinearMap.id

variable (A) in
omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
lemma incl_tmul (x : ℚ) (l : lattice (A _ ℂ)) : incl A (x ⊗ₜ[ℤ] l) = ((x : ℝ) ⊗ₜ[ℤ] l) := by
  rfl

-- aided and cleaned by Claude
variable (A) in
lemma lattice_incl_smul {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F)
    (x : F) (v : ℚ ⊗[ℤ] (lattice (A _ ℂ))) :
    letI := module_rational_lattice_of_CMStructure ι
    lattice_isLattice_map (A _ ℂ) (incl A (x • v)) = rationalEnd_lie_algebra_represenation (A _ ℂ)
    ((ι.basechange ℂ).incl x) (lattice_isLattice_map (A _ ℂ) (incl A v)) := by
  let := module_rational_lattice_of_CMStructure ι
  induction v using TensorProduct.inductionOn with
  | tmul r l =>
    let f := rationalEnd_ringHom_rationalLattice A
    suffices ∀ e : End⁰ (A _ ℂ), lattice_isLattice_map (A _ ℂ) (incl A (f e (r ⊗ₜ[ℤ] l))) =
        rationalEnd_lie_algebra_represenation (A _ ℂ) e
          (lattice_isLattice_map (A _ ℂ) (incl A (r ⊗ₜ[ℤ] l))) from
      this ((ι.basechange ℂ).incl x)
    intro e
    induction e using TensorProduct.inductionOn with
    | tmul a φ =>
      have : f (a ⊗ₜ[ℤ] φ) (r ⊗ₜ[ℤ] l) = (a * r) ⊗ₜ[ℤ] (lattice_representation (A _ ℂ) φ l) :=
        rfl
      simp only [this, incl_tmul, lattice_isLattice_map_tmul, LinearMap.map_smul_of_tower,
        Rat.cast_mul, mul_comm (a : ℝ), mul_smul]
      congr 1
    | add F₁ F₂ hF₁ hF₂ => simp only [map_add, LinearMap.add_apply, hF₁, hF₂]
  | add a b ha hb => simp [smul_add, map_add, ha, hb]

variable (A) in
omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
-- proof written by Claude
lemma ψ₂_tmul : ∀ x : ℝ, ∀ y : (ℚ ⊗[ℤ] (lattice (A _ ℂ))), ψ₂ A (x ⊗ₜ[ℚ] y) = x • (incl A y) := by
  intro x y
  induction y using TensorProduct.inductionOn with
  | tmul q l =>
    simp only [ψ₂, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    erw [TensorProduct.map_tmul, TensorProduct.smul_tmul']
    congr 1
    simp [Algebra.smul_def, mul_comm]
  | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂, smul_add]

/- The isomorphisms `ℝ ⊗[ℤ] L ≃ₗ[ℝ] Lie (A _ ℂ )` -/
#check lattice_isLattice_map (A _ ℂ)

/-- The isomorphism `ℝ ⊗[ℚ] F ≃ₗ[ℝ] (Lie (A _ ℂ))` which takes `x ⊗ y` to -/
def u_ℝ {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    ℝ ⊗[ℚ] F ≃ₗ[ℝ] (Lie (A _ ℂ)) :=
  ((ψ₁ ι).trans (ψ₂ A)).trans (lattice_isLattice_map (A _ ℂ))

lemma u_ℝ_one_tmul_mul {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    ∀ x : F, ∀ y : ℝ ⊗[ℚ] F, (u_ℝ ι) (1 ⊗ₜ[ℚ] x * y) = rationalEnd_lie_algebra_represenation (A _ ℂ)
    ((ι.basechange ℂ).incl x) ((u_ℝ ι) y) := by
  let := module_rational_lattice_of_CMStructure ι
  intro x y
  induction y using TensorProduct.inductionOn with
  | tmul r t =>
      have (f : End⁰ (A _ ℂ)) : ∀ r : ℝ, ∀ v : Lie (A _ ℂ), rationalEnd_lie_algebra_represenation
          (A _ ℂ) f (r • v) = r • rationalEnd_lie_algebra_represenation (A _ ℂ) f v :=
        fun r v ↦ by simp
      have h : (lattice_isLattice_map (A _ ℂ)) ((incl A) ((u ι) (x * t))) =
          (rationalEnd_lie_algebra_represenation (A _ ℂ)) ((ι.basechange ℂ).incl x)
          ((lattice_isLattice_map (A _ ℂ)) ((incl A) ((u ι) t))) := by
        simp [u_mul ι x t, lattice_incl_smul]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        u_ℝ, LinearEquiv.trans_apply, LinearEquiv.trans_apply, ψ₁_tmul, ψ₂_tmul, map_smul, this, h]
  | add y₁ y₂ h₁ h₂ =>
      rw [mul_add, map_add, h₁, h₂, map_add, map_add]

def complex_I_mul (V : Type*) [AddCommGroup V] [Module ℂ V] : V →ₗ[ℂ] V :=
  DistribSMul.toLinearMap _ V Complex.I

def J {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    ℝ ⊗[ℚ] F →ₗ[ℝ] ℝ ⊗[ℚ] F :=
  ((u_ℝ ι).symm.toLinearMap.comp ((complex_I_mul (Lie (A _ ℂ))).restrictScalars ℝ)).comp
  (u_ℝ ι).toLinearMap

-- aided by claude
open LinearMap in
lemma J_one {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    J ι 1 * J ι 1 = -1 := by
  have hJ : ∀ v : ℝ ⊗[ℚ] F, J ι (J ι v) = -v := by
    intro v
    simp [J, complex_I_mul, smul_smul]
  let μ (x : F) : ℝ ⊗[ℚ] F →ₗ[ℝ] ℝ ⊗[ℚ] F := mulLeft ℝ (1 ⊗ₜ[ℚ] x)
  have hμ : ∀ x : F, ∀ y : ℝ ⊗[ℚ] F, (u_ℝ ι) (μ x y) = rationalEnd_lie_algebra_represenation (A _ ℂ)
      ((ι.basechange ℂ).incl x) ((u_ℝ ι) y) :=
    u_ℝ_one_tmul_mul ι
  have h : ∀ x : F, (J ι).comp (μ x) = (μ x).comp (J ι) := by
    intro x
    ext v
    apply (u_ℝ ι).injective
    simp [J, hμ, complex_I_mul]
  have : ∀ y : ℝ ⊗[ℚ] F, J ι y = J ι 1 * y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul r f =>
      have : r ⊗ₜ[ℚ] f = r • μ f 1 := by
        simp [μ, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
      rw [this, map_smul, ← LinearMap.comp_apply, h f, LinearMap.comp_apply]
      simp [μ, mul_comm]
    | add a b ha hb => rw [map_add, ha, hb, mul_add]
  rw [← this, hJ]

/-- Given a CM strucutre on an Abelian variety `A` over a field `K`, such that `K` is
a subfield of `ℂ`, and `F` is the CM Field in the CM Structure. The, we have a preCMType
on the field `F`. -/
def CMType {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) :
    preCMType F := preCMType.ofComplexStructure (J_one ι)

end CMType

end CMStructure
