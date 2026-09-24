module

public import CMAbelianVarieties.AlgebraicGeometry.Finite
public import CMAbelianVarieties.ForMathlib.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import CMAbelianVarieties.AbstractNonsense.PullbackAddGrp
public import CMAbelianVarieties.AbstractNonsense.IntHom

/-!

## Properties of [n]

The Goal of this file is discuss some basics about the map `[n] : A ⟶ A`. The
main result is that when `n ≠ 0` `A[n]` is finite over `K` and hence discrete
as a topological space.

_Incomplete tasks_
• commutativity of abelian varieties
• finiteness of `[n]`
• finiteness of `A[n]`

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AddGrp Limits AddMonObj MonoidalCategory
open CartesianMonoidalCategory IntHom

variable {K} [Field K]
variable {A : Over (Spec ↧K)} {B : Over (Spec ↧K)}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable [IsProper B.hom] [GeometricallyIntegral B.hom] [AddGrpObj B]

instance : IsCommAddMonObj A := sorry

lemma int_hom_comp (n m : ℤ) (A₀ : Over (Spec ↧K))
    [IsProper A₀.hom] [GeometricallyIntegral A₀.hom] [AddGrpObj A₀]
    : ([n]_ A₀) ≫ ([m]_ A₀) =  ([m * n]_ A₀) := by
  simp [int_hom]

abbrev ker_int (A₀ : Over (Spec ↧K)) (n : ℤ)
    [IsProper A₀.hom] [GeometricallyIntegral A₀.hom] [AddGrpObj A₀]
    : Over (Spec ↧K) := (pullback ([n]_ A₀) ζ[A₀])

notation:50 A:51 "[" n:51 "]" => ker_int A n

def ker_int_hom {m n : ℤ} (A₀ : Over (Spec ↧K))
    [IsProper A₀.hom] [GeometricallyIntegral A₀.hom] [AddGrpObj A₀]
    (h : m ∣ n) : A₀[n] ⟶ A₀[m] := by
  let k := n/m
  have hk : m * k = n := by
    exact Int.mul_ediv_cancel' h
  have : ((pullback.fst ([n]_ A₀) ζ) ≫ ([k]_ A₀)) ≫ ([m]_ A₀) = (pullback.snd ([n]_ A₀) ζ) ≫ ζ
      := by
    rw [← hk, Category.assoc, int_hom_comp]
    exact pullback.condition
  exact pullback.lift ((pullback.fst ([n]_ A₀) ζ) ≫ ([k]_ A₀)) (pullback.snd ([n]_ A₀) ζ)

def functorial_ker_int {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] {B : Over (Spec ↧K)} [IsProper B.hom] [GeometricallyIntegral B.hom]
    [AddGrpObj B] (n : ℤ) (f : A ⟶ B) [IsAddMonHom f] : A[n] ⟶ B [n] := by
  have : ((pullback.fst ([n]_ A) ζ) ≫ f) ≫ ([n]_ B) = (pullback.snd ([n]_ A) ζ) ≫ ζ
      := by
    rw [Category.assoc, int_commute, Category.assoc', pullback.condition]
    simp
  exact pullback.lift ((pullback.fst ([n]_ A) ζ ≫ f)) (pullback.snd ([n]_ A) ζ)

lemma IsAddMonHom_functorial_ker_int {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral
    A.hom] [AddGrpObj A] {B : Over (Spec ↧K)} [IsProper B.hom] [GeometricallyIntegral B.hom]
    [AddGrpObj B] {n : ℤ} {f : A ⟶ B} [IsAddMonHom f] : IsAddMonHom (functorial_ker_int n f) := by
  apply IsAddMonHom.pullback_lift

instance {m n : ℤ} {h : m ∣ n} : IsAddMonHom (ker_int_hom A h) := by
  apply IsAddMonHom.pullback_lift

lemma isFinite_int_hom {n : ℤ} (hn : n ≠ 0)
  : IsFinite ([n]_ A).left := sorry

lemma step₁ {n : ℤ} (hn : n ≠ 0) : IsFinite (pullback.snd ([n]_ A).left ζ[A].left) := by
  have : IsFinite ([n]_ A).left := isFinite_int_hom hn
  exact IsFinite.instSndScheme ([n]_ A).left ζ[A].left

lemma step₂ {n : ℤ} (hn : n ≠ 0) : IsFinite (pullback.snd ([n]_ A) ζ[A]).left := by
  let φ := (PreservesPullback.iso (Over.forget (Spec ↧K)) ([n]_ A) ζ)
  let φ' := (Over.forget (Spec ↧K)).map (pullback.snd ([n]_ A) ζ)
  have : IsFinite (φ.inv ≫ φ') := by
    rw[PreservesPullback.iso_inv_snd (Over.forget (Spec ↧K)) ([n]_ A) ζ[A]]
    exact step₁ hn
  have finite_comp : IsFinite ((𝟙 ((Over.forget (Spec ↧K)).obj (pullback ([n]_ A) ζ))) ≫ φ') := by
    rw [← Iso.hom_inv_id φ, Category.assoc]
    infer_instance
  exact finite_comp

lemma torsion_top_fintie {n : ℤ} {hn : n ≠ 0} : Finite (A[n]).left :=
  @Finite_of_isFiniteOverField _ _ _ (pullback.snd ([n]_ A) ζ[A]).left (step₂ hn)

lemma step₂' {n : ℤ} (hn : n ≠ 0) : IsAffine (pullback ([n]_ A) ζ[A]).left := by
  sorry

lemma step₃ {n : ℤ} (hn : n ≠ 0) : DiscreteTopology (A[n]).left :=
  @discrete_of_isFiniteOverField _ _ _ (pullback.snd ([n]_ A) ζ[A]).left (step₂ hn)

#min_imports
