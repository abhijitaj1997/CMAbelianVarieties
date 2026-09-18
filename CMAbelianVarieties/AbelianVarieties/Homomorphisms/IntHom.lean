module

public import CMAbelianVarieties.AlgebraicGeometry.Finite
public import CMAbelianVarieties.ForMathlib.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import CMAbelianVarieties.AbstractNonsense.PullbackAddGrp

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
open CartesianMonoidalCategory

variable {K} [Field K]
variable {A : Over (Spec ↧K)} {B : Over (Spec ↧K)}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable [IsProper B.hom] [GeometricallyIntegral B.hom] [AddGrpObj B]

instance : IsCommAddMonObj A := sorry

def int_hom (n : ℤ) (A₀ : Over (Spec ↧K))
    [IsProper A₀.hom] [GeometricallyIntegral A₀.hom] [AddGrpObj A₀]
    : A₀ ⟶ A₀ := (n • (1 : End (mk A₀))).hom.hom

notation:50 n:51 "[" A:51 "]" => int_hom n A

instance {n : ℤ} : IsAddMonHom (n[A]) := by
  rw [int_hom]
  infer_instance

lemma int_hom_comp (n m : ℤ) (A₀ : Over (Spec ↧K))
    [IsProper A₀.hom] [GeometricallyIntegral A₀.hom] [AddGrpObj A₀]
    : (n[A₀]) ≫ (m[A₀]) =  ((m * n)[A₀]) := by
  simp [int_hom]

abbrev ker_int (A₀ : Over (Spec ↧K)) (n : ℤ)
    [IsProper A₀.hom] [GeometricallyIntegral A₀.hom] [AddGrpObj A₀]
    : Over (Spec ↧K) := (pullback (n[A₀]) ζ[A₀])

notation:50 A:51 "[" n:51 "]" => ker_int A n

def ker_int_hom {m n : ℤ} (A₀ : Over (Spec ↧K))
    [IsProper A₀.hom] [GeometricallyIntegral A₀.hom] [AddGrpObj A₀]
    (h : m ∣ n) : A₀[n] ⟶ A₀[m] := by
  let k := n/m
  have hk : m * k = n := by
    exact Int.mul_ediv_cancel' h
  have : ((pullback.fst (n[A₀]) ζ) ≫ (k[A₀])) ≫ (m[A₀]) = (pullback.snd (n[A₀]) ζ) ≫ ζ
      := by
    rw [← hk, Category.assoc, int_hom_comp]
    exact pullback.condition
  exact pullback.lift ((pullback.fst (n[A₀]) ζ) ≫ (k[A₀])) (pullback.snd (n[A₀]) ζ)


instance {m n : ℤ} {h : m ∣ n} : IsAddMonHom (ker_int_hom A h) := by
  apply IsAddMonHom.pullback_lift

lemma isFinite_int_hom {n : ℤ} (hn : n ≠ 0)
  : IsFinite (n[A]).left := sorry

lemma step₁ {n : ℤ} (hn : n ≠ 0) : IsFinite (pullback.snd (n[A]).left ζ[A].left) := by
  have : IsFinite (n[A]).left := isFinite_int_hom hn
  exact IsFinite.instSndScheme (n[A]).left ζ[A].left

lemma step₂ {n : ℤ} (hn : n ≠ 0) : IsFinite (pullback.snd (n[A]) ζ[A]).left := by
  let φ := (PreservesPullback.iso (Over.forget (Spec ↧K)) (n[A]) ζ)
  let φ' := (Over.forget (Spec ↧K)).map (pullback.snd (n[A]) ζ)
  have : IsFinite (φ.inv ≫ φ') := by
    rw[PreservesPullback.iso_inv_snd (Over.forget (Spec ↧K)) (n[A]) ζ[A]]
    exact step₁ hn
  have finite_comp : IsFinite ((𝟙 ((Over.forget (Spec ↧K)).obj (pullback (n[A]) ζ))) ≫ φ') := by
    rw [← Iso.hom_inv_id φ, Category.assoc]
    infer_instance
  exact finite_comp

lemma torsion_top_fintie {n : ℤ} {hn : n ≠ 0} : Finite (A[n]).left :=
  @Finite_of_isFiniteOverField _ _ _ (pullback.snd (n[A]) ζ[A]).left (step₂ hn)

lemma step₂' {n : ℤ} (hn : n ≠ 0) : IsAffine (pullback (n[A]) ζ[A]).left := by
  sorry

lemma step₃ {n : ℤ} (hn : n ≠ 0) : DiscreteTopology (A[n]).left :=
  @discrete_of_isFiniteOverField _ _ _ (pullback.snd (n[A]) ζ[A]).left (step₂ hn)

#min_imports
