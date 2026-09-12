module

public import CMAbelianVarieties.AbelianVarieties.Homomorphisms.FiniteFree
public import CMAbelianVarieties.AlgebraicGeometry.Finite

/-!
## Properties of [n]

The Goal of this file is discuss some basics about the map `[n] : A ⟶ A`. The
main result is that when `n ≠ 0` `A[n]` is finite over `K` and hence discrete
as a topological space.

_Incomplete bits_
• I still haven't shown that fact that `[n] : A ⟶ A` is finite when `n ≠ 0`

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AddGrp Limits AddMonObj MonoidalCategory

variable {K} [Field K]
variable {A : Over (Spec (.of K))} {B : Over (Spec ↧K)}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable [IsProper B.hom] [GeometricallyIntegral B.hom] [AddGrpObj B]


def int_hom (n : ℤ) (A₀ : Over (Spec ↧K))
    [IsProper A₀.hom] [GeometricallyIntegral A₀.hom] [AddGrpObj A₀]
    : A₀ ⟶ A₀ := (n • (1 : End (mk A₀))).hom.hom

notation:50 n:51 "[" A:51 "]" => int_hom n A

instance {n : ℤ} : IsAddMonHom (n[A]) := by
  rw [int_hom]
  infer_instance

abbrev ker_int (A₀ : Over (Spec ↧K)) (n : ℤ)
    [IsProper A₀.hom] [GeometricallyIntegral A₀.hom] [AddGrpObj A₀]
    : Over (Spec ↧K) := (pullback (n[A₀]) ζ[A₀])


notation:50 A:51 "[" n:51 "]" => ker_int A n

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

lemma step₃ {n : ℤ} (hn : n ≠ 0) : DiscreteTopology (A[n]).left :=
  @discrete_of_isFiniteOverField _ _ _ (pullback.snd (n[A]) ζ[A]).left (step₂ hn)

#min_imports
