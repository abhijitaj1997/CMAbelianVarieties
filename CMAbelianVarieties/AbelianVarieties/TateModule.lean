module

public import Mathlib
public import CMAbelianVarieties.AbelianVarieties.Homomorphisms.IntHom
public import CMAbelianVarieties.AbstractNonsense.PullbackAddGrp

/-!
## Main goal

The main goal of this section is to define the Tate module of an Abelian Variety
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AddGrp Limits CartesianMonoidalCategory
open AddMonObj MonoidalCategory

open AlgebraicGeometry Scheme Hom CategoryTheory Iso

variable {K : Type*} [Field K]
variable {A : Over (Spec ↧K)}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable {p : ℕ} {hp : p.Prime}

/-
the unit element in `Over (Spec ↧K)`, i.e, `Spec K`
-/
abbrev specᵤ (K : Type*) [Field K] := 𝟙_ (Over (Spec ↧K))
abbrev p₁ (n : ℤ) := pullback.fst (n[A]) ζ
abbrev p₂ (n : ℤ) := pullback.snd (n[A]) ζ


notation:50 A:51 "[" n:51 "]( " K:50 " )" => (specᵤ K ⟶ A[n])

lemma int_hom_rational (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (n : ℕ) (X : Over (Spec ↧K)) : ∀ g : X ⟶ A, n • g = g ≫ (n[A]) := sorry

lemma rational_torsion (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (n : ℕ) : ∀ g : A[n](K), n • g = 0 := by
  intro g
  let p : (specᵤ K ⟶ A[n]) →ₗ[ℤ] (specᵤ K ⟶ A)
    := AddMonoidHom.toIntLinearMap (IsAddMonHom.addMonoidHom (p₁ n) (specᵤ K))
  have : p (n • g) = n • p g := LinearMap.map_smul_of_tower p n g
  have : n • p g = p g ≫ (n[A]) := by
    induction n with
    | zero =>
        simp [int_hom]; rfl
    | succ k hk =>

        sorry
  sorry

def torsion_map (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (p n m : ℕ) (h : n ≥ m) : A[p ^ n](K) →+ A[p ^ m](K) where
  toFun := sorry
  map_zero' := sorry
  map_add' := sorry

#check ProfiniteGrp.limit

#min_imports
