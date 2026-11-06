/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.AbelianVarieties.Homomorphism.EndLimit

/-!
## Main result

`exists_finiteDimensional_bijective_baseChangeHom`: for an abelian variety `A` over `K₀` and an
extension `K / K₀`, there is an intermediate field `E` of `K / K₀`, finite over `K₀`, such that
base change `End⁰ (A _ E) → End⁰ (A _ K)` is bijective.

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry RationalEnd
open scoped BaseChange AddGrp.End

universe u

variable {K₀ : Type u} [Field K₀]
variable {A : Over (Spec ↧K₀)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable {K : Type u} [Field K] [Algebra K₀ K]

variable (A K) in
def I := (Fin (Module.finrank ℚ (End⁰ (A _ K))))

-- written by Claude
variable (A K) in
/-- A `ℚ`-basis of `End⁰ (A _ K)`, indexed by `Fin n` with `n` its `ℚ`-dimension. -/
def ℬ : Module.Basis (I A K) ℚ (End⁰ (A _ K)) :=
  Module.finBasis ℚ _

-- aided by Claude
lemma exists_baseChangeHom_eq_ℬ (i : I A K) : ∃ (E : IntermediateField K₀ K)
    (_ : FiniteDimensional K₀ E) (φ : End⁰ (A _ E)), baseChangeHom A E K φ = ℬ A K i := by
  have : IsDirectedOrder {L : IntermediateField K₀ K // FiniteDimensional K₀ L} :=
    ⟨fun L₁ L₂ ↦ ⟨⟨L₁.1 ⊔ L₂.1, have := L₁.2; have := L₂.2; inferInstance⟩,
      le_sup_left (a := L₁.1), le_sup_right (a := L₁.1)⟩⟩
  have : Nonempty {L : IntermediateField K₀ K // FiniteDimensional K₀ L} :=
    ⟨⟨⊥, inferInstance⟩⟩
  obtain ⟨E, φ, hφ⟩ := Limits.Concrete.isColimit_exists_rep _ (limitRatEnd.isColimit A K) (ℬ A K i)
  exact ⟨E.1, E.2, φ, hφ⟩

-- aided by claude
open Function in
theorem exists_finiteDimensional_bijective_baseChangeHom : ∃ (E : IntermediateField K₀ K)
    (_ : FiniteDimensional K₀ E), Bijective (baseChangeHom A E K) := by
  let E' (i : I A K) : IntermediateField K₀ K := (exists_baseChangeHom_eq_ℬ i).choose
  have (i : I A K) : FiniteDimensional K₀ (E' i) := (exists_baseChangeHom_eq_ℬ i).choose_spec.choose
  let φ (i : I A K) : End⁰ (A _ (E' i)) := by
    have (i : I A K) : E' i = (exists_baseChangeHom_eq_ℬ i).choose := rfl
    rw [this]
    exact (exists_baseChangeHom_eq_ℬ i).choose_spec.choose_spec.choose
  have hφ (i : I A K) : baseChangeHom A (E' i) K (φ i) = ℬ A K i := by
    have : φ i = (exists_baseChangeHom_eq_ℬ i).choose_spec.choose_spec.choose := rfl
    rw [this]
    exact (exists_baseChangeHom_eq_ℬ i).choose_spec.choose_spec.choose_spec
  let E := ⨆ i : I A K, E' i
  have hle (i : I A K) : E' i ≤ E := le_iSup E' i
  let {i : I A K} : Algebra (E' i) E :=
    (IntermediateField.inclusion (hle i)).toRingHom.toAlgebra
  have {i : I A K} : IsScalarTower K₀ (E' i) E := ⟨fun x y z ↦ by
    ext; simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc]⟩
  have {i : I A K} : IsScalarTower (E' i) E K := ⟨fun x y z ↦ by
    simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc]⟩
  have : FiniteDimensional K₀ E :=
    have : Finite (I A K) := inferInstanceAs (Finite (Fin _))
    IntermediateField.finiteDimensional_iSup_of_finite
  use E, this
  constructor
  · exact baseChangeHom_inj A (↥E) K
  · have (i : I A K) : ∃ φ : End⁰ (A _ E), baseChangeHom A E K φ = ℬ A K i := by
      use baseChangeHom A (E' i) E (φ i)
      simp [← hφ i, ← baseChangeHom_comp A (E' i) E K]
    let f := (baseChangeHom A E K).toAddMonoidHom.toRatLinearMap
    change Surjective f
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (ℬ A K).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact this i
