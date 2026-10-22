/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.AbelianVarieties.Homomorphisms.EndomorphismRing

/-!
## Goal

All the background need for `𝓞 F →+* End A` for a CMStrucutre.

-/
@[expose] public section

open CategoryTheory AlgebraicGeometry AddGrp RationalEnd Algebra TensorProduct
open scoped End

variable {K : Type*} [Field K]
variable {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

-- claude solved this
open TensorProduct in
lemma ratEnd_as_fraction (φ₀ : End⁰ A) :
    ∃ (φ : End (mk A)) (n : ℤ), (1 / (n : ℚ)) ⊗ₜ[ℤ] φ = φ₀ := by
  obtain ⟨⟨φ, s⟩, h⟩ :=
    IsLocalizedModule.surj (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ (End (mk A)) 1) φ₀
  refine ⟨φ, s, ?_⟩
  have hs : ((s : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero s
  simp only [TensorProduct.mk_apply] at h
  calc (1 / ((s : ℤ) : ℚ)) ⊗ₜ[ℤ] φ = (1 / ((s : ℤ) : ℚ)) • ((1 : ℚ) ⊗ₜ[ℤ] φ) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
    _ = (1 / ((s : ℤ) : ℚ)) • (((s : ℤ) : ℚ) • φ₀) := by
        rw [← h, Submonoid.smul_def, Int.cast_smul_eq_zsmul]
    _ = φ₀ := by rw [smul_smul, one_div_mul_cancel hs, one_smul]


/- The natural map `End (mk A) → End⁰ A`, `φ ↦ 1 ⊗ₜ φ`, as a ring hom (`ℤ`-algebra hom).
Its underlying `ℤ`-linear map is `TensorProduct.mk ℤ ℚ (End (mk A)) 1`. -/
#check (includeRight : End (mk A) →ₐ[ℤ] End⁰ A)
