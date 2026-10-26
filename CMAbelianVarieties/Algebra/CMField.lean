/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.NumberTheory.NumberField.CMField

/-!
## Goal

This section contains the isomorphisms `ℝ ⊗[ℚ] F → ∏_{w : InfinitePlace F} ℂ`, where
the morphisms is defined by `x ⊗ y ↦ x * w(y)`

-/

@[expose] public noncomputable section

variable {F : Type*} [Field F] [NumberField F]

open scoped TensorProduct

namespace NumberField

variable (F) in
abbrev Sigma := F →+* ℂ

variable (F) in
-- Cleaned up by Claude.
def real_tensor_CMField [IsCMField F] :
    (ℝ ⊗[ℚ] F) ≃ₐ[ℝ] (InfinitePlace F → ℂ) :=
  let ψ : ℝ ⊗[ℚ] F →ₐ[ℝ] (InfinitePlace F → ℂ) := Algebra.TensorProduct.lift (Algebra.ofId ℝ _)
    (RingHom.pi fun w ↦ w.embedding).toRatAlgHom fun _ _ ↦ .all _ _
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ : ∃ x : mixedEmbedding.mixedSpace F,
        (fun w ↦ x.2 ⟨w, IsTotallyComplex.isComplex w⟩) = y := ⟨(0, fun w ↦ y w.1), rfl⟩
    rw [← (mixedEmbedding.latticeBasis F).sum_repr x]
    refine ⟨∑ i, (mixedEmbedding.latticeBasis F).repr x i ⊗ₜ (integralBasis F i : F), ?_⟩
    ext w
    simp [ψ, Prod.snd_sum, Finset.sum_apply, Complex.real_smul]
  have hdim : Module.finrank ℝ (ℝ ⊗[ℚ] F) = Module.finrank ℝ (InfinitePlace F → ℂ) := by
    rw [Module.finrank_baseChange, IsTotallyComplex.finrank, Module.finrank_pi_fintype,
      Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul, Finset.card_univ,
      InfinitePlace.nrComplexPlaces, mul_comm]
    congr 1
    simp [Fintype.card_subtype, IsTotallyComplex.isComplex]
  AlgEquiv.ofBijective ψ
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := ψ.toLinearMap)).mpr hsurj,
      hsurj⟩

variable (F) in
-- Proof written by Claude
lemma real_tensor_CMField_tmsul [IsCMField F] (x : ℝ) (y : F) :
    real_tensor_CMField F (x ⊗ₜ[ℚ] y) = fun w : InfinitePlace F ↦ x * w.embedding y := by
  ext w
  simp [real_tensor_CMField, InfinitePlace.embedding]

end NumberField
