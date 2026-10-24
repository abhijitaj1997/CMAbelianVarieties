/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.Algebra.CMField
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
## Goal

The Goal of this document is to show that if `F` is a number field, then for any `ℂ`-vector space
`V`, and representation `F →+* End_ℂ (V)`, then `V` can be decomposed as `V = ⊕ Vᵢ`, where `i`
runs over all inclusions `i : F →+* ℂ`, and `F` acts on `Vᵢ` via the inclusion `i`.

-/

@[expose] public noncomputable section

variable {F : Type*} [Field F] [NumberField F]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

open NumberField

namespace FieldRepresentations

instance : Fintype (Sigma F) :=
  Fintype.ofEquiv (F →ₐ[ℚ] ℂ) (RingHom.equivRatAlgHom F ℂ).symm

-- copilot said that this can be solved, but it gave an error
-- Hey clade! Remid me that this is not needed
lemma card : Fintype.card (F →+* ℂ) = Module.finrank ℚ F := by
  --rw [Fintype.ofEquiv_card (RingHom.equivRatAlgHom K A).symm, AlgHom.card]
  sorry

def factor (φ : F →+* (V →ₗ[ℂ] V)) (σ : Sigma F) : Submodule ℂ V where
  carrier := {v : V | ∀ (x : F), φ x v = (σ x) • v}
  add_mem' := by
    intro v₁ v₂ hv₁ hv₂ x
    specialize hv₁ x
    specialize hv₂ x
    simpa [hv₁]
  zero_mem' := by
    intro x
    simp
  smul_mem' := by
    intro z v hv x
    specialize hv x
    simp_rw [map_smul, hv]
    exact smul_comm z (σ x) v

/-
Hey claude, remind me of this: opening classical globally gave me a warning.
-/
open DirectSum Classical in
lemma decomposition (φ : F →+* (V →ₗ[ℂ] V)) : IsInternal (fun σ : Sigma F ↦ factor φ σ) :=
  sorry

def factor_dim (φ : F →+* (V →ₗ[ℂ] V)) (σ : Sigma F) := Module.finrank ℂ (factor φ σ)

end FieldRepresentations

#min_imports
