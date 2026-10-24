/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.NumberTheory.NumberField.CMField

/-!

## Goal

In this section, we will show that the embedding into `ℝ` is a product of
half the complex embeddings.

-/

@[expose] public noncomputable section

variable {F : Type*} [Field F] [NumberField F]

open scoped TensorProduct

namespace NumberField

variable (F) in
abbrev Sigma := F →+* ℂ

-- Statement changed by Claude: the index was `Fin (InfinitePlace.nrComplexPlaces F)`.
-- Indexing by the complex places `{w : InfinitePlace F // w.IsComplex}` themselves is canonical:
-- with `Fin` one has to choose an ordering of the places (via `Fintype.equivFin`), which is not
-- canonical and gets in the way of proofs. Both index types have `nrComplexPlaces F = [F : ℚ] / 2`
-- elements, so the ℝ-dimensions still match. This index also agrees with Mathlib's mixed space
-- (`NumberField.mixedEmbedding`), whose complex part is `{w // IsComplex w} → ℂ`; for each `w`
-- the map should be `x ⊗ a ↦ x • w.embedding a`.
def real_tensor_CMField [IsCMField F] :
    (ℝ ⊗[ℚ] F) ≃ₐ[ℝ] ({w : InfinitePlace F // w.IsComplex} → ℂ) := sorry

end NumberField



section

open NumberField

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

#check (Module.finrank ℚ K)

#synth Finite (K →+* ℂ)

/- The number of complex embeddings equals the degree `[K : ℚ]`. -/
#check NumberField.Embeddings.card K ℂ

/- A totally complex field (e.g. a CM field) has even degree. -/
#check NumberField.IsTotallyComplex.finrank K
#check InfinitePlace.nrComplexPlaces K

#check InfinitePlace.nrComplexPlaces


end
#min_imports
