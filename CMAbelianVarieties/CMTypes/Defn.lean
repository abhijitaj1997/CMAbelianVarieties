module

public import Mathlib.NumberTheory.NumberField.CMField

/-!
# CM Types

In this section we define CM types

-/

@[expose] public section

open ComplexConjugate NumberField

structure preCMType (K : Type*) [Field K] [NumberField K] [IsCMField K] where
  partition : Set (K →+* ℂ)
  partition_condition : ∀ φ : (K →+* ℂ), φ ∈ partition ↔
    (conj : ℂ →+* ℂ).comp φ ∈ partitionᶜ

/-
Maybe a lemma should be created which says that given a `preCMType`, we
have a natural map from to the set of places of `K`
-/

section

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

#check (Module.finrank ℚ K)

#synth Finite (K →+* ℂ)

/- The number of complex embeddings equals the degree `[K : ℚ]`. -/
#check NumberField.Embeddings.card K ℂ

/- A totally complex field (e.g. a CM field) has even degree. -/
#check NumberField.IsTotallyComplex.finrank K

#check InfinitePlace.nrComplexPlaces


end

#min_imports
