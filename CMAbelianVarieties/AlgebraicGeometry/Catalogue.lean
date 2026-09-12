module

public import Mathlib

open AlgebraicGeometry Scheme Hom CategoryTheory Iso

variable {X Y : Scheme} {f : X ⟶ Y} {U : X.Opens} {V : Y.Opens}
variable {A : Type*} [CommRing A]
variable {R S : CommRingCat} (π : R ⟶ S)

variable {C : Type*} [Category* C] {α β : C} {φ : α ⟶ β}
variable {ψ : α ⟶ β} [IsIso ψ]

-- ## NOTATION

#check (↧A : CommRingCat)         -- the a-coercion
#check Spec R                     -- the affine spectrum
#check Γ(X, U)                    -- the sections
#check f⁻¹ᵁ V                     -- `f⁻¹(V)` as a topological space
#check U.ι                        -- the open immersion `↑U ⟶ X`

-- ## STRUCTURES

#check X.Opens                    -- open subsets of `X`

-- ## MORPHISMS

#check X.toSpecΓ                  -- `X ⟶ Spec Γ(X, ⊤)`
#check Spec.homEquiv              -- `(Spec S ⟶ Spec R) → (R ⟶ S)`
#check Spec.map                   -- `(R ⟶ S) → (Spec S ⟶ Spec R)`
#check X.topIso                   -- `↑⊤ ≅ X`
#check ΓSpecIso R                 -- `Γ(Spec R, ⊤) ≅ R`
#check π.hom                      -- `↑R →+* ↑S`
#check commRingCatIsoToRingEquiv  -- `(R ≅ S) → (↑R ≃+* ↑S)`

-- ## PROPERTIES

#check IsAffine.affine            -- if `X` is affine, then `X.toSpecΓ` is an iso
#check IsAffine.of_isIso          -- Affineness defined up to isomorphism
#check isAffine_of_isAffineHom    -- finite morphism + target affine => source is affine
#check preimage_top f             -- `f⁻¹ᵁ ⊤ = ⊤`
#check hom_inv_apply              -- `e : X ≅ Y`, `∀ x : X`, `e.inv (e.hom x) = x`
#check inv_hom_apply              -- `e : X ≅ Y`, `∀ x : X`, `e.hom (e.inv x) = x`
#check f.app V                    -- `Γ(Y, V) ⟶ Γ(X, f⁻¹ᵁ V)`
#check IsFinite.finite_app        -- if `f` is finite and `V` affine open, `(f.app V).hom` is finite
#check IsArtinianScheme.finite    -- Artinian schemes are set theoretically finite

-- ## algebraize TACTIC

/-algebraize[π.hom]-/             -- creates the tactic `Algebra ↑R ↑S` to be used in a proof

-- ## CATEGORY THOERY STUFF

#check IsIso φ                    -- `φ` is an isomorphism
#check asIso ψ                    -- gives the corresponding term of type `α ≅ β`
