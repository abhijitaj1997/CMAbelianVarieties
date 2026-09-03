import Mathlib

open AlgebraicGeometry CategoryTheory MorphismProperty

variable {K : Type*} [Field K] (A : CategoryTheory.Over (Spec (.of K)))


-- There are already results about abelian varieties in Lean, but the name is
-- not used. So, I am just using it.

/--
An abelian variety is a group object in the category of `K`- schemes which is
proper and smooth over `K` and connected as a topological space.
-/
class AbelianVariety extends GrpObj A, IsProper A.hom, Smooth A.hom, ConnectedSpace A.left










namespace AbelianVariety

variable {F} [Field F] [Algebra K F]



instance [AbelianVariety A] : GeometricallyIntegral A.hom where
  geometrically_isIntegral := by
    intro F _ f X φ₁ φ₂ hX
    constructor
    · sorry
    · sorry

theorem isAbelian [AbelianVariety A] : IsCommMonObj A :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A

end AbelianVariety
