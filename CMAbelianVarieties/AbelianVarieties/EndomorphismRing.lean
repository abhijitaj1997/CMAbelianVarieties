--import Mathlib
import CMAbelianVarieties.AbstractNonsense.EndomorphismRing
import Mathlib.AlgebraicGeometry.Group.Abelian

open CategoryTheory AlgebraicGeometry

variable {K} [Field K]
variable (A : Over (Spec (.of K)))
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [GrpObj A]

instance : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A

/-
## Main Goal
The goal of this file is to show that the Endomorphism ring of an abelian variety
is a commutative ring.
-/

noncomputable instance : CommRing (EndRing A) where
  zero_add := zero_add
  add_zero := add_zero
  one_mul := one_mul
  mul_one := mul_one
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := left_distrib
  right_distrib := right_distrib
  neg_add_cancel := neg_add_cancel
  mul_comm φ ψ := sorry

#min_imports
