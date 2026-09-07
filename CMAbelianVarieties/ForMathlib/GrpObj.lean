module

public import CMAbelianVarieties.ForMathlib.MonObj
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp


@[expose] public section

open CategoryTheory MonoidalCategory Mon MonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {A : C} [GrpObj A] [IsCommMonObj A]
variable {B : C} [GrpObj B] [IsCommMonObj B]

def inv_comp (f : A ⟶ B) := f ≫ ι

def mon_hom.zsmul (n : ℤ) : (Hom (mk A) (mk B)) → (Hom (mk A) (mk B)) :=
  match n with
  | Int.ofNat m => Hom.nsmul m
  | Int.negSucc m => fun f => {
      hom := inv_comp (Hom.nsmul (m + 1) f).hom
      isMonHom_hom := instIsMonHomComp (Hom.nsmul (m + 1) f).hom ι
  }

instance : AddCommGroup (Hom (mk A) (mk B)) where
  add f g := f + g
  add_assoc := add_assoc
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  neg f := {
    hom := inv_comp f.hom
    isMonHom_hom := instIsMonHomComp f.hom ι
  }
  zsmul := mon_hom.zsmul
  neg_add_cancel f := by
    ext
    simp only [add_def_hom_of_Mon_Hom]
    have : lift (inv_comp f.hom) f.hom = f.hom ≫ (lift ι (𝟙 B)) := by
      ext
      · simp only [lift_fst, comp_lift, Category.comp_id]
        rfl
      · simp only [lift_snd, comp_lift, Category.comp_id]
    simp only [this, Category.assoc, GrpObj.left_inv, comp_toUnit_assoc]
    rfl
  add_comm := add_comm

instance : Ring (Hom (mk A) (mk A)) where
  zero_add := zero_add
  add_zero := add_zero
  one_mul := one_mul
  mul_one := mul_one
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := left_distrib
  right_distrib := right_distrib
  neg_add_cancel := neg_add_cancel
