module

public import CMAbelianVarieties.ForMathlib.Addition
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

@[expose] public section

open CategoryTheory MonoidalCategory Mon MonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {G : Mon C}
variable {H : Mon C} [hH : IsCommMonObj H.X]


instance : AddCommSemigroup (Hom G H) where
  add f g := f + g
  add_assoc f g h := by
    ext
    simp only [add_def_hom_of_Mon_Hom]
    have : ((lift (lift f.hom g.hom) (h.hom)) ≫ (μ[H.X] ▷ H.X))
        = lift (lift f.hom g.hom ≫ μ) h.hom := by
      ext <;> simp
    rw[← this]
    have : (lift (lift f.hom g.hom) h.hom) ≫ (μ ▷ H.X) ≫ μ
        = ((lift (lift f.hom g.hom) h.hom) ≫ (μ ▷ H.X)) ≫ μ := by
      apply Category.assoc'
    simp only [← this, MonObj.mul_assoc, Category.assoc']
    have : ((lift (lift f.hom g.hom) h.hom ≫ (α_ H.X H.X H.X).hom) ≫ H.X ◁ μ)
        = lift f.hom (lift g.hom h.hom ≫ μ) := by
      ext <;> simp
    rw[this]
  add_comm f g := by
    ext
    simp only [add_def_hom_of_Mon_Hom]
    nth_rw 1 [← IsCommMonObj.mul_comm H.X, ← Category.assoc,
      lift_braiding_hom f.hom g.hom]

def Mon.Hom.zero_hom (G₀ H₀ : Mon C) [IsCommMonObj H₀.X] : (Hom G₀ H₀) where
  hom := (toUnit G₀.X) ≫ (MonObj.one : 𝟙_ C ⟶ H₀.X)
  isMonHom_hom := instIsMonHomComp (toUnit G₀.X) η[H₀.X]

lemma Mon.Hom.zero_add (f : Hom G H) : (Mon.Hom.zero_hom G H) + f = f := by
    ext
    rw[add_def_hom_of_Mon_Hom]
    have : lift (Mon.Hom.zero_hom G H).hom f.hom
        = lift (toUnit G.X) (f.hom) ≫ (η ⊗ₘ (𝟙 H.X)) := by
      ext
      · simp only [lift_fst, tensorHom_id, lift_whiskerRight]; rfl
      · simp only [lift_snd, tensorHom_id, lift_whiskerRight]
    simp only [this, Category.assoc, tensorHom_id, MonObj.one_mul, lift_leftUnitor_hom]

instance : AddZeroClass (Hom G H) where
  zero := Mon.Hom.zero_hom G H
  add f g := f + g
  zero_add f := Mon.Hom.zero_add f
  add_zero f := by
    rw[add_comm]
    exact Mon.Hom.zero_add f

def Mon.Hom.nsmul (n : ℕ) : (Hom G H) →  (Hom G H) :=
  match n with
  | Nat.zero => fun _ => 0
  | Nat.succ m => fun f => (Mon.Hom.nsmul m f) + f

instance : AddCommMonoid (Hom G H) where
  add f g := f + g
  add_assoc := add_assoc
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  nsmul := Mon.Hom.nsmul
  add_comm := add_comm


instance : Mul (Hom G G) where
  mul f g := {
    hom := g.hom ≫ f.hom
    isMonHom_hom := by infer_instance
  }

set_option linter.unusedSectionVars false
lemma mul_def_hom_of_Mon_Hom (f g : (Hom G G)) :
    (f * g).hom = g.hom ≫ f.hom := rfl

set_option linter.style.show false
instance [IsCommMonObj G.X] : Semiring (Hom G G) where
  mul_assoc f g h := by
    ext
    simp[mul_def_hom_of_Mon_Hom]
  one := {
    hom := 𝟙 G.X
    isMonHom_hom := by infer_instance
  }
  one_mul f := by
    ext
    show f.hom ≫ (𝟙 G.X) = f.hom
    simp only [Category.comp_id]
  mul_one f := by
    ext
    show (𝟙 G.X) ≫ f.hom = f.hom
    simp only [Category.id_comp]
  zero_mul f := by
    ext
    show f.hom ≫ ((toUnit G.X) ≫ (MonObj.one : 𝟙_ C ⟶ G.X)) = ((toUnit G.X) ≫ (
      MonObj.one : 𝟙_ C ⟶ G.X))
    simp only [comp_toUnit_assoc]
  mul_zero f := by
    ext
    show ((toUnit G.X) ≫ (MonObj.one : 𝟙_ C ⟶ G.X)) ≫ f.hom = ((toUnit G.X) ≫
      (MonObj.one : 𝟙_ C ⟶ G.X))
    simp only [Category.assoc, IsMonHom.one_hom]
  left_distrib f g h := by
    ext
    simp only [mul_def_hom_of_Mon_Hom, add_def_hom_of_Mon_Hom,
      Category.assoc, IsMonHom.mul_hom f.hom]
    have : lift (g.hom ≫ f.hom) (h.hom ≫ f.hom)
        = lift g.hom h.hom ≫ (f.hom ⊗ₘ f.hom) := by ext <;> simp
    rw[this, Category.assoc]
  right_distrib f g h := by
    ext
    simp only [mul_def_hom_of_Mon_Hom, add_def_hom_of_Mon_Hom]
    rw[← Category.assoc]
    have : lift (h.hom ≫ f.hom) (h.hom ≫ g.hom)
        = (h.hom ≫ lift f.hom g.hom) := by ext <;> simp
    rw[this]
