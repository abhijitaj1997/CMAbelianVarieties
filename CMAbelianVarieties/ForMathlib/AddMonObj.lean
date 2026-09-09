module

public import CMAbelianVarieties.ForMathlib.Addition_
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

@[expose] public section

open CategoryTheory MonoidalCategory AddMon AddMonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {G : AddMon C}
variable {H : AddMon C} [hH : IsCommAddMonObj H.X]


instance : AddCommSemigroup (Hom G H) where
  add f g := f + g
  add_assoc f g h := by
    ext
    simp only [AddMonHom.add_hom]
    have : ((lift (lift f.hom g.hom) (h.hom)) ≫ (σ[H.X] ▷ H.X))
        = lift (lift f.hom g.hom ≫ σ) h.hom := by
      ext <;> simp
    rw[← this]
    have : (lift (lift f.hom g.hom) h.hom) ≫ (σ ▷ H.X) ≫ σ
        = ((lift (lift f.hom g.hom) h.hom) ≫ (σ ▷ H.X)) ≫ σ := by
      apply Category.assoc'
    simp only [← this, AddMonObj.add_assoc, Category.assoc']
    have : ((lift (lift f.hom g.hom) h.hom ≫ (α_ H.X H.X H.X).hom) ≫ H.X ◁ σ)
        = lift f.hom (lift g.hom h.hom ≫ σ) := by
      ext <;> simp
    rw[this]
  add_comm f g := by
    ext
    simp only [AddMonHom.add_hom]
    nth_rw 1 [← IsCommAddMonObj.add_comm H.X, ← Category.assoc,
      lift_braiding_hom f.hom g.hom]

def AddMon.Hom.zero_hom (G₀ H₀ : AddMon C) [IsCommAddMonObj H₀.X] : (Hom G₀ H₀) where
  hom := (toUnit G₀.X) ≫ (AddMonObj.zero : 𝟙_ C ⟶ H₀.X)
  isAddMonHom_hom := instIsAddMonHomComp (toUnit G₀.X) ζ[H₀.X]

lemma AddMon.Hom.zero_add (f : Hom G H) : (AddMon.Hom.zero_hom G H) + f = f := by
    ext
    rw[AddMonHom.add_hom]
    have : lift (AddMon.Hom.zero_hom G H).hom f.hom
        = lift (toUnit G.X) (f.hom) ≫ (ζ ⊗ₘ (𝟙 H.X)) := by
      ext
      · simp only [lift_fst, tensorHom_id, lift_whiskerRight]; rfl
      · simp only [lift_snd, tensorHom_id, lift_whiskerRight]
    simp only [this, Category.assoc, tensorHom_id, AddMonObj.zero_add, lift_leftUnitor_hom]

instance : AddZeroClass (Hom G H) where
  zero := AddMon.Hom.zero_hom G H
  add f g := f + g
  zero_add f := AddMon.Hom.zero_add f
  add_zero f := by
    rw[add_comm]
    exact AddMon.Hom.zero_add f

def AddMon.Hom.nsmul (n : ℕ) : (Hom G H) →  (Hom G H) :=
  match n with
  | Nat.zero => fun _ => 0
  | Nat.succ m => fun f => (AddMon.Hom.nsmul m f) + f

instance : AddCommMonoid (Hom G H) where
  add f g := f + g
  add_assoc := add_assoc
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  nsmul := AddMon.Hom.nsmul
  add_comm := add_comm


instance : Mul (Hom G G) where
  mul f g := {
    hom := g.hom ≫ f.hom
    isAddMonHom_hom := inferInstance
  }

set_option linter.unusedSectionVars false
lemma AddMonHom.mul_hom (f g : (Hom G G)) :
    (f * g).hom = g.hom ≫ f.hom := rfl

set_option linter.style.show false
instance [IsCommAddMonObj G.X] : Semiring (Hom G G) where
  mul_assoc f g h := by
    ext
    simp[AddMonHom.mul_hom]
  one := {
    hom := 𝟙 G.X
    isAddMonHom_hom := by infer_instance
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
    show f.hom ≫ ((toUnit G.X) ≫ (AddMonObj.zero : 𝟙_ C ⟶ G.X)) = ((toUnit G.X) ≫ (
      AddMonObj.zero : 𝟙_ C ⟶ G.X))
    simp only [comp_toUnit_assoc]
  mul_zero f := by
    ext
    show ((toUnit G.X) ≫ (AddMonObj.zero : 𝟙_ C ⟶ G.X)) ≫ f.hom = ((toUnit G.X) ≫
      (AddMonObj.zero : 𝟙_ C ⟶ G.X))
    simp only [Category.assoc, IsAddMonHom.zero_hom]
  left_distrib f g h := by
    ext
    simp only [AddMonHom.mul_hom, AddMonHom.add_hom,
      Category.assoc, IsAddMonHom.add_hom f.hom]
    have : lift (g.hom ≫ f.hom) (h.hom ≫ f.hom)
        = lift g.hom h.hom ≫ (f.hom ⊗ₘ f.hom) := by ext <;> simp
    rw[this, Category.assoc]
  right_distrib f g h := by
    ext
    simp only [AddMonHom.mul_hom, AddMonHom.add_hom]
    rw[← Category.assoc]
    have : lift (h.hom ≫ f.hom) (h.hom ≫ g.hom)
        = (h.hom ≫ lift f.hom g.hom) := by ext <;> simp
    rw[this]
