import algebraic_geometry.AffineScheme

import random_lemmas
import about_local_rings

/-

# 01I1

-/

noncomputable theory

universes u

open opposite
open Top.presheaf
open category_theory

namespace algebraic_geometry

variables (X Y : Scheme.{u}) [is_affine Y]

namespace Scheme


-- concrete
@[simps] def stalk_iso_of_affine (pt : prime_spectrum $ Γ.obj $ op Y)  : 
    Y.presheaf.stalk (Y.iso_Spec.inv.1.base pt)
  ≃+* localization.at_prime pt.as_ideal :=
ring_equiv.trans 
(CommRing.from_iso 
{ hom := PresheafedSpace.stalk_map (Y.iso_Spec.inv.1) _,
  inv := stalk_specializes _ (by rw [←Scheme.comp_val_base_apply, iso.inv_hom_id, 
    Scheme.id_val_base, id_apply]) ≫ PresheafedSpace.stalk_map (Y.iso_Spec.hom.1) _,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }) 
{ to_fun := (structure_sheaf.stalk_iso _ _).hom,
  inv_fun := (structure_sheaf.stalk_iso _ _).inv,
  left_inv := λ x, by erw [←comp_apply, iso.hom_inv_id, id_apply],
  right_inv := λ x, by erw [←comp_apply, iso.inv_hom_id, id_apply],
  map_mul' := map_mul _,
  map_add' := map_add _ }

def stalk_iso_of_affine' (x : Y.carrier) : 
    Y.presheaf.stalk x
  ≃+* localization.at_prime (Y.iso_Spec.hom.1.base x).as_ideal :=
sorry

instance gloabl_sections_algebra (y : Y.carrier) :
  algebra (Scheme.Γ.obj $ op Y) $ Y.presheaf.stalk y :=
ring_hom.to_algebra $ ring_hom.comp 
  (PresheafedSpace.stalk_map Y.iso_Spec.hom.1 _) $
  (structure_sheaf.stalk_iso _ _).inv.comp $ 
  @algebra_map (Γ.obj $ op Y) 
    (localization.at_prime (Y.iso_Spec.hom.1.base y).as_ideal) _ _ $
      by { dsimp, exact localization.algebra }

instance stalk_is_localization (y : Y.carrier) : 
  @@is_localization.at_prime _ (Y.presheaf.stalk y)
    _ (algebraic_geometry.Scheme.gloabl_sections_algebra Y y) 
    (Y.iso_Spec.hom.1.base y).as_ideal _ :=
{ map_units := λ z, 
  begin 
    rw [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply, 
      ring_hom.comp_apply],
    refine is_unit.map _ (is_unit.map _ _),
    erw [←localization.mk_algebra_map, algebra.algebra_map_self], 
    rw [ring_hom.id_apply, localization.at_prime.mk_is_unit_iff],
    exact z.2,
  end,
  surj := λ z,
  begin 
    simp_rw [ring_hom.algebra_map_to_algebra, ←ring_hom.comp_assoc],
    let z' : localization.at_prime (Y.iso_Spec.hom.val.base y).as_ideal := sorry,
    have eq0 : z = (PresheafedSpace.stalk_map Y.iso_Spec.hom.val y).comp
      (structure_sheaf.stalk_iso (Γ.obj $ op Y) ((Y.iso_Spec.hom.val.base) y)).inv z',
    { sorry },
    simp_rw [eq0, ring_hom.comp_apply, ←map_mul],
    obtain ⟨⟨a, b⟩, eq1⟩ := localization.is_localization.surj z',
    refine ⟨⟨a, b⟩, _⟩,
    dsimp at eq1 ⊢,
    congr' 1,
    erw ←eq1,
    rw [map_mul],
  end,
  eq_iff_exists := sorry }

end Scheme

namespace Scheme.hom

open Scheme opposite category_theory

-- 01I1
def target_AffineScheme :
  (X ⟶ Y) ≃ ((Γ.obj $ op Y) ⟶ (Γ.obj $ op X)) :=
equiv.trans 
{ to_fun := λ α, α ≫ Y.iso_Spec.hom,
  inv_fun := λ α, α ≫ Y.iso_Spec.inv,
  left_inv := λ α, by simp_rw [category.assoc, iso.hom_inv_id, category.comp_id],
  right_inv := λ α, by simp_rw [category.assoc, iso.inv_hom_id, category.comp_id] } $ 
(Γ_Spec.adjunction.hom_equiv X (op $ Γ.obj $ op Y)).symm.trans $
op_equiv _ _

end Scheme.hom

end algebraic_geometry

