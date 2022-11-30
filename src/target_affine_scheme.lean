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

instance (R : CommRing) [local_ring R] : 
  local_ring $ Γ.obj $ op $ Spec_obj R := 
local_ring.of_equiv _ R 
{ to_fun := (structure_sheaf.global_sections_iso R).inv,
  inv_fun := (structure_sheaf.global_sections_iso R).hom,
  left_inv := λ x, by rw [←comp_apply, iso.inv_hom_id, id_apply],
  right_inv := λ x, by rw [←comp_apply, iso.hom_inv_id, id_apply],
  map_mul' := map_mul _,
  map_add' := map_add _ }

-- concrete
@[simps]
def stalk_iso_of_affine (pt : prime_spectrum $ Γ.obj $ op Y)  : 
    Y.stalk (Y.iso_Spec.inv.1.base pt)
  ≃+* localization.at_prime pt.as_ideal :=
ring_equiv.trans 
{ to_fun := (Scheme.stalk_iso _ _ Y.iso_Spec (Y.iso_Spec.inv.1.base pt)).hom,
  inv_fun := (Scheme.stalk_iso _ _ Y.iso_Spec (Y.iso_Spec.inv.1.base pt)).inv,
  left_inv := λ x, by rw [←comp_apply, iso.hom_inv_id, id_apply],
  right_inv := λ x, by simp_rw [←comp_apply, iso.inv_hom_id, id_apply],
  map_mul' := map_mul _,
  map_add' := map_add _ } $
ring_equiv.trans 
{ to_fun := stalk_specializes (Spec_obj $ Γ.obj $ op Y).presheaf 
    (by erw [←comp_apply, ←comp_val_base, iso.inv_hom_id, id_val_base, id_apply]),
  inv_fun := stalk_specializes (Spec_obj $ Γ.obj $ op Y).presheaf 
    (by erw [←comp_apply, ←comp_val_base, iso.inv_hom_id, id_val_base, id_apply]),
  left_inv := λ x,
  begin 
    simp_rw [←comp_apply],
    convert id_apply _,
    apply stalk_hom_ext,
    intros U h,
    erw [category.comp_id],
    rw [germ_stalk_specializes'_assoc, germ_stalk_specializes],
    refl,
  end,
  right_inv := λ x, 
  begin 
    simp_rw [←comp_apply],
    convert id_apply _,
    apply stalk_hom_ext,
    intros U h,
    erw [category.comp_id],
    rw [germ_stalk_specializes'_assoc, germ_stalk_specializes],
    refl,
  end,
  map_mul' := map_mul _,
  map_add' := map_add _ }
{ to_fun := (structure_sheaf.stalk_iso _ _).hom,
  inv_fun := (structure_sheaf.stalk_iso _ _).inv,
  left_inv := λ x, by erw [←comp_apply, iso.hom_inv_id, id_apply],
  right_inv := λ x, by erw [←comp_apply, iso.inv_hom_id, id_apply],
  map_mul' := map_mul _,
  map_add' := map_add _ }

@[simps]
def stalk_iso_of_affine' (y : Y.carrier) : 
    Y.stalk y
  ≃+* localization.at_prime (Y.iso_Spec.hom.1.base y).as_ideal :=
ring_equiv.trans 
{ to_fun := (Y.stalk_iso _ Y.iso_Spec y).hom,
  inv_fun := (Y.stalk_iso _ Y.iso_Spec y).inv,
  left_inv := λ x, by rw [←comp_apply, iso.hom_inv_id, id_apply],
  right_inv := λ x, by rw [←comp_apply, iso.inv_hom_id, id_apply],
  map_mul' := map_mul _,
  map_add' := map_add _ } 
{ to_fun := (structure_sheaf.stalk_iso _ _).hom,
  inv_fun := (structure_sheaf.stalk_iso _ _).inv,
  left_inv := λ x, by rw [iso.hom_inv_id_apply],
  right_inv := λ x, by rw [iso.inv_hom_id_apply],
  map_mul' := map_mul _,
  map_add' := map_add _ }

instance gloabl_sections_algebra (y : Y.carrier) :
  algebra (Γ.obj $ op Y) $ Y.presheaf.stalk y :=
ring_hom.to_algebra $ (Y.stalk_iso_of_affine' y).symm.to_ring_hom.comp $
  @@algebra_map _ _ _ _ (by { dsimp, exactI localization.algebra })

instance stalk_is_localization (y : Y.carrier) : 
  @@is_localization.at_prime _ (Y.presheaf.stalk y)
    _ (algebraic_geometry.Scheme.gloabl_sections_algebra Y y) 
    (Y.iso_Spec.hom.1.base y).as_ideal _ :=
{ map_units := λ z, 
  begin 
    rw [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply],
    refine is_unit.map _ _,
    erw [←localization.mk_algebra_map, algebra.algebra_map_self], 
    rw [ring_hom.id_apply, localization.at_prime.mk_is_unit_iff],
    exact z.2,
  end,
  surj := λ z,
  begin
    simp_rw [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply],
    set z' : localization.at_prime (Y.iso_Spec.hom.val.base y).as_ideal := 
      (stalk_iso_of_affine' Y y) z with z'_eq,
    have eq0 : z = (stalk_iso_of_affine' Y y).symm.to_ring_hom z',
    { erw ring_equiv.symm_apply_apply },
    simp_rw [eq0, ←map_mul],
    obtain ⟨⟨a, b⟩, eq1⟩ := localization.is_localization.surj z',
    refine ⟨⟨a, b⟩, _⟩,
    dsimp at eq1 ⊢,
    congr' 1,
  end,
  eq_iff_exists := λ z1 z2,
  begin 
    rw [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply, 
      ring_hom.comp_apply, function.injective.eq_iff,
      localization.is_localization.eq_iff_exists],

    exact (Y.stalk_iso_of_affine' y).symm.bijective.injective,
  end }

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
