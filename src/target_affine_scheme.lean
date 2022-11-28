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
    rw [ring_hom.algebra_map_to_algebra],
    let z' := (stalk_specializes _ _ ≫ PresheafedSpace.stalk_map Y.iso_Spec.inv.1
      (Y.iso_Spec.hom.1 y)) z,
    work_on_goal 2
    { erw [←Scheme.comp_val_base_apply, iso.hom_inv_id, Scheme.id_val_base, 
        id_apply], },
    sorry
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

