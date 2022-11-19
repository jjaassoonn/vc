import algebraic_geometry.AffineScheme
/-

# 01I1

-/

noncomputable theory

universes u

namespace algebraic_geometry

variables (X Y : Scheme.{u}) [is_affine Y]

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

