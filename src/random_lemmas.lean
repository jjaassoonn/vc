import algebra.category.Ring
import algebraic_geometry.stalks
import algebraic_geometry.Scheme

open category_theory category_theory.limits
open Top.presheaf Top.sheaf topological_space

namespace CommRing

@[simps] def from_iso {A B : CommRing} (i : A ≅ B) : A ≃+* B :=
{ to_fun := i.hom,
  inv_fun := i.inv,
  left_inv := λ f, by rw [←comp_apply, i.hom_inv_id, id_apply],
  right_inv := λ f, by rw [←comp_apply, i.inv_hom_id, id_apply],
  map_mul' := map_mul i.hom,
  map_add' := map_add i.hom }

lemma from_iso_to_ring_hom {A B : CommRing} (i : A ≅ B) :
  (from_iso i).to_ring_hom = i.hom :=
ring_hom.ext $ λ (a : A), show from_iso i a = i.hom a, from rfl

@[simps] def to_iso {A B : Type*} [comm_ring A] [comm_ring B] 
  (i : A ≃+* B) : CommRing.of A ≅ CommRing.of B :=
{ hom := i.to_ring_hom,
  inv := i.symm.to_ring_hom,
  hom_inv_id' := fun_like.ext _ _ $ λ a,
    show (i.symm $ i a) = a, from i.symm_apply_apply a,
  inv_hom_id' := fun_like.ext _ _ $ λ (a : B), 
    show (i $ i.symm a) = a, from i.apply_symm_apply a, }

lemma ring_equiv_eq_iff_to_iso_eq {A B : Type*} [comm_ring A] [comm_ring B]
  (i i' : A ≃+* B) : i = i' ↔ to_iso i = to_iso i' :=
{ mp := λ h, h ▸ rfl,
  mpr := λ h, ring_equiv.ext $ λ x, show (to_iso i).hom x = (to_iso i').hom x, 
    from h ▸ rfl }

lemma CommRing_comp_eq_comp {R S T : Type*} 
  [comm_ring R] [comm_ring S] [comm_ring T] (f : R →+* S) (g : S →+* T) :
  g.comp f = (show CommRing.of R ⟶ CommRing.of S, from f) ≫ 
    (show CommRing.of S ⟶ CommRing.of T, from g) := 
rfl

end CommRing

namespace algebra

variables (R R' X X' : Type*) 
variables [comm_ring R] [comm_ring R'] 
variables [comm_ring X] [comm_ring X'] [algebra R X]

@[simps] def of_equiv' (i : R ≃+* R') [algebra R X] : algebra R' X :=
ring_hom.to_algebra $ (algebra_map _ _).comp i.symm.to_ring_hom

@[simps] def of_equiv (i : X ≃+* X') [algebra R X] : algebra R X' :=
ring_hom.to_algebra $ i.to_ring_hom.comp (algebra_map R X)

lemma algebra_map_self : 
  algebra_map R R = ring_hom.id R := by { ext : 1, refl }

end algebra

namespace Top.presheaf

universes u v

variables {C : Type u} [category.{v} C] [has_colimits C] {X : Top.{v}}

lemma stalk_specializes_eq_to_hom (F : Top.presheaf C X) {x y : X} (h : x = y) :
  stalk_specializes F (by rw h : x ⤳ y) = eq_to_hom (by rw h) :=
begin 
  subst h,
  rw [eq_to_hom_refl],
  apply stalk_hom_ext,
  intros U h,
  erw [germ_stalk_specializes, category.comp_id],
  refl,
end

end Top.presheaf

namespace algebraic_geometry

namespace PresheafedSpace

universes u v w

variables {C : Type u} [category.{v} C] [has_colimits C] (X Y : PresheafedSpace.{v v u} C)
variables (i : X ≅ Y) (x : X.carrier)

@[simps] noncomputable def stalk_iso : X.stalk x ≅ Y.stalk (i.hom.base x) :=
{ hom := stalk_specializes _ (by erw [←comp_apply i.hom.base, ←comp_base, 
    iso.hom_inv_id, id_base, id_apply]) 
    ≫ PresheafedSpace.stalk_map i.inv (i.hom.base x),
  inv := PresheafedSpace.stalk_map i.hom _,
  hom_inv_id' := 
  begin 
    rw Top.presheaf.stalk_specializes_eq_to_hom,
    work_on_goal 2 
    { erw [←comp_apply i.hom.base, ←comp_base, iso.hom_inv_id, id_base, id_apply], },
    refine stalk_hom_ext _ _,
    intros U h,
    rw [category.assoc, ←stalk_map.comp i.hom i.inv],
    rw PresheafedSpace.stalk_map.congr_hom,
    work_on_goal 2 { exact iso.hom_inv_id _, },
    rw [eq_to_hom_trans_assoc, eq_to_hom_refl, stalk_map.id],
    erw category.comp_id,
  end,
  inv_hom_id' := 
  begin 
    rw Top.presheaf.stalk_specializes_eq_to_hom,
    work_on_goal 2 
    { erw [←comp_apply i.hom.base, ←comp_base, iso.hom_inv_id, id_base, id_apply], },
    rw [←category.assoc, PresheafedSpace.stalk_map.congr_point],
    work_on_goal 2 
    { erw [←comp_apply i.hom.base, ←comp_base, iso.hom_inv_id, id_base, id_apply], },
    rw [category.assoc], 
    erw [←stalk_map.comp i.inv i.hom],
    rw stalk_map.congr_hom,
    work_on_goal 2 { exact iso.inv_hom_id _, },
    rw [eq_to_hom_trans_assoc, eq_to_hom_refl, stalk_map.id],
    erw category.id_comp _,
  end }

end PresheafedSpace

namespace LocallyRingedSpace

universe u

variables (X Y : LocallyRingedSpace.{u})
variables (i : X ≅ Y) (x : X.carrier)

@[simps] noncomputable def stalk_iso : X.stalk x ≅ Y.stalk (i.hom.1.base x) :=
let i' : X.to_PresheafedSpace ≅ Y.to_PresheafedSpace :=
{ hom := i.hom.1,
  inv := i.inv.1,
  hom_inv_id' := by erw [←comp_val, iso.hom_inv_id, id_val]; refl,
  inv_hom_id' := by erw [←comp_val, iso.inv_hom_id, id_val]; refl } in 
PresheafedSpace.stalk_iso _ _ i' x

end LocallyRingedSpace

namespace Scheme

universe u

variables (X Y : Scheme.{u}) (i : X ≅ Y) (x : X.carrier)

noncomputable def stalk_iso : X.stalk x ≅ Y.stalk (i.hom.1.base x) :=
LocallyRingedSpace.stalk_iso X.to_LocallyRingedSpace Y.to_LocallyRingedSpace 
{ hom := i.hom,
  inv := i.inv,
  hom_inv_id' := i.hom_inv_id',
  inv_hom_id' := i.inv_hom_id' } x

end Scheme

end algebraic_geometry

namespace local_ring

universe u

variables (R S : Type u) [comm_ring R] [comm_ring S] [local_ring S] (f : R ≃+* S)

def of_equiv : local_ring R :=
@@local_ring.of_is_unit_or_is_unit_of_is_unit_add _
  (⟨⟨f.symm nontrivial.exists_pair_ne.some, 
    f.symm nontrivial.exists_pair_ne.some_spec.some, 
    λ r, nontrivial.exists_pair_ne.some_spec.some_spec $ f.symm.injective r⟩⟩ : nontrivial R) $ λ a b h,
begin 
  have h' : is_unit (f (a + b)) := f.to_ring_hom.is_unit_map h,
  rw [map_add] at h',
  obtain h''|h'' := local_ring.is_unit_or_is_unit_of_is_unit_add h',
  left,
  convert f.symm.to_ring_hom.is_unit_map h'',
  erw [equiv.symm_apply_apply],
  right,
  convert f.symm.to_ring_hom.is_unit_map h'',
  erw [equiv.symm_apply_apply],
end

end local_ring

namespace category_theory.limits

universes u v u' v'

variables {J : Type u} [category.{v} J] 
variables {C : Type u'} [category.{v'} C] {F : J ⥤ C} 
variables (a1 a2 : cocone F) [is_colimit a1] [is_colimit a2]

lemma uniq_iso (x y : a1 ≅ a2)
  (h1 : ∀ (j : J), a1.ι.app j ≫ x.hom.hom = a2.ι.app j)
  (h2 : ∀ (j : J), a1.ι.app j ≫ y.hom.hom = a2.ι.app j) : x = y :=
begin 
  ext,
  rw is_colimit.uniq _ _ x.hom.hom h1,
  rw is_colimit.uniq _ _ y.hom.hom h2,
  exact _inst_3,
end

example : true :=
begin 
  have := @is_colimit,
end

end category_theory.limits
