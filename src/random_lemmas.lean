import algebra.category.Ring

open category_theory

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

end CommRing