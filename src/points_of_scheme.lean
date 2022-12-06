import random_lemmas
import target_affine_scheme

noncomputable theory

universe u

open category_theory category_theory.limits
open topological_space
open Top.presheaf Top.sheaf
open opposite

namespace algebraic_geometry

namespace Scheme

variables (X : Scheme.{u}) (R : CommRing.{u}) [local_ring R]

structure point_affine_open_stalk_ring_hom_triple :=
(pt : X.carrier)
(aopen : opens X.carrier)
(mem_aopen : pt ∈ aopen)
(aopen_is_affine : is_affine_open aopen)
(ring_hom_ : X.stalk pt ⟶ R)
[ring_hom_local : is_local_ring_hom ring_hom_]

namespace point_affine_open_stalk_ring_hom_triple

variables (P Q : point_affine_open_stalk_ring_hom_triple X R)

local notation X `|_` P := (X.restrict (P.aopen.open_embedding) : Scheme)

instance is_affine_restrict : is_affine $ X |_ P :=
P.aopen_is_affine

variables {X R}

structure refine : Prop :=
(subset : P.aopen ≤ Q.aopen)
(pt_eq : P.pt = Q.pt)
(ring_hom_eq : stalk_specializes X.presheaf (by rw pt_eq) ≫ P.ring_hom_ = Q.ring_hom_)

def restrict_stalk_iso : (X |_ P).stalk ⟨P.pt, P.mem_aopen⟩  ≅ X.stalk P.pt:=
PresheafedSpace.restrict_stalk_iso X.to_PresheafedSpace 
  (P.aopen.open_embedding) ⟨P.pt, _⟩

def restrict_Γ_iso : (Γ.obj $ op $ X |_ P) ≅ X.presheaf.obj (op P.aopen) :=
{ hom := X.presheaf.map $ (hom_of_le 
    begin 
      rintros x (hx : x ∈ P.aopen),
      refine ⟨⟨x, hx⟩, ⟨⟩, rfl⟩,
    end : P.aopen ⟶ ((_ : is_open_map _).functor.obj ⊤)).op,
  inv := X.presheaf.map $ (hom_of_le
    begin
      rintros _ ⟨x, -, rfl⟩,
      exact x.2,
    end : (_ : is_open_map _).functor.obj ⊤ ⟶ P.aopen).op,
  hom_inv_id' := by erw [←X.presheaf.map_comp, X.presheaf.map_id]; refl,
  inv_hom_id' := by erw [←X.presheaf.map_comp, X.presheaf.map_id]; refl }

def to_Spec_local_ring_to_Scheme_restrict : Spec_obj R ⟶ X.restrict P.aopen.open_embedding :=
(hom.target_AffineScheme (Spec_obj R) _).symm $ 
    (P.restrict_Γ_iso.hom ≫ germ _ ⟨P.pt, P.mem_aopen⟩ ≫ P.ring_hom_ : Γ.obj (op $ X |_ P) ⟶ R) 
  ≫ (structure_sheaf.global_sections_iso R).hom

def to_Spec_local_ring_to_Scheme : Spec_obj R ⟶ X :=
P.to_Spec_local_ring_to_Scheme_restrict ≫ X.of_restrict _

section refine

variables (P Q) 

@[reducible] def restrict_of_refine (h : P.refine Q) : (X |_ P) ⟶ (X |_ Q) :=
is_open_immersion.lift 
  (X.of_restrict Q.aopen.open_embedding) 
  (X.of_restrict P.aopen.open_embedding)
begin
  rintros _ ⟨⟨x, hx⟩, rfl⟩,
  refine ⟨⟨x, h.subset hx⟩, rfl⟩,
end

@[reducible] def restrict_of_refine' (h : P.refine Q) : (X |_ P) ⟶ (X |_ Q) :=
(hom.target_AffineScheme (X |_ P) (X |_ Q)).symm $ 
X.presheaf.map $ (hom_of_le
  begin
    rintros _ ⟨⟨x, hx⟩, -, rfl⟩,
    refine ⟨⟨x, h.subset hx⟩, ⟨⟩, rfl⟩,
  end : (_ : is_open_map _).functor.obj ⊤ ⟶ (_ : is_open_map _).functor.obj ⊤).op

example (h : P.refine Q) : 
  P.restrict_of_refine' _ h =
  P.restrict_of_refine _ h :=
begin 
  dsimp only [restrict_of_refine, restrict_of_refine'],
  refine is_open_immersion.lift_uniq _ _ _ _ _,
  sorry
end


lemma restrict_of_refine_comp_of_restrict (h : P.refine Q) : 
  X.of_restrict (P.aopen.open_embedding) =
  P.restrict_of_refine _ h ≫ X.of_restrict _ :=
by rw is_open_immersion.lift_fac

/--
Spec R ⟶ X | P
    \       ↓
      --> X | Q
-/
lemma to_Spec_local_ring_to_Scheme_restrict_eq_of_refine (h : P.refine Q) :
  Q.to_Spec_local_ring_to_Scheme_restrict =
  P.to_Spec_local_ring_to_Scheme_restrict ≫ restrict_of_refine _ _ h :=
begin
  dsimp only [to_Spec_local_ring_to_Scheme_restrict],
  -- haveI : is_open_immersion (P.restrict_of_refine Q h) := sorry,
  -- have := is_open_immersion.lift_fac
  --   (restrict_of_refine _ _ h) (Q.to_Spec_local_ring_to_Scheme_restrict),
end

def to_Spec_local_ring_to_Scheme.resp_refine (h : P.refine Q) :
  P.to_Spec_local_ring_to_Scheme = Q.to_Spec_local_ring_to_Scheme :=
begin 
  dsimp [to_Spec_local_ring_to_Scheme],
  rw [restrict_of_refine_comp_of_restrict _ _ h, ←category.assoc],
  congr' 1,
end

end refine

end point_affine_open_stalk_ring_hom_triple

structure point_stalk_ring_hom_pair :=
(pt : X.carrier)
(stalk_ : CommRing.{u})
(stalk_iso : stalk_ ≅ X.presheaf.stalk pt)
(ring_hom_ : stalk_ ⟶ R)
[is_local_ring_hom_ : is_local_ring_hom ring_hom_]

attribute [instance] point_stalk_ring_hom_pair.is_local_ring_hom_

namespace point_stalk_ring_hom_pair

variables {X R} (P Q S : point_stalk_ring_hom_pair X R)

@[reducible]
def ring_hom_' : X.presheaf.stalk P.pt ⟶ R := 
  P.stalk_iso.inv ≫ P.ring_hom_

variables {P Q S}

@[simps] 
def stalk_equiv_of_pt_eq (pt_eq : P.pt = Q.pt) :
  P.stalk_ ≅ Q.stalk_ :=
{ hom := P.stalk_iso.hom 
    ≫ stalk_specializes X.presheaf (by rw pt_eq : Q.pt ⤳ P.pt) 
    ≫ Q.stalk_iso.inv,
  inv := Q.stalk_iso.hom 
    ≫ stalk_specializes X.presheaf (by rw pt_eq : P.pt ⤳ Q.pt) 
    ≫ P.stalk_iso.inv,
  hom_inv_id' := 
  begin 
    rw [category.assoc, category.assoc, iso.inv_hom_id_assoc,
      ←category.assoc, ←category.assoc, iso.comp_inv_eq, category.id_comp,
      category.assoc],
    convert category.comp_id _,
    refine stalk_hom_ext _ _,
    intros U h,
    rw [germ_stalk_specializes'_assoc], 
    erw [category.comp_id, germ_stalk_specializes'],
    refl,
  end,
  inv_hom_id' := 
  begin 
    rw [category.assoc, category.assoc, iso.inv_hom_id_assoc,
      ←category.assoc, ←category.assoc, iso.comp_inv_eq, category.id_comp,
      category.assoc],
    convert category.comp_id _,
    refine stalk_hom_ext _ _,
    intros U h,
    rw [germ_stalk_specializes'_assoc], 
    erw [category.comp_id, germ_stalk_specializes'],
    refl,
  end }

variables (P Q S)
structure equiv : Prop :=
(pt_eq : P.pt = Q.pt)
(ring_hom_eq : P.ring_hom_ = (stalk_equiv_of_pt_eq pt_eq).hom ≫ Q.ring_hom_)

structure equiv' : Prop :=
(pt_eq : P.pt = Q.pt)
(ring_hom_eq : (stalk_equiv_of_pt_eq pt_eq).inv ≫ P.ring_hom_ = Q.ring_hom_)

@[refl] lemma equiv_self : P.equiv P :=
{ pt_eq := rfl,
  ring_hom_eq := 
  begin 
    symmetry,
    convert category.id_comp _,
    rw [stalk_equiv_of_pt_eq_hom, ←category.assoc, iso.comp_inv_eq, 
      category.id_comp],
    convert category.comp_id _,
    apply stalk_hom_ext,
    intros U h,
    rw [germ_stalk_specializes'],
    erw category.comp_id _,
    refl,
  end }

variables {P Q S}

@[symm] lemma equiv_symm (h : P.equiv Q) : Q.equiv P :=
{ pt_eq := h.pt_eq.symm,
  ring_hom_eq := 
  begin 
    rw [h.ring_hom_eq, ←category.assoc],
    symmetry,
    convert category.id_comp _,
    rw [stalk_equiv_of_pt_eq_hom, stalk_equiv_of_pt_eq_hom, category.assoc,
      category.assoc, iso.inv_hom_id_assoc, ←category.assoc, ←category.assoc,
      iso.comp_inv_eq, category.id_comp, category.assoc],
    convert category.comp_id _,
    apply stalk_hom_ext,
    intros U h,
    rw [germ_stalk_specializes'_assoc, germ_stalk_specializes'],
    erw category.comp_id,
    refl,
  end }

@[trans] lemma equiv_trans (h1 : P.equiv Q) (h2 : Q.equiv S) : P.equiv S :=
{ pt_eq := h1.pt_eq.trans h2.pt_eq,
  ring_hom_eq :=
  begin 
    rw [h1.ring_hom_eq, h2.ring_hom_eq, stalk_equiv_of_pt_eq_hom,
      stalk_equiv_of_pt_eq_hom, stalk_equiv_of_pt_eq_hom, category.assoc,
      category.assoc, category.assoc, iso.inv_hom_id_assoc, ←category.assoc,
      ←category.assoc],
    congr' 1,
    rw [←category.assoc, ←category.assoc],
    congr' 1,
    rw [category.assoc],
    congr' 1,
    apply stalk_hom_ext,
    intros U h,
    rw [germ_stalk_specializes'_assoc, germ_stalk_specializes, 
      germ_stalk_specializes],
  end }

variables (P Q S)

@[simps]
def stalk_cocone : cocone ((open_nhds.inclusion P.pt).op ⋙ X.presheaf) :=
{ X := P.stalk_,
  ι := 
  { app := λ j, colimit.ι ((open_nhds.inclusion P.pt).op ⋙ X.presheaf) j ≫ 
      P.stalk_iso.inv,
    naturality' := λ U V i, 
    begin 
      dsimp,
      rw [category.comp_id, ←category.assoc],
      erw colimit.w ((open_nhds.inclusion P.pt).op ⋙ X.presheaf) i,
    end }  }

def stalk_cocone_is_colimit : is_colimit (P.stalk_cocone) :=
{ desc := λ s, P.stalk_iso.hom ≫ (colimit.is_colimit ((open_nhds.inclusion P.pt).op ⋙ X.presheaf)).desc s,
  fac' := λ s j, 
  begin 
    rw ←(colimit.is_colimit ((open_nhds.inclusion P.pt).op ⋙ X.presheaf)).fac s j,
    rw [←category.assoc],
    congr' 1,
    dsimp,
    rw [category.assoc, iso.inv_hom_id, category.comp_id],
  end,
  uniq' := λ s m j, 
  begin 
    rw ←(colimit.is_colimit ((open_nhds.inclusion P.pt).op ⋙ X.presheaf)).uniq s (_ ≫ m) j,
    rw iso.hom_inv_id_assoc,
  end }

section affine

variables [is_affine X]

def stalk_iso_localization (P : point_stalk_ring_hom_pair X R) :
  P.stalk_ ≅ CommRing.of (localization.at_prime (X.iso_Spec.hom.1 P.pt).as_ideal) :=
P.stalk_iso ≪≫ 
(PresheafedSpace.stalk_map.stalk_iso 
  ({ hom := X.iso_Spec.hom.1, 
    inv := X.iso_Spec.inv.1, 
    hom_inv_id' := by erw [←Scheme.comp_val, iso.hom_inv_id]; refl, 
    inv_hom_id' := by erw [←Scheme.comp_val, iso.inv_hom_id]; refl } : X.to_PresheafedSpace ≅ (Spec_obj $ Γ.obj $ op X).to_PresheafedSpace) P.pt).symm
≪≫ (structure_sheaf.stalk_iso _ _)

def Γ_to_germ (P : point_stalk_ring_hom_pair X R) :
  (Γ.obj $ op X) ⟶ P.stalk_ :=
(structure_sheaf.global_sections_iso (Γ.obj $ op X)).hom ≫ 
  X.iso_Spec.hom.1.c.app (op ⊤) ≫ P.stalk_cocone.ι.app (op ⊤)

end affine

end point_stalk_ring_hom_pair

section affine

variables {X R} [is_affine X]

def from_point_stalk_ring_hom_pair_of_affine (P : point_stalk_ring_hom_pair X R) :
  Spec_obj R ⟶ X :=
(hom.target_AffineScheme (Spec_obj R) X).symm $ 
  local_ring.from_point_local_ring_hom_pair 
  { pt := X.iso_Spec.hom.1.base P.pt,
    localized_ring := X.presheaf.stalk P.pt,
    algebra_localized_ring := infer_instance,
    is_localization := infer_instance,
    ring_hom_ := P.stalk_iso.inv ≫ P.ring_hom_ 
      ≫ (structure_sheaf.global_sections_iso R.α).hom,
    is_local_ring_hom_ := infer_instance }

lemma from_point_stalk_ring_hom_pair_of_affine.resp_equiv
  (P Q : point_stalk_ring_hom_pair X R) (h : P.equiv Q) :
  from_point_stalk_ring_hom_pair_of_affine P =
  from_point_stalk_ring_hom_pair_of_affine Q :=
begin
  dsimp only [from_point_stalk_ring_hom_pair_of_affine],
  congr' 1,
  refine local_ring.from_point_local_ring_hom_pair.resp_equiv _,
  fconstructor,
  { dsimp only, rw h.pt_eq, },
  { dsimp only, 
    simp_rw h.ring_hom_eq, 
    rw [point_stalk_ring_hom_pair.stalk_equiv_of_pt_eq_hom, category.assoc,
      category.assoc, iso.inv_hom_id_assoc, category.assoc],
    congr' 1,
    -- use the fact they are both "colimit", so unique up to a **unique** 
    -- isomorphism
    sorry, },
end

@[simps]
def to_point_stalk_ring_hom_pair_of_affine (α : Spec_obj R ⟶ X) :
  point_stalk_ring_hom_pair X R :=
let P := local_ring.to_point_local_ring_hom_pair 
  ((hom.target_AffineScheme (Spec_obj R) X) α) in
{ pt := X.iso_Spec.inv.1.base P.pt,
  stalk_ := CommRing.of P.localized_ring,
  stalk_iso :=
    let α := @is_localization.alg_equiv (Γ.obj $ op X) _ 
      P.pt.as_ideal.prime_compl P.localized_ring _ _ _
      (X.stalk (X.iso_Spec.inv.1.base P.pt)) _
      (X.global_sections_algebra _) (X.stalk_is_localization P.pt) in
  { hom := α.to_ring_equiv.to_ring_hom,
    inv := α.to_ring_equiv.symm.to_ring_hom,
    hom_inv_id' := 
    begin
      ext : 1,
      rw [comp_apply, id_apply, 
        ring_equiv.symm_to_ring_hom_apply_to_ring_hom_apply],
    end,
    inv_hom_id' := 
    begin 
      ext : 1,
      rw [comp_apply, id_apply,
        ring_equiv.to_ring_hom_apply_symm_to_ring_hom_apply],
    end },
  ring_hom_ := P.ring_hom_ ≫ (structure_sheaf.global_sections_iso _).inv,
  is_local_ring_hom_ := infer_instance }

end affine

end Scheme

end algebraic_geometry