/-
# EGAI 2.4.1
-/

import algebraic_geometry.AffineScheme
-- imports from mathlib

import about_local_rings
-- imports from this repo

noncomputable theory

open algebraic_geometry
open category_theory category_theory.limits
open topological_space
open opposite

namespace algebraic_geometry

universe u

namespace Scheme

section local_scheme

variables {Y : Scheme.{u}} (y : Y.carrier)

def _root_.algebraic_geometry.is_affine_open.iso_Spec 
  {V : opens Y.carrier} (hV : is_affine_open V) :
  Y.restrict V.open_embedding ≅ _ :=
@Scheme.iso_Spec _ hV

def _root_.algebraic_geometry.is_affine_open.stalk_iso
  {V : opens Y.carrier} (hV : is_affine_open V)
  (y : Y.carrier) (mem_ : y ∈ V) :
  (Y.restrict V.open_embedding).stalk ⟨y, mem_⟩ ≅ 
  CommRing.of 
    (localization.at_prime ((hV.iso_Spec.hom.1.base ⟨y, mem_⟩).as_ideal : 
      ideal $ Γ.obj $ op $ Y.restrict V.open_embedding)) :=
let i1 : (Y.restrict V.open_embedding).to_PresheafedSpace ≅
  Spec.to_PresheafedSpace.obj (op $ Γ.obj $ op $ Y.restrict V.open_embedding) :=
  { hom := hV.iso_Spec.hom.1,
    inv := hV.iso_Spec.inv.1,
    hom_inv_id' := by erw [←Scheme.comp_val, iso.hom_inv_id]; refl,
    inv_hom_id' := by erw [←Scheme.comp_val, iso.inv_hom_id]; refl } in
PresheafedSpace.stalk_iso _ _ i1 ⟨y, mem_⟩ ≪≫ 
  structure_sheaf.stalk_iso _ _

instance restrict_stalk_is_local 
  (V : opens Y.carrier) (hV : is_affine_open V) (mem_ : y ∈ V) :
  local_ring ((Y.restrict V.open_embedding).stalk ⟨y, mem_⟩) :=
@local_ring.of_equiv _ 
  (localization.at_prime ((hV.iso_Spec.hom.1.base ⟨y, mem_⟩).as_ideal : 
    ideal $ Γ.obj $ op $ Y.restrict V.open_embedding)) _ _ _ $
  let i := hV.stalk_iso y mem_ in
  { to_fun := i.hom,
    inv_fun := i.inv,
    left_inv := λ x, by rw [iso.hom_inv_id_apply],
    right_inv := λ x, by rw [iso.inv_hom_id_apply],
    map_mul' := map_mul _,
    map_add' := map_add _ }

instance stalk_is_local : local_ring (Y.stalk y) :=
begin 
  obtain ⟨⟨V, mem_y⟩, A, ⟨i⟩⟩ := Y.2 y,
  have hV : is_affine_open V,
  { refine @@is_affine_of_iso _ _ (algebraic_geometry.Spec_is_affine (op A)),
    exact i.hom, refine ⟨⟨i.inv, i.hom_inv_id, i.inv_hom_id⟩⟩, },
  haveI : local_ring ((Y.restrict V.open_embedding).stalk ⟨y, mem_y⟩) :=
    Scheme.restrict_stalk_is_local _ _ hV _,
  let i := Y.1.to_PresheafedSpace.restrict_stalk_iso V.open_embedding ⟨y, mem_y⟩,
  refine local_ring.of_equiv _ 
    ((Y.restrict V.open_embedding).stalk ⟨y, mem_y⟩) 
    ⟨i.inv, i.hom, i.inv_hom_id_apply, i.hom_inv_id_apply, map_mul _, map_add _⟩,
end

section

variable {y}

def sections_to_stalk_restrict_aux
  {V : opens Y.carrier} (hV : is_affine_open V) (mem_ : y ∈ V) : 
  Γ.obj (op $ Y.restrict V.open_embedding) ⟶ 
  (Y.restrict V.open_embedding).stalk ⟨y, mem_⟩ :=
Top.presheaf.germ (Y.restrict V.open_embedding).presheaf 
  ⟨⟨y, mem_⟩, by tauto⟩

section

-- lemma sections_to_stalk_restrict_aux.eq
--   {V : opens Y.carrier} (hV : is_affine_open V) (mem_ : y ∈ V) :
--   sections_to_stalk_restrict_aux hV mem_ = 
--   begin 
--     have := algebra_map _ _,
--     refine this,
--     dsimp,
--     exact localization.algebra,
--   end ≫ (hV.stalk_iso y mem_).inv :=
-- begin 
--   symmetry,
--   rw iso.comp_inv_eq,
--   dsimp only [sections_to_stalk_restrict_aux, is_affine_open.stalk_iso],
--   rw iso.trans_hom,
--   dsimp only [unop_op],
--   rw PresheafedSpace.stalk_iso_hom,
--   dsimp only,
--   rw [category.assoc],
 
-- end

-- lemma sections_to_stalk_restrict_aux.lemma1
--   {V : opens Y.carrier} (hV : is_affine_open V) (mem_ : y ∈ V) 
--   (z : Γ.obj (op $ Y.restrict V.open_embedding)) :
--   (sections_to_stalk_restrict_aux hV mem_ z) = 
--   (hV.stalk_iso y mem_).inv (localization.mk z 1) :=
-- begin
--   rw [is_affine_open.stalk_iso], 
--   dsimp only, 
--   rw [iso.trans_inv],
--   dsimp only [unop_op],
--   rw structure_sheaf.stalk_iso_inv,
--   rw comp_apply,
--   rw localization.mk_eq_mk',
--   rw structure_sheaf.localization_to_stalk_mk',
--   rw PresheafedSpace.stalk_iso_inv,
--   erw ←structure_sheaf.to_open_eq_const,
--   rw structure_sheaf.germ_to_open,
--   dsimp,
--   rw ←structure_sheaf.germ_to_top,
--   have := PresheafedSpace.stalk_map_germ_apply,
-- end

-- lemma sections_to_stalk_restrict_aux.is_unit_of_mem_prime_compl
--   {V : opens Y.carrier} (hV : is_affine_open V) (mem_ : y ∈ V) 
--   {z : Γ.obj (op $ Y.restrict V.open_embedding)} 
--   (hz : z ∈ (hV.iso_Spec.hom.1.base ⟨y, mem_⟩).as_ideal.prime_compl) : 
--   is_unit (sections_to_stalk_restrict_aux hV mem_ z) :=
-- begin
--   have := structure_sheaf.is_unit_to_stalk _ _ ⟨z, hz⟩,
--   dsimp [subtype.coe_mk] at this,
-- end
-- is_unit_of_mul_eq_one _ ((hV.stalk_iso y mem_).inv (localization.mk 1 ⟨z, hz⟩)) 
-- begin 
--   dsimp [sections_to_stalk_restrict_aux, is_affine_open.stalk_iso],
--   rw [comp_apply, localization.mk_eq_mk', structure_sheaf.localization_to_stalk_mk'],
--   -- erw PresheafedSpace.stalk_iso_hom,
-- end

-- lemma sections_to_stalk_restrict_aux.is_unit_iff
--   {V : opens Y.carrier} (hV : is_affine_open V) (mem_ : y ∈ V) (z) : 
--   is_unit (sections_to_stalk_restrict_aux hV mem_ z) ↔
--   z ∈ (hV.iso_Spec.hom.1.base ⟨y, mem_⟩).as_ideal.prime_compl :=
-- sorry

end

def sections_to_stalk_restrict
  {V : opens Y.carrier} (hV : is_affine_open V) (mem_ : y ∈ V) : 
  Γ.obj (op $ Y.restrict V.open_embedding) ⟶ Y.stalk y :=
sections_to_stalk_restrict_aux hV mem_ ≫ 
(Y.1.to_PresheafedSpace.restrict_stalk_iso _ _).hom

def Spec_stalk_to_restrict
  {V : opens Y.carrier} (hV : is_affine_open V) (mem_ : y ∈ V) :
  (Spec_obj $ Y.stalk y) ⟶ Y.restrict V.open_embedding :=
Spec_map (sections_to_stalk_restrict hV mem_) ≫ hV.iso_Spec.inv

section

variable (y)
def Spec_stalk_to_self :
  (Spec_obj $ Y.stalk y) ⟶ Y :=
Spec_stalk_to_restrict 
begin 
  have := (Y.2 y).some_spec.some_spec.some,
  refine @@is_affine_of_iso _ _ (algebraic_geometry.Spec_is_affine
    $ op $ (Y.2 y).some_spec.some),
  work_on_goal 2 { exact ((Y.2 y).some_spec.some_spec.some.hom) },
  refine ⟨⟨(Y.2 y).some_spec.some_spec.some.inv, iso.hom_inv_id _, 
    iso.inv_hom_id _⟩⟩,
end 
begin 
  refine (Y.2 y).some.2,
end ≫ Scheme.of_restrict _ _

end

namespace Spec_stalk_to_self_independence_proof

variables {V W : opens Y.carrier} (hV : is_affine_open V) (hW : is_affine_open W)

def restrict_of_subset_rel (subset_rel : V ≤ W) :
  Y.restrict V.open_embedding ⟶ Y.restrict W.open_embedding :=
is_open_immersion.lift 
  (Y.of_restrict W.open_embedding) 
  (Y.of_restrict V.open_embedding) 
  begin 
    rintros _ ⟨⟨y, hy⟩, rfl⟩,
    refine ⟨⟨y, subset_rel hy⟩, rfl⟩,
  end

@[simps] def restrict_of_subset_rel'_PresheafedSpace (subset_rel : V ≤ W) :
  (Y.restrict V.open_embedding).to_PresheafedSpace ⟶ 
  (Y.restrict W.open_embedding).to_PresheafedSpace :=
{ base := ⟨λ y, ⟨y.1, subset_rel y.2⟩, by continuity⟩,
  c := 
  { app := λ U, Y.presheaf.map (hom_of_le 
    begin 
      rintros _ ⟨y, hy, rfl⟩,
      erw set.mem_preimage at hy,
      refine ⟨⟨_, subset_rel y.2⟩, hy, rfl⟩,
    end : V.open_embedding.is_open_map.functor.obj _ ⟶ W.open_embedding.is_open_map.functor.obj _).op,
    naturality' := λ U V inc, 
    begin 
      erw [←Y.presheaf.map_comp, ←Y.presheaf.map_comp],
      congr,
    end } }

lemma restrict_of_subset_rel'_PresheafedSpace_comp (subset_rel : V ≤ W) :
  restrict_of_subset_rel'_PresheafedSpace subset_rel ≫ 
    Y.to_PresheafedSpace.of_restrict W.open_embedding = 
  Y.to_PresheafedSpace.of_restrict V.open_embedding :=
begin 
  ext z,
  { dsimp, erw [←Y.presheaf.map_comp, ←Y.presheaf.map_comp], congr, },
  { ext pt : 1,
    dsimp, refl, },
end

lemma restrict_of_subset_rel'_PresheafedSpace_eq (subset_rel : V ≤ W) :
  restrict_of_subset_rel'_PresheafedSpace subset_rel = 
  (restrict_of_subset_rel subset_rel).1 :=
begin 
  dsimp [restrict_of_subset_rel, is_open_immersion.lift],
  rw PresheafedSpace.is_open_immersion.lift_uniq _ _ _ _
    (restrict_of_subset_rel'_PresheafedSpace_comp subset_rel),
  symmetry,
  refine PresheafedSpace.is_open_immersion.lift_uniq _ _ _ _ _,
  { rintros _ ⟨⟨y, hy⟩, rfl⟩,
    refine ⟨⟨y, subset_rel hy⟩, rfl⟩, },
  have := LocallyRingedSpace.is_open_immersion.lift_fac _ _ _,
  rw LocallyRingedSpace.hom.ext_iff at this,
  convert this,
end

instance (subset_rel : V ≤ W) (y) : is_local_ring_hom $ 
  PresheafedSpace.stalk_map (restrict_of_subset_rel'_PresheafedSpace subset_rel) y :=
begin 
  rw restrict_of_subset_rel'_PresheafedSpace_eq,
  exact (restrict_of_subset_rel subset_rel).2 y,
end

def restrict_of_subset_rel' (subset_rel : V ≤ W) :
  Y.restrict V.open_embedding ⟶ Y.restrict W.open_embedding :=
{ val := restrict_of_subset_rel'_PresheafedSpace subset_rel,
  prop := infer_instance }

lemma restrict_of_subset_rel'_comp (subset_rel : V ≤ W) :
  restrict_of_subset_rel' subset_rel ≫ Y.of_restrict W.open_embedding = 
  Y.of_restrict V.open_embedding :=
begin 
  ext z,
  { dsimp, erw [←Y.presheaf.map_comp, ←Y.presheaf.map_comp], congr, },
  { ext pt : 1,
    dsimp, refl, },
end

lemma restrict_of_subset_rel_comp (subset_rel : V ≤ W) :
  restrict_of_subset_rel subset_rel ≫ Y.of_restrict W.open_embedding = 
  Y.of_restrict V.open_embedding :=
is_open_immersion.lift_fac _ _ _

lemma restrict_of_subset_rel_comp' (subset_rel : V ≤ W) :
  Γ.map (Y.of_restrict W.open_embedding).op ≫ 
    Γ.map (restrict_of_subset_rel' subset_rel).op = 
  Γ.map (Y.of_restrict V.open_embedding).op := 
by rw [←Γ.map_comp, ←op_comp, restrict_of_subset_rel'_comp]

def ring_hom_of_subset 
  (subset_rel : V ≤ W) :
  Γ.obj (op $ Y.restrict W.open_embedding) ⟶ Γ.obj (op $ Y.restrict V.open_embedding) :=
Γ.map (restrict_of_subset_rel' subset_rel).op

lemma commutes (subset_rel : V ≤ W) (mem_ : y ∈ V) :
  ring_hom_of_subset subset_rel ≫ sections_to_stalk_restrict hV mem_ = 
  sections_to_stalk_restrict hW (subset_rel mem_) := 
begin 
  dsimp only [ring_hom_of_subset, sections_to_stalk_restrict,
    sections_to_stalk_restrict_aux, restrict_of_subset_rel', Γ],
  dsimp,
  erw PresheafedSpace.restrict_stalk_iso_hom_eq_germ,
  erw PresheafedSpace.restrict_stalk_iso_hom_eq_germ,
  convert Top.presheaf.germ_res _ _ _,
  rw subtype.coe_mk, refl,
end

example : true := ⟨⟩

lemma commutes' (subset_rel : V ≤ W) (mem_ : y ∈ V) :
  Spec_stalk_to_restrict hW (subset_rel mem_) = 
  Spec_stalk_to_restrict hV mem_ ≫ 
  restrict_of_subset_rel' subset_rel :=
begin 
  dsimp only [Spec_stalk_to_restrict],
  rw ←commutes hV hW subset_rel mem_,
  rw Spec_map_comp,
  rw [category.assoc, category.assoc],
  congr' 1,
  dsimp only [ring_hom_of_subset],
  have := whisker_eq hV.iso_Spec.inv 
    (Γ_Spec.adjunction.unit_naturality (restrict_of_subset_rel' subset_rel)),
  dsimp at this,
  erw is_iso.inv_hom_id_assoc at this,
  erw this,
  erw [category.assoc, category.assoc, is_iso.hom_inv_id, category.comp_id],
end

lemma independent_aux (subset_rel : V ≤ W) (mem_V : y ∈ V) :
  Spec_stalk_to_restrict hW (subset_rel mem_V) ≫ Y.of_restrict W.open_embedding = 
  Spec_stalk_to_restrict hV mem_V ≫ Y.of_restrict V.open_embedding :=
by rw [commutes' hV, category.assoc, restrict_of_subset_rel'_comp]

lemma is_affine_open.of_restrict 
  (U : opens (Y.restrict V.open_embedding).carrier)
  (hU : is_affine_open U) :
  is_affine_open (V.open_embedding.is_open_map.functor.obj U) :=
begin 
  refine is_affine_of_iso _,
  rotate 3, { exact hU },
  generalize_proofs h1 h2 h3 h4,
  let i : Y.restrict h3 ≅ (Y.restrict h2).restrict h4,
  { refine is_open_immersion.iso_of_range_eq (Scheme.of_restrict _ _) 
      (Scheme.of_restrict _ _ ≫ Scheme.of_restrict _ _) _,
    ext : 1,
    rw [set.mem_range, set.mem_range],
    split,
    { rintros ⟨⟨_, ⟨⟨y, hy1⟩, hy2, rfl⟩⟩, rfl⟩,
      refine ⟨⟨⟨y, hy1⟩, hy2⟩, rfl⟩, },
    { rintros ⟨⟨⟨y, hy1⟩, hy2⟩, rfl⟩,
      refine ⟨⟨y, ⟨⟨y, hy1⟩, hy2, rfl⟩⟩, rfl⟩, }, },
  exact i.hom,
  exact is_iso.of_iso _,
end

lemma independent (mem_V : y ∈ V) (mem_W : y ∈ W) :
  Spec_stalk_to_restrict hW mem_W ≫ Y.of_restrict W.open_embedding = 
  Spec_stalk_to_restrict hV mem_V ≫ Y.of_restrict V.open_embedding :=
begin 
  suffices : ∃ (U : opens Y.carrier), is_affine_open U ∧ U ≤ V ⊓ W ∧ y ∈ U,
  { obtain ⟨U, hU, U_le, mem_U⟩ := this,
    have U_le1 : U ≤ V := U_le.trans inf_le_left,
    have U_le2 : U ≤ W := U_le.trans inf_le_right,
    erw independent_aux hU hV U_le1 mem_U,
    erw independent_aux hU hW U_le2 mem_U, },
  obtain ⟨⟨U, hU⟩, R, ⟨i⟩⟩ := (Y.restrict (V ⊓ W).open_embedding).2 ⟨y, ⟨mem_V, mem_W⟩⟩,
  refine ⟨(V ⊓ W).open_embedding.is_open_map.functor.obj U, _, _, _⟩,
  { apply is_affine_open.of_restrict,
    refine is_affine_of_iso _,
    rotate 3, { exact algebraic_geometry.Spec_is_affine (op R), },
    { exact i.hom },
    { refine ⟨⟨i.inv, i.hom_inv_id, i.inv_hom_id⟩⟩, }, },
  { rintros _ ⟨y, hy, rfl⟩, exact y.2, },
  { refine ⟨⟨y, ⟨mem_V, mem_W⟩⟩, hU, rfl⟩, },
end

end Spec_stalk_to_self_independence_proof

lemma Spec_stalk_to_self_on_affine_open {V : opens Y.carrier}
  (hV : is_affine_open V) (mem_ : y ∈ V) :
  Spec_stalk_to_self y = 
  Spec_stalk_to_restrict hV mem_ ≫ Y.of_restrict _ :=
Spec_stalk_to_self_independence_proof.independent _ _ _ _

instance is_affine_open.algebra {V : opens Y.carrier}
  (hV : is_affine_open V) (mem_ : y ∈ V) :
  algebra (Γ.obj $ op $ Y.restrict V.open_embedding) (Y.stalk y) :=
ring_hom.to_algebra $ sections_to_stalk_restrict hV mem_

instance is_affine_open.is_localization {V : opens Y.carrier}
  (hV : is_affine_open V) (mem_ : y ∈ V) :
  @@is_localization.at_prime _ (Y.stalk y) _
    (algebraic_geometry.Scheme.is_affine_open.algebra hV mem_)
    (hV.iso_Spec.hom.1.base ⟨y, mem_⟩).as_ideal _ := 
begin
  have := @@is_localization.is_localization_of_alg_equiv _ _ _ _ _ _
    localization.is_localization _,
  refine this,
  refine { to_fun := _, inv_fun := _, left_inv := _, right_inv := _, 
    map_mul' := _, map_add' := _, commutes' := _ },
  { -- to_fun
    refine λ x, (Y.1.restrict_stalk_iso V.open_embedding ⟨y, mem_⟩).hom $
      (hV.stalk_iso _ _).inv x,
   },
  { -- inv_fun
    refine λ x, (hV.stalk_iso _ mem_).hom $ 
      (Y.1.restrict_stalk_iso V.open_embedding ⟨y, mem_⟩).inv x,
   },
  { -- left inverse
    sorry },
  { -- right_inverse 
    sorry },
  { -- map_mul,
    intros, simp only [map_mul], },
  { -- map_add,
    intros, simp only [map_add] },
  { -- commutes,
    intros r,
    rw [←comp_apply, is_affine_open.stalk_iso, iso.trans_inv, PresheafedSpace.stalk_iso_inv],
    rw [ring_hom.algebra_map_to_algebra, sections_to_stalk_restrict, sections_to_stalk_restrict_aux],
    erw PresheafedSpace.restrict_stalk_iso_hom_eq_germ,
    dsimp only [unop_op],
    simp only [category.assoc],
    rw [comp_apply, structure_sheaf.stalk_iso_inv, 
      ←localization.mk_one_eq_algebra_map, localization.mk_eq_mk',
      structure_sheaf.localization_to_stalk_mk'],
    dsimp only [submonoid.coe_one],
    erw ←structure_sheaf.to_open_eq_const,
    rw structure_sheaf.germ_to_open,
    rw [←comp_apply],
    dsimp only [structure_sheaf.to_stalk],
    rw [category.assoc], -- ←category.assoc (Top.presheaf.germ _ _)],
    congr' 1, symmetry,
    rw [←category.assoc, ←category.assoc],
    erw ←iso.comp_inv_eq,
    rw PresheafedSpace.restrict_stalk_iso_inv_eq_germ,
    rw [category.assoc],
    dsimp,
    have := PresheafedSpace.stalk_map_germ hV.iso_Spec.hom.1 ⊤ ⟨⟨y, mem_⟩, ⟨⟩⟩,
    erw this,
    rw [←category.assoc],
    rw structure_sheaf.to_global_factors,
    
    -- rw PresheafedSpace.restrict_sta
    -- rw PresheafedSpace.stalk_map.stalk_map_germ,
     }
end

end

end local_scheme

end Scheme

end algebraic_geometry