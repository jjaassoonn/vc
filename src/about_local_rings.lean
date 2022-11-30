import ring_theory.ideal.local_ring
import ring_theory.localization.at_prime
import algebraic_geometry.prime_spectrum.basic

import random_lemmas

noncomputable theory

universe u

open_locale big_operators
open category_theory

namespace ring_hom

variables {R R' S S' : Type u} 
variables [comm_ring R] [comm_ring R'] [comm_ring S] [comm_ring S']
variables (f : R →+* S) (g : R →+* S') (e : S ≃+* S') (e' : R ≃+* R')
variables (f' : R' →+* S)

lemma equiv_to_ring_hom_comp_eq_iff :
  e.to_ring_hom.comp f = g ↔ f = e.symm.to_ring_hom.comp g :=
{ mp := λ h, by simp [←h, ←comp_assoc],
  mpr := λ h, by erw [h, ←comp_assoc]; simp }

lemma comp_equiv_to_ring_hom_eq_iff :
  f.comp e'.symm.to_ring_hom = f' ↔ f = f'.comp e'.to_ring_hom :=
{ mp := λ h, by rw [←h, comp_assoc]; simp,
  mpr := λ h, by erw [h, comp_assoc]; simp }

lemma is_local_ring_hom.map_inv [is_local_ring_hom f]
  (x : R) (h : is_unit x) : 
  f (h.unit.inv) = (is_unit.map f h).unit.inv :=
begin 
  generalize_proofs h1,
  rw [units.inv_eq_coe_inv, units.inv_eq_coe_inv],
  apply units.eq_inv_of_mul_eq_one_left,
  erw [←map_mul], convert map_one _,
  convert units.mul_inv _,
  refl,
end

end ring_hom

namespace localization.at_prime

variables {R : Type u} [comm_ring R] (p : ideal R) [ideal.is_prime p]

lemma mk_is_unit_iff (a : R) (b : p.prime_compl) : is_unit (localization.mk a b) ↔ a ∉ p :=
{ mp := λ ⟨⟨x, y, hx1, hx2⟩, hx⟩, 
  begin
    dsimp at hx,
    rw hx at hx1 hx2,
    induction y using localization.induction_on with data,
    rcases data with ⟨c, d⟩,
    dsimp at hx1 hx2,
    rw [←localization.mk_one, localization.mk_mul, localization.mk_eq_mk_iff, 
      localization.r_iff_exists] at hx1 hx2,
    obtain ⟨e, he⟩ := hx1,
    dsimp at he,
    rw [mul_one, one_mul] at he,
    intros r,
    have mem1 : a * c * e ∈ p := ideal.mul_mem_right _ _ (ideal.mul_mem_right _ _ r),
    rw he at mem1,
    exact submonoid.mul_mem _ (submonoid.mul_mem _ b.2 d.2) e.2 mem1,
  end,
  mpr := λ ha, ⟨⟨localization.mk a b, localization.mk b ⟨a, ha⟩, 
    by { rw [localization.mk_mul, mul_comm], exact localization.mk_self (b * ⟨a, ha⟩) }, 
    by { rw [localization.mk_mul, mul_comm], exact localization.mk_self (⟨a, _⟩ * b)}⟩, rfl⟩ }

@[simps] def concrete_description_of_ideal_map (m : ideal R) :
  ideal (localization.at_prime p) :=
{ carrier := {x | ∃ (a : m) (b : p.prime_compl), x = localization.mk a b},
    add_mem' := 
    begin 
      rintros _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩,
      rw [localization.add_mk],
      refine ⟨⟨b * a' + b' * a, _⟩, b*b', rfl⟩,
      refine submodule.add_mem _ 
        (ideal.mul_mem_left _ _ a'.2) 
        (ideal.mul_mem_left _ _ a.2),
    end,
    zero_mem' := ⟨0, 1, (localization.mk_zero _).symm⟩,
    smul_mem' :=
    begin 
      rintros c _ ⟨a, b, rfl⟩,
      induction c using localization.induction_on with data,
      rcases data with ⟨x, y⟩,
      dsimp,
      rw [localization.mk_mul],
      refine ⟨⟨x * a, ideal.mul_mem_left _ _ a.2⟩, y * b, rfl⟩,
    end }

lemma ideal_map_is (m : ideal R) :
  concrete_description_of_ideal_map p m = 
  m.map (algebra_map R (localization.at_prime p)) :=
have aux1 : ∀ (x : localization.at_prime p), 
    x ∈ ideal.map (algebra_map R (localization.at_prime p)) m →
    ∃ (a : m) (b: p.prime_compl), x = localization.mk a b,
begin
  rintros x h, 
  refine submodule.span_induction h _ _ _ _,
  { rintros _ ⟨y, hy, rfl⟩, refine ⟨⟨y, hy⟩, 1, rfl⟩, },
  { refine ⟨0, 1, (localization.mk_zero _).symm⟩, },
  { rintros _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩,
    refine ⟨⟨b * a' + b' * a, submodule.add_mem _ (ideal.mul_mem_left _ _ a'.2) (ideal.mul_mem_left _ _ a.2) ⟩, b * b', _⟩,
    rw [localization.add_mk],
    refl, },
  { rintros x _ ⟨a, b, rfl⟩,
    induction x using localization.induction_on with data,
    rcases data with ⟨c, d⟩,
    refine ⟨⟨c * a, ideal.mul_mem_left _ _ a.2⟩, d * b, _⟩,
    dsimp,
    rw [localization.mk_mul], }
end,
begin 
  ext : 1, split,
  { rintros ⟨a, b, rfl⟩, 
    rw show (localization.mk a b : localization.at_prime p) = 
      localization.mk a 1 * localization.mk 1 b, from _,
    refine ideal.mul_mem_right _ _ (submodule.subset_span _),
    refine ⟨a, a.2, rfl⟩,
    rw [localization.mk_mul, mul_one, one_mul], },
  { exact aux1 _, }
end

lemma maximal_ideal_is :
  local_ring.maximal_ideal (localization.at_prime p) =
  concrete_description_of_ideal_map p p :=
begin
  ext x : 1,
  induction x using localization.induction_on with data,
  rcases data with ⟨a, b⟩,
  dsimp only,
  rw [local_ring.mem_maximal_ideal, mem_nonunits_iff, mk_is_unit_iff, not_not],
  split,
  { intros ha,
    rw show localization.mk a b = localization.mk a 1 * localization.mk 1 b, 
      by rw [localization.mk_mul, mul_one, one_mul],
    refine ideal.mul_mem_right _ _ _,
    refine ⟨⟨a, ha⟩, 1, rfl⟩, },
  { rintros ⟨c, d, h⟩,
    erw [localization.mk_eq_mk_iff, localization.r_iff_exists] at h,
    obtain ⟨e, he⟩ := h,
    dsimp at he,
    have eq0 : (c * b * e : R) ∈ p := ideal.mul_mem_right _ _ (ideal.mul_mem_right _ _ c.2),
    rw ←he at eq0,
    obtain h0|h1 := ideal.is_prime.mem_or_mem infer_instance eq0,
    work_on_goal 2 { exact (e.2 h1).elim },
    obtain h0|h1 := ideal.is_prime.mem_or_mem infer_instance h0,
    exact h0,
    exact (d.2 h1).elim, },
end

lemma maximal_ideal_is' :
  local_ring.maximal_ideal (localization.at_prime p) =
  p.map (algebra_map R (localization.at_prime p)) := 
(maximal_ideal_is p).trans $ ideal_map_is _ _

end localization.at_prime

namespace ring_hom

variables (R : Type u) [comm_ring R] [local_ring R]

section target_local_ring

variables {R} {A : Type u} [comm_ring A] (φ : A →+* R)

variables (M : Type u) [comm_ring M] [algebra A M] 
variable [is_localization.at_prime M ((local_ring.maximal_ideal R).comap φ)] 

@[reducible] 
def fac' : M →+* R :=
@is_localization.lift A _ ((local_ring.maximal_ideal R).comap φ).prime_compl 
  _ _ _ _ _ _ φ 
begin 
  intros y,
  have h' := y.2,
  contrapose! h',
  rw [←mem_nonunits_iff, ←local_ring.mem_maximal_ideal, ←ideal.mem_comap] at h',
  exact λ r, r h',
end

lemma fac'_comp_algebra_map : (φ.fac' M).comp (algebra_map _ _) = φ :=
is_localization.lift_comp _

section fac'_uniq

variables (p : ideal A) [ideal.is_prime p]
variables (N : Type u) [comm_ring N] 
variables [algebra A N] [is_localization.at_prime N p]
variables (f : N →+* R) [is_local_ring_hom f]

lemma fac'_uniq_pt_eq (h : f.comp (algebra_map A N) = φ) : 
  p = (local_ring.maximal_ideal R).comap φ := 
begin 
  refine le_antisymm _ _,
  { intros x hx,
    rw [ideal.mem_comap, local_ring.mem_maximal_ideal, ←h, mem_nonunits_iff,
      ring_hom.comp_apply],
    intros r,
    have r' := is_local_ring_hom.map_nonunit _ r,
    rw [←is_localization.mk'_one N, 
      is_localization.at_prime.is_unit_mk'_iff N p] at r',
    exact r' hx, },
  { intros x hx,
    rw [ideal.mem_comap, ←h, local_ring.mem_maximal_ideal, ring_hom.comp_apply,
      mem_nonunits_iff] at hx,
    contrapose! hx,
    replace hx := (is_localization.at_prime.is_unit_mk'_iff N p x 1).mpr hx,
    rw is_localization.mk'_one at hx,
    refine is_unit.map _ hx, },
end

lemma fac'_uniq (h : f.comp (algebra_map A N) = φ) : 
  f = (φ.fac' M).comp (is_localization.map M (ring_hom.id A) 
    (by { refine le_of_eq _, simp_rw [fac'_uniq_pt_eq φ p N f h],
      erw submonoid.comap_id, } : p.prime_compl ≤
        submonoid.comap _ ((local_ring.maximal_ideal R).comap φ).prime_compl)) :=
begin 
  simp_rw [←h],
  ext x : 1,
  obtain ⟨a, b, rfl⟩ := is_localization.mk'_surjective p.prime_compl x,
  rw [ring_hom.comp_apply, is_localization.map_mk', is_localization.lift_mk',
    ring_hom.id_apply],
  simp_rw [ring_hom.id_apply],
  rw units.eq_mul_inv_iff_mul_eq,
  change _ * f _ = _,
  rw [←map_mul, ring_hom.comp_apply, ←is_localization.mk'_one N, 
    ←is_localization.mk'_one N a, ←is_localization.mk'_mul, mul_one],
  work_on_goal 3 { exactI (infer_instance : is_localization.at_prime N p) },
  congr' 1,
  dsimp,
  rw is_localization.eq,
  refine ⟨1, _⟩,
  simp only [submonoid.coe_one, mul_one],
end

end fac'_uniq

instance is_local_fac' : is_local_ring_hom $ φ.fac' M :=
{ map_nonunit := λ x hx, 
  begin 
    obtain ⟨a, b, rfl⟩ := is_localization.mk'_surjective 
      ((local_ring.maximal_ideal _).comap φ).prime_compl x,
    rw is_localization.at_prime.is_unit_mk'_iff,
    rintros rid,
    rw [set_like.mem_coe, ideal.mem_comap, local_ring.mem_maximal_ideal,
      mem_nonunits_iff] at rid,
    refine rid _, clear rid,
    rw is_localization.lift_mk' at hx,
    refine (units.is_unit_mul_units _ _).mp hx,
  end }

@[simps] def fac : 
  localization.at_prime (ideal.comap φ (local_ring.maximal_ideal _)) →+* R :=
φ.fac' _

instance is_local.fac : is_local_ring_hom φ.fac := φ.is_local_fac' _

@[simp] lemma fac_comp_algebra_map : φ.fac.comp (algebra_map A _) = φ :=
φ.fac'_comp_algebra_map _

lemma fac_uniq_pt_eq (p : ideal A) [p.is_prime]
  (f : localization.at_prime p →+* R) [is_local_ring_hom f]
  (hf : f.comp (algebra_map A (localization.at_prime p)) = φ) :
  p = (local_ring.maximal_ideal _).comap φ :=
φ.fac'_uniq_pt_eq _ (localization.at_prime p) f hf

-- 01J6, first sentence in proof
lemma fac_uniq (p : ideal A) [p.is_prime]
  (f : localization.at_prime p →+* R) 
  (hf : f.comp (algebra_map A (localization.at_prime p)) = φ)
  [is_local_ring_hom f] :
  f = φ.fac.comp (is_localization.map _ (ring_hom.id A) 
    (by { simp_rw [φ.fac_uniq_pt_eq p f hf], erw submonoid.comap_id, 
      exact le_refl _} : p.prime_compl ≤ submonoid.comap (ring_hom.id A) 
        ((local_ring.maximal_ideal R).comap φ).prime_compl)) := 
φ.fac'_uniq _ _ _ f hf

end target_local_ring

end ring_hom

namespace local_ring

variables (A R : CommRing.{u}) [local_ring R] 

@[ext] structure point_local_ring_hom_pair :=
(pt : prime_spectrum A)
(localized_ring : CommRing.{u})
[algebra_localized_ring : algebra A localized_ring]
[is_localization : is_localization.at_prime localized_ring pt.as_ideal]
(ring_hom_ : localized_ring ⟶ R)
[is_local_ring_hom_ : is_local_ring_hom ring_hom_]

attribute [instance] point_local_ring_hom_pair.algebra_localized_ring
attribute [instance] point_local_ring_hom_pair.is_localization
attribute [instance] point_local_ring_hom_pair.is_local_ring_hom_

namespace point_local_ring_hom_pair

variables (P Q S : point_local_ring_hom_pair A R)

section

variables {A R P Q}

@[simps]
def localized_ring_equiv_of_pt_eq (pt_eq : P.pt = Q.pt) :
  P.localized_ring ≅ Q.localized_ring :=
{ hom := is_localization.map _ (ring_hom.id A) $
      show P.pt.as_ideal.prime_compl ≤ 
        submonoid.comap (ring_hom.id A) Q.pt.as_ideal.prime_compl, 
      by erw [submonoid.comap_id, pt_eq]; exact le_refl _,
  inv := is_localization.map _ (ring_hom.id A) $
      show Q.pt.as_ideal.prime_compl ≤ 
        submonoid.comap (ring_hom.id A) P.pt.as_ideal.prime_compl, 
      by erw [submonoid.comap_id, pt_eq]; exact le_refl _,
  hom_inv_id' := 
  begin 
    change ring_hom.comp _ _ = ring_hom.id _,
    rw is_localization.map_comp_map,
    simp_rw [ring_hom.id_comp],
    ext : 1,
    rw is_localization.map_id,
    refl,
  end,
  inv_hom_id' := 
  begin 
    change ring_hom.comp _ _ = ring_hom.id _,
    rw is_localization.map_comp_map,
    simp_rw [ring_hom.id_comp],
    ext : 1,
    rw is_localization.map_id,
    refl,
  end }
-- { to_fun := 
-- is_localization.map _ (ring_hom.id A) $
--       show P.pt.as_ideal.prime_compl ≤ 
--         submonoid.comap (ring_hom.id A) Q.pt.as_ideal.prime_compl, 
--       by erw [submonoid.comap_id, pt_eq]; exact le_refl _,
--   inv_fun := is_localization.map _ (ring_hom.id A) $
--       show Q.pt.as_ideal.prime_compl ≤ 
--         submonoid.comap (ring_hom.id A) P.pt.as_ideal.prime_compl, 
--       by erw [submonoid.comap_id, pt_eq]; exact le_refl _,
--   left_inv := λ x, 
--   begin
--     obtain ⟨a, b, eq0⟩ := is_localization.mk'_surjective P.pt.as_ideal.prime_compl x,
--     rw [←eq0, is_localization.map_mk', is_localization.map_mk', 
--       ring_hom.id_apply, ring_hom.id_apply],
--     congr,
--     ext,
--     refl,
--   end,
--   right_inv := λ x,
--   begin
--     obtain ⟨a, b, eq0⟩ := is_localization.mk'_surjective Q.pt.as_ideal.prime_compl x,
--     rw [←eq0, is_localization.map_mk', is_localization.map_mk', 
--       ring_hom.id_apply, ring_hom.id_apply],
--     congr,
--     ext,
--     refl,
--   end,
--   map_mul' := map_mul _,
--   map_add' := map_add _ }

variable (P)

def localized_ring_equiv :
  P.localized_ring ≃+* localization.at_prime P.pt.as_ideal :=
(is_localization.alg_equiv P.pt.as_ideal.prime_compl P.localized_ring
  (localization.at_prime P.pt.as_ideal)).to_ring_equiv

end

variables {A R}

@[reducible]
def ring_hom_' : localization.at_prime P.pt.as_ideal →+* R :=
P.ring_hom_.comp $ P.localized_ring_equiv.symm.to_ring_hom

instance is_local_ring_hom' : is_local_ring_hom P.ring_hom_' :=
@@is_local_ring_hom_comp _ _ _ _ _ _ $
  is_local_ring_hom_equiv (P.localized_ring_equiv.symm)

lemma ring_hom'_comp_algebra_map :
  P.ring_hom_'.comp (algebra_map A _) =
  P.ring_hom_.comp (algebra_map A _) :=
begin 
  dsimp [ring_hom_'],
  erw [ring_hom.comp_assoc, is_localization.map_comp],
  congr,
  convert ring_hom.comp_id _,
end 

section

variables {A R}

structure equiv : Prop :=
(pt_eq : P.pt = Q.pt)
(ring_hom_eq : P.ring_hom_ 
    = (localized_ring_equiv_of_pt_eq pt_eq).hom ≫ Q.ring_hom_) 

lemma equiv.refl : P.equiv P :=
{ pt_eq := rfl,
  ring_hom_eq :=
  begin 
    ext : 1,
    obtain ⟨a, b, rfl⟩ := is_localization.mk'_surjective 
      P.pt.as_ideal.prime_compl x,
    erw [ring_hom.comp_apply, is_localization.map_mk'],
    refl,
  end }

lemma equiv.symm (h : P.equiv Q) : Q.equiv P :=
{ pt_eq := h.pt_eq.symm,
  ring_hom_eq := 
  begin 
    rw [h.ring_hom_eq, ←category.assoc],
    symmetry, convert ring_hom.comp_id _,
    change ring_hom.comp _ _ = _,
    erw is_localization.map_comp_map,
    ext : 1,
    erw [is_localization.map_id, ring_hom.id_apply],
  end }

lemma equiv.trans (h1 : P.equiv Q) (h2 : Q.equiv S) : P.equiv S :=
{ pt_eq := h1.pt_eq.trans h2.pt_eq,
  ring_hom_eq := 
  begin 
    rw [h1.ring_hom_eq, h2.ring_hom_eq, ←category.assoc],
    congr' 1,
    change ring_hom.comp _ _ = _,
    erw [is_localization.map_comp_map],
    refl,
  end }

end

end point_local_ring_hom_pair

variables {A R}

@[simps]
def to_point_local_ring_hom_pair (f : A ⟶ R) : 
  point_local_ring_hom_pair A R :=
{ pt := ⟨(local_ring.maximal_ideal R).comap f, infer_instance⟩,
  localized_ring := CommRing.of $ localization.at_prime $ 
    (local_ring.maximal_ideal R).comap f,
  algebra_localized_ring := localization.algebra,
  is_localization := localization.is_localization ,
  ring_hom_ := f.fac,
  is_local_ring_hom_ := infer_instance }

@[simps] 
def from_point_local_ring_hom_pair (P : point_local_ring_hom_pair A R) :
  A ⟶ R :=
P.ring_hom_.comp $ algebra_map _ _

lemma from_point_local_ring_hom_pair.resp_equiv 
  {P Q : point_local_ring_hom_pair A R} (r : P.equiv Q) :
  from_point_local_ring_hom_pair P = from_point_local_ring_hom_pair Q :=
begin 
  ext a,
  rw [from_point_local_ring_hom_pair_apply, from_point_local_ring_hom_pair,
    r.ring_hom_eq, ring_hom.comp_apply], 
  erw [point_local_ring_hom_pair.localized_ring_equiv_of_pt_eq_hom],
  rw [←comp_apply, ←comp_apply, ←category.assoc],
  change ring_hom.comp _ (ring_hom.comp _ _) _ = ring_hom.comp _ _ _,
  rw [is_localization.map_comp, ring_hom.comp_id],
end

lemma from_point_local_ring_hom_pair.surjective (f : A ⟶ R) :
  ∃ (P : point_local_ring_hom_pair A R), from_point_local_ring_hom_pair P = f :=
⟨{ pt := ⟨(local_ring.maximal_ideal R).comap f, infer_instance⟩,
    localized_ring := CommRing.of $ localization.at_prime $ 
      (local_ring.maximal_ideal R).comap f,
    algebra_localized_ring := localization.algebra,
    is_localization := localization.is_localization,
    ring_hom_ := f.fac,
    is_local_ring_hom_ := infer_instance }, 
begin 
  dsimp [from_point_local_ring_hom_pair],
  rw f.fac_comp_algebra_map,  
end⟩

lemma from_point_local_ring_hom_pair.almost_injective {P Q : point_local_ring_hom_pair A R}
  (h : from_point_local_ring_hom_pair P = from_point_local_ring_hom_pair Q) :
  P.equiv Q :=
begin 
  have pt_eq : P.pt = Q.pt,
  { dsimp [from_point_local_ring_hom_pair] at h,
    have eq0 := ring_hom.fac_uniq_pt_eq (P.ring_hom_.comp (algebra_map A P.localized_ring))
      P.pt.as_ideal P.ring_hom_' P.ring_hom'_comp_algebra_map,
    have eq1 := ring_hom.fac_uniq_pt_eq (Q.ring_hom_.comp (algebra_map A Q.localized_ring))
      Q.pt.as_ideal Q.ring_hom_' Q.ring_hom'_comp_algebra_map,
    ext1,
    change P.pt.as_ideal = Q.pt.as_ideal,
    rw [eq0, eq1, h], },
  refine ⟨pt_eq, _⟩,
  ext : 1,
  obtain ⟨a, b, rfl⟩:= is_localization.mk'_surjective P.pt.as_ideal.prime_compl x,
  rw [comp_apply], 
  erw [is_localization.map_mk'],
  simp_rw [ring_hom.id_apply],
  haveI u1 : is_unit (algebra_map A P.localized_ring b),
  { rw [←is_localization.mk'_one P.localized_ring, 
      is_localization.at_prime.is_unit_mk'_iff _ P.pt.as_ideal],
    exact b.2,
    exactI P.is_localization },
  generalize_proofs h1 h2 h3 h4 h5,
  haveI u2 : is_unit (algebra_map A Q.localized_ring (⟨_, h5⟩ : Q.pt.as_ideal.prime_compl)),
  { rw [←is_localization.mk'_one Q.localized_ring, 
      is_localization.at_prime.is_unit_mk'_iff _ Q.pt.as_ideal],
    exact h5,
    exactI Q.is_localization },
  have eq0 : is_localization.mk' P.localized_ring a b = 
    (algebra_map _ _ a) * u1.unit.inv,
  { erw [units.eq_mul_inv_iff_mul_eq, u1.some_spec, 
      ←is_localization.mk'_one P.localized_ring,
      ←is_localization.mk'_one P.localized_ring,
      ←is_localization.mk'_mul, mul_one, is_localization.eq],
    refine ⟨1, _⟩,
    simp only [submonoid.coe_one, mul_one], },
  have eq1 : is_localization.mk' Q.localized_ring a ⟨_, h5⟩ =
    (algebra_map _ _ a) * u2.unit.inv,
  { erw [units.eq_mul_inv_iff_mul_eq, u2.some_spec, 
      ←is_localization.mk'_one Q.localized_ring,
      ←is_localization.mk'_one Q.localized_ring,
      ←is_localization.mk'_mul, mul_one, is_localization.eq],
    refine ⟨1, _⟩,
    simp only [submonoid.coe_one, mul_one], },
  rw [eq0, eq1, map_mul, map_mul, ←ring_hom.comp_apply, ←ring_hom.comp_apply,
    units.inv_eq_coe_inv, units.inv_eq_coe_inv],
  erw [fun_like.congr_fun h a, ring_hom.is_local_ring_hom.map_inv, 
    ring_hom.is_local_ring_hom.map_inv],
  congr' 1,
  rw [units.inv_eq_coe_inv, units.inv_eq_coe_inv],
  apply units.eq_inv_of_mul_eq_one_left, symmetry,
  rw [units.eq_mul_inv_iff_mul_eq, one_mul],
  dsimp,
  rw [←ring_hom.comp_apply, ←ring_hom.comp_apply],
  erw fun_like.congr_fun h (b : A),
  refl,
end

lemma to_point_local_ring_hom_pair.almost_surjective (f : A →+* R) : 
  ∃ (P : point_local_ring_hom_pair A R), 
    P.equiv (to_point_local_ring_hom_pair f) :=
  /-
  This is saying if `f : A →+* R`, then there exists a triple 
  `P := (𝔭, M ⟶ R, M ≅ A_𝔭)` such that `to_point_local_ring_hom_pair f` is
  equivalent to `P`.
  -/  
⟨{ pt := ⟨(local_ring.maximal_ideal R).comap f, infer_instance⟩,
    localized_ring := CommRing.of $ localization.at_prime $ 
      (local_ring.maximal_ideal R).comap f,
    algebra_localized_ring := localization.algebra,
    is_localization := localization.is_localization,
    ring_hom_ := f.fac,
    is_local_ring_hom_ := infer_instance },
  { pt_eq := rfl,
    ring_hom_eq := 
    begin 
      dsimp only [to_point_local_ring_hom_pair_ring_hom_],
      symmetry, convert ring_hom.comp_id _,
      ext x : 1,
      induction x using localization.induction_on with data,
      rcases data with ⟨a, b, hab⟩,
      erw point_local_ring_hom_pair.localized_ring_equiv_of_pt_eq_hom,
      rw [ring_hom.id_apply], 
      erw is_localization.map_id,
    end }⟩

lemma to_point_local_ring_hom_pair.almost_injective {f g : A ⟶ R}
  (hfg : (to_point_local_ring_hom_pair f).equiv (to_point_local_ring_hom_pair g)) :
  f = g :=
begin 
  have := hfg.ring_hom_eq,
  dsimp at this,
  replace this := congr_arg (λ h, ring_hom.comp h (algebra_map A (localization.at_prime (ideal.comap f (maximal_ideal R))))) this,
  dsimp at this,
  rw f.fac_comp_algebra_map at this,
  erw [this, ring_hom.comp_assoc],
  convert ←g.fac_comp_algebra_map,
  erw is_localization.map_comp,
  rw [ring_hom.comp_id],
  refl,
end

lemma from_to_point_local_ring_hom_pair (f : A ⟶ R) :
  from_point_local_ring_hom_pair (to_point_local_ring_hom_pair f) = f :=
begin 
  ext x : 1,
  rw [from_point_local_ring_hom_pair_apply, 
    to_point_local_ring_hom_pair_ring_hom_, ←ring_hom.comp_apply],
  conv_rhs { rw ←f.fac_comp_algebra_map },
  congr' 1,
end

lemma to_from_point_local_ring_hom_pair (P : point_local_ring_hom_pair A R) :
  (to_point_local_ring_hom_pair (from_point_local_ring_hom_pair P)).equiv P := 
from_point_local_ring_hom_pair.almost_injective 
  (from_to_point_local_ring_hom_pair _)

end local_ring