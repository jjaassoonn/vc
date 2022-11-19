import ring_theory.ideal.local_ring
import ring_theory.localization.at_prime

noncomputable theory

universe u

open_locale big_operators

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

section target

variables {R} {A : Type u} [comm_ring A] (φ : A →+* R)

@[simps] def factor_through_target_local_ring : 
  localization.at_prime (ideal.comap φ (local_ring.maximal_ideal _)) →+* R :=
{ to_fun := λ x, x.lift_on (λ a b, φ a * (begin 
    have := (local_ring.mem_maximal_ideal (φ b)).not.mp _,
    rwa [mem_nonunits_iff, not_not] at this,
    have : b.1 ∉ ideal.comap φ (local_ring.maximal_ideal _) := b.2,
    simpa only [ideal.mem_comap] using this,
  end : is_unit (φ b)).unit.inv) $ λ a a' b b' h, 
  begin 
    dsimp,
    rw localization.r_iff_exists at h,
    obtain ⟨⟨c, (hc1 : c ∉ ideal.comap φ (local_ring.maximal_ideal R))⟩, hc2⟩ := h,
    have hc3 := ideal.mem_comap.not.mp hc1,
    dsimp only [subtype.coe_mk] at hc2,
    have hc4 := ring_hom.congr_arg φ hc2,
    rw [map_mul, map_mul, map_mul, map_mul] at hc4,
    have hc5 : is_unit (φ c),
    { simpa only [mem_nonunits_iff, not_not] using 
        (local_ring.mem_maximal_ideal (φ c)).not.mp hc3, },
    have eq0 := is_unit.mul_left_injective hc5 hc4,
    generalize_proofs h0 h1 h2,
    refine h2.mul_right_injective _,
    rw [←mul_assoc, mul_comm _ (φ a), eq0, ←mul_assoc, mul_comm _ (φ a'), 
      mul_assoc, mul_assoc, is_unit.mul_coe_inv, is_unit.mul_coe_inv],
  end,
  map_one' := 
  begin 
    rw [←localization.mk_one, localization.lift_on_mk, map_one, one_mul],
    generalize_proofs h0 h1,
    rw [units.inv_eq_coe_inv, units.coe_eq_one, inv_eq_one],
    ext1,
    change φ 1 = 1,
    rw map_one,
  end,
  map_mul' := λ x y,
  begin 
    induction x using localization.induction_on with data_x,
    induction y using localization.induction_on with data_y,
    rcases data_x with ⟨a, b⟩,
    rcases data_y with ⟨a', b'⟩,
    rw [localization.mk_mul, localization.lift_on_mk, localization.lift_on_mk, 
      localization.lift_on_mk, map_mul],
    dsimp only [],
    rw [←mul_assoc, mul_assoc _ _ (φ a'), mul_comm (_ : is_unit _).unit.inv (φ a'),
      ←mul_assoc, mul_assoc, mul_assoc, mul_assoc],
    congr' 2,
    rw [units.inv_eq_coe_inv, units.inv_eq_coe_inv, units.inv_eq_coe_inv,
      ←units.coe_mul, ←mul_inv],
    congr' 2,
    ext1,
    change φ (b * b') = φ b * φ b',
    rw map_mul,
  end,
  map_zero' := 
  begin
    rw [←localization.mk_zero, localization.lift_on_mk, map_zero, zero_mul],
    use 1,
  end,
  map_add' := λ x y, 
  begin
    induction x using localization.induction_on with data_x,
    induction y using localization.induction_on with data_y,
    rcases data_x with ⟨a, b⟩,
    rcases data_y with ⟨a', b'⟩,
    rw [localization.add_mk, localization.lift_on_mk, localization.lift_on_mk,
      localization.lift_on_mk, map_add, map_mul, map_mul],
    dsimp only,
    generalize_proofs h0 h1 h2 h3,
    symmetry,
    rw [units.inv_eq_coe_inv, units.inv_eq_coe_inv, units.inv_eq_coe_inv,
      units.eq_mul_inv_iff_mul_eq],
    change _ * φ (b * b') = _,
    rw [map_mul, add_mul, mul_assoc, ←mul_assoc ↑(h2.unit)⁻¹, 
      is_unit.coe_inv_mul, one_mul, mul_assoc, mul_comm (φ b),
      ←mul_assoc ↑(h3.unit)⁻¹, is_unit.coe_inv_mul, one_mul,
      mul_comm (φ a), mul_comm (φ a'), add_comm],
  end }

lemma is_local.factor_through_target_local_ring :
  is_local_ring_hom (factor_through_target_local_ring φ) :=
{ map_nonunit := localization.ind 
  begin 
    rintros ⟨a, b⟩ h,
    dsimp at h ⊢,
    rw [localization.lift_on_mk] at h,
    generalize_proofs h0 h1 at h,
    have ha : is_unit (φ a),
    { have := h.mul h1,
      rw [mul_assoc] at this,
      erw [units.inv_mul] at this,
      rwa [mul_one] at this, },
    have ha' := (local_ring.mem_maximal_ideal (φ a)).not.mpr (λ r, r ha),
    have ha'' : a ∉ ideal.comap φ (local_ring.maximal_ideal R),
    { rwa ideal.mem_comap, },
    refine ⟨⟨localization.mk a b, localization.mk b ⟨a, ha''⟩, _, _⟩, rfl⟩;
    { rw [localization.mk_mul, mul_comm],
      convert localization.mk_self _,
      refl, },
  end }

@[simp] lemma target_local_ring_eq_comp_factors :
  (factor_through_target_local_ring φ).comp
    (algebra_map A (localization.at_prime (ideal.comap φ (local_ring.maximal_ideal _)))) = φ :=
begin 
  ext a,
  rw [ring_hom.comp_apply],
  change φ.factor_through_target_local_ring (localization.mk a 1) = _,
  rw [factor_through_target_local_ring_apply, localization.lift_on_mk],
  rw [units.inv_eq_coe_inv, mul_comm, units.inv_mul_eq_iff_eq_mul],
  change φ a = φ 1 * _,
  rw [map_one, one_mul]
end

-- 01J6, first sentence in proof
lemma factor_through_target_local_ring_uniq (p : ideal A) [p.is_prime]
  (f : localization.at_prime p →+* R) 
  (hf1 : f.comp (algebra_map A (localization.at_prime p)) = φ)
  (hf2 : is_local_ring_hom f) :
  ∃ (eq1 : p = ideal.comap φ (local_ring.maximal_ideal _)),
    (f.comp $ localization.local_ring_hom _ _ (ring_hom.id A) $
      by rw [ideal.comap_id, eq1] : localization.at_prime (ideal.comap φ (local_ring.maximal_ideal _)) →+* R) = 
    φ.factor_through_target_local_ring := 
begin 
  let 𝔪 := ideal.comap φ (local_ring.maximal_ideal _),
  have ineq1 : p ≤ 𝔪,
  { intros a ha,
    rw [ideal.mem_comap, local_ring.mem_maximal_ideal, mem_nonunits_iff],
    contrapose! ha,
    have eq2 := ring_hom.congr_fun hf1 a,
    rw [ring_hom.comp_apply] at eq2,
    change f (localization.mk a 1) = φ a at eq2,
    have := hf2.map_nonunit (localization.mk a 1) (by rwa eq2),
    rwa localization.at_prime.mk_is_unit_iff at this, },
  have ineq2' := ideal.map_mono ineq1,
  rw ←localization.at_prime.maximal_ideal_is' p at ineq2',
  have ideal_eq' := ideal.is_maximal.eq_of_le (local_ring.maximal_ideal.is_maximal _) _ ineq2',
  swap,
  { intros rid,
    rw [ideal.eq_top_iff_one] at rid,
    have rid' : f 1 ∈ ideal.map φ 𝔪,
    { rw [←hf1, ←ideal.map_map],
      refine ideal.mem_map_of_mem _ rid, },
    rw [map_one] at rid',
    have rid'' := ideal.map_comap_le rid',
    rw [←ideal.eq_top_iff_one] at rid'',
    refine (_ : ideal.is_prime _).ne_top rid'',
    exact ideal.is_maximal.is_prime' (local_ring.maximal_ideal R) },
  have ineq2 : 𝔪 ≤ p,
  { intros m hm,
    rw [localization.at_prime.maximal_ideal_is'] at ideal_eq',
    have mem1 : (localization.mk m 1 : localization.at_prime p) ∈ 
      ideal.map (algebra_map A (localization.at_prime p)) 𝔪,
    { rw ←localization.at_prime.ideal_map_is, exact ⟨⟨m, hm⟩, 1, rfl⟩, },
    rw [←ideal_eq', ←localization.at_prime.ideal_map_is] at mem1,
    obtain ⟨a, b, eq0⟩ := mem1,
    rw [localization.mk_eq_mk_iff, localization.r_iff_exists] at eq0,
    obtain ⟨c, eq0⟩ := eq0,
    dsimp at eq0,
    rw [mul_one] at eq0,
    have mem1 : (a * c : A) ∈ p := ideal.mul_mem_right _ _ a.2,
    rw [←eq0] at mem1,
    obtain h0|h2 := ideal.is_prime.mem_or_mem infer_instance mem1,
    obtain h0|h1 := ideal.is_prime.mem_or_mem infer_instance h0,
    exact h0, exact (b.2 h1).elim, exact (c.2 h2).elim, },
  have ideal_eq : p = 𝔪 := le_antisymm ineq1 ineq2,
  refine ⟨ideal_eq, _⟩,
  ext x : 1,
  induction x using localization.induction_on with data,
  rcases data with ⟨a, b⟩,
  rw [factor_through_target_local_ring_apply, localization.lift_on_mk,
    ring_hom.comp_apply, localization.local_ring_hom, localization.mk_eq_mk',
    is_localization.map_mk', ←localization.mk_eq_mk'],
  dsimp,
  generalize_proofs h0 h1 h2,
  rw show localization.mk a ⟨b, h1⟩ = localization.mk a 1 * localization.mk 1 ⟨b, h1⟩, from _,
  work_on_goal 2 
  { rw [localization.mk_mul, mul_one, one_mul], },
  rw [map_mul],
  change (f.comp (algebra_map A (localization.at_prime p))) _ * _ = _,
  rw hf1, congr' 1,
  apply units.eq_inv_of_mul_eq_one_left,
  change φ b * f _ = 1,
  simp_rw ←hf1,
  rw [ring_hom.comp_apply, ←map_mul],
  convert_to f 1 = 1,
  { congr' 1,
    change localization.mk ↑b 1 * _ = 1,
    rw [localization.mk_mul, mul_one, one_mul],
    exact localization.mk_self (⟨_, h1⟩ : ideal.prime_compl _), },
  rw map_one,
end

end target

end ring_hom

namespace local_ring

variables (R S : Type u) [comm_ring R] [comm_ring S] [local_ring S] (f : R ≃+* S)

instance of_equiv : local_ring R :=
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
-- begin 
--   have ha' : f a ∈ nonunits S,
--   { intros h, },
-- end
-- suffices f.symm (f a + f b) ∈ nonunits R, by simpa only [map_add, ring_equiv.symm_apply_apply], 
-- suffices f a + f b ∈ nonunits S, from λ r,
-- begin 
--   have := f.symm.to_ring_hom.is_unit_map,
-- end, _

end local_ring