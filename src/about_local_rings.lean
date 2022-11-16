import ring_theory.ideal.local_ring
import ring_theory.localization.at_prime

noncomputable theory

universe u

namespace ring_hom

variables (R : Type u) [comm_ring R] [local_ring R]

section target

variables {R} {A : Type u} [comm_ring A] (φ : A →+* R)

@[simps] def factors_of_target_local_ring : 
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

lemma is_local.factors_of_target_local_ring :
  is_local_ring_hom (factors_of_target_local_ring φ) :=
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

end target

end ring_hom