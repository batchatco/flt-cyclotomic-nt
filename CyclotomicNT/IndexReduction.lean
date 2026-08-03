import CyclotomicNT.EigenIndep
import CyclotomicNT.EigenSum

/-!
# Thm 8.14, step (2) — the index reduction `p ∣ [E:C] ⟺ Cbar ≠ ⊤` (foundation)

To turn `{Ēᵢ} span V` into `p ∤ [E:C]`, the key is that `Ēᵢ = 0` in `V = E/E^p` exactly when `Eᵢ`
    is a
`p`-th power.  This file starts with that kernel characterization of `vOf`; the remaining wiring
(`Cbar` = image of `C`, `Cbar=⊤ ⟹ E=C·E^p ⟹ p∤[E:C]` via `prime_dvd_card_iff_not_surjective_pow`)
    comes
next. -/

namespace CyclotomicNT

open scoped NumberField
open NumberField NumberField.IsCMField Finset

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}

omit hpri [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/-- The kernel of the class map: `[u] = 0` in `V = E/E^p` iff `u` is a `p`-th power in `E`.
In particular `Ēᵢ = 0 ⟺ Eᵢ ∈ E^p`. -/
theorem vOf_eq_zero_iff (u : realUnits K) :
    (vOf u : ModN (Additive (realUnits K)) p) = 0 ↔ ∃ v : realUnits K, u = v ^ p := by
  rw [vOf, show (ModN.mkQ p (Additive.ofMul u) : ModN (Additive (realUnits K)) p)
      = Submodule.Quotient.mk (Additive.ofMul u) from rfl,
    Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    rw [LinearMap.lsmul_apply, natCast_zsmul] at hw
    refine ⟨Additive.toMul w, ?_⟩
    apply Additive.ofMul.injective
    rw [ofMul_pow]; exact hw.symm
  · rintro ⟨v, rfl⟩
    exact ⟨Additive.ofMul v, by rw [LinearMap.lsmul_apply, natCast_zsmul, ← ofMul_pow]⟩

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`E = C·E^p`** from `span{Ēᵢ}=⊤`: every real unit is a cyclotomic unit times a `p`-th power.
The `vOf e ∈ span{Ēᵢ}` decomposition lifts (via `vOf_pow`/`vOf_prod`) to a product of cyclotomic
units `c`, and `e·c⁻¹` has trivial class hence is a `p`-th power (`vOf_eq_zero_iff`). -/
theorem mem_C_mul_pow (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2)
    (hspan : Submodule.span (ZMod p) (Set.range (eigenFamily hζ hp)) = ⊤) (e : realUnits K) :
    ∃ c : realUnits K, (c : (𝓞 K)ˣ) ∈ cyclotomicUnitGroup hζ ∧ ∃ w : realUnits K, e = c * w ^ p :=
        by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  have hmem : vOf e ∈ Submodule.span (ZMod p) (Set.range (eigenFamily hζ hp)) :=
    hspan ▸ Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨a, ha⟩ := hmem
  simp only [eigenFamily] at ha
  set c : realUnits K := ∏ k, (⟨eigenCyclotomicUnit hζ (2 * (k.1 + 1)),
    eigenCyclotomicUnit_mem_realUnits hζ hp _⟩ : realUnits K) ^ ((a k).val) with hc
  have hvc : (vOf c : ModN (Additive (realUnits K)) p) = vOf e := by
    rw [hc, vOf_prod, ← ha]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hval : ((a k).val : ZMod p) = a k := ZMod.natCast_zmod_val (a k)
    rw [vOf_pow, ← Nat.cast_smul_eq_nsmul (ZMod p) ((a k).val), hval]
  refine ⟨c, ?_, ?_⟩
  · rw [hc, SubmonoidClass.coe_finsetProd]
    refine Subgroup.prod_mem _ fun k _ => ?_
    rw [SubmonoidClass.coe_pow]
    exact Subgroup.pow_mem _ (eigenCyclotomicUnit_mem hζ _) _
  · obtain ⟨w, hw⟩ := (vOf_eq_zero_iff (p := p) (e * c⁻¹)).mp (by rw [vOf_mul, vOf_inv, hvc,
      add_neg_cancel])
    exact ⟨w, by rw [← hw, mul_comm c, mul_assoc, inv_mul_cancel, mul_one]⟩

/-- **Thm 8.14 conclusion (one direction)**: if no `Eᵢ` is a `p`-th power (all class-images
`Ēᵢ ≠ 0`), then `p ∤ h⁺` — i.e. `p` is a Vandiver prime.  From `{Ēᵢ}` spanning `E/E^p` (step 4),
`E = C·E^p` (`mem_C_mul_pow`), so `x ↦ x^p` is surjective on `E/C`, whence `p ∤ [E:C] = h⁺` (the
    index
engine + Thm 8.2). -/
theorem vandiver_aux (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2)
    (hne : ∀ k : Fin ((p - 3) / 2), eigenFamily hζ hp k ≠ 0) :
    ¬ (p ∣ Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))) := by
  obtain ⟨g, hg⟩ := exists_primRoot_pow_inj (p := p)
  have hspan := eigenFamily_span hζ hp g hg hne
  rw [← cyclotomic_unit_index hζ hp, Subgroup.relIndex, Subgroup.index_eq_card]
  haveI : Finite (↥(realUnits K) ⧸ (cyclotomicUnitGroup hζ).subgroupOf (realUnits K)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [← Subgroup.index_eq_card, ← Subgroup.relIndex, cyclotomic_unit_index hζ hp]
    exact (Fintype.card_pos).ne'
  rw [prime_dvd_card_iff_not_surjective_pow, not_not]
  intro q
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨c, hc, w, hw⟩ := mem_C_mul_pow hζ hp hspan e
  refine ⟨QuotientGroup.mk w, ?_⟩
  change (QuotientGroup.mk w) ^ p = QuotientGroup.mk e
  rw [hw, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff c).mpr (Subgroup.mem_subgroupOf.mpr hc), one_mul, ←
        QuotientGroup.mk_pow]

end CyclotomicNT
