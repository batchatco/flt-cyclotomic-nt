import CyclotomicNT.CyclotomicEmbedding

/-!
# Cyclic indexing of the places of `ℚ(ζ_p)` by `ℤ/m`, `m = (p−1)/2`

For a generator `g` of `(ℤ/p)ˣ` (`p` odd), `g^m = −1`, so `n ↦ w_{g^n}` is `m`-periodic
(conjugate places `w_{−b} = w_b`) and descends to a **bijection** `ℤ/m ≃ InfinitePlace K`.
Along it the regulator data becomes a function on the cyclic group `ℤ/m`:

* `vFun g n = log‖1 − e(g^n/p)‖` (`m`-periodic), `vIdx : ℤ/m → ℝ`;
* `cycUnitFun g i = ξ_{(g^i mod p)}` the cyclotomic unit attached to `g^i`;
* the **entry formula** `log w_{g^j}(ξ_{g^i}) = vFun(i+j) − vFun(j)` — the reduced group-matrix
  shape over `G = ℤ/m` fed to `norm_det_reduced_groupMatrix`.
-/

open NumberField

namespace CyclotomicNT

variable {p : ℕ} [hpri : Fact p.Prime]

section HalfOrder

/-- For a generator `g` of `(ℤ/p)ˣ` (`p ≠ 2`), `g^{(p−1)/2} = −1` — the unique element of
order `2`. -/
theorem generator_pow_half {g : (ZMod p)ˣ} (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g)
    (hp : p ≠ 2) : g ^ ((p - 1) / 2) = -1 := by
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hpri.out]
  have horder : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, Nat.card_eq_fintype_card, hcard]
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp)
  have hp3 : 3 ≤ p := by have := hpri.out.two_le; omega
  have hsq : (g ^ ((p - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, show (p - 1) / 2 * 2 = p - 1 by omega, ← horder, pow_orderOf_eq_one]
  have hne1 : g ^ ((p - 1) / 2) ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [horder] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hcast : ((g ^ ((p - 1) / 2) : (ZMod p)ˣ) : ZMod p) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
  have hfact : (((g ^ ((p - 1) / 2) : (ZMod p)ˣ) : ZMod p) - 1)
      * (((g ^ ((p - 1) / 2) : (ZMod p)ˣ) : ZMod p) + 1) = 0 := by
    linear_combination hcast
  rcases mul_eq_zero.mp hfact with h | h
  · exact absurd (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h)) hne1
  · refine Units.ext ?_
    rw [Units.val_neg, Units.val_one]
    linear_combination h

/-- `(p−1)/2 ≠ 0` for odd primes. -/
theorem half_pred_ne_zero (hp : p ≠ 2) : (p - 1) / 2 ≠ 0 := by
  have h2 := hpri.out.two_le
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp)
  omega

end HalfOrder

section VFun

variable (g : (ZMod p)ˣ)

/-- The regulator-entry function `vFun g n = log‖1 − e(g^n/p)‖`. -/
noncomputable def vFun (n : ℕ) : ℝ :=
  Real.log ‖1 - ZMod.stdAddChar ((g ^ n : (ZMod p)ˣ) : ZMod p)‖

/-- The descended function on `ℤ/m`. -/
noncomputable def vIdx (j : ZMod ((p - 1) / 2)) : ℝ := vFun g j.val

variable {g}

/-- `‖1 − e(−c/p)‖ = ‖1 − e(c/p)‖` (complex conjugation). -/
theorem norm_one_sub_stdAddChar_neg (c : ZMod p) :
    ‖1 - ZMod.stdAddChar (-c)‖ = ‖1 - ZMod.stdAddChar c‖ := by
  rw [← conj_stdAddChar, show (1 : ℂ) - (starRingEnd ℂ) (ZMod.stdAddChar c)
    = (starRingEnd ℂ) (1 - ZMod.stdAddChar c) by rw [map_sub, map_one], RCLike.norm_conj]

/-- `vFun` is `(p−1)/2`-periodic: `g^{n+m} = −g^n` and conjugation symmetry. -/
theorem vFun_periodic (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2) :
    Function.Periodic (vFun g) ((p - 1) / 2) := by
  intro n
  rw [vFun, vFun, pow_add, generator_pow_half hgen hp, mul_neg_one, Units.val_neg,
    norm_one_sub_stdAddChar_neg]

theorem vIdx_natCast (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2) (n : ℕ) :
    vIdx g (n : ZMod ((p - 1) / 2)) = vFun g n := by
  haveI : NeZero ((p - 1) / 2) := ⟨half_pred_ne_zero hp⟩
  rw [vIdx, ZMod.val_natCast]
  exact (vFun_periodic hgen hp).map_mod_nat n

/-- The group-matrix kernel form: `vIdx (i + j) = vFun (i.val + j.val)`. -/
theorem vIdx_add (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2)
    (i j : ZMod ((p - 1) / 2)) :
    vIdx g (i + j) = vFun g (i.val + j.val) := by
  haveI : NeZero ((p - 1) / 2) := ⟨half_pred_ne_zero hp⟩
  rw [show i + j = ((i.val + j.val : ℕ) : ZMod ((p - 1) / 2)) by
      push_cast [ZMod.natCast_val, ZMod.cast_id]
      rfl, vIdx_natCast hgen hp]

end VFun

section Places

variable {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ)

/-- The place sequence `n ↦ w_{g^n}`. -/
noncomputable def cycPlaceFun (n : ℕ) : InfinitePlace K := cycPlace hζ (g ^ n)

/-- The descended place indexing `ℤ/m → InfinitePlace K`. -/
noncomputable def cycPlaceIdx (j : ZMod ((p - 1) / 2)) : InfinitePlace K :=
  cycPlaceFun hζ g j.val

variable {g}

theorem cycPlaceFun_periodic (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2) :
    Function.Periodic (cycPlaceFun hζ g) ((p - 1) / 2) := by
  intro n
  rw [cycPlaceFun, cycPlaceFun, pow_add, generator_pow_half hgen hp, mul_neg_one, cycPlace_neg]

theorem cycPlaceIdx_natCast (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2)
    (n : ℕ) : cycPlaceIdx hζ g (n : ZMod ((p - 1) / 2)) = cycPlaceFun hζ g n := by
  haveI : NeZero ((p - 1) / 2) := ⟨half_pred_ne_zero hp⟩
  rw [cycPlaceIdx, ZMod.val_natCast]
  exact (cycPlaceFun_periodic hζ hgen hp).map_mod_nat n

theorem cycPlaceIdx_surjective (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2) :
    Function.Surjective (cycPlaceIdx hζ g) := by
  intro w
  obtain ⟨b, rfl⟩ := cycPlace_surjective hζ w
  obtain ⟨k, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hgen b)
  exact ⟨(k : ZMod ((p - 1) / 2)), cycPlaceIdx_natCast hζ hgen hp k⟩

/-- The number of infinite places of `ℚ(ζ_p)` is `(p−1)/2` (totally complex, degree `p−1`). -/
theorem card_infinitePlace_eq [NumberField K] (hp : p ≠ 2) :
    Fintype.card (InfinitePlace K) = (p - 1) / 2 := by
  have hlt : 2 < p := by have := hpri.out.two_le; omega
  haveI : NumberField.IsTotallyComplex K := IsCyclotomicExtension.Rat.isTotallyComplex K hlt
  have hfr : Module.finrank ℚ K = p - 1 := by
    rw [IsCyclotomicExtension.finrank (K := ℚ) (L := K)
      (Polynomial.cyclotomic.irreducible_rat hpri.out.pos), Nat.totient_prime hpri.out]
  have hcx : InfinitePlace.nrComplexPlaces K = (p - 1) / 2 := by
    have h := IsTotallyComplex.finrank (K := K)
    rw [hfr] at h
    omega
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, hcx]

/-- **The cyclic indexing of the places of `ℚ(ζ_p)`**: `j ↦ w_{g^j}` is a bijection
`ℤ/m ≃ InfinitePlace K`. -/
theorem cycPlaceIdx_bijective [NumberField K]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2) :
    Function.Bijective (cycPlaceIdx hζ g) := by
  haveI : NeZero ((p - 1) / 2) := ⟨half_pred_ne_zero hp⟩
  rw [Fintype.bijective_iff_surjective_and_card]
  exact ⟨cycPlaceIdx_surjective hζ hgen hp, by rw [ZMod.card, card_infinitePlace_eq hp]⟩

end Places

section Units

variable {K : Type*} [Field K] [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ)

/-- The cyclotomic-unit sequence `i ↦ ξ_{(g^i mod p)}` attached to the generator cycle. -/
noncomputable def cycUnitFun (i : ℕ) : (𝓞 K)ˣ :=
  realCyclotomicUnit hζ ((g ^ i : (ZMod p)ˣ) : ZMod p).val (ZMod.val_coe_unit_coprime _)

omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
theorem cycUnitFun_mem (i : ℕ) : cycUnitFun hζ g i ∈ cyclotomicUnitGroup hζ :=
  realCyclotomicUnit_mem hζ _ _

omit [NumberField K] in
/-- **The regulator entry formula**: `log w_{g^j}(ξ_{g^i}) = vFun(i+j) − vFun(j)` — the reduced
group-matrix kernel over `ℤ/m`. -/
theorem log_cycPlaceFun_cycUnitFun (i j : ℕ) :
    Real.log (cycPlaceFun hζ g j (cycUnitFun hζ g i : K)) = vFun g (i + j) - vFun g j := by
  rw [cycPlaceFun, cycUnitFun,
    log_cycPlace_realCyclotomicUnit hζ (g ^ j) _ (ZMod.val_coe_unit_coprime _), vFun, vFun]
  congr 3
  rw [ZMod.natCast_val, ZMod.cast_id, ← Units.val_mul, ← pow_add]

end Units

end CyclotomicNT
