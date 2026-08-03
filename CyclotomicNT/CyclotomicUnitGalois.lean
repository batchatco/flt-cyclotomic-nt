import CyclotomicNT.CyclotomicUnitGroup
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# Thm 8.14, piece 1 — the Galois automorphism `σ_g : ζ ↦ ζ^g`

This sets up the *single* Galois operator that the eigenspace bridge (Washington Thm 8.14) is built
on.  For `g ∈ (ℤ/p)ˣ`, `σ_g` is the
automorphism of `K = ℚ(ζ_p)` sending `ζ ↦ ζ^g`; restricting along a primitive root `g` mod `p`
gives the generator of `Δ = Gal(K⁺/ℚ)` whose eigenvectors on `E/E^p` are exactly the cyclotomic
units `Eᵢ`.

* `galAut hζ g : K ≃ₐ[ℚ] K`  with `galAut_zeta : σ_g ζ = ζ^g`  (built via `equivOfMinpoly`, since
    `ζ`
  and `ζ^g` share the minimal polynomial `cyclotomic p ℚ`);
* `galUnit hζ g : (𝓞 K)ˣ ≃* (𝓞 K)ˣ`  the induced action on units, with `coe_galUnit` and
  `galUnit_zetaUnit : σ_g (ζ-as-unit) = (ζ-as-unit)^g`. -/

namespace CyclotomicNT

open scoped NumberField
open NumberField

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K}

/-- A unit `g` of `ℤ/p`, as a natural number, is coprime to `p`. -/
theorem coprime_val (g : (ZMod p)ˣ) : ((g : ZMod p).val).Coprime p := ZMod.val_coe_unit_coprime g

omit [NumberField K] in
private theorem galAut_minpoly (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) :
    minpoly ℚ (hζ.powerBasis ℚ).gen
      = minpoly ℚ ((hζ.pow_of_coprime _ (coprime_val g)).powerBasis ℚ).gen := by
  haveI : NeZero ((p : ℚ)) := ⟨by exact_mod_cast hpri.out.ne_zero⟩
  have hirr : Irreducible (Polynomial.cyclotomic p ℚ) :=
    Polynomial.cyclotomic.irreducible_rat hpri.out.pos
  rw [IsPrimitiveRoot.powerBasis_gen, IsPrimitiveRoot.powerBasis_gen,
    ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
    ← (hζ.pow_of_coprime _ (coprime_val g)).minpoly_eq_cyclotomic_of_irreducible hirr]

/-- **The Galois automorphism `σ_g : ζ ↦ ζ^g`** of `K = ℚ(ζ_p)`, for `g ∈ (ℤ/p)ˣ`. -/
noncomputable def galAut (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) : K ≃ₐ[ℚ] K :=
  (hζ.powerBasis ℚ).equivOfMinpoly ((hζ.pow_of_coprime _ (coprime_val g)).powerBasis ℚ)
    (galAut_minpoly hζ g)

omit [NumberField K] in
@[simp] theorem galAut_zeta (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) :
    galAut hζ g ζ = ζ ^ (g : ZMod p).val := by
  have key := (hζ.powerBasis ℚ).equivOfMinpoly_gen
    ((hζ.pow_of_coprime _ (coprime_val g)).powerBasis ℚ) (galAut_minpoly hζ g)
  rw [IsPrimitiveRoot.powerBasis_gen, IsPrimitiveRoot.powerBasis_gen] at key
  exact key

/-- The action of `σ_g` on the units of `𝓞 K`. -/
noncomputable def galUnit (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) : (𝓞 K)ˣ ≃* (𝓞 K)ˣ :=
  Units.mapEquiv (RingOfIntegers.mapRingEquiv (galAut hζ g).toRingEquiv)

omit [NumberField K] in
@[simp] theorem coe_galUnit (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) (u : (𝓞 K)ˣ) :
    ((galUnit hζ g u : 𝓞 K) : K) = galAut hζ g (u : K) := rfl

omit [NumberField K] in
theorem galUnit_zetaUnit (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) :
    galUnit hζ g (zetaUnit hζ) = zetaUnit hζ ^ (g : ZMod p).val := by
  refine Units.ext (FaithfulSMul.algebraMap_injective (𝓞 K) K ?_)
  rw [← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, coe_galUnit,
    coe_zetaUnit, galAut_zeta, Units.val_pow_eq_pow_val]
  push_cast [coe_zetaUnit]
  ring

open Finset in
omit [NumberField K] in
/-- The geometric-sum identity underlying the Galois action on cyclotomic units:
`σ_g(∑_{i<a} ζ^i)·(∑_{i<g} ζ^i) = ∑_{i<ag} ζ^i` (i.e. `(ζ^{ag}-1)/(ζ^g-1)·(ζ^g-1)/(ζ-1)`). -/
theorem galAut_geom_sum (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) (a : ℕ) :
    galAut hζ g (∑ i ∈ range a, ζ ^ i) * (∑ i ∈ range (g : ZMod p).val, ζ ^ i)
      = ∑ i ∈ range (a * (g : ZMod p).val), ζ ^ i := by
  have hne : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one hpri.out.one_lt)
  apply mul_right_cancel₀ hne
  rw [mul_assoc, geom_sum_mul, geom_sum_mul, map_sum]
  simp_rw [map_pow, galAut_zeta]
  rw [geom_sum_mul, ← pow_mul, Nat.mul_comm]

open Finset in
omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- The `K`-value of the (integer) cyclotomic unit: `∑_{i<a} ζ^i`. -/
theorem coe_cyclotomicUnit_K (hζ : IsPrimitiveRoot ζ p) (a : ℕ) (ha : a.Coprime p) :
    ((cyclotomicUnit hζ.toInteger_isPrimitiveRoot hpri.out.two_le ha : 𝓞 K) : K)
      = ∑ i ∈ range a, ζ ^ i := by
  have ht : (algebraMap (𝓞 K) K) hζ.toInteger = ζ := hζ.coe_toInteger
  simp only [coe_cyclotomicUnit, map_sum, map_pow, ht]

omit [NumberField K] in
/-- The Galois action on the (integer) cyclotomic unit: `σ_g(c_a)·c_g = c_{ag}`. -/
theorem galUnit_cyclotomicUnit (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) (a : ℕ) (ha : a.Coprime
    p) :
    galUnit hζ g (cyclotomicUnit hζ.toInteger_isPrimitiveRoot hpri.out.two_le ha)
      * cyclotomicUnit hζ.toInteger_isPrimitiveRoot hpri.out.two_le (coprime_val g)
      = cyclotomicUnit hζ.toInteger_isPrimitiveRoot hpri.out.two_le
          (Nat.coprime_mul_iff_left.mpr ⟨ha, coprime_val g⟩) := by
  refine Units.ext (FaithfulSMul.algebraMap_injective (𝓞 K) K ?_)
  rw [← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, Units.val_mul]
  push_cast
  simp only [coe_galUnit, coe_cyclotomicUnit_K]
  exact galAut_geom_sum hζ g a

omit [NumberField K] in
/-- **Thm 8.14, piece 3a-ii** — the Galois action on the real cyclotomic unit:
`σ_g(ξ_a) = ξ_{a·g}·ξ_g⁻¹`.  The `ζ^{(1−a)/2}` normalizing exponents satisfy
`(g·val)·e_a = e_{ag} − e_g` *exactly* (no mod-`p` needed), so the `zetaUnit` parts match by `ring`
and the cyclotomic parts by `galUnit_cyclotomicUnit`. -/
theorem galUnit_realCyclotomicUnit (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) (a : ℕ)
    (ha : a.Coprime p) :
    galUnit hζ g (realCyclotomicUnit hζ a ha)
      = realCyclotomicUnit hζ (a * (g : ZMod p).val)
          (Nat.coprime_mul_iff_left.mpr ⟨ha, coprime_val g⟩)
        * (realCyclotomicUnit hζ (g : ZMod p).val (coprime_val g))⁻¹ := by
  have hcu := eq_mul_inv_of_mul_eq (galUnit_cyclotomicUnit hζ g a ha)
  have key : (zetaUnit hζ ^ (g : ZMod p).val) ^ ((1 - (a : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ))
      = zetaUnit hζ ^ ((1 - ((a * (g : ZMod p).val : ℕ) : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ))
        * (zetaUnit hζ ^ ((1 - ((g : ZMod p).val : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ)))⁻¹ := by
    rw [← zpow_natCast (zetaUnit hζ) ((g : ZMod p).val), ← zpow_mul, ← zpow_neg, ← zpow_add]
    congr 1
    push_cast
    ring
  simp only [realCyclotomicUnit]
  rw [map_mul, map_zpow, galUnit_zetaUnit, hcu, key, mul_inv]
  simp only [mul_comm, mul_left_comm, mul_assoc]

omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **Thm 8.14, piece 3a-iii (α) — the reflection identity** `ξ_{p−x} = −ξ_x` (`x < p`,
both coprime).
The `ζ^{(1−a)/2}` exponent difference `e_{p−x} − x − e_x` equals `p·(x − (p+1)/2)` *exactly* (given
`2·(p+1)/2 = p+1`), so with `ζ^p = 1` and `s_{p−x} = −ζ^{−x} s_x` the two sides collapse to a single
sign `−1`.  In `E/E^p` this gives `v_{p−x} = v_x`, since `−1 = (−1)^p ∈ E^p` (`p` odd). -/
theorem realCyclotomicUnit_reflect (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) (x : ℕ) (hxlt : x < p)
    (hx : x.Coprime p) (hpx : (p - x).Coprime p) :
    realCyclotomicUnit hζ (p - x) hpx = -realCyclotomicUnit hζ x hx := by
  have hz_ne : ζ ≠ 0 := hζ.ne_zero hpri.out.pos.ne'
  have hsub : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one hpri.out.one_lt)
  have hz_p : ζ ^ (p : ℤ) = 1 := by rw [zpow_natCast]; exact hζ.pow_eq_one
  have hp1 : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp2)
  refine Units.ext (FaithfulSMul.algebraMap_injective (𝓞 K) K ?_)
  rw [Units.val_neg, map_neg, coe_realCyclotomicUnit, coe_realCyclotomicUnit]
  simp only [zpow_natCast]
  apply mul_right_cancel₀ hsub
  rw [mul_assoc, geom_sum_mul, neg_mul, mul_assoc, geom_sum_mul,
    ← zpow_natCast ζ (p - x), ← zpow_natCast ζ x]
  have hpxpow : (ζ : K) ^ ((p - x : ℕ) : ℤ) = ζ ^ (-(x : ℤ)) := by
    rw [Nat.cast_sub hxlt.le, zpow_sub₀ hz_ne, hz_p, one_div, ← zpow_neg]
  have hfac : (ζ : K) ^ (-(x : ℤ)) - 1 = -(ζ ^ (-(x : ℤ)) * (ζ ^ (x : ℤ) - 1)) := by
    rw [mul_sub, ← zpow_add₀ hz_ne, neg_add_cancel, zpow_zero]; ring
  rw [hpxpow, hfac]
  rw [show (ζ : K) ^ ((1 - ((p - x : ℕ) : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ))
        * (-(ζ ^ (-(x : ℤ)) * (ζ ^ (x : ℤ) - 1)))
      = -(ζ ^ ((1 - ((p - x : ℕ) : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ) + (-(x : ℤ))) * (ζ ^ (x : ℤ) - 1))
          by
    rw [zpow_add₀ hz_ne]; ring]
  congr 2
  have hexp : (1 - ((p - x : ℕ) : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ) + (-(x : ℤ))
      = (1 - (x : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ) + (p : ℤ) * ((x : ℤ) - (((p + 1) / 2 : ℕ) : ℤ)) :=
          by
    have hM : (2 : ℤ) * (((p + 1) / 2 : ℕ) : ℤ) = (p : ℤ) + 1 := by omega
    rw [Nat.cast_sub hxlt.le]; linear_combination (x : ℤ) * hM
  rw [hexp, zpow_add₀ hz_ne, zpow_mul ζ (p : ℤ) ((x : ℤ) - (((p + 1) / 2 : ℕ) : ℤ)),
    hz_p, one_zpow, mul_one]

omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **Thm 8.14, piece 3a-iii (β) — periodicity** `ξ_j = ξ_{j'}` whenever `j ≡ j' (mod p)`.  At the
    field
level (`×(ζ−1)`, `geom_sum_mul`) the cyclotomic parts agree because `ζ^j = ζ^{j'}` (`p ∣ j−j'`,
`ζ^p = 1`), and the `ζ^{(1−·)/2}` exponents agree mod `p` for the same reason. -/
theorem realCyclotomicUnit_periodic (hζ : IsPrimitiveRoot ζ p) (j j' : ℕ) (hjj' : j ≡ j' [MOD p])
    (hj : j.Coprime p) (hj' : j'.Coprime p) :
    realCyclotomicUnit hζ j hj = realCyclotomicUnit hζ j' hj' := by
  have hz_ne : ζ ≠ 0 := hζ.ne_zero hpri.out.pos.ne'
  have hsub : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one hpri.out.one_lt)
  have hz_p : ζ ^ (p : ℤ) = 1 := by rw [zpow_natCast]; exact hζ.pow_eq_one
  refine Units.ext (FaithfulSMul.algebraMap_injective (𝓞 K) K ?_)
  rw [coe_realCyclotomicUnit, coe_realCyclotomicUnit]
  simp only [zpow_natCast]
  obtain ⟨d, hd⟩ := Nat.modEq_iff_dvd.mp hjj'
  have hzjj' : (ζ : K) ^ j = ζ ^ j' := by
    rw [← zpow_natCast ζ j, ← zpow_natCast ζ j',
      show (j : ℤ) = (j' : ℤ) + (p : ℤ) * (-d) by linear_combination -hd,
      zpow_add₀ hz_ne, zpow_mul ζ (p : ℤ) (-d), hz_p, one_zpow, mul_one]
  apply mul_right_cancel₀ hsub
  rw [mul_assoc, geom_sum_mul, mul_assoc, geom_sum_mul, hzjj']
  congr 1
  rw [show (1 - (j : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ)
      = (1 - (j' : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ) + (p : ℤ) * (d * (((p + 1) / 2 : ℕ) : ℤ)) by
    linear_combination (((p + 1) / 2 : ℕ) : ℤ) * hd]
  rw [zpow_add₀ hz_ne, zpow_mul ζ (p : ℤ) (d * (((p + 1) / 2 : ℕ) : ℤ)), hz_p, one_zpow, mul_one]

end CyclotomicNT
