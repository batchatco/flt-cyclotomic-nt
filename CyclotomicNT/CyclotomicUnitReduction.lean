import CyclotomicNT.CyclotomicUnitGroup

/-!
# Reduction relations among the cyclotomic units `ξ_a`

The real cyclotomic unit `ξ_a = ζ^{(1−a)(p+1)/2}·(ζ^a−1)/(ζ−1)` depends only on `a mod p`,
and negating the residue flips the sign:

* `realCyclotomicUnit_modEq` : `a ≡ b (mod p)` → `ξ_a = ξ_b`;
* `realCyclotomicUnit_neg_modEq` : `a + b ≡ 0 (mod p)` → `ξ_a = −ξ_b`.

These let the full generating family `{ξ_a : a coprime p}` of the cyclotomic unit group `C`
be reduced — modulo torsion — to the cycle family `ξ_{(g^i mod p)}` of `CyclotomicPlaceCycle`
(`g` a generator of `(ℤ/p)ˣ`), which is what the regulator computation indexes.
-/

open Finset
open scoped NumberField

namespace CyclotomicNT

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

omit [CharZero K] [NumberField K] hζ in
/-- Units of `𝓞 K` agreeing in `K` are equal. -/
private theorem units_eq_of_coe {u v : (𝓞 K)ˣ} (h : (u : K) = (v : K)) : u = v :=
  Units.ext (FaithfulSMul.algebraMap_injective (𝓞 K) K h)

omit [CharZero K] [NumberField K] in
/-- The geometric sum against `ζ − 1` (in `zpow` form): `(∑_{i<c} ζ^i)(ζ−1) = ζ^c − 1`. -/
private theorem zpow_geom_sum_mul (c : ℕ) :
    (∑ i ∈ range c, ζ ^ (i : ℤ)) * (ζ - 1) = ζ ^ (c : ℤ) - 1 := by
  rw [show ∑ i ∈ range c, ζ ^ (i : ℤ) = ∑ i ∈ range c, ζ ^ i from
    sum_congr rfl fun i _ => zpow_natCast ζ i, geom_sum_mul, zpow_natCast]

omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **Periodicity step**: `ξ_{a+p} = ξ_a`. -/
theorem realCyclotomicUnit_add_p (a : ℕ) (ha : a.Coprime p) (hap : (a + p).Coprime p) :
    realCyclotomicUnit hζ (a + p) hap = realCyclotomicUnit hζ a ha := by
  have hz_ne : ζ ≠ 0 := hζ.ne_zero hpri.out.pos.ne'
  have hzp : ζ ^ (p : ℤ) = 1 := by rw [zpow_natCast]; exact hζ.pow_eq_one
  apply units_eq_of_coe
  rw [coe_realCyclotomicUnit, coe_realCyclotomicUnit]
  have hsum : ∑ i ∈ range (a + p), ζ ^ (i : ℤ) = ∑ i ∈ range a, ζ ^ (i : ℤ) := by
    rw [Finset.sum_range_add]
    have hblock : ∑ i ∈ range p, ζ ^ ((a + i : ℕ) : ℤ) = 0 := by
      have hterm : ∀ i : ℕ, ζ ^ ((a + i : ℕ) : ℤ) = ζ ^ (a : ℤ) * ζ ^ (i : ℤ) := fun i => by
        push_cast
        rw [zpow_add₀ hz_ne]
      rw [sum_congr rfl fun i _ => hterm i, ← mul_sum,
        show ∑ i ∈ range p, ζ ^ (i : ℤ) = ∑ i ∈ range p, ζ ^ i from
          sum_congr rfl fun i _ => zpow_natCast ζ i,
        hζ.geom_sum_eq_zero hpri.out.one_lt, mul_zero]
    rw [hblock, add_zero]
  rw [hsum]
  congr 1
  have hexp : (1 - ((a : ℤ) + p)) * (((p + 1) / 2 : ℕ) : ℤ)
      = (1 - a) * (((p + 1) / 2 : ℕ) : ℤ) + (p : ℤ) * (-(((p + 1) / 2 : ℕ) : ℤ)) := by ring
  have hp1 : ζ ^ ((p : ℤ) * (-(((p + 1) / 2 : ℕ) : ℤ))) = 1 := by
    rw [zpow_mul, hzp, one_zpow]
  rw [Nat.cast_add, hexp, zpow_add₀ hz_ne, hp1, mul_one]

omit hpri [Field K] [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] hζ in
/-- Coprimality to `p` descends to the residue. -/
theorem coprime_mod_p {a : ℕ} (ha : a.Coprime p) : (a % p).Coprime p := by
  have h := Nat.gcd_rec p a
  unfold Nat.Coprime at ha ⊢
  rw [← h, Nat.gcd_comm]
  exact ha

omit [CharZero K] [NumberField K] in
/-- Transport `ξ` across an index equality (proof-irrelevant in the coprimality argument). -/
theorem realCyclotomicUnit_congr {a b : ℕ} (h : a = b) (ha : a.Coprime p)
    (hb : b.Coprime p) :
    realCyclotomicUnit hζ a ha = realCyclotomicUnit hζ b hb := by
  subst h
  rfl

omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- `ξ_{a + kp} = ξ_a`. -/
theorem realCyclotomicUnit_add_mul_p (a k : ℕ) (ha : a.Coprime p)
    (hak : (a + k * p).Coprime p) :
    realCyclotomicUnit hζ (a + k * p) hak = realCyclotomicUnit hζ a ha := by
  induction k with
  | zero => exact realCyclotomicUnit_congr hζ (by ring) _ _
  | succ n ih =>
      have han : (a + n * p).Coprime p := (Nat.coprime_add_mul_right_left a p n).mpr ha
      have hanp : ((a + n * p) + p).Coprime p := Nat.coprime_add_self_left.mpr han
      rw [realCyclotomicUnit_congr hζ (show a + (n + 1) * p = (a + n * p) + p by ring) hak hanp,
        realCyclotomicUnit_add_p hζ _ han hanp, ih han]

omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- `ξ_a = ξ_{a % p}`. -/
theorem realCyclotomicUnit_mod (a : ℕ) (ha : a.Coprime p) :
    realCyclotomicUnit hζ a ha = realCyclotomicUnit hζ (a % p) (coprime_mod_p ha) := by
  have he : a % p + a / p * p = a := Nat.mod_add_div' a p
  rw [realCyclotomicUnit_congr hζ he.symm ha (by rwa [he]),
    realCyclotomicUnit_add_mul_p hζ (a % p) (a / p) (coprime_mod_p ha)]

omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **`ξ_a` depends only on `a mod p`**: `a ≡ b (mod p)` → `ξ_a = ξ_b`. -/
theorem realCyclotomicUnit_modEq {a b : ℕ} (hab : a ≡ b [MOD p]) (ha : a.Coprime p)
    (hb : b.Coprime p) :
    realCyclotomicUnit hζ a ha = realCyclotomicUnit hζ b hb := by
  rw [realCyclotomicUnit_mod hζ a ha, realCyclotomicUnit_mod hζ b hb]
  exact realCyclotomicUnit_congr hζ hab (coprime_mod_p ha) (coprime_mod_p hb)

omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **Negating the residue flips the sign** (exact-sum case): `a + b = p` → `ξ_a = −ξ_b`. -/
theorem realCyclotomicUnit_add_eq_p (hp : p ≠ 2) {a b : ℕ} (hab : a + b = p)
    (ha : a.Coprime p) (hb : b.Coprime p) :
    realCyclotomicUnit hζ a ha = - realCyclotomicUnit hζ b hb := by
  have hz_ne : ζ ≠ 0 := hζ.ne_zero hpri.out.pos.ne'
  have hzp : ζ ^ (p : ℤ) = 1 := by rw [zpow_natCast]; exact hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζ.ne_one hpri.out.one_lt
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp)
  apply units_eq_of_coe
  have hneg : ((- realCyclotomicUnit hζ b hb : (𝓞 K)ˣ) : K)
      = -(realCyclotomicUnit hζ b hb : K) := by
    rw [Units.val_neg, map_neg]
  rw [hneg, coe_realCyclotomicUnit, coe_realCyclotomicUnit]
  set E := (((p + 1) / 2 : ℕ) : ℤ) with hE
  apply mul_right_cancel₀ (sub_ne_zero.mpr hζ1)
  rw [mul_assoc, zpow_geom_sum_mul, neg_mul, mul_assoc, zpow_geom_sum_mul]
  -- key exponent identities
  have h2E : 2 * E = (p : ℤ) + 1 := by rw [hE]; omega
  have hza : ζ ^ ((a : ℕ) : ℤ) = ζ ^ (-(b : ℤ)) := by
    rw [show ((a : ℕ) : ℤ) = -(b : ℤ) + p by push_cast [← hab]; ring, zpow_add₀ hz_ne, hzp,
      mul_one]
  have hXb : ζ ^ ((1 - (a : ℤ)) * E - b) = ζ ^ ((1 - (b : ℤ)) * E) := by
    have hexp : (1 - (a : ℤ)) * E - b = (1 - (b : ℤ)) * E + (p : ℤ) * ((b : ℤ) - E) := by
      have hab' : (a : ℤ) = (p : ℤ) - b := by push_cast [← hab]; ring
      rw [hab']
      linear_combination (b : ℤ) * h2E
    have hp2 : ζ ^ ((p : ℤ) * ((b : ℤ) - E)) = 1 := by rw [zpow_mul, hzp, one_zpow]
    rw [hexp, zpow_add₀ hz_ne, hp2, mul_one]
  calc ζ ^ ((1 - (a : ℤ)) * E) * (ζ ^ ((a : ℕ) : ℤ) - 1)
      = ζ ^ ((1 - (a : ℤ)) * E) * ζ ^ (-(b : ℤ)) - ζ ^ ((1 - (a : ℤ)) * E) := by
        rw [hza, mul_sub, mul_one]
    _ = ζ ^ ((1 - (a : ℤ)) * E - b)
        - ζ ^ ((1 - (a : ℤ)) * E - b) * ζ ^ ((b : ℕ) : ℤ) := by
        rw [← zpow_add₀ hz_ne, ← zpow_add₀ hz_ne]
        congr 2; ring
    _ = ζ ^ ((1 - (b : ℤ)) * E) - ζ ^ ((1 - (b : ℤ)) * E) * ζ ^ ((b : ℕ) : ℤ) := by
        rw [hXb]
    _ = -(ζ ^ ((1 - (b : ℤ)) * E) * (ζ ^ ((b : ℕ) : ℤ) - 1)) := by ring

omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **Negating the residue flips the sign**: `a + b ≡ 0 (mod p)` → `ξ_a = −ξ_b`. -/
theorem realCyclotomicUnit_neg_modEq (hp : p ≠ 2) {a b : ℕ} (hab : (a + b) % p = 0)
    (ha : a.Coprime p) (hb : b.Coprime p) :
    realCyclotomicUnit hζ a ha = - realCyclotomicUnit hζ b hb := by
  have hp1 : 1 < p := hpri.out.one_lt
  have hmod0 : ∀ {c : ℕ}, c.Coprime p → c % p ≠ 0 := by
    intro c hc h
    have hdvd : p ∣ c := Nat.dvd_iff_mod_eq_zero.mpr h
    have := Nat.eq_one_of_dvd_coprimes hc hdvd (dvd_refl p)
    omega
  have hsum : a % p + b % p = p := by
    have h1 : (a % p + b % p) % p = 0 := by rw [Nat.add_mod] at hab; exact hab
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h1
    have h2 : a % p < p := Nat.mod_lt _ (by omega)
    have h3 : b % p < p := Nat.mod_lt _ (by omega)
    have h4 := hmod0 ha
    have h5 := hmod0 hb
    match k, hk with
    | 0, hk => omega
    | 1, hk => omega
    | (k + 2), hk =>
      have : p * 2 ≤ p * (k + 2) := Nat.mul_le_mul_left p (by omega)
      omega
  rw [realCyclotomicUnit_mod hζ a ha, realCyclotomicUnit_mod hζ b hb]
  exact realCyclotomicUnit_add_eq_p hζ hp hsum (coprime_mod_p ha) (coprime_mod_p hb)

end CyclotomicNT
