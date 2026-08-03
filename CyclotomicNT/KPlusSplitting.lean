import CyclotomicNT.KPlusGalois
import CyclotomicNT.KPlusBasic
import CyclotomicNT.EvenCharLocalFactor
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Splitting of rational primes in `K⁺ = maximalRealSubfield ℚ(ζ_p)`

For a prime `q ≠ p` with `g^j = q` in `(ℤ/p)ˣ`:

* `q` is unramified in `K⁺`, with common inertia degree `f⁺ = addOrderOf (j : ℤ/m)` (the order
  of the `±q`-class, `m = (p−1)/2`) and `m/f⁺` primes above it;
* `p` is totally ramified in `K⁺` (one prime, inertia degree `1`).

Route (all at the `In`-level, no choice of primes):
`fIn(q, 𝓞K⁺)·fIn(Q⁺, 𝓞K) = fIn(q, 𝓞K) = ord_q` (Mathlib's `inertiaDegIn_mul_inertiaDegIn` +
the cyclotomic values), where `fIn(Q⁺, 𝓞K) = #stab_{Gal(K/K⁺)}(Q) ∈ {1,2}` is `2` iff
conjugation fixes `Q` iff `−1 ∈ ⟨q⟩` (Mathlib's `galEquivZMod_stabilizer` + `conj ↦ −1`)
iff `ord_q` is even; a gcd computation turns `ord_q/(2 or 1)` into `m / gcd m j` uniformly. -/

open NumberField MulAction Ideal IsCyclotomicExtension.Rat
open scoped Pointwise

namespace CyclotomicNT

section GroupTheory

variable {p : ℕ} [hpri : Fact p.Prime]

/-- In `(ℤ/p)ˣ`, `−1` lies in a subgroup iff the subgroup has even order (Cauchy + the unique
element of order `2` in a cyclic group). -/
theorem neg_one_mem_iff_even_card {H : Subgroup (ZMod p)ˣ} (hp : p ≠ 2) :
    (-1 : (ZMod p)ˣ) ∈ H ↔ 2 ∣ Nat.card H := by
  classical
  have hlt : 2 < p := by have := hpri.out.two_le; omega
  constructor
  · intro hmem
    have horder : orderOf (⟨-1, hmem⟩ : H) = 2 := by
      have h1 : ((⟨-1, hmem⟩ : H) : (ZMod p)ˣ) = -1 := rfl
      rw [← orderOf_injective H.subtype Subtype.coe_injective ⟨-1, hmem⟩]
      change orderOf (-1 : (ZMod p)ˣ) = 2
      refine orderOf_eq_prime (by rw [neg_one_sq]) ?_
      intro h
      haveI : Fact (2 < p) := ⟨hlt⟩
      exact ZMod.neg_one_ne_one (by
        have := congrArg Units.val h
        rwa [Units.val_neg, Units.val_one] at this)
    rw [← horder]
    exact orderOf_dvd_natCard _
  · intro hdvd
    -- Cauchy: an element of order 2 in `H`; it equals `−1` by the field argument
    rw [Nat.card_eq_fintype_card] at hdvd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := H) 2 hdvd
    have hy2 : ((y : (ZMod p)ˣ) : ZMod p) ^ 2 = 1 := by
      have h2 : (y : (ZMod p)ˣ) ^ 2 = 1 := by
        have hpow := pow_orderOf_eq_one y
        rw [hy] at hpow
        have := congrArg (Subgroup.subtype H) hpow
        rwa [map_pow, map_one] at this
      rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
    have hy1 : (y : (ZMod p)ˣ) ≠ 1 := by
      intro h1
      have : y = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hy
      omega
    -- `x² = 1` in the field forces `x = ±1`
    have hfact : (((y : (ZMod p)ˣ) : ZMod p) - 1) * (((y : (ZMod p)ˣ) : ZMod p) + 1) = 0 := by
      linear_combination hy2
    rcases mul_eq_zero.mp hfact with h | h
    · exact absurd (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h)) hy1
    · have hyneg : (y : (ZMod p)ˣ) = -1 := Units.ext (by
        rw [Units.val_neg, Units.val_one]
        linear_combination h)
      rw [← hyneg]
      exact y.2

/-- **The gcd bridge**: `(2m/gcd(2m,j)) / (2 if even else 1) = m/gcd(m,j)` — the dichotomy
between split and inert resolves to a uniform formula. -/
theorem gcd_bridge {m : ℕ} (j : ℕ) (hm : m ≠ 0) :
    (2 * m / Nat.gcd (2 * m) j) / (if 2 ∣ 2 * m / Nat.gcd (2 * m) j then 2 else 1)
      = m / Nat.gcd m j := by
  set d1 := Nat.gcd m j with hd1
  set d2 := Nat.gcd (2 * m) j with hd2
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
  have hd1_pos : 0 < d1 := Nat.gcd_pos_of_pos_left j hm_pos
  have hd2_pos : 0 < d2 := Nat.gcd_pos_of_pos_left j (by positivity)
  have hd2_dvd : d2 ∣ 2 * m := Nat.gcd_dvd_left _ _
  have hd1_dvd_d2 : d1 ∣ d2 :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left m j).mul_left 2) (Nat.gcd_dvd_right m j)
  have hd2_dvd_2d1 : d2 ∣ 2 * d1 := by
    rw [hd1, ← Nat.gcd_mul_left 2 m j]
    exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
      ((Nat.gcd_dvd_right (2 * m) j).trans (dvd_mul_left j 2))
  -- evenness of `2m/d₂` ⟺ `d₂ ∣ m`
  have heven : (2 ∣ 2 * m / d2) ↔ d2 ∣ m := by
    constructor
    · rintro ⟨k, hk⟩
      have h2m : 2 * m = d2 * (2 * k) := Nat.eq_mul_of_div_eq_right hd2_dvd hk
      have h2m' : 2 * m = 2 * (d2 * k) := by rw [h2m]; ring
      exact ⟨k, Nat.eq_of_mul_eq_mul_left two_pos h2m'⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hk, show 2 * (d2 * k) = d2 * (2 * k) by ring, Nat.mul_div_cancel_left _ hd2_pos]
  by_cases hcase : d2 ∣ m
  · rw [if_pos (heven.mpr hcase)]
    have heq : d1 = d2 :=
      Nat.dvd_antisymm hd1_dvd_d2 (Nat.dvd_gcd hcase (Nat.gcd_dvd_right _ _))
    rw [← heq, Nat.mul_div_assoc 2 (heq ▸ hcase : d1 ∣ m), Nat.mul_div_cancel_left _ two_pos]
  · rw [if_neg (fun h => hcase (heven.mp h))]
    obtain ⟨t, ht⟩ := hd1_dvd_d2
    have ht2 : t ∣ 2 := (Nat.mul_dvd_mul_iff_left hd1_pos).mp
      (by rw [← ht]; rwa [mul_comm 2 d1] at hd2_dvd_2d1)
    rcases (Nat.dvd_prime Nat.prime_two).mp ht2 with rfl | rfl
    · rw [mul_one] at ht
      exact absurd (ht ▸ Nat.gcd_dvd_left m j) hcase
    · rw [ht, show d1 * 2 = 2 * d1 by ring, Nat.mul_div_mul_left m d1 two_pos, Nat.div_one]

end GroupTheory

section Splitting

attribute [local instance] Ideal.Quotient.field

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {g : (ZMod p)ˣ}

/-- The two conjugation actions (over `ℚ` and over `K⁺`) move ideals of `𝓞 K` identically. -/
theorem conjGal_smul_ideal (Q : Ideal (𝓞 K)) :
    (conjGal (K := K)) • Q = (NumberField.IsCMField.complexConj K) • Q := by
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have heq : (conjGal (K := K))⁻¹ • x = (NumberField.IsCMField.complexConj K)⁻¹ • x := rfl
  rw [heq]

/-- `Gal(K/K⁺)` has two elements. -/
theorem card_gal_over_real : Nat.card (K ≃ₐ[maximalRealSubfield K] K) = 2 := by
  have h := NumberField.IsCMField.orderOf_complexConj K
  rw [← Nat.card_zpowers, NumberField.IsCMField.zpowers_complexConj_eq_top] at h
  rwa [Subgroup.card_top] at h

/-- The stabilizer dichotomy in the two-element group `Gal(K/K⁺)`. -/
theorem card_stabilizer_gal_over_real (Q : Ideal (𝓞 K)) :
    Nat.card (MulAction.stabilizer (K ≃ₐ[maximalRealSubfield K] K) Q)
      = if (NumberField.IsCMField.complexConj K) • Q = Q then 2 else 1 := by
  by_cases hfix : (NumberField.IsCMField.complexConj K) • Q = Q
  · rw [if_pos hfix]
    have htop : MulAction.stabilizer (K ≃ₐ[maximalRealSubfield K] K) Q = ⊤ := by
      rw [eq_top_iff, ← NumberField.IsCMField.zpowers_complexConj_eq_top]
      exact Subgroup.zpowers_le.mpr hfix
    rw [htop, Subgroup.card_top, card_gal_over_real]
  · rw [if_neg hfix]
    -- a proper subgroup of a 2-element group is trivial
    have hdvd : Nat.card (MulAction.stabilizer (K ≃ₐ[maximalRealSubfield K] K) Q)
        ∣ Nat.card (K ≃ₐ[maximalRealSubfield K] K) := Subgroup.card_subgroup_dvd_card _
    rw [card_gal_over_real] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact h1
    · exfalso
      have htop : MulAction.stabilizer (K ≃ₐ[maximalRealSubfield K] K) Q = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by rw [h2, card_gal_over_real])
      exact hfix (by
        have := htop ▸ Subgroup.mem_top (NumberField.IsCMField.complexConj K)
        exact this)

/-- `q ≠ p` is unramified in `K⁺` (In-level). -/
theorem ramificationIdxIn_real_eq_one {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    (span {(q : ℤ)}).ramificationIdxIn (𝓞 (maximalRealSubfield K)) = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  haveI := isGalois_maximalRealSubfield (K := K) (hpri := hpri)
  haveI : (span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hq).irreducible
  have hnd : ¬ q ∣ p := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hpri.out).mp h)
  obtain ⟨⟨Qp, hQp1, hQp2⟩⟩ :=
    (span {(q : ℤ)}).nonempty_primesOver (S := 𝓞 (maximalRealSubfield K))
  haveI := hQp1
  haveI := hQp2
  have htower := ramificationIdxIn_mul_ramificationIdxIn' (p := span {(q : ℤ)}) (P := Qp)
    ((maximalRealSubfield K) ≃ₐ[ℚ] (maximalRealSubfield K)) (𝓞 K)
    (K ≃ₐ[ℚ] K) (K ≃ₐ[maximalRealSubfield K] K)
  rw [ramificationIdxIn_eq_of_not_dvd q K hnd] at htower
  exact Nat.dvd_one.mp ⟨_, htower.symm⟩

/-- **The inertia degree of `q ≠ p` in `K⁺` is the order of the `±q` class**:
`fIn(q, 𝓞 K⁺) = addOrderOf (j : ℤ/m)` where `g^j = q` in `(ℤ/p)ˣ`. -/
theorem inertiaDegIn_real_eq (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp2 : p ≠ 2)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) {j : ℕ}
    (hj : g ^ j = ZMod.unitOfCoprime q ((Nat.coprime_primes hq hpri.out).mpr hqp)) :
    (span {(q : ℤ)}).inertiaDegIn (𝓞 (maximalRealSubfield K))
      = addOrderOf ((j : ZMod ((p - 1) / 2))) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  haveI := isGalois_maximalRealSubfield (K := K) (hpri := hpri)
  haveI : (span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hq).irreducible
  set hcop := (Nat.coprime_primes hq hpri.out).mpr hqp with hhcop
  have hnd : ¬ q ∣ p := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hpri.out).mp h)
  have hm0 : (p - 1) / 2 ≠ 0 := half_pred_ne_zero hp2
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp2)
  have hq0 : (span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  -- choose primes `Q over Qp over q`
  obtain ⟨⟨Qp, hQp1, hQp2⟩⟩ :=
    (span {(q : ℤ)}).nonempty_primesOver (S := 𝓞 (maximalRealSubfield K))
  haveI := hQp1
  haveI := hQp2
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ := Qp.nonempty_primesOver (S := 𝓞 K)
  haveI := hQ1
  haveI := hQ2
  haveI : Q.LiesOver (span {(q : ℤ)}) := Ideal.LiesOver.trans Q Qp _
  have hQp_ne : Qp ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hq0 Qp
  have hQ_ne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hQp_ne Q
  haveI : Qp.IsMaximal := Ideal.IsPrime.isMaximal hQp1 hQp_ne
  haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal hQ1 hQ_ne
  -- the K-side In-values and the towers
  have hfK : (span {(q : ℤ)}).inertiaDegIn (𝓞 K) = orderOf ((q : ZMod p)) :=
    inertiaDegIn_eq_of_not_dvd q K hnd
  have heK : (span {(q : ℤ)}).ramificationIdxIn (𝓞 K) = 1 :=
    ramificationIdxIn_eq_of_not_dvd q K hnd
  have htower_f := inertiaDegIn_mul_inertiaDegIn (p := span {(q : ℤ)}) (P := Qp)
    ((maximalRealSubfield K) ≃ₐ[ℚ] (maximalRealSubfield K)) (𝓞 K)
    (K ≃ₐ[ℚ] K) (K ≃ₐ[maximalRealSubfield K] K)
  have htower_e := ramificationIdxIn_mul_ramificationIdxIn' (p := span {(q : ℤ)}) (P := Qp)
    ((maximalRealSubfield K) ≃ₐ[ℚ] (maximalRealSubfield K)) (𝓞 K)
    (K ≃ₐ[ℚ] K) (K ≃ₐ[maximalRealSubfield K] K)
  rw [heK] at htower_e
  rw [hfK] at htower_f
  have he' : Qp.ramificationIdxIn (𝓞 K) = 1 :=
    Nat.dvd_one.mp ⟨_, by rw [mul_comm] at htower_e; exact htower_e.symm⟩
  -- `f' = #stab ∈ {1,2}` by the conjugation dichotomy
  have hstab := Ideal.card_stabilizer_eq Qp hQp_ne Q
    (G := (K ≃ₐ[maximalRealSubfield K] K))
  rw [he', one_mul, card_stabilizer_gal_over_real] at hstab
  -- the dictionary: conj fixes `Q` ⟺ `−1 ∈ ⟨q⟩` ⟺ `2 ∣ ord_q`
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  have hdict : ((NumberField.IsCMField.complexConj K) • Q = Q)
      ↔ (-1 : (ZMod p)ˣ) ∈ Subgroup.zpowers (ZMod.unitOfCoprime q hcop) := by
    rw [← conjGal_smul_ideal, show ((conjGal (K := K)) • Q = Q)
        ↔ conjGal (K := K) ∈ MulAction.stabilizer (K ≃ₐ[ℚ] K) Q from Iff.rfl,
      ← galEquivZMod_stabilizer p K q Q hcop, MulEquiv.coe_mapSubgroup,
      Subgroup.mem_map_equiv]
    have hconj : (galEquivZMod p K).symm
        ((galEquivZMod p K) (conjGal (K := K))) = conjGal (K := K) :=
      MulEquiv.symm_apply_apply _ _
    rw [galEquivZMod_conjGal hζ] at hconj
    rw [hconj]
  -- orders
  have horder : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hpri.out]
  have hord_chain : orderOf ((q : ZMod p)) = (p - 1) / Nat.gcd (p - 1) j := by
    rw [← ZMod.coe_unitOfCoprime q hcop, orderOf_units, ← hj, orderOf_pow, horder]
  -- assemble: `f⁺·f' = ord` with `f' = if 2 ∣ ord then 2 else 1`
  simp only [hdict, neg_one_mem_iff_even_card hp2, Nat.card_zpowers, ← hj, orderOf_pow,
    horder] at hstab
  rw [hord_chain] at htower_f
  have hpm : p - 1 = 2 * ((p - 1) / 2) := by omega
  have hf'pos : 0 < Qp.inertiaDegIn (𝓞 K) := by
    rw [← hstab]
    split <;> norm_num
  rw [ZMod.addOrderOf_coe j hm0, ← gcd_bridge j hm0, ← hpm, hstab, ← htower_f,
    Nat.mul_div_cancel _ hf'pos]

/-- **Per-prime inertia degree** of `q ≠ p` in `K⁺`. -/
theorem inertiaDeg_real_eq (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp2 : p ≠ 2)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) {j : ℕ}
    (hj : g ^ j = ZMod.unitOfCoprime q ((Nat.coprime_primes hq hpri.out).mpr hqp))
    (Qp : Ideal (𝓞 (maximalRealSubfield K))) [Qp.IsPrime] [Qp.LiesOver (span {(q : ℤ)})] :
    (span {(q : ℤ)}).inertiaDeg Qp = addOrderOf ((j : ZMod ((p - 1) / 2))) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI := isGalois_maximalRealSubfield (K := K) (hpri := hpri)
  rw [← inertiaDegIn_eq_inertiaDeg (span {(q : ℤ)}) Qp
    ((maximalRealSubfield K) ≃ₐ[ℚ] (maximalRealSubfield K))]
  exact inertiaDegIn_real_eq hgen hp2 hq hqp hj

/-- **The number of primes of `K⁺` above `q ≠ p`** is `m / f⁺`. -/
theorem ncard_primesOver_real (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp2 : p ≠ 2)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) {j : ℕ}
    (hj : g ^ j = ZMod.unitOfCoprime q ((Nat.coprime_primes hq hpri.out).mpr hqp)) :
    ((span {(q : ℤ)}).primesOver (𝓞 (maximalRealSubfield K))).ncard
      = ((p - 1) / 2) / addOrderOf ((j : ZMod ((p - 1) / 2))) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero ((p - 1) / 2) := ⟨half_pred_ne_zero hp2⟩
  haveI := isGalois_maximalRealSubfield (K := K) (hpri := hpri)
  haveI : (span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hq).irreducible
  have hq0 : (span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  have hfund := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hq0
    (𝓞 (maximalRealSubfield K)) ((maximalRealSubfield K) ≃ₐ[ℚ] (maximalRealSubfield K))
  rw [ramificationIdxIn_real_eq_one hq hqp, one_mul, inertiaDegIn_real_eq hgen hp2 hq hqp hj,
    IsGaloisGroup.card_eq_finrank ((maximalRealSubfield K) ≃ₐ[ℚ] (maximalRealSubfield K))
      ℚ (maximalRealSubfield K),
    finrank_maximalRealSubfield hp2] at hfund
  exact (Nat.div_eq_of_eq_mul_left (addOrderOf_pos _) hfund.symm).symm

/-- **The ramified prime**: above `p`, `K⁺` has a single prime, with inertia degree `1` and
ramification index `m`. -/
theorem splitting_real_at_p (hp2 : p ≠ 2) :
    (span {(p : ℤ)}).inertiaDegIn (𝓞 (maximalRealSubfield K)) = 1
      ∧ ((span {(p : ℤ)}).primesOver (𝓞 (maximalRealSubfield K))).ncard = 1 := by
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  haveI := isGalois_maximalRealSubfield (K := K) (hpri := hpri)
  haveI : (span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (Nat.prime_iff_prime_int.mp hpri.out).irreducible
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hpri.out.ne_zero
  have hm0 : (p - 1) / 2 ≠ 0 := half_pred_ne_zero hp2
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp2)
  -- primes
  obtain ⟨⟨Qp, hQp1, hQp2⟩⟩ :=
    (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 (maximalRealSubfield K))
  haveI := hQp1
  haveI := hQp2
  have hQp_ne : Qp ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Qp
  haveI : Qp.IsMaximal := Ideal.IsPrime.isMaximal hQp1 hQp_ne
  -- the K-side values and towers
  have hfK : (span {(p : ℤ)}).inertiaDegIn (𝓞 K) = 1 := inertiaDegIn_eq_of_prime p K
  have heK : (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) = p - 1 :=
    ramificationIdxIn_eq_of_prime p K
  have htower_f := inertiaDegIn_mul_inertiaDegIn (p := span {(p : ℤ)}) (P := Qp)
    ((maximalRealSubfield K) ≃ₐ[ℚ] (maximalRealSubfield K)) (𝓞 K)
    (K ≃ₐ[ℚ] K) (K ≃ₐ[maximalRealSubfield K] K)
  have htower_e := ramificationIdxIn_mul_ramificationIdxIn' (p := span {(p : ℤ)}) (P := Qp)
    ((maximalRealSubfield K) ≃ₐ[ℚ] (maximalRealSubfield K)) (𝓞 K)
    (K ≃ₐ[ℚ] K) (K ≃ₐ[maximalRealSubfield K] K)
  rw [hfK] at htower_f
  rw [heK] at htower_e
  have hf : (span {(p : ℤ)}).inertiaDegIn (𝓞 (maximalRealSubfield K)) = 1 :=
    Nat.dvd_one.mp ⟨_, htower_f.symm⟩
  refine ⟨hf, ?_⟩
  -- fundamental identities at `K⁺/ℚ` and at `K/K⁺`
  have hfund := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp0
    (𝓞 (maximalRealSubfield K)) ((maximalRealSubfield K) ≃ₐ[ℚ] (maximalRealSubfield K))
  rw [hf, mul_one,
    IsGaloisGroup.card_eq_finrank ((maximalRealSubfield K) ≃ₐ[ℚ] (maximalRealSubfield K))
      ℚ (maximalRealSubfield K),
    finrank_maximalRealSubfield hp2] at hfund
  have hfund2 := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hQp_ne
    (𝓞 K) (K ≃ₐ[maximalRealSubfield K] K)
  rw [card_gal_over_real] at hfund2
  -- `e' ∣ 2` from the second identity, and the arithmetic squeeze
  have he'_dvd : Qp.ramificationIdxIn (𝓞 K) ∣ 2 :=
    ⟨(Qp.primesOver (𝓞 K)).ncard * Qp.inertiaDegIn (𝓞 K), by rw [← hfund2]; ring⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp he'_dvd with h1 | h2
  · -- `e' = 1` forces `e⁺ = p−1 > m`, impossible
    exfalso
    rw [h1, mul_one] at htower_e
    have hle : (span {(p : ℤ)}).ramificationIdxIn (𝓞 (maximalRealSubfield K)) ∣ (p - 1) / 2 :=
      ⟨((span {(p : ℤ)}).primesOver (𝓞 (maximalRealSubfield K))).ncard,
        by rw [← hfund]; ring⟩
    have := Nat.le_of_dvd (by omega) hle
    omega
  · -- `e' = 2` gives `e⁺ = m`, so `ncard = 1`
    rw [h2] at htower_e
    have he : (span {(p : ℤ)}).ramificationIdxIn (𝓞 (maximalRealSubfield K)) = (p - 1) / 2 := by
      omega
    rw [he] at hfund
    have hm_pos : 0 < (p - 1) / 2 := Nat.pos_of_ne_zero hm0
    exact Nat.eq_of_mul_eq_mul_right hm_pos (by omega)

end Splitting

end CyclotomicNT
