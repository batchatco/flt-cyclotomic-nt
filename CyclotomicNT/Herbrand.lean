import CyclotomicNT.HerbrandEigen
import CyclotomicNT.HerbrandBernoulli
import CyclotomicNT.EigenProjection
import CyclotomicNT.MirimanoffSum
import CyclotomicNT.BernoulliMod

/-!
# Herbrand's theorem (Washington, Thm 6.17, the Stickelberger direction)

If the class group of `ℚ(ζ_p)` contains a nontrivial element of order `p` on which the Galois
group acts through the `k`-th power of the cyclotomic character (`σ_a · cl = cl^{a^k}`, odd
`k`, `3 ≤ k ≤ p−2`), then `p` divides the numerator of the Bernoulli number `B_{p−k}` — i.e.
`p − k` is an irregular index for `p`.

Assembly: the eigenspace projection of Stickelberger (`eigenClass_dvd_sum`, HerbrandEigen)
kills the integer `∑_a a^{−k}⌊c·a/p⌋` for every `c`; the analytic congruence
(`den_mul_sum_floor_modEq`, HerbrandBernoulli) identifies that sum with
`(c^{p−k} − 1)·B_{p−k}` modulo `p`; choosing `c` a primitive root makes `c^{p−k} − 1` a
`p`-unit, forcing `p ∣ num B_{p−k}`. -/

open Finset NumberField IsCyclotomicExtension.Rat
open CyclotomicNT.QiCert (IsIrregularIndex)

namespace CyclotomicNT

variable {p : ℕ} [hpri : Fact p.Prime] {k₀ : Type*} [Field k₀] [NumberField k₀]
  [IsCyclotomicExtension {p} ℚ k₀]

/-- **Herbrand's theorem** (Washington Thm 6.17, easy direction): a nontrivial order-`p`
eigenclass of odd weight `k`, `3 ≤ k ≤ p − 2`, forces `p ∣ num B_{p−k}` — that is, `p − k`
is an irregular index. -/
theorem herbrand {k : ℕ} (hk_odd : Odd k) (hk3 : 3 ≤ k) (hkp : k ≤ p - 2)
    {cl : ClassGroup (𝓞 k₀)} (hcl1 : cl ≠ 1) (hclp : cl ^ p = 1)
    (heig : IsEigenClass p k cl) :
    IsIrregularIndex p (p - k) := by
  classical
  have hp5 : 5 ≤ p := by
    have h2 := hpri.out.two_le
    omega
  have hp2 : p ≠ 2 := by omega
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  set m : ℕ := p - 1 - k with hm
  have hm1 : m + 1 = p - k := by omega
  have hmp : m + 1 ≤ p - 2 := by omega
  have hm_pos : 1 ≤ m := by omega
  -- the primitive root
  obtain ⟨g, hgen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  set c : ℕ := ((g : ZMod p)).val with hc_def
  have hc : ¬ p ∣ c := by
    rw [hc_def]
    intro hdvd
    have hz : ((g : ZMod p)).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    exact g.ne_zero (by rwa [← ZMod.val_eq_zero])
  have hcast : ((c : ℕ) : ZMod p) = (g : ZMod p) := by
    rw [hc_def, ZMod.natCast_val, ZMod.cast_id]
  -- Step 1: the Stickelberger kill
  have hkill := eigenClass_dvd_sum hcl1 hclp heig c
  -- Step 2: transfer to the `range p` power sum, in `ZMod p`
  have hU : ((∑ a ∈ Finset.range p, a ^ m * (c * a / p) : ℕ) : ZMod p) = 0 := by
    have hSkill : ((∑ a : (ZMod p)ˣ,
        ((a⁻¹ ^ k : (ZMod p)ˣ) : ZMod p).val * (c * (a : ZMod p).val / p) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ p).mpr hkill
    rw [← hSkill]
    -- both sides as `ZMod p` sums
    have hrange : ((∑ a ∈ Finset.range p, a ^ m * (c * a / p) : ℕ) : ZMod p)
        = ∑ x : ZMod p, x ^ m * ((c * x.val / p : ℕ) : ZMod p) := by
      push_cast
      rw [← sum_val_eq_sum_range (p := p)
        (fun a => ((a : ZMod p)) ^ m * ((c * a / p : ℕ) : ZMod p))]
      exact Finset.sum_congr rfl fun x _ => by rw [ZMod.natCast_val, ZMod.cast_id]
    have hunits : ((∑ a : (ZMod p)ˣ,
        ((a⁻¹ ^ k : (ZMod p)ˣ) : ZMod p).val * (c * (a : ZMod p).val / p) : ℕ) : ZMod p)
        = ∑ x : ZMod p, x ^ m * ((c * x.val / p : ℕ) : ZMod p) := by
      push_cast [-Nat.cast_sum]
      push_cast
      rw [← sum_units_eq_sum_zmod (p := p)
        (fun x => x ^ m * ((c * x.val / p : ℕ) : ZMod p))
        (by simp [zero_pow (show m ≠ 0 by omega)])]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hu0 : ((u : ZMod p)) ≠ 0 := u.ne_zero
      have hpow : ((u : ZMod p)) ^ m = (((u⁻¹ ^ k : (ZMod p)ˣ) : ZMod p)) := by
        have hfl : ((u : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hu0
        have hsplit : ((u : ZMod p)) ^ m * ((u : ZMod p)) ^ k = 1 := by
          rw [← pow_add, show m + k = p - 1 by omega, hfl]
        have hinv : ((u : ZMod p)) ^ m = (((u : ZMod p)) ^ k)⁻¹ :=
          eq_inv_of_mul_eq_one_left hsplit
        rw [hinv, ← inv_pow]
        push_cast
        rfl
      rw [ZMod.natCast_val, ZMod.cast_id, hpow]
      push_cast
      ring
    rw [hrange, hunits]
  -- Step 3: `T = c^m · U`, hence `T ≡ 0 (mod p)`
  have hT : ((∑ a ∈ Finset.range p, (c * a) ^ m * (c * a / p) : ℕ) : ZMod p) = 0 := by
    have hfac : (∑ a ∈ Finset.range p, (c * a) ^ m * (c * a / p) : ℕ)
        = c ^ m * ∑ a ∈ Finset.range p, a ^ m * (c * a / p) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [mul_pow]; ring
    rw [hfac]
    push_cast [-Nat.cast_sum]
    rw [hU, mul_zero]
  -- Step 4: the analytic congruence forces `p ∣ (c^{m+1} − 1)·num`
  have hcong := den_mul_sum_floor_modEq (p := p) hp2 hmp hc
  have hcongZ := (ZMod.intCast_eq_intCast_iff _ _ _).mpr
    (hcong.of_dvd (by norm_num : ((p : ℤ)) ∣ ((p : ℕ) : ℤ)))
  push_cast [-Nat.cast_sum] at hcongZ
  rw [hT, mul_zero] at hcongZ
  -- `c^{m+1} ≠ 1` in `ZMod p`: the generator has order `p − 1 ∤ p − k`
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hpri.out]
  have hcm : ((c : ZMod p)) ^ (m + 1) ≠ 1 := by
    rw [hcast]
    intro h1
    have hg1 : g ^ (m + 1) = 1 := by
      ext
      push_cast
      exact h1
    have := orderOf_dvd_of_pow_eq_one hg1
    rw [hord] at this
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) this
  have hnum : ((bernoulli (m + 1)).num : ZMod p) = 0 := by
    rcases mul_eq_zero.mp hcongZ.symm with h | h
    · exact absurd (by linear_combination h) hcm
    · exact h
  -- Step 5: package as an irregular index
  have hdvd : (p : ℤ) ∣ (bernoulli (p - k)).num := by
    rw [← hm1]
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hnum
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp2)
  have hkodd : k % 2 = 1 := Nat.odd_iff.mp hk_odd
  exact ⟨Nat.even_iff.mpr (by omega), by omega, by omega, hdvd⟩

/-- **Herbrand via the eigenprojection**: if the weight-`k` eigencomponent of an order-`p`
class is nontrivial (odd `k`, `3 ≤ k ≤ p−2`), then `p − k` is an irregular index.  Together
with `exists_eigenProj_ne_one` this converts any nontrivial order-`p` class into an
irregularity statement at one of its nontrivial weights. -/
theorem herbrand_eigenProj {k : ℕ} (hk_odd : Odd k) (hk3 : 3 ≤ k) (hkp : k ≤ p - 2)
    {cl : ClassGroup (𝓞 k₀)} (hclp : cl ^ p = 1) (hne : eigenProj p k cl ≠ 1) :
    IsIrregularIndex p (p - k) :=
  herbrand hk_odd hk3 hkp hne (eigenProj_pow_p hclp k) (isEigenClass_eigenProj hclp k)

end CyclotomicNT
