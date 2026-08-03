import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

/-!
# A power-sum vanishing lemma over `ZMod p` (Thm 8.14, piece 3a-iii)

The half-range power sum `∑_{a=1}^{(p−1)/2} a^k` vanishes mod `p` for even `k` with `0 < k < p−1`.

This is the fact that kills the leftover `ξ_g^{−S}` factor when computing `σ_g(Eᵢ)` in `E/E^p`:
with `k = p−1−i` (even for even `i`, odd `p`) and `S = ∑_{a=1}^{(p−1)/2} a^{p−1−i}`, we get `S ≡ 0`.

Proof: the full nonzero-range sum `∑_{x : ZMod p} x^k = 0` (`FiniteField.sum_pow_lt_card_sub_one`,
as `k < p−1`); the half-range doubles to the full range via the involution `a ↦ p−a`
(`(p−a)^k = (−a)^k = a^k` since `k` is even); and `2 ≠ 0` cancels.
-/

namespace CyclotomicNT

open Finset

/-- `∑_{a=1}^{(p−1)/2} a^k ≡ 0 (mod p)` for `p` an odd prime, `k` even, `0 < k < p−1`. -/
theorem half_sum_pow_eq_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (k : ℕ)
    (hk0 : 0 < k) (hkp : k < p - 1) (hke : Even k) :
    ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), ((a : ZMod p)) ^ k = 0 := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  have hp1 : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out (p := p.Prime)).odd_of_ne_two hp2)
  have h2le : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have h2 : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    intro hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
  have hrange : ∑ a ∈ Finset.range p, ((a : ZMod p)) ^ k = 0 := by
    have hcard : Fintype.card (ZMod p) = p := ZMod.card p
    have hfull : ∑ x : ZMod p, x ^ k = 0 :=
      FiniteField.sum_pow_lt_card_sub_one (ZMod p) k (by rw [hcard]; exact hkp)
    rw [← hfull]
    refine Finset.sum_nbij' (fun a => (a : ZMod p)) (fun x => x.val)
      (fun a _ => mem_univ _) (fun x _ => mem_range.mpr (ZMod.val_lt x))
      (fun a ha => ?_) (fun x _ => ?_) (fun a _ => rfl)
    · rw [mem_range] at ha; exact ZMod.val_natCast_of_lt ha
    · exact ZMod.natCast_rightInverse x
  have hIcc : ∑ a ∈ Finset.Icc 1 (p - 1), ((a : ZMod p)) ^ k = 0 := by
    rw [← hrange]
    apply Finset.sum_subset
    · intro a ha; rw [mem_Icc] at ha; rw [mem_range]; omega
    · intro a ha hna; rw [mem_range] at ha; rw [mem_Icc] at hna
      have : a = 0 := by omega
      subst this; simp [zero_pow hk0.ne']
  have hsplit : ∑ a ∈ Finset.Icc 1 (p - 1), ((a : ZMod p)) ^ k
      = 2 * ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), ((a : ZMod p)) ^ k := by
    have hunion : Finset.Icc 1 (p - 1)
        = Finset.Icc 1 ((p - 1) / 2) ∪ Finset.Icc ((p - 1) / 2 + 1) (p - 1) := by
      ext a; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    rw [hunion, Finset.sum_union (by
      rw [Finset.disjoint_left]; intro a ha hb
      simp only [Finset.mem_Icc] at ha hb; omega)]
    have hrefl : ∑ a ∈ Finset.Icc ((p - 1) / 2 + 1) (p - 1), ((a : ZMod p)) ^ k
        = ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), ((a : ZMod p)) ^ k := by
      refine Finset.sum_nbij' (fun a => p - a) (fun a => p - a) ?_ ?_ ?_ ?_ ?_
      · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha; show p - (p - a) = a; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha; show p - (p - a) = a; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha
        have hcast : ((p - a : ℕ) : ZMod p) = -(a : ZMod p) := by
          rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
        rw [hcast, hke.neg_pow]
    rw [hrefl]; ring
  rw [hsplit] at hIcc
  exact (mul_eq_zero.mp hIcc).resolve_left h2

end CyclotomicNT
