import CyclotomicNT.DedekindEulerProduct
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Local Euler factor of the Dedekind zeta function (analytic side)

Toward the Euler matching `ζ_K = ∏_χ L(s,χ)` (rung A step 4 of the Iwasawa ladder): the local
factor of `ζ_K` at a rational prime `p` is `∑_e idealCount(pᵉ)·(pᵉ)^{-s}`.  For an **unramified**
prime that splits into `g` primes each of residue degree `f` (so `f·g = [K:ℚ]`), the number of
ideals of norm `pᵉ` is the negative-binomial coefficient `C(e/f + g−1, g−1)` (when `f ∣ e`, else 0):
an ideal of norm `pᵉ` is `∏ 𝔭ᵢ^{aᵢ}` with `∑ aᵢ = e/f`.

This file supplies the **analytic half**: given that ideal count (the number-theoretic input, left
    as
a hypothesis `hcount`), the local factor equals `(1 − (p^{-s})^f)^{-g}` — matching the local factor
`∏_χ (1 − χ(p)·p^{-s})^{-1}` of `∏_χ L` (via `AbelianLFactorization.prod_one_sub_C_apply_mul_X`,
`(1−X^f)^g`).  The negative-binomial sum is Mathlib's
`hasSum_choose_mul_geometric_of_norm_lt_one`. -/

open Finset Filter Topology Complex

namespace CyclotomicNT

/-- `((pᵉ : ℕ) : ℂ)^{-s} = ((p:ℂ)^{-s})^e` — pulling the natural power out of the `cpow`
(via the nonnegative-real product rule, by induction on `e`). -/
private theorem natCast_pow_cpow_neg (p : ℕ) (s : ℂ) (e : ℕ) :
    ((p ^ e : ℕ) : ℂ) ^ (-s) = (((p : ℂ)) ^ (-s)) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hcpow : ((p ^ e * p : ℕ) : ℂ) ^ (-s)
        = ((p ^ e : ℕ) : ℂ) ^ (-s) * ((p : ℕ) : ℂ) ^ (-s) := by
      simpa only [Nat.cast_mul, Complex.ofReal_natCast] using
        Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg (p ^ e)) (Nat.cast_nonneg p) (-s)
    rw [pow_succ, hcpow, ih, pow_succ]

/-- **Negative-binomial local factor (analytic brick).**  A power series supported on the multiples
of `f`, with negative-binomial coefficients `C(e/f + k, k)`, sums to `(1 − Y^f)^{-(k+1)}`.
Reindex `e = f·m` and apply `hasSum_choose_mul_geometric_of_norm_lt_one`. -/
theorem tsum_localFactor {Y : ℂ} (hY : ‖Y‖ < 1) (f k : ℕ) (hf : 0 < f) :
    ∑' e : ℕ, (if f ∣ e then ((e / f + k).choose k : ℂ) else 0) * Y ^ e
      = 1 / (1 - Y ^ f) ^ (k + 1) := by
  have hYf : ‖Y ^ f‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hY hf.ne'
  have hsupp : Function.support
      (fun e => (if f ∣ e then ((e / f + k).choose k : ℂ) else 0) * Y ^ e)
      ⊆ Set.range (fun m => f * m) := by
    intro e he
    simp only [Function.mem_support, ne_eq] at he
    have hd : f ∣ e := by by_contra h; exact he (by rw [if_neg h, zero_mul])
    obtain ⟨c, rfl⟩ := hd
    exact ⟨c, rfl⟩
  rw [← (mul_right_injective₀ hf.ne').tsum_eq hsupp,
      ← hasSum_choose_mul_geometric_of_norm_lt_one k hYf |>.tsum_eq]
  refine tsum_congr (fun m => ?_)
  rw [if_pos (dvd_mul_right f m), Nat.mul_div_cancel_left m hf, pow_mul]

/-- **Local Euler factor of `ζ_K` at `p`** (modulo the ideal count).  Given the negative-binomial
ideal count `idealCount(pᵉ) = C(e/f + g−1, g−1)` for `f ∣ e` (else 0) — the number-theoretic input
from the splitting of the unramified prime `p` into `g` primes of residue degree `f` — the local
factor equals `(1 − (p^{-s})^f)^{-g}`.  Directly pluggable into `dedekindZeta_eulerProduct`. -/
theorem tsum_dedekindSummand_prime_pow (K : Type*) [Field K] [NumberField K] (s : ℂ)
    (p : ℕ) (hY : ‖(p : ℂ) ^ (-s)‖ < 1) (f g : ℕ) (hf : 0 < f) (hg : 1 ≤ g)
    (hcount : ∀ e : ℕ,
      idealCount K (p ^ e) = if f ∣ e then (e / f + (g - 1)).choose (g - 1) else 0) :
    ∑' e : ℕ, dedekindSummand K s (p ^ e) = 1 / (1 - ((p : ℂ) ^ (-s)) ^ f) ^ g := by
  have key : ∀ e : ℕ, dedekindSummand K s (p ^ e)
      = (if f ∣ e then ((e / f + (g - 1)).choose (g - 1) : ℂ) else 0) * ((p : ℂ) ^ (-s)) ^ e := by
    intro e
    rw [dedekindSummand_apply, hcount e, natCast_pow_cpow_neg p s e]
    split_ifs <;> push_cast <;> ring
  rw [tsum_congr key, tsum_localFactor hY f (g - 1) hf, Nat.sub_add_cancel hg]

end CyclotomicNT
