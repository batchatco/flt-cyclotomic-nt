import CyclotomicNT.CyclotomicIdealCount
import CyclotomicNT.DedekindFactorization
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Local Euler factors of `ζ_{ℚ(ζ_p)}` and `∏_χ L(s,χ)` coincide

The payoff of the two-sided build: at every prime `q ≠ p` the `ζ_K` local Euler factor
(`tsum_dedekindSummand_cyclotomic_unramified'`, `= 1/(1−(q^{-s})^f)^{φ(p)/f}`) equals the
    `q`-factor of
`∏_{χ mod p} L(s,χ)` (`DedekindFactorization.prod_char_factor_prime`, `=
    ((1−(q^{-s})^f)^{(p−1)/f})⁻¹`),
since `φ(p) = p − 1` for `p` prime.  This is the term-by-term agreement underlying
`ζ_{ℚ(ζ_p)}(s) · (1 − p^{-s}) = ∏_{χ mod p} L(s,χ)` (the full identity then needs only the
    tprod-level
assembly and the single ramified prime `q = p`). -/

open NumberField Ideal

namespace CyclotomicNT

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K]

/-- **Local Euler factors match.**  For a prime `q ≠ p` (with `‖q^{-s}‖ < 1`), the `ζ_{ℚ(ζ_p)}`
    local
factor `∑'_e dedekindSummand(qᵉ)` equals the `q`-factor `∏_χ (1 − χ(q)·q^{-s})⁻¹` of `∏_χ
L(s,χ)`. -/
theorem local_factor_match (s : ℂ) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hY : ‖(q : ℂ) ^ (-s)‖ < 1) :
    ∑' e : ℕ, dedekindSummand K s (q ^ e)
      = ∏ χ : DirichletCharacter ℂ p, (1 - χ (q : ZMod p) * (q : ℂ) ^ (-s))⁻¹ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hnd : ¬ q ∣ p := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp h)
  rw [tsum_dedekindSummand_cyclotomic_unramified' s hq hnd hY,
    DedekindFactorization.prod_char_factor_prime hq hqp, Nat.totient_prime Fact.out, one_div]

/-- **The ramified local factor at `q = p`.**  In `ℚ(ζ_p)` the prime `p` is totally ramified (one
prime of norm `p`, residue degree `1`), so `idealCount(pᵉ) = 1` for all `e` and the local factor is
`∑'_e dedekindSummand(pᵉ) = (1 − p^{-s})⁻¹`.  This is the factor the `∏_χ L`-side LACKS at `p`
(`prod_char_factor_ramified` gives `1` there) — the source of the `(1 − p^{-s})` in
`ζ_K · (1 − p^{-s}) = ∏_χ L`. -/
theorem tsum_dedekindSummand_cyclotomic_ramified (s : ℂ) (hY : ‖(p : ℂ) ^ (-s)‖ < 1) :
    ∑' e : ℕ, dedekindSummand K s (p ^ e) = (1 - (p : ℂ) ^ (-s))⁻¹ := by
  have hdeg : ∀ Q ∈ primesOver (Ideal.span {(p : ℤ)}) (𝓞 K),
      (Ideal.span {(p : ℤ)}).inertiaDeg Q = 1 := by
    rintro Q ⟨hQP, hQlo⟩
    haveI := hQP; haveI := hQlo
    exact IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime p K Q
  have hg : Nat.card (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) = 1 := by
    rw [Nat.card_coe_set_eq]; exact IsCyclotomicExtension.Rat.ncard_primesOver_of_prime p K
  have hcount : ∀ e : ℕ, idealCount K (p ^ e)
      = if (1 : ℕ) ∣ e then (e / 1 + (1 - 1)).choose (1 - 1) else 0 :=
    fun e => idealCount_prime_pow (e := e) Fact.out one_pos one_pos hdeg hg
  rw [tsum_dedekindSummand_prime_pow K s p hY 1 1 one_pos le_rfl hcount, pow_one, pow_one, one_div]

open scoped LSeries.notation in
/-- **`ζ_{ℚ(ζ_p)}(s) · (1 − p^{-s}) = ∏_{χ mod p} L(s,χ)`** for `Re s > 1`.  Both sides are Euler
products over rational primes; the local factors coincide at every `q ≠ p` (`local_factor_match`),
and at the ramified `q = p` the `ζ_K` factor `(1 − p^{-s})⁻¹` exceeds the `∏_χ L` factor `1` by
    exactly
`(1 − p^{-s})`.  Formally `B(q) = A(q)·c(q)` with `A` the `ζ_K` factor, `B` the `∏_χ L` factor, and
`c` equal to `(1 − p^{-s})` at `p` and `1` elsewhere; then `∏ B = (∏ A)·(∏ c) = ζ_K·(1 −
p^{-s})`. -/
theorem prod_dirichletL_eq_dedekindZeta_mul (s : ℂ) (hs : 1 < s.re) :
    ∏ χ : DirichletCharacter ℂ p, (L ↗χ s) = dedekindZeta K s * (1 - (p : ℂ) ^ (-s)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hnorm : ∀ n : ℕ, n.Prime → ‖(n : ℂ) ^ (-s)‖ < 1 := by
    intro n hn
    rw [Complex.norm_natCast_cpow_of_pos hn.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn.one_lt) (by linarith)
  have hpne : (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have hh := hnorm p Fact.out; rw [← h, norm_one] at hh; exact lt_irrefl 1 hh
  set A : Nat.Primes → ℂ := fun q => ∑' e : ℕ, dedekindSummand K s ((q : ℕ) ^ e) with hA
  set c : Nat.Primes → ℂ := fun q => if (q : ℕ) = p then (1 - (p : ℂ) ^ (-s)) else 1 with hc
  have hsumN : Summable (fun n => ‖dedekindSummand K s n‖) :=
    summable_norm_iff.mpr (summable_dedekindSummand K hs)
  have hAmul : Multipliable A :=
    (ArithmeticFunction.IsMultiplicative.eulerProduct_hasProd
      (isMultiplicative_dedekindSummand K s) hsumN).multipliable
  have hc1 : ∀ q : Nat.Primes, q ≠ (⟨p, Fact.out⟩ : Nat.Primes) → c q = 1 := by
    intro q hq
    rw [hc]; exact if_neg (fun h => hq (Subtype.ext h))
  have hc_hasProd : HasProd c (1 - (p : ℂ) ^ (-s)) := by
    have h := hasProd_single (⟨p, Fact.out⟩ : Nat.Primes) hc1
    rwa [show c (⟨p, Fact.out⟩ : Nat.Primes) = 1 - (p : ℂ) ^ (-s) from by simp [hc]] at h
  have hcmul : Multipliable c := hc_hasProd.multipliable
  have hBAc : ∀ q : Nat.Primes,
      (∏ χ : DirichletCharacter ℂ p, (1 - χ (q : ZMod p) * (q : ℂ) ^ (-s))⁻¹) = A q * c q := by
    intro q
    by_cases hqp : (q : ℕ) = p
    · have hB1 : (∏ χ : DirichletCharacter ℂ p, (1 - χ (q : ZMod p) * (q : ℂ) ^ (-s))⁻¹) = 1 := by
        rw [show (q : ZMod p) = (p : ZMod p) from by rw [hqp]]
        exact DedekindFactorization.prod_char_factor_ramified _
      have hAp : A q = (1 - (p : ℂ) ^ (-s))⁻¹ := by
        change (∑' e : ℕ, dedekindSummand K s ((q : ℕ) ^ e)) = (1 - (p : ℂ) ^ (-s))⁻¹
        rw [hqp]; exact tsum_dedekindSummand_cyclotomic_ramified s (hnorm p Fact.out)
      have hcq : c q = 1 - (p : ℂ) ^ (-s) := if_pos hqp
      rw [hB1, hAp, hcq, inv_mul_cancel₀ hpne]
    · have hcq : c q = 1 := if_neg hqp
      rw [hcq, mul_one]
      change (∏ χ : DirichletCharacter ℂ p, (1 - χ (q : ZMod p) * (q : ℂ) ^ (-s))⁻¹)
        = ∑' e : ℕ, dedekindSummand K s ((q : ℕ) ^ e)
      exact (local_factor_match s q.2 hqp (hnorm (q : ℕ) q.2)).symm
  rw [DedekindFactorization.prod_dirichletL_eq_tprod hs, tprod_congr hBAc,
    Multipliable.tprod_mul hAmul hcmul, hc_hasProd.tprod_eq]
  congr 1
  exact dedekindZeta_eulerProduct K hs

open scoped LSeries.notation Classical in
/-- **The cyclotomic factorization, canonical form:** `ζ_{ℚ(ζ_p)}(s) = ζ(s) · ∏_{χ ≠ 1} L(s,χ)` for
`Re s > 1`.  Splits the principal character `χ = 1` off `prod_dirichletL_eq_dedekindZeta_mul`, using
`L(s, 1_p) = (1 − p^{-s})·ζ(s)` (Mathlib `LFunctionTrivChar_eq_mul_riemannZeta`, `primeFactors p =
    {p}`)
and cancelling the common `(1 − p^{-s})`.  This is the textbook statement
`ζ_{ℚ(ζ_p)} = ζ · ∏_{χ ≠ χ₀} L(·, χ)` (Washington (4.3) / the analytic backbone of Thm 8.2). -/
theorem dedekindZeta_eq_riemannZeta_mul_prod (s : ℂ) (hs : 1 < s.re) :
    dedekindZeta K s
      = riemannZeta s * ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p), (L ↗χ s) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl 1 hs
  have hpne : (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have hh : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (Fact.out : p.Prime).pos, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (Fact.out : p.Prime).one_lt)
        (by linarith)
    rw [← h, norm_one] at hh; exact lt_irrefl 1 hh
  -- the principal character's L-series
  have hχ1 : (L ↗(1 : DirichletCharacter ℂ p) s) = (1 - (p : ℂ) ^ (-s)) * riemannZeta s := by
    rw [← DirichletCharacter.LFunction_eq_LSeries (1 : DirichletCharacter ℂ p) hs,
      show DirichletCharacter.LFunction (1 : DirichletCharacter ℂ p) s
        = DirichletCharacter.LFunctionTrivChar p s from rfl,
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1,
      (Fact.out : p.Prime).primeFactors, Finset.prod_singleton]
  -- split off `χ = 1` and combine with the main identity, then cancel `(1 − p^{-s})`
  have hmain := prod_dirichletL_eq_dedekindZeta_mul (p := p) (K := K) s hs
  have hsplit : (∏ χ : DirichletCharacter ℂ p, L ↗χ s)
      = (L ↗(1 : DirichletCharacter ℂ p) s)
        * ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p), L ↗χ s :=
    (Finset.mul_prod_erase Finset.univ (fun χ : DirichletCharacter ℂ p => L ↗χ s)
      (Finset.mem_univ _)).symm
  rw [hsplit, hχ1] at hmain
  refine mul_right_cancel₀ hpne ?_
  rw [← hmain]; ring

end CyclotomicNT
