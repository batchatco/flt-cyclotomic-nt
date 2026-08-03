import CyclotomicNT.KPlusSplitting
import CyclotomicNT.CyclotomicClassNumber

/-!
# `ζ_{K⁺}(s)·(1−p^{−s}) = ∏_{χ even} L(s,χ)` and the residue `∏_{χ even ≠1} L(1,χ)`

The `K⁺`-analogue of `CyclotomicEulerMatch`/`CyclotomicClassNumber`: the Euler factors of
`ζ_{K⁺}` (computed from the splitting data of `KPlusSplitting` through the generic counting
framework `idealCount_prime_pow`/`tsum_dedekindSummand_prime_pow`) match the even-character
local products (`prod_even_char_one_sub`) factor by factor; the ramified prime `p` contributes
`(1−p^{−s})⁻¹` on the zeta side and `1` on the character side.  Splitting off the principal
character and taking `s → 1⁺` gives

  `(dedekindZeta_residue K⁺ : ℂ) = ∏_{χ even, χ ≠ 1} L(1,χ)`.
-/

open NumberField Ideal Finset
open scoped LSeries.notation

namespace CyclotomicNT

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {g : (ZMod p)ˣ}

section LocalFactors

open scoped Classical in
/-- **The unramified local factor match for `K⁺`**: at a prime `q ≠ p`,
`∑'_e a_{K⁺}(qᵉ)q^{−es} = ∏_{χ even}(1−χ(q)q^{−s})⁻¹`. -/
theorem local_factor_match_real [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp2 : p ≠ 2) (s : ℂ) {q : ℕ}
    (hq : q.Prime) (hqp : q ≠ p) (hY : ‖(q : ℂ) ^ (-s)‖ < 1) :
    ∑' e : ℕ, dedekindSummand (maximalRealSubfield K) s (q ^ e)
      = ∏ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even),
          (1 - χ (q : ZMod p) * (q : ℂ) ^ (-s))⁻¹ := by
  have hcop : q.Coprime p := (Nat.coprime_primes hq hpri.out).mpr hqp
  obtain ⟨j, hj0⟩ := mem_powers_iff_mem_zpowers.mpr (hgen (ZMod.unitOfCoprime q hcop))
  have hj : g ^ j = ZMod.unitOfCoprime q hcop := hj0
  have hm0 : (p - 1) / 2 ≠ 0 := half_pred_ne_zero hp2
  set f := addOrderOf ((j : ZMod ((p - 1) / 2))) with hf
  have hf_pos : 0 < f := addOrderOf_pos _
  have hf_dvd : f ∣ (p - 1) / 2 := addOrderOf_dvd_card _
  have hg_pos : 1 ≤ ((p - 1) / 2) / f :=
    Nat.one_le_div_iff hf_pos |>.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hf_dvd)
  -- the zeta-side local factor from the splitting data
  have hdeg : ∀ Q ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (maximalRealSubfield K)),
      (Ideal.span {(q : ℤ)}).inertiaDeg Q = f := by
    rintro Q ⟨hQ1, hQ2⟩
    haveI := hQ1
    haveI := hQ2
    exact inertiaDeg_real_eq hgen hp2 hq hqp hj Q
  have hcard : Nat.card
      (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (maximalRealSubfield K)))
      = ((p - 1) / 2) / f := by
    rw [Nat.card_coe_set_eq]
    exact ncard_primesOver_real hgen hp2 hq hqp hj
  have hcount : ∀ e : ℕ, idealCount (maximalRealSubfield K) (q ^ e)
      = if f ∣ e then (e / f + (((p - 1) / 2) / f - 1)).choose (((p - 1) / 2) / f - 1)
        else 0 :=
    fun e => idealCount_prime_pow hq hf_pos (by omega) hdeg hcard
  rw [tsum_dedekindSummand_prime_pow _ s q hY f (((p - 1) / 2) / f) hf_pos hg_pos hcount]
  -- the character-side local factor
  rw [Finset.prod_inv_distrib]
  have hchi := prod_even_char_one_sub hgen hp2 hj ((q : ℂ) ^ (-s))
  rw [ZMod.coe_unitOfCoprime] at hchi
  rw [hchi, one_div]

/-- **The ramified local factor for `K⁺`**: `∑'_e a_{K⁺}(pᵉ)p^{−es} = (1−p^{−s})⁻¹`
(one prime above `p`, residue degree `1`). -/
theorem tsum_dedekindSummand_real_ramified (hp2 : p ≠ 2) (s : ℂ)
    (hY : ‖(p : ℂ) ^ (-s)‖ < 1) :
    ∑' e : ℕ, dedekindSummand (maximalRealSubfield K) s (p ^ e)
      = (1 - (p : ℂ) ^ (-s))⁻¹ := by
  haveI := isGalois_maximalRealSubfield (K := K) (hpri := hpri)
  obtain ⟨hf1, hg1⟩ := splitting_real_at_p (K := K) hp2
  have hdeg : ∀ Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (maximalRealSubfield K)),
      (Ideal.span {(p : ℤ)}).inertiaDeg Q = 1 := by
    rintro Q ⟨hQ1, hQ2⟩
    haveI := hQ1
    haveI := hQ2
    rw [← inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) Q
      ((maximalRealSubfield K) ≃ₐ[ℚ] (maximalRealSubfield K))]
    exact hf1
  have hcard : Nat.card
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (maximalRealSubfield K))) = 1 := by
    rw [Nat.card_coe_set_eq]
    exact hg1
  have hcount : ∀ e : ℕ, idealCount (maximalRealSubfield K) (p ^ e)
      = if (1 : ℕ) ∣ e then (e / 1 + (1 - 1)).choose (1 - 1) else 0 :=
    fun e => idealCount_prime_pow hpri.out one_pos one_pos hdeg hcard
  rw [tsum_dedekindSummand_prime_pow _ s p hY 1 1 one_pos le_rfl hcount, pow_one, pow_one,
    one_div]

open scoped Classical in
/-- The even-character `L`-product as an Euler product over rational primes. -/
theorem prod_even_dirichletL_eq_tprod {s : ℂ} (hs : 1 < s.re) :
    ∏ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even), (L ↗χ s)
      = ∏' q : Nat.Primes, ∏ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even),
          (1 - χ ((q : ℕ) : ZMod p) * (q : ℂ) ^ (-s))⁻¹ := by
  have hmul : ∀ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even),
      Multipliable (fun q : Nat.Primes => (1 - χ ((q : ℕ) : ZMod p) * (q : ℂ) ^ (-s))⁻¹) :=
    fun χ _ => (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable
  rw [Multipliable.tprod_finsetProd hmul]
  exact Finset.prod_congr rfl
    (fun χ _ => (DirichletCharacter.LSeries_eulerProduct_tprod χ hs).symm)

open scoped Classical in
/-- **`∏_{χ even} L(s,χ) = ζ_{K⁺}(s)·(1−p^{−s})`** for `Re s > 1`. -/
theorem prod_even_dirichletL_eq_dedekindZeta_mul [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp2 : p ≠ 2) (s : ℂ) (hs : 1 < s.re) :
    ∏ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even), (L ↗χ s)
      = dedekindZeta (maximalRealSubfield K) s * (1 - (p : ℂ) ^ (-s)) := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  have hnorm : ∀ n : ℕ, n.Prime → ‖(n : ℂ) ^ (-s)‖ < 1 := by
    intro n hn
    rw [Complex.norm_natCast_cpow_of_pos hn.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn.one_lt) (by linarith)
  have hpne : (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hh := hnorm p hpri.out
    rw [← h, norm_one] at hh
    exact lt_irrefl 1 hh
  set A : Nat.Primes → ℂ :=
    fun q => ∑' e : ℕ, dedekindSummand (maximalRealSubfield K) s ((q : ℕ) ^ e) with hA
  set c : Nat.Primes → ℂ := fun q => if (q : ℕ) = p then (1 - (p : ℂ) ^ (-s)) else 1 with hc
  have hsumN : Summable (fun n => ‖dedekindSummand (maximalRealSubfield K) s n‖) :=
    summable_norm_iff.mpr (summable_dedekindSummand (maximalRealSubfield K) hs)
  have hAmul : Multipliable A :=
    (ArithmeticFunction.IsMultiplicative.eulerProduct_hasProd
      (isMultiplicative_dedekindSummand (maximalRealSubfield K) s) hsumN).multipliable
  have hc1 : ∀ q : Nat.Primes, q ≠ (⟨p, hpri.out⟩ : Nat.Primes) → c q = 1 := by
    intro q hq
    rw [hc]
    exact if_neg (fun h => hq (Subtype.ext h))
  have hc_hasProd : HasProd c (1 - (p : ℂ) ^ (-s)) := by
    have h := hasProd_single (⟨p, hpri.out⟩ : Nat.Primes) hc1
    rwa [show c (⟨p, hpri.out⟩ : Nat.Primes) = 1 - (p : ℂ) ^ (-s) from by simp [hc]] at h
  have hcmul : Multipliable c := hc_hasProd.multipliable
  have hBAc : ∀ q : Nat.Primes,
      (∏ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even),
        (1 - χ ((q : ℕ) : ZMod p) * (q : ℂ) ^ (-s))⁻¹) = A q * c q := by
    intro q
    by_cases hqp : (q : ℕ) = p
    · have hB1 : (∏ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even),
          (1 - χ ((q : ℕ) : ZMod p) * (q : ℂ) ^ (-s))⁻¹) = 1 := by
        have hq0 : (((q : ℕ) : ZMod p)) = 0 := by rw [hqp]; exact ZMod.natCast_self p
        simp only [hq0, MulChar.map_zero, zero_mul, sub_zero, inv_one, Finset.prod_const_one]
      have hAp : A q = (1 - (p : ℂ) ^ (-s))⁻¹ := by
        change (∑' e : ℕ, dedekindSummand (maximalRealSubfield K) s ((q : ℕ) ^ e))
          = (1 - (p : ℂ) ^ (-s))⁻¹
        rw [hqp]
        exact tsum_dedekindSummand_real_ramified hp2 s (hnorm p hpri.out)
      have hcq : c q = 1 - (p : ℂ) ^ (-s) := if_pos hqp
      rw [hB1, hAp, hcq, inv_mul_cancel₀ hpne]
    · have hcq : c q = 1 := if_neg hqp
      rw [hcq, mul_one]
      change (∏ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even),
          (1 - χ ((q : ℕ) : ZMod p) * (q : ℂ) ^ (-s))⁻¹)
        = ∑' e : ℕ, dedekindSummand (maximalRealSubfield K) s ((q : ℕ) ^ e)
      exact (local_factor_match_real hgen hp2 s q.2 hqp (hnorm (q : ℕ) q.2)).symm
  rw [prod_even_dirichletL_eq_tprod hs, tprod_congr hBAc,
    Multipliable.tprod_mul hAmul hcmul, hc_hasProd.tprod_eq]
  congr 1
  exact dedekindZeta_eulerProduct (maximalRealSubfield K) hs

open scoped Classical in
/-- **`ζ_{K⁺}(s) = ζ(s)·∏_{χ even ≠ 1} L(s,χ)`** for `Re s > 1`. -/
theorem dedekindZeta_real_eq_riemannZeta_mul_prod [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp2 : p ≠ 2) (s : ℂ) (hs : 1 < s.re) :
    dedekindZeta (maximalRealSubfield K) s
      = riemannZeta s
        * ∏ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even)).erase 1, (L ↗χ s) := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl 1 hs
  have hpne : (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hh : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpri.out.pos, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpri.out.one_lt) (by linarith)
    rw [← h, norm_one] at hh
    exact lt_irrefl 1 hh
  have hχ1 : (L ↗(1 : DirichletCharacter ℂ p) s) = (1 - (p : ℂ) ^ (-s)) * riemannZeta s := by
    rw [← DirichletCharacter.LFunction_eq_LSeries (1 : DirichletCharacter ℂ p) hs,
      show DirichletCharacter.LFunction (1 : DirichletCharacter ℂ p) s
        = DirichletCharacter.LFunctionTrivChar p s from rfl,
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1,
      hpri.out.primeFactors, Finset.prod_singleton]
  have hmain := prod_even_dirichletL_eq_dedekindZeta_mul (K := K) hgen hp2 s hs
  have hone_mem : (1 : DirichletCharacter ℂ p)
      ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_even⟩
  have hsplit : (∏ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even), L ↗χ s)
      = (L ↗(1 : DirichletCharacter ℂ p) s)
        * ∏ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even)).erase 1, L ↗χ s :=
    (Finset.mul_prod_erase _ (fun χ : DirichletCharacter ℂ p => L ↗χ s) hone_mem).symm
  rw [hsplit, hχ1] at hmain
  refine mul_right_cancel₀ hpne ?_
  rw [← hmain]
  ring

open Filter Topology in
open scoped Classical in
/-- **The residue of `ζ_{K⁺}` is the product of the even nontrivial `L(1,χ)`**:
`(dedekindZeta_residue K⁺ : ℂ) = ∏_{χ even ≠1} L(1,χ)`. -/
theorem dedekindZeta_residue_real_eq_prod [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp2 : p ≠ 2) :
    ((dedekindZeta_residue (maximalRealSubfield K) : ℝ) : ℂ)
      = ∏ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even)).erase 1,
          DirichletCharacter.LFunction χ 1 := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  have hcast_ne : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : (1 : ℝ) < s := hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have hs2 : s = 1 := by exact_mod_cast h
    linarith
  have hcast_nhds : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) :=
    hcast_ne.mono_right nhdsWithin_le_nhds
  have hzeta : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ)) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp hcast_ne
  have hLχ : ∀ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even)).erase 1,
      Tendsto (fun s : ℝ => DirichletCharacter.LFunction χ (s : ℂ)) (𝓝[>] 1)
        (𝓝 (DirichletCharacter.LFunction χ 1)) := fun χ hχ =>
    ((DirichletCharacter.differentiable_LFunction
      (Finset.ne_of_mem_erase hχ)).continuous.tendsto 1).comp hcast_nhds
  have hprod : Tendsto
      (fun s : ℝ => ∏ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even)).erase 1,
        DirichletCharacter.LFunction χ (s : ℂ)) (𝓝[>] 1)
      (𝓝 (∏ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even)).erase 1,
        DirichletCharacter.LFunction χ 1)) :=
    tendsto_finsetProd _ hLχ
  have hRHS : Tendsto
      (fun s : ℝ => ((s : ℂ) - 1) * dedekindZeta (maximalRealSubfield K) (s : ℂ)) (𝓝[>] 1)
      (𝓝 (∏ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even)).erase 1,
        DirichletCharacter.LFunction χ 1)) := by
    have hmul := hzeta.mul hprod
    rw [one_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsre : 1 < (s : ℂ).re := by rw [Complex.ofReal_re]; exact hs
    rw [dedekindZeta_real_eq_riemannZeta_mul_prod (K := K) hgen hp2 (s : ℂ) hsre,
      Finset.prod_congr rfl
        (fun χ _ => (DirichletCharacter.LFunction_eq_LSeries χ hsre).symm)]
    ring
  exact tendsto_nhds_unique
    (tendsto_sub_one_mul_dedekindZeta_nhdsGT (maximalRealSubfield K)) hRHS

end LocalFactors

end CyclotomicNT
