import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Toward the Dedekind zeta Euler product  (the real step-2 wall of rung A)

Mathlib has `NumberField.dedekindZeta K s = LSeries (fun n ↦ #{I : absNorm I = n}) s` and the
analytic class-number formula (the residue at `s = 1`), but **no Euler product** for it.  This
file builds it:
`ζ_K(s) = ∏_p (∑_e a(pᵉ) p^{-es}) = ∏_𝔭 (1 - N𝔭^{-s})⁻¹`,  where `a(n) = #{I : absNorm I = n}`.

## Proof strategy
1. **`a` is multiplicative** (this file, the load-bearing brick): for coprime `m, n`,
   `#{I : N I = m·n} = #{I : N I = m} · #{I : N I = n}`.  Bijection `(J,J') ↦ J·J'` with inverse
   `I ↦ (I + (m), I + (n))` — built purely from `absNorm_mem` (`N(I) ∈ I`), Bézout coprimality,
   the modular law, and `N(J) ∣ N((m)) = m^{[K:ℚ]}` (no multiset factorization).
2. Package as a multiplicative `ArithmeticFunction`; twist by `n^{-s}` (completely multiplicative).
3. Summability for `Re s > 1` (from the merged ideal-counting asymptotics).
4. Apply `IsMultiplicative.eulerProduct_tprod` ⟹ `ζ_K = ∏_p (local factor)`.
5. (Optional) refine the rational-prime product to the prime-ideal product `∏_𝔭 (1-N𝔭^{-s})⁻¹`.
-/

open Ideal NumberField
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- **Coprime decomposition of an ideal by its norm.** If `absNorm I = m·n` with `m, n` coprime
and nonzero, then `I = (I + (m))·(I + (n))` and the two factors have norms exactly `m` and `n`.
This is the engine of the multiplicativity of `n ↦ #{I : absNorm I = n}`. -/
private theorem absNorm_decomp {m n : ℕ} (hmn : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0)
    {I : Ideal (𝓞 K)} (hI : absNorm I = m * n) :
    (I ⊔ span {(m : 𝓞 K)}) * (I ⊔ span {(n : 𝓞 K)}) = I ∧
      absNorm (I ⊔ span {(m : 𝓞 K)}) = m ∧ absNorm (I ⊔ span {(n : 𝓞 K)}) = n := by
  set A := span {(m : 𝓞 K)} with hA
  set B := span {(n : 𝓞 K)} with hB
  set J := I ⊔ A with hJ
  set J' := I ⊔ B with hJ'
  -- `(m) ⊔ (n) = ⊤` from `Nat.Coprime`
  have hAB : A ⊔ B = ⊤ := (Ideal.sup_eq_top_iff_isCoprime _ _).mpr hmn.cast
  -- `↑(m·n) = ↑(absNorm I) ∈ I`
  have hmn_mem : (↑(m * n) : 𝓞 K) ∈ I := by have := absNorm_mem I; rwa [hI] at this
  -- `A · B = (m·n) ≤ I`
  have hAB_le : A * B ≤ I := by
    rw [hA, hB, Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul,
      Ideal.span_singleton_le_iff_mem]
    exact hmn_mem
  -- `J · J' ≤ I`
  have hJJ'_le : J * J' ≤ I := by
    rw [hJ, hJ', Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le Ideal.mul_le_right Ideal.mul_le_right) (sup_le Ideal.mul_le_left hAB_le)
  -- `J ⊔ J' = ⊤`
  have hJtop : J ⊔ J' = ⊤ := by
    rw [eq_top_iff, ← hAB]; exact sup_le_sup le_sup_right le_sup_right
  -- `I = J · J'`
  have hII : J * J' = I := by
    refine le_antisymm hJJ'_le ?_
    rw [Ideal.mul_eq_inf_of_coprime hJtop]; exact le_inf le_sup_left le_sup_left
  -- the norm of a principal `(a)` is `a ^ [K:ℚ]`
  have hnorm_span : ∀ a : ℕ, absNorm (span {(a : 𝓞 K)}) = a ^ Module.finrank ℤ (𝓞 K) := by
    intro a
    rw [Ideal.absNorm_span_singleton, Algebra.norm_natCast, Int.natAbs_pow, Int.natAbs_natCast]
  -- `N J ∣ m^d`, hence coprime to `n`;  symmetrically for `J'`
  have hNJ_dvd : absNorm J ∣ m ^ Module.finrank ℤ (𝓞 K) := by
    rw [← hnorm_span m]; exact absNorm_dvd_absNorm_of_le (le_sup_right)
  have hNJ'_dvd : absNorm J' ∣ n ^ Module.finrank ℤ (𝓞 K) := by
    rw [← hnorm_span n]; exact absNorm_dvd_absNorm_of_le (le_sup_right)
  have hNJ_cop : Nat.Coprime (absNorm J) n :=
    Nat.Coprime.coprime_dvd_left hNJ_dvd (hmn.pow_left _)
  have hNJ'_cop : Nat.Coprime (absNorm J') m :=
    Nat.Coprime.coprime_dvd_left hNJ'_dvd (hmn.symm.pow_left _)
  -- `N J · N J' = m·n`
  have hNmul : absNorm J * absNorm J' = m * n := by rw [← map_mul, hII, hI]
  -- pin the two norms
  have hNJ_m : absNorm J ∣ m := hNJ_cop.dvd_of_dvd_mul_right (hNmul ▸ dvd_mul_right _ _)
  have hNJ'_n : absNorm J' ∣ n :=
    hNJ'_cop.dvd_of_dvd_mul_left (hNmul ▸ dvd_mul_left (absNorm J') (absNorm J))
  obtain ⟨k, hk⟩ := hNJ_m
  obtain ⟨j, hj⟩ := hNJ'_n
  have hpos : 0 < absNorm J * absNorm J' := by
    rw [hNmul]; exact Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
  have hexp : absNorm J * absNorm J' = absNorm J * absNorm J' * (k * j) := by
    conv_lhs => rw [hNmul, hk, hj]
    ring
  have hkj : k * j = 1 :=
    (Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact hexp)).symm
  have hk1 : k = 1 := Nat.dvd_one.mp ⟨j, hkj.symm⟩
  have hj1 : j = 1 := Nat.dvd_one.mp ⟨k, by rw [mul_comm]; exact hkj.symm⟩
  refine ⟨hII, ?_, ?_⟩
  · rw [hk, hk1, mul_one]
  · rw [hj, hj1, mul_one]

/-- The `m`-part recovery: if `N J = m`, `N J' = n` with `m, n` coprime, then `J·J' + (m) = J`
(via the modular law and `J' + (m) = ⊤`).  This is the `right_inv` of the counting bijection. -/
private theorem mul_sup_span_left {m n : ℕ} (hmn : Nat.Coprime m n)
    {J J' : Ideal (𝓞 K)} (hJ : absNorm J = m) (hJ' : absNorm J' = n) :
    J * J' ⊔ span {(m : 𝓞 K)} = J := by
  have hmem_m : (m : 𝓞 K) ∈ J := by have := absNorm_mem J; rwa [hJ] at this
  have hmem_n : (n : 𝓞 K) ∈ J' := by have := absNorm_mem J'; rwa [hJ'] at this
  have hsm : span {(m : 𝓞 K)} ≤ J := (Ideal.span_singleton_le_iff_mem J).mpr hmem_m
  have hsn : span {(n : 𝓞 K)} ≤ J' := (Ideal.span_singleton_le_iff_mem J').mpr hmem_n
  have hcop : span {(m : 𝓞 K)} ⊔ span {(n : 𝓞 K)} = ⊤ :=
    (Ideal.sup_eq_top_iff_isCoprime _ _).mpr hmn.cast
  have hJJ'top : J ⊔ J' = ⊤ := by rw [eq_top_iff, ← hcop]; exact sup_le_sup hsm hsn
  have hJ'm_top : J' ⊔ span {(m : 𝓞 K)} = ⊤ := by
    rw [eq_top_iff, ← hcop]; exact sup_le le_sup_right (le_trans hsn le_sup_left)
  rw [Ideal.mul_eq_inf_of_coprime hJJ'top, sup_comm, inf_comm,
    ← sup_inf_assoc_of_le J' hsm, sup_comm (span {(m : 𝓞 K)}) J', hJ'm_top, top_inf_eq]

/-- **Multiplicativity of the ideal-counting function.**  For coprime nonzero `m, n`,
`#{I : N I = m·n} = #{I : N I = m} · #{I : N I = n}` — the load-bearing fact behind the
Dedekind-zeta Euler product. -/
theorem card_setOf_absNorm_eq_mul {m n : ℕ} (hmn : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = m * n}
      = Nat.card {I : Ideal (𝓞 K) // absNorm I = m}
        * Nat.card {I : Ideal (𝓞 K) // absNorm I = n} := by
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun I => (⟨I.1 ⊔ span {(m : 𝓞 K)}, (absNorm_decomp hmn hm hn I.2).2.1⟩,
                         ⟨I.1 ⊔ span {(n : 𝓞 K)}, (absNorm_decomp hmn hm hn I.2).2.2⟩)
      invFun := fun p => ⟨p.1.1 * p.2.1, by rw [map_mul, p.1.2, p.2.2]⟩
      left_inv := fun I => Subtype.ext (absNorm_decomp hmn hm hn I.2).1
      right_inv := fun p => ?_ }
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact mul_sup_span_left hmn p.1.2 p.2.2
  · show p.1.1 * p.2.1 ⊔ span {(n : 𝓞 K)} = p.2.1
    rw [mul_comm p.1.1 p.2.1]
    exact mul_sup_span_left hmn.symm p.2.2 p.1.2

/-- There is exactly one ideal of norm `1`, namely `⊤`. -/
theorem card_setOf_absNorm_eq_one :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = 1} = 1 := by
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun I J => ?_⟩, ⟨⊤, absNorm_eq_one_iff.mpr rfl⟩⟩
  exact Subtype.ext ((absNorm_eq_one_iff.mp I.2).trans (absNorm_eq_one_iff.mp J.2).symm)

/-- The ideal-counting function `n ↦ #{I : absNorm I = n}` as an `ArithmeticFunction ℕ`
(overriding the value `1` at `0` to `0`, as required; this does not affect the `L`-series). -/
noncomputable def idealCount (K : Type*) [Field K] [NumberField K] : ArithmeticFunction ℕ where
  toFun n := if n = 0 then 0 else Nat.card {I : Ideal (𝓞 K) // absNorm I = n}
  map_zero' := if_pos rfl

theorem idealCount_apply (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    idealCount K n = if n = 0 then 0 else Nat.card {I : Ideal (𝓞 K) // absNorm I = n} := rfl

theorem idealCount_apply_of_ne_zero (K : Type*) [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    idealCount K n = Nat.card {I : Ideal (𝓞 K) // absNorm I = n} := by
  rw [idealCount_apply, if_neg hn]

/-- **The ideal-counting function is a multiplicative arithmetic function.** -/
theorem isMultiplicative_idealCount (K : Type*) [Field K] [NumberField K] :
    (idealCount K).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [idealCount_apply_of_ne_zero K one_ne_zero, card_setOf_absNorm_eq_one], ?_⟩
  intro m n hm hn hmn
  rw [idealCount_apply_of_ne_zero K (mul_ne_zero hm hn), idealCount_apply_of_ne_zero K hm,
    idealCount_apply_of_ne_zero K hn, card_setOf_absNorm_eq_mul hmn hm hn]

/-- The Dedekind-zeta summand `n ↦ #{I : N I = n} · n^{-s}` as an `ArithmeticFunction ℂ`. -/
noncomputable def dedekindSummand (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    ArithmeticFunction ℂ where
  toFun n := (idealCount K n : ℂ) * (n : ℂ) ^ (-s)
  map_zero' := by simp

theorem dedekindSummand_apply (K : Type*) [Field K] [NumberField K] (s : ℂ) (n : ℕ) :
    dedekindSummand K s n = (idealCount K n : ℂ) * (n : ℂ) ^ (-s) := rfl

/-- **The Dedekind-zeta summand is multiplicative** (counting function × completely-multiplicative
`n^{-s}`). -/
theorem isMultiplicative_dedekindSummand (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    (dedekindSummand K s).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [dedekindSummand_apply, (isMultiplicative_idealCount K).map_one]; simp
  · intro m n hm hn hmn
    have hcpow : ((m * n : ℕ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
      simpa only [Nat.cast_mul, Complex.ofReal_natCast] using
        Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n) (-s)
    simp only [dedekindSummand_apply]
    rw [(isMultiplicative_idealCount K).2 hmn, hcpow]
    push_cast
    ring

open Finset Filter Topology Asymptotics in
/-- **Summability for `Re s > 1`.** The Dedekind-zeta `L`-series of the ideal-counting
coefficients converges for `1 < Re s`: the partial sums `∑_{k≤n} a(k) = #{nonzero I : N I ≤ n}`
are `O(n)` (merged asymptotics `tendsto_norm_le_div_atTop₀`), so `LSeriesSummable_of_sum_norm_bigO`
applies. -/
theorem lSeriesSummable_idealCount (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((idealCount K n : ℝ) : ℂ)) s := by
  -- partial sum of the counting function = number of nonzero ideals of norm `≤ n`
  have hnat : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealCount K k
      = Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ n} := by
    intro n
    rw [Finset.sum_congr rfl fun k hk => idealCount_apply_of_ne_zero K
        (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hk).1),
      ← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq fun k _ => Ideal.finite_setOf_absNorm_eq k]
    simp [Set.coe_eq_subtype]
  -- hence the (real) partial sums tend to a constant after dividing by `n`
  have htend : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / (n : ℝ))
      atTop (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
    simp only [Function.comp_apply, Nat.cast_le]
    congr 1
    rw [← Nat.cast_sum, hnat n]
  -- so they are `O(n)`, giving summability
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) =O[atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) :=
    isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (r := 1)
      (htend.congr fun n => by simp [Real.rpow_one])
  exact LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun _ => Nat.cast_nonneg _) zero_le_one hs

/-- **The Dedekind-zeta Euler product** (rational-prime form), valid for `Re s > 1`:
`∏_p (∑_e a(pᵉ) p^{-es}) = ζ_K(s)` where `a(n) = #{I : absNorm I = n}`.  This is the
genuinely-missing-from-Mathlib step-2 result, obtained from `IsMultiplicative.eulerProduct_tprod`
applied to the multiplicative summand, with summability from `lSeriesSummable_idealCount`. -/
theorem dedekindZeta_eulerProduct (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, ∑' e : ℕ, dedekindSummand K s (p ^ e) = dedekindZeta K s := by
  -- the summand is exactly the `L`-series term of the (real-cast) ideal-counting coefficients
  have heqterm : ∀ n, dedekindSummand K s n
      = LSeries.term (fun m => ((idealCount K m : ℝ) : ℂ)) s n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [dedekindSummand_apply, LSeries.term_zero]; simp
    · rw [dedekindSummand_apply, LSeries.term_of_ne_zero hn, Complex.ofReal_natCast,
        Complex.cpow_neg, div_eq_mul_inv]
  -- norm-summability (ℂ is finite-dim over ℝ, so `summable_norm_iff` applies)
  have hsum : Summable (fun n => ‖dedekindSummand K s n‖) := by
    have hLS := lSeriesSummable_idealCount K hs
    rw [LSeriesSummable, ← summable_norm_iff] at hLS
    exact hLS.congr fun n => by rw [heqterm n]
  rw [ArithmeticFunction.IsMultiplicative.eulerProduct_tprod
    (isMultiplicative_dedekindSummand K s) hsum]
  calc ∑' n, dedekindSummand K s n
      = ∑' n, LSeries.term (fun m => ((idealCount K m : ℝ) : ℂ)) s n := tsum_congr heqterm
    _ = LSeries (fun m => ((idealCount K m : ℝ) : ℂ)) s := rfl
    _ = LSeries (fun m => ((Nat.card {I : Ideal (𝓞 K) // absNorm I = m} : ℕ) : ℂ)) s :=
        LSeries_congr
          (fun {n} hn => by rw [idealCount_apply_of_ne_zero K hn, Complex.ofReal_natCast]) s
    _ = dedekindZeta K s := rfl

/-- The summand equals the `L`-series term of the (real-cast) ideal-counting coefficients. -/
theorem dedekindSummand_eq_term (K : Type*) [Field K] [NumberField K] (s : ℂ) (n : ℕ) :
    dedekindSummand K s n = LSeries.term (fun m => ((idealCount K m : ℝ) : ℂ)) s n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [dedekindSummand_apply, LSeries.term_zero]; simp
  · rw [dedekindSummand_apply, LSeries.term_of_ne_zero hn, Complex.ofReal_natCast,
      Complex.cpow_neg, div_eq_mul_inv]

/-- The Dedekind-zeta summand is summable for `Re s > 1`. -/
theorem summable_dedekindSummand (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) : Summable (dedekindSummand K s) := by
  have hLS := lSeriesSummable_idealCount K hs
  rw [LSeriesSummable] at hLS
  exact hLS.congr fun n => (dedekindSummand_eq_term K s n).symm
