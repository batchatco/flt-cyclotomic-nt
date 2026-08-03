import CyclotomicNT.OddLOneValue

/-!
# Toward `L(1, χ)` for even characters — the Gauss-sum Fourier inversion brick

The cyclotomic-unit regulator (the content of `cyclotomic_unit_index`, Washington Thm 8.2) is
`∏_{χ even} L(1,χ)`, and the classical evaluation of even `L(1,χ)` is

  `L(1,χ) = −(τ(χ̄)/p) · ∑_{a=1}^{p-1} χ(a)·log(1 − ζ^a)`     (Dirichlet),

obtained from `L(1,χ) = ∑_n χ(n)/n` by replacing `χ(n)` with its finite
**Fourier expansion** via the
Gauss sum and summing the log series `∑_n z^n/n = −log(1−z)`.

This file provides the purely **algebraic** step — the Fourier/Gauss-sum inversion
`∑_x χ⁻¹(x)·ψ(n·x) = χ(n)·gaussSum(χ⁻¹, ψ)` (a direct consequence of Mathlib's `gaussSum_mulShift`).
The conditionally-convergent boundary value `∑χ(n)/n` via Abel summation (cf. `DirichletAbel.lean`
for the `s=0` analogue) and the complex log series are handled in their own files.
-/

open Complex DirichletCharacter AddChar

namespace CyclotomicNT

variable {p : ℕ} [Fact p.Prime]

/-- **Gauss-sum Fourier inversion** (`p` prime).  For a unit `n` mod `p`,
`gaussSum(χ⁻¹, ψ(n·−)) = χ(n)·gaussSum(χ⁻¹, ψ)`, i.e. `∑_x χ⁻¹(x)·ψ(n·x) = χ(n)·∑_x χ⁻¹(x)·ψ(x)`.
The Fourier-expansion building block for the `L(1,χ)`-as-`∑χ(a)log(1−ζ^a)` formula.  Pure algebra,
from `gaussSum_mulShift` (which gives `χ⁻¹(n)·gaussSum(χ⁻¹, ψ(n·−)) = gaussSum(χ⁻¹, ψ)`) by
multiplying through by `χ(n) = (χ⁻¹(n))⁻¹`. -/
theorem gaussSum_mulShift_inv (χ : DirichletCharacter ℂ p) (n : (ZMod p)ˣ) :
    gaussSum χ⁻¹ (mulShift ZMod.stdAddChar (n : ZMod p))
      = χ (n : ZMod p) * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have h := gaussSum_mulShift χ⁻¹ ZMod.stdAddChar n
  have hu : χ (n : ZMod p) * χ⁻¹ (n : ZMod p) = 1 := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply n.isUnit]
  rw [← h, ← mul_assoc, hu, one_mul]

/-- The sum of `χ` over `p` consecutive integers is `0` (a full residue system mod `p`, and
`∑_{ZMod p} χ = 0` for `χ ≠ 1`). -/
theorem sum_Ico_char_eq_zero (χ : DirichletCharacter ℂ p) (hχ1 : χ ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.Ico M (M + p), χ (n : ZMod p) = 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hinj : ∀ a ∈ Finset.Ico M (M + p), ∀ b ∈ Finset.Ico M (M + p),
      (a : ZMod p) = (b : ZMod p) → a = b := by
    intro a ha b hb hab
    simp only [Finset.mem_Ico] at ha hb
    rw [ZMod.natCast_eq_natCast_iff] at hab
    rcases le_total a b with h | h
    · have hz : b - a = 0 := Nat.eq_zero_of_dvd_of_lt ((Nat.modEq_iff_dvd' h).mp hab) (by omega)
      omega
    · have hz : a - b = 0 :=
        Nat.eq_zero_of_dvd_of_lt ((Nat.modEq_iff_dvd' h).mp hab.symm) (by omega)
      omega
  have himg : (Finset.Ico M (M + p)).image (fun n : ℕ => (n : ZMod p)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (fun a ha b hb => hinj a ha b hb), Nat.card_Ico,
      Nat.add_sub_cancel_left, ZMod.card]
  rw [← MulChar.sum_eq_zero_of_ne_one hχ1, ← himg, Finset.sum_image hinj]

/-- **Character partial-sum bound:** `‖∑_{n<N} χ(n)‖ ≤ p` for `χ ≠ 1`.  The
partial sums are periodic
mod `p` (each block of `p` consecutive sums to `0`), so `S(N) = S(N mod p)`, a sum of `< p` terms of
norm `≤ 1`. -/
theorem norm_sum_char_le (χ : DirichletCharacter ℂ p) (hχ1 : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ (n : ZMod p)‖ ≤ p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set S : ℕ → ℂ := fun N => ∑ n ∈ Finset.range N, χ (n : ZMod p) with hS
  have hper : Function.Periodic S p := by
    intro N
    show (∑ n ∈ Finset.range (N + p), χ (n : ZMod p)) = ∑ n ∈ Finset.range N, χ (n : ZMod p)
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le N) (Nat.le_add_right N p),
      sum_Ico_char_eq_zero χ hχ1 N, add_zero]
  have hmod : (∑ n ∈ Finset.range N, χ (n : ZMod p))
      = ∑ n ∈ Finset.range (N % p), χ (n : ZMod p) := (hper.map_mod_nat N).symm
  rw [hmod]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 (fun n _ => χ.norm_le_one _)).trans ?_
  rw [Finset.card_range, nsmul_eq_mul, mul_one]
  exact_mod_cast le_of_lt (Nat.mod_lt N (Fact.out : p.Prime).pos)

open Filter Topology MeasureTheory Asymptotics Set in
/-- **Integral Abel summation for the character series** (`0 < s`).  The partial sums
`∑_{k≤n} χ(k)/k^s` converge to `−∫₁^∞ (d/dt t^{-s}) · D(⌊t⌋) dt`, where
`D(n)=∑_{k≤n}χ(k)` is bounded
(`norm_sum_char_le`).  Mirror of `DirichletAbel.tendsto_partialSum_sub_integral` with `c = χ(k)`
(complex) and `f = ↑(k^{-s})`.  Boundary term vanishes (`l = 0`) since `D`
bounded and `k^{-s} → 0`. -/
theorem tendsto_partialSum_char_sub_integral (χ : DirichletCharacter ℂ p) (hχ1 : χ ≠ 1)
    (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, (((k : ℝ) ^ (-s) : ℝ) : ℂ) * χ (k : ZMod p))
      atTop (𝓝 (0 - ∫ t in Ioi (1 : ℝ), deriv (fun x : ℝ => (((x ^ (-s) : ℝ)) : ℂ)) t *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, χ (k : ZMod p))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set c : ℕ → ℂ := fun k => χ (k : ZMod p) with hc_def
  set f : ℝ → ℂ := fun x => (((x ^ (-s) : ℝ)) : ℂ) with hf_def
  have hker : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 0 n, c k‖ ≤ (p : ℝ) := by
    intro n
    rw [show Finset.Icc 0 n = Finset.range (n + 1) by
      ext k; rw [Finset.mem_Icc, Finset.mem_range]; omega]
    exact norm_sum_char_le χ hχ1 (n + 1)
  have hc0 : c 0 = 0 := by rw [hc_def]; simp [MulChar.map_zero]
  have hf_hasDeriv : ∀ t ∈ Ici (1 : ℝ),
      HasDerivAt f ((((-s) * t ^ (-s - 1) : ℝ)) : ℂ) t := by
    intro t ht
    have ht0 : t ≠ 0 := by simp only [mem_Ici] at ht; linarith
    exact (Real.hasDerivAt_rpow_const (Or.inl ht0)).ofReal_comp
  have hf_diff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ f t :=
    fun t ht => (hf_hasDeriv t ht).differentiableAt
  have hderiv_eq : ∀ t ∈ Ici (1 : ℝ), deriv f t = (((-s) * t ^ (-s - 1) : ℝ) : ℂ) :=
    fun t ht => (hf_hasDeriv t ht).deriv
  have hcont : ContinuousOn (fun t => (((-s) * t ^ (-s - 1) : ℝ) : ℂ)) (Ici 1) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    apply ContinuousOn.mul continuousOn_const
    intro t ht
    have ht0 : t ≠ 0 := by simp only [mem_Ici] at ht; linarith
    exact (Real.continuousAt_rpow_const t (-s - 1) (Or.inl ht0)).continuousWithinAt
  have hf_int : LocallyIntegrableOn (deriv f) (Ici 1) := by
    refine (hcont.locallyIntegrableOn measurableSet_Ici).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact (hderiv_eq t ht).symm
  have h_lim : Tendsto (fun n : ℕ ↦ f n * ∑ k ∈ Finset.Icc 0 n, c k) atTop (𝓝 0) := by
    have hbound : ∀ n : ℕ, ‖f n * ∑ k ∈ Finset.Icc 0 n, c k‖ ≤ (p : ℝ) * (n : ℝ) ^ (-s) := by
      intro n
      rw [norm_mul]
      have hfn : ‖f n‖ = (n : ℝ) ^ (-s) := by
        rw [hf_def, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      rw [hfn, mul_comm (p : ℝ)]
      exact mul_le_mul_of_nonneg_left (hker n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    refine squeeze_zero_norm hbound ?_
    rw [show (0 : ℝ) = (p : ℝ) * 0 by ring]
    exact Tendsto.const_mul _ ((tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop)
  have hg_dom : (fun t ↦ deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
      =O[atTop] (fun t : ℝ => t ^ (-s - 1)) := by
    rw [isBigO_iff]
    refine ⟨s * p, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have htmem : t ∈ Ici (1 : ℝ) := by simp only [mem_Ici]; exact ht
    have ht0 : (0 : ℝ) ≤ t := by linarith
    have hrpow : (0 : ℝ) ≤ t ^ (-s - 1) := Real.rpow_nonneg ht0 _
    have hB : ‖(t : ℝ) ^ (-s - 1)‖ = t ^ (-s - 1) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hrpow]
    rw [hB, hderiv_eq t htmem, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_pos hs, abs_of_nonneg hrpow]
    calc s * t ^ (-s - 1) * ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖
        ≤ s * t ^ (-s - 1) * (p : ℝ) :=
          mul_le_mul_of_nonneg_left (hker ⌊t⌋₊) (by positivity)
      _ = s * (p : ℝ) * t ^ (-s - 1) := by ring
  have hg_int : IntegrableAtFilter (fun t : ℝ => t ^ (-s - 1)) atTop :=
    ⟨Ioi (1 : ℝ), Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)⟩
  exact tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c hc0 hf_diff hf_int h_lim hg_dom hg_int

open Filter Topology Set in
/-- **`LFunction χ s` as the Abel integral** (`s > 1`).  The naive `L`-series equals the boundary
integral of `tendsto_partialSum_char_sub_integral`, by uniqueness of limits (partial sums of the
absolutely-convergent series converge to `LSeries`, and also to the integral). -/
theorem LFunction_char_eq_integral (χ : DirichletCharacter ℂ p) (hχ1 : χ ≠ 1) (s : ℝ) (hs : 1 < s) :
    DirichletCharacter.LFunction χ (s : ℂ)
      = 0 - ∫ t in Ioi (1 : ℝ), deriv (fun x : ℝ => (((x ^ (-s) : ℝ)) : ℂ)) t *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, χ (k : ZMod p) := by
  have hsre : 1 < ((s : ℂ)).re := by rw [Complex.ofReal_re]; exact hs
  rw [DirichletCharacter.LFunction_eq_LSeries χ hsre]
  have hterm : ∀ k : ℕ, LSeries.term (fun n => χ (n : ZMod p)) (s : ℂ) k
      = (((k : ℝ) ^ (-s) : ℝ) : ℂ) * χ (k : ZMod p) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [LSeries.term, MulChar.map_zero]
    · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      rw [LSeries.term_of_ne_zero (by exact_mod_cast hk.ne') _ _, Complex.ofReal_cpow hkpos.le]
      push_cast
      rw [Complex.cpow_neg, div_eq_mul_inv, mul_comm]
  have hsum := (LSeriesSummable_of_one_lt_re χ hsre).hasSum
  have hcx1 := hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hre := tendsto_partialSum_char_sub_integral χ hχ1 s (by linarith)
  have heq : (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
      LSeries.term (fun m => χ (m : ZMod p)) (s : ℂ) k)
      = (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, (((k : ℝ) ^ (-s) : ℝ) : ℂ) * χ (k : ZMod p)) := by
    funext n
    rw [show Finset.Icc 0 n = Finset.range (n + 1) by
      ext k; rw [Finset.mem_Icc, Finset.mem_range]; omega]
    exact Finset.sum_congr rfl (fun k _ => hterm k)
  rw [Function.comp_def] at hcx1
  simp only [heq] at hcx1
  exact tendsto_nhds_unique hcx1 hre

/-- `deriv (x ↦ ↑(x^{-s})) t = ↑(−s·t^{-s-1})` for `t ≠ 0`. -/
theorem deriv_ofReal_rpow_neg (s : ℝ) {t : ℝ} (ht : t ≠ 0) :
    deriv (fun x : ℝ => (((x ^ (-s) : ℝ)) : ℂ)) t = (((-s) * t ^ (-s - 1) : ℝ) : ℂ) :=
  ((Real.hasDerivAt_rpow_const (Or.inl ht)).ofReal_comp).deriv

open Filter Topology Set MeasureTheory in
/-- **Dominated convergence in `s`** for the character Abel integral: as `s → 1⁺` the integral
`Iχ(s)` tends to `Iχ(1)`.  Dominating function `2p·t^{-2}` (the kernel `D=∑χ(k)` is bounded by `p`,
`norm_sum_char_le`). -/
theorem tendsto_integral_dc_char (χ : DirichletCharacter ℂ p) (hχ1 : χ ≠ 1) :
    Tendsto (fun s : ℝ => ∫ t in Ioi (1 : ℝ),
        deriv (fun x : ℝ => (((x ^ (-s) : ℝ)) : ℂ)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, χ (k : ZMod p))
      (𝓝[>] 1)
      (𝓝 (∫ t in Ioi (1 : ℝ),
        deriv (fun x : ℝ => (((x ^ (-(1 : ℝ)) : ℝ)) : ℂ)) t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, χ (k : ZMod p))) := by
  set D : ℝ → ℂ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, χ (k : ZMod p) with hD_def
  have hker : ∀ t : ℝ, ‖D t‖ ≤ (p : ℝ) := by
    intro t
    show ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, χ (k : ZMod p)‖ ≤ (p : ℝ)
    rw [show Finset.Icc 0 ⌊t⌋₊ = Finset.range (⌊t⌋₊ + 1) by
      ext k; rw [Finset.mem_Icc, Finset.mem_range]; omega]
    exact norm_sum_char_le χ hχ1 _
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun t => 2 * p * t ^ (-(2 : ℝ)))
  · refine Eventually.of_forall (fun s => ?_)
    apply AEStronglyMeasurable.mul
    · apply (ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi).congr
        (ae_restrict_of_forall_mem measurableSet_Ioi
          (fun t ht => (deriv_ofReal_rpow_neg s (by simp only [mem_Ioi] at ht; linarith)).symm))
      apply Complex.continuous_ofReal.comp_continuousOn
      apply ContinuousOn.mul continuousOn_const
      intro t ht
      exact (Real.continuousAt_rpow_const t (-s - 1)
        (Or.inl (by simp only [mem_Ioi] at ht; linarith))).continuousWithinAt
    · exact (Measurable.aestronglyMeasurable
        ((measurable_of_countable (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, χ (k : ZMod p))).comp
          Nat.measurable_floor))
  · have hev : ∀ᶠ s : ℝ in 𝓝[>] 1, s < 2 :=
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [hev, self_mem_nhdsWithin] with s hs2 hs1
    rw [mem_Ioi] at hs1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [mem_Ioi] at ht
    have ht0 : t ≠ 0 := by linarith
    have ht1 : (1 : ℝ) ≤ t := by linarith
    have hrpow : (0 : ℝ) ≤ t ^ (-s - 1) := Real.rpow_nonneg (by linarith) _
    rw [deriv_ofReal_rpow_neg s ht0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_neg,
      abs_of_pos (by linarith : (0 : ℝ) < s), abs_of_nonneg hrpow]
    calc s * t ^ (-s - 1) * ‖D t‖
        ≤ s * t ^ (-s - 1) * (p : ℝ) := mul_le_mul_of_nonneg_left (hker t) (by positivity)
      _ ≤ 2 * t ^ (-(2 : ℝ)) * (p : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul (by linarith)
            (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) hrpow (by norm_num)
      _ = 2 * (p : ℝ) * t ^ (-(2 : ℝ)) := by ring
  · exact (integrableOn_Ioi_rpow_of_lt (show (-(2 : ℝ)) < -1 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)).const_mul (2 * p)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [mem_Ioi] at ht
    have ht0 : t ≠ 0 := by linarith
    have key : Tendsto (fun s : ℝ => (((-s) * t ^ (-s - 1) : ℝ) : ℂ) * D t) (𝓝 (1 : ℝ))
        (𝓝 ((((-(1 : ℝ)) * t ^ (-(1 : ℝ) - 1) : ℝ) : ℂ) * D t)) := by
      apply Tendsto.mul_const
      apply (Complex.continuous_ofReal.tendsto _).comp
      apply Tendsto.mul tendsto_id.neg
      exact (Real.continuous_const_rpow ht0).tendsto _ |>.comp (tendsto_id.neg.sub_const 1)
    simp only [deriv_ofReal_rpow_neg _ ht0]
    exact key.mono_left nhdsWithin_le_nhds

open Filter Topology Set in
/-- **`LFunction χ 1 = ∑'_n χ(n)/n`** (the conditionally-convergent boundary value, sequential
partial sums), for `χ ≠ 1` mod a prime.  The `s → 1⁺` Abel boundary: `LFunction χ s = −Iχ(s)`
(`LFunction_char_eq_integral`, `s>1`) and `LFunction χ` continuous at `1`; `Iχ(s) → Iχ(1)`
(`tendsto_integral_dc_char`); uniqueness gives `LFunction χ 1 = −Iχ(1)`, which the `s=1` Abel
representation (`tendsto_partialSum_char_sub_integral`) equates with the partial-sum limit. -/
theorem tendsto_partialSum_char_LFunction_one (χ : DirichletCharacter ℂ p) (hχ1 : χ ≠ 1) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, (((k : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) * χ (k : ZMod p))
      atTop (𝓝 (DirichletCharacter.LFunction χ 1)) := by
  have hcont : Tendsto (fun s : ℝ => DirichletCharacter.LFunction χ (s : ℂ)) (𝓝[>] 1)
      (𝓝 (DirichletCharacter.LFunction χ 1)) :=
    ((DirichletCharacter.differentiable_LFunction hχ1).continuous.tendsto _).comp
      ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds)
  have hdc := (tendsto_const_nhds (x := (0 : ℂ)) (f := 𝓝[>] (1 : ℝ))).sub
    (tendsto_integral_dc_char χ hχ1)
  have heq_s : Tendsto (fun s : ℝ => DirichletCharacter.LFunction χ (s : ℂ)) (𝓝[>] 1)
      (𝓝 (0 - ∫ t in Ioi (1 : ℝ), deriv (fun x : ℝ => (((x ^ (-(1 : ℝ)) : ℝ)) : ℂ)) t *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, χ (k : ZMod p))) := by
    refine hdc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [mem_Ioi] at hs
    exact (LFunction_char_eq_integral χ hχ1 s hs).symm
  rw [tendsto_nhds_unique hcont heq_s]
  exact tendsto_partialSum_char_sub_integral χ hχ1 1 (by norm_num)

/-- **Fourier expansion of `χ`** (all `a`): `χ(a)·τ(χ⁻¹) = ∑_x χ⁻¹(x)·ψ(a·x)`, `ψ = stdAddChar`.
For `a` a unit this is `gaussSum_mulShift_inv`; for `a = 0` both sides vanish
(`χ(0)=0`, `∑χ⁻¹=0`). -/
theorem char_mul_gaussSum (χ : DirichletCharacter ℂ p) (hχ1 : χ ≠ 1) (a : ZMod p) :
    χ a * gaussSum χ⁻¹ ZMod.stdAddChar = ∑ x : ZMod p, χ⁻¹ x * ZMod.stdAddChar (a * x) := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [MulChar.map_zero, zero_mul,
      show (∑ x : ZMod p, χ⁻¹ x * ZMod.stdAddChar (0 * x)) = ∑ x : ZMod p, χ⁻¹ x from
        Finset.sum_congr rfl (fun x _ => by rw [zero_mul, AddChar.map_zero_eq_one, mul_one])]
    exact (MulChar.sum_eq_zero_of_ne_one (inv_ne_one.mpr hχ1)).symm
  · obtain ⟨u, rfl⟩ := (isUnit_iff_ne_zero.mpr ha)
    rw [← gaussSum_mulShift_inv χ u]
    simp only [gaussSum, AddChar.mulShift_apply]

open Filter Topology in
/-- **Per-`a` log boundary** (`a ≠ 0`): `∑_{k≤n} (1/k)·ψ(k·a) → −log(1 − ψ(a))`, since
`ψ(k·a) = ψ(a)^k` and `ψ(a)` is on the unit circle, `≠ 1`
(`SawtoothFourier.tendsto_sum_pow_div`). -/
theorem tendsto_per_a (a : ZMod p) (ha : a ≠ 0) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n,
        (((k : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) * ZMod.stdAddChar ((k : ZMod p) * a))
      atTop (𝓝 (- Complex.log (1 - ZMod.stdAddChar a))) := by
  have hwn : ‖ZMod.stdAddChar a‖ = 1 := by rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  have hw1 : ZMod.stdAddChar a ≠ 1 := fun h =>
    ha (ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one _).symm))
  have heq : ∀ n : ℕ, (∑ k ∈ Finset.Icc 0 n,
        (((k : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) * ZMod.stdAddChar ((k : ZMod p) * a))
      = ∑ k ∈ Finset.range (n + 1), (ZMod.stdAddChar a) ^ k / (k : ℂ) := by
    intro n
    rw [show Finset.Icc 0 n = Finset.range (n + 1) by
      ext k; rw [Finset.mem_Icc, Finset.mem_range]; omega]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show ((k : ZMod p) * a) = k • a from by rw [nsmul_eq_mul], AddChar.map_nsmul_eq_pow,
      Real.rpow_neg_one, Complex.ofReal_inv, Complex.ofReal_natCast]
    ring
  simp only [heq]
  exact (CyclotomicNT.Sawtooth.tendsto_sum_pow_div hw1 hwn).comp (tendsto_add_atTop_nat 1)

open Filter Topology in
/-- **Even `L(1,χ)` Dirichlet log formula:** `τ(χ⁻¹)·L(1,χ) = ∑_a χ⁻¹(a)·(−log(1 − ζ^a))`
(`ζ^a = stdAddChar a`).  Combines `LFunction χ 1 = ∑χ(n)/n`
(`tendsto_partialSum_char_LFunction_one`),
the Fourier expansion `char_mul_gaussSum`, and the per-`a` log boundary
`tendsto_per_a`, interchanging
the (sequential) limit with the finite sum over `a`.  This is the analytic
input to the cyclotomic-unit
regulator (`reg(C) = ∏_{χ even} L(1,χ)`, the content of `cyclotomic_unit_index`). -/
theorem gaussSum_mul_LFunction_one (χ : DirichletCharacter ℂ p) (hχ1 : χ ≠ 1) :
    gaussSum χ⁻¹ ZMod.stdAddChar * DirichletCharacter.LFunction χ 1
      = ∑ a : ZMod p, χ⁻¹ a * (- Complex.log (1 - ZMod.stdAddChar a)) := by
  have hL := (tendsto_partialSum_char_LFunction_one χ hχ1).const_mul
    (gaussSum χ⁻¹ ZMod.stdAddChar)
  have hstep : ∀ n : ℕ, gaussSum χ⁻¹ ZMod.stdAddChar *
        ∑ k ∈ Finset.Icc 0 n, (((k : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) * χ (k : ZMod p)
      = ∑ a : ZMod p, χ⁻¹ a * ∑ k ∈ Finset.Icc 0 n,
          (((k : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) * ZMod.stdAddChar ((k : ZMod p) * a) := by
    intro n
    rw [Finset.mul_sum]
    rw [show (∑ k ∈ Finset.Icc 0 n, gaussSum χ⁻¹ ZMod.stdAddChar *
          ((((k : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) * χ (k : ZMod p)))
        = ∑ k ∈ Finset.Icc 0 n, ∑ a : ZMod p,
            (((k : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) * (χ⁻¹ a * ZMod.stdAddChar ((k : ZMod p) * a)) from
      Finset.sum_congr rfl (fun k _ => by
        rw [show gaussSum χ⁻¹ ZMod.stdAddChar * ((((k : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) * χ (k : ZMod p))
              = (((k : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)
                  * (χ (k : ZMod p) * gaussSum χ⁻¹ ZMod.stdAddChar) by
            ring, char_mul_gaussSum χ hχ1, Finset.mul_sum])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  simp only [hstep] at hL
  refine tendsto_nhds_unique hL (tendsto_finsetSum Finset.univ (fun a _ => ?_))
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [MulChar.map_zero, zero_mul]; exact tendsto_const_nhds
  · exact (tendsto_per_a a ha).const_mul (χ⁻¹ a)

/-- **Even `L(1,χ)` with real-log regulator entries:** for **even** `χ`, the
imaginary (`arg`) part of
the log formula cancels (`a ↦ −a` pairing, `χ⁻¹` even, `1−ζ^{-a} = conj(1−ζ^a)`), giving
`τ(χ⁻¹)·L(1,χ) = −∑_a χ⁻¹(a)·log‖1−ζ^a‖`.  The `log‖1−ζ^a‖ = log(2 sin πa/p)` are exactly the
cyclotomic-unit regulator matrix entries. -/
theorem gaussSum_mul_LFunction_one_even (χ : DirichletCharacter ℂ p) (hχ1 : χ ≠ 1) (hev : χ.Even) :
    gaussSum χ⁻¹ ZMod.stdAddChar * DirichletCharacter.LFunction χ 1
      = ∑ a : ZMod p, χ⁻¹ a * (- ((Real.log ‖1 - ZMod.stdAddChar a‖ : ℝ) : ℂ)) := by
  rw [gaussSum_mul_LFunction_one χ hχ1]
  have hχinv_ev : χ⁻¹ (-1) = 1 := by
    have h : (χ⁻¹ * χ) (-1) = 1 := by
      rw [inv_mul_cancel]; exact MulChar.one_apply (isUnit_one.neg)
    rwa [MulChar.mul_apply, show χ (-1) = 1 from hev, mul_one] at h
  -- the `arg`-part of the sum vanishes (even symmetry)
  have harg : ∑ a : ZMod p, χ⁻¹ a * ((Complex.arg (1 - ZMod.stdAddChar a) : ℝ) : ℂ) = 0 := by
    have hgneg : ∀ a : ZMod p,
        χ⁻¹ (-a) * ((Complex.arg (1 - ZMod.stdAddChar (-a)) : ℝ) : ℂ)
          = - (χ⁻¹ a * ((Complex.arg (1 - ZMod.stdAddChar a) : ℝ) : ℂ)) := by
      intro a
      rcases eq_or_ne a 0 with rfl | ha
      · simp [MulChar.map_zero]
      · have hψn : ‖ZMod.stdAddChar a‖ = 1 := by
          rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
        have hne : ZMod.stdAddChar a ≠ 1 := fun h =>
          ha (ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one _).symm))
        have hrele : (ZMod.stdAddChar a).re < 1 := by
          rcases (Complex.re_le_norm (ZMod.stdAddChar a)).lt_or_eq with h | h
          · rwa [hψn] at h
          · refine absurd ?_ hne
            have hre1 : (ZMod.stdAddChar a).re = 1 := h.trans hψn
            have hns : (ZMod.stdAddChar a).re * (ZMod.stdAddChar a).re
                + (ZMod.stdAddChar a).im * (ZMod.stdAddChar a).im = 1 := by
              rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hψn, one_pow]
            have him : (ZMod.stdAddChar a).im = 0 := by
              rw [hre1] at hns; exact mul_self_eq_zero.mp (by linarith)
            exact Complex.ext (by rw [hre1, Complex.one_re]) (by rw [him, Complex.one_im])
        have hargne : Complex.arg (1 - ZMod.stdAddChar a) ≠ Real.pi := by
          intro h
          rw [Complex.arg_eq_pi_iff, Complex.sub_re, Complex.one_re] at h
          linarith [h.1]
        rw [show (1 : ℂ) - ZMod.stdAddChar (-a) = (starRingEnd ℂ) (1 - ZMod.stdAddChar a) by
            rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj hψn, map_sub, map_one],
          Complex.arg_conj, if_neg hargne,
          show χ⁻¹ (-a) = χ⁻¹ a by
            rw [show (-a : ZMod p) = -1 * a by ring, map_mul, hχinv_ev, one_mul]]
        push_cast; ring
    have h1 : (∑ a : ZMod p, χ⁻¹ a * ((Complex.arg (1 - ZMod.stdAddChar a) : ℝ) : ℂ))
        = ∑ a : ZMod p, χ⁻¹ (-a) * ((Complex.arg (1 - ZMod.stdAddChar (-a)) : ℝ) : ℂ) :=
      (Equiv.sum_comp (Equiv.neg (ZMod p)) _).symm
    rw [Finset.sum_congr rfl (fun a _ => hgneg a), Finset.sum_neg_distrib] at h1
    linear_combination (1 / 2 : ℂ) * h1
  -- split each log into real-log + arg·I, the arg part summing to 0
  have hlog : ∀ a : ZMod p, χ⁻¹ a * (- Complex.log (1 - ZMod.stdAddChar a))
      = χ⁻¹ a * (- ((Real.log ‖1 - ZMod.stdAddChar a‖ : ℝ) : ℂ))
        - Complex.I * (χ⁻¹ a * ((Complex.arg (1 - ZMod.stdAddChar a) : ℝ) : ℂ)) := by
    intro a
    rw [show Complex.log (1 - ZMod.stdAddChar a)
          = ((Real.log ‖1 - ZMod.stdAddChar a‖ : ℝ) : ℂ)
            + ((Complex.arg (1 - ZMod.stdAddChar a) : ℝ) : ℂ) * Complex.I from by
        conv_lhs => rw [← Complex.re_add_im (Complex.log (1 - ZMod.stdAddChar a))]
        rw [Complex.log_re, Complex.log_im]]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hlog a), Finset.sum_sub_distrib, ← Finset.mul_sum, harg,
    mul_zero, sub_zero]

end CyclotomicNT
