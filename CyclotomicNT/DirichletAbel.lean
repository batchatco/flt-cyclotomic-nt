import CyclotomicNT.SawtoothFourier
import CyclotomicNT.HurwitzOddZero
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd

/-!
# Dirichlet–Abel link: `sinZeta a 1 = π·(½ − a)`

The sawtooth (`CyclotomicNT.Sawtooth.tendsto_sum_sin_div`) gives the **sequential** sum
`∑_{n} sin(2πna)/n = π(½ − a)`.  Mathlib's `sinZeta a 1` is the value of the **analytic
continuation**, equal to `∑ sin(2πan)/nˢ` only for `Re s > 1` (`hasSum_nat_sinZeta`).

Connecting the two is a Dirichlet-series Abel theorem (the boundary `s → 1⁺` limit), which
Mathlib lacks.  We assemble it from Mathlib's **Abel summation in integral form**
(`tendsto_sum_mul_atTop_nhds_one_sub_integral₀`) plus a dominated-convergence limit in `s`.

This file builds the ingredients bottom-up.  The first is the **bounded Dirichlet kernel**
`|∑_{n<N} sin(2πan)| ≤ 1/sin(πa)`, which supplies the `=O` decay needed by Abel summation.
-/

open Complex Finset Real

namespace CyclotomicNT.DirichletAbel

/-- `‖e^{2πia} − 1‖ = 2·sin(πa)` for `a ∈ (0,1)`. -/
theorem norm_exp_sub_one (a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1) :
    ‖Complex.exp (((2*π*a:ℝ):ℂ)*Complex.I) - 1‖ = 2 * Real.sin (π*a) := by
  have hsin : 0 < Real.sin (π*a) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have := ha.1; positivity
    · have h2 := ha.2; nlinarith [Real.pi_pos]
  rw [show Complex.exp (((2*π*a:ℝ):ℂ)*Complex.I) - 1
        = -(1 - Complex.exp (((2*π*a:ℝ):ℂ)*Complex.I)) by ring,
    norm_neg, CyclotomicNT.Sawtooth.one_sub_exp_factor, norm_mul, Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 2 * Real.sin (π*a))]

/-- `e^{2πia} ≠ 1` for `a ∈ (0,1)`. -/
theorem exp_ne_one (a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1) :
    Complex.exp (((2*π*a:ℝ):ℂ)*Complex.I) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  rw [show (n:ℂ)*(2*↑π*Complex.I) = ((n*2*π:ℝ):ℂ)*Complex.I by push_cast; ring] at hn
  have hcancel := mul_right_cancel₀ Complex.I_ne_zero hn
  rw [Complex.ofReal_inj] at hcancel
  have hpi := Real.pi_pos
  have han : a = (n:ℝ) := by
    field_simp at hcancel
    nlinarith [hcancel]
  have h0 : (0:ℝ) < (n:ℝ) := han ▸ ha.1
  have h1 : (n:ℝ) < 1 := han ▸ ha.2
  have hn0 : 0 < n := by exact_mod_cast h0
  have hn1 : n < 1 := by exact_mod_cast h1
  omega

/-- **Bounded Dirichlet kernel.**  `|∑_{n<N} sin(2πan)| ≤ 1/sin(πa)` for `a ∈ (0,1)`, uniformly
in `N`.  (Imaginary part of the geometric sum `∑ e^{2πian}`, bounded via `norm_geom_sum_le`.) -/
theorem abs_sum_sin_le (a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1) (N : ℕ) :
    |∑ n ∈ range N, Real.sin (2*π*a*n)| ≤ 1 / Real.sin (π*a) := by
  set z₀ : ℂ := Complex.exp (((2*π*a:ℝ):ℂ)*Complex.I) with hz0
  have hsin : 0 < Real.sin (π*a) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have := ha.1; positivity
    · have h2 := ha.2; nlinarith [Real.pi_pos]
  have hznorm : ‖z₀‖ = 1 := by rw [hz0, Complex.norm_exp_ofReal_mul_I]
  have hzne : z₀ ≠ 1 := exp_ne_one a ha
  have hImsum : (∑ n ∈ range N, z₀^n).im = ∑ n ∈ range N, Real.sin (2*π*a*n) := by
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [hz0, ← Complex.exp_nat_mul,
      show (n:ℂ) * (((2*π*a:ℝ):ℂ)*Complex.I) = ((2*π*a*n:ℝ):ℂ)*Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_im]
  have hnb := CyclotomicNT.Sawtooth.norm_geom_sum_le hzne hznorm N
  have hnormsub : ‖z₀ - 1‖ = 2 * Real.sin (π*a) := by
    rw [hz0]; exact norm_exp_sub_one a ha
  rw [hnormsub] at hnb
  calc |∑ n ∈ range N, Real.sin (2*π*a*n)| = |(∑ n ∈ range N, z₀^n).im| := by rw [hImsum]
    _ ≤ ‖∑ n ∈ range N, z₀^n‖ := Complex.abs_im_le_norm _
    _ ≤ 2 / (2 * Real.sin (π*a)) := hnb
    _ = 1 / Real.sin (π*a) := by field_simp

open Filter Topology MeasureTheory Asymptotics

/-- **Abel summation, integral form (applied).**  For `0 < s` and `a ∈ (0,1)`, the partial sums of
the Dirichlet-type series `∑ sin(2πak)/kˢ` converge to `−∫₁^∞ (d/dt t^{-s})·D(⌊t⌋) dt`, where
`D(m) = ∑_{k≤m} sin(2πak)` is the (bounded) Dirichlet kernel.  This is Mathlib's
`tendsto_sum_mul_atTop_nhds_one_sub_integral₀` with `c k = sin(2πak)`, `f x = x^{-s}`; the boundary
term vanishes (`l = 0`) because `D` is bounded (`abs_sum_sin_le`) and `n^{-s} → 0`. -/
theorem tendsto_partialSum_sub_integral (a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, ((k:ℝ) ^ (-s)) * Real.sin (2*π*a*k)) atTop
      (𝓝 (0 - ∫ t in Set.Ioi (1:ℝ), deriv (fun x : ℝ => x ^ (-s)) t *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, Real.sin (2*π*a*k))) := by
  have hsin : 0 < Real.sin (π*a) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have := ha.1; positivity
    · have h2 := ha.2; nlinarith [Real.pi_pos]
  set M : ℝ := 1 / Real.sin (π*a) with hM_def
  have hM0 : 0 ≤ M := by rw [hM_def]; positivity
  have hker : ∀ n : ℕ, |∑ k ∈ Finset.Icc 0 n, Real.sin (2*π*a*k)| ≤ M := by
    intro n
    rw [show Finset.Icc 0 n = Finset.range (n+1) by
      ext k; rw [Finset.mem_Icc, Finset.mem_range]; omega]
    exact abs_sum_sin_le a ha (n+1)
  set c : ℕ → ℝ := fun k => Real.sin (2*π*a*k) with hc_def
  set f : ℝ → ℝ := fun x => x ^ (-s) with hf_def
  have hderiv_eq : deriv f = fun t => (-s) * t ^ (-s - 1) := by
    rw [hf_def]; exact Real.deriv_rpow_const' (-s)
  have hc0 : c 0 = 0 := by simp [hc_def]
  have hf_diff : ∀ t ∈ Set.Ici (1:ℝ), DifferentiableAt ℝ f t := by
    intro t ht
    have ht0 : t ≠ 0 := by simp at ht; linarith
    exact (Real.hasDerivAt_rpow_const (Or.inl ht0)).differentiableAt
  have hf_int : LocallyIntegrableOn (deriv f) (Set.Ici 1) := by
    rw [hderiv_eq]
    apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ici
    apply ContinuousOn.mul continuousOn_const
    intro t ht
    have ht0 : t ≠ 0 := by simp at ht; linarith
    exact (Real.continuousAt_rpow_const t (-s-1) (Or.inl ht0)).continuousWithinAt
  have h_lim : Tendsto (fun n : ℕ ↦ f n * ∑ k ∈ Finset.Icc 0 n, c k) atTop (𝓝 0) := by
    have hbound : ∀ n : ℕ, ‖f n * ∑ k ∈ Finset.Icc 0 n, c k‖ ≤ M * (n:ℝ) ^ (-s) := by
      intro n
      rw [hf_def, hc_def]
      simp only [Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), mul_comm M _]
      exact mul_le_mul_of_nonneg_left (hker n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have htend : Tendsto (fun n : ℕ => M * (n:ℝ) ^ (-s)) atTop (𝓝 0) := by
      rw [show (0:ℝ) = M * 0 by ring]
      exact Tendsto.const_mul _
        ((tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop)
    exact squeeze_zero_norm hbound htend
  have hg_dom : (fun t ↦ deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
      =O[atTop] (fun t : ℝ => t ^ (-s-1)) := by
    rw [hderiv_eq, Asymptotics.isBigO_iff]
    refine ⟨s * M, ?_⟩
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have ht0 : (0:ℝ) ≤ t := by linarith
    have hrpow : (0:ℝ) ≤ t ^ (-s-1) := Real.rpow_nonneg ht0 _
    simp only [Real.norm_eq_abs, abs_mul, abs_neg]
    rw [abs_of_pos hs, abs_of_nonneg hrpow]
    rw [show s * M * t ^ (-s-1) = s * (t ^ (-s-1) * M) by ring,
        show s * t ^ (-s-1) * |∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k|
           = s * (t ^ (-s-1) * |∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k|) by ring]
    apply mul_le_mul_of_nonneg_left _ hs.le
    exact mul_le_mul_of_nonneg_left (hker ⌊t⌋₊) hrpow
  have hg_int : IntegrableAtFilter (fun t : ℝ => t ^ (-s-1)) atTop :=
    ⟨Set.Ioi (1:ℝ), Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)⟩
  exact tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c hc0 hf_diff hf_int h_lim hg_dom hg_int

open HurwitzZeta

/-- **Continuity half.**  `sinZeta` is entire (`differentiableAt_sinZeta`), so `s ↦ sinZeta a s`
along `𝓝[>] 1` tends to its boundary value `sinZeta a 1`. -/
theorem tendsto_sinZeta_nhdsWithin (a : ℝ) :
    Tendsto (fun s : ℝ => sinZeta (↑a) (↑s : ℂ)) (𝓝[>] 1) (𝓝 (sinZeta (↑a) 1)) := by
  have hcont : Continuous (fun s : ℝ => sinZeta (↑a) (↑s : ℂ)) :=
    (differentiableAt_sinZeta a).continuous.comp Complex.continuous_ofReal
  simpa using tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi 1) (hcont.tendsto 1)

/-- **Integral representation of `sinZeta a s` for `Re s > 1` (`s` real).**  Combining
`tendsto_partialSum_sub_integral` with `hasSum_nat_sinZeta` (and the cast `sin(2πak)/(k:ℂ)ˢ =
↑((k:ℝ)^{-s}·sin(2πak))`): the analytic value `sinZeta a s` equals the real Abel integral
`−∫₁^∞ (d/dt t^{-s})·D(⌊t⌋) dt`. -/
theorem sinZeta_eq_ofReal (a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1) (s : ℝ) (hs : 1 < s) :
    sinZeta (↑a) (↑s) = (((0 - ∫ t in Set.Ioi (1:ℝ), deriv (fun x : ℝ => x ^ (-s)) t *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, Real.sin (2*π*a*k)) : ℝ) : ℂ) := by
  have hterm : ∀ k : ℕ, (Real.sin (2*π*a*k) : ℂ) / ((k:ℂ) ^ ((s:ℝ):ℂ))
      = ((((k:ℝ) ^ (-s)) * Real.sin (2*π*a*k) : ℝ) : ℂ) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
      rw [Complex.ofReal_mul, Complex.ofReal_cpow hkpos.le]
      push_cast
      rw [Complex.cpow_neg, div_eq_mul_inv, mul_comm]
  have hsum := hasSum_nat_sinZeta a (s := (s:ℂ)) (by rw [Complex.ofReal_re]; exact hs)
  have hcx1 := hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hre := tendsto_partialSum_sub_integral a ha s (by linarith)
  have hre' := (Complex.continuous_ofReal.tendsto _).comp hre
  have heq : (fun n : ℕ => ∑ k ∈ Finset.range (n+1), (Real.sin (2*π*a*k) : ℂ) / ((k:ℂ) ^ ((s:ℝ):ℂ)))
           = (fun n : ℕ => ((∑ k ∈ Finset.Icc 0 n,
              ((k:ℝ) ^ (-s)) * Real.sin (2*π*a*k) : ℝ) : ℂ)) := by
    funext n
    rw [Complex.ofReal_sum, show Finset.Icc 0 n = Finset.range (n+1) by
      ext k; rw [Finset.mem_Icc, Finset.mem_range]; omega]
    exact Finset.sum_congr rfl (fun k _ => hterm k)
  rw [Function.comp_def] at hcx1
  simp only [heq] at hcx1
  exact tendsto_nhds_unique hcx1 hre'

/-- **Identifying the boundary integral with the sawtooth value.**  At `s = 1` the same Abel
representation, paired with the sawtooth limit `∑ sin(2πka)/k = π(½−a)`
(`CyclotomicNT.Sawtooth.tendsto_sum_sin_div`), forces `−∫₁^∞ (d/dt t^{-1})·D(⌊t⌋) dt = π(½−a)`. -/
theorem integral_eq_sawtooth (a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1) :
    (0 - ∫ t in Set.Ioi (1:ℝ), deriv (fun x : ℝ => x ^ (-(1:ℝ))) t *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, Real.sin (2*π*a*k)) = π * (1/2 - a) := by
  have h1 := tendsto_partialSum_sub_integral a ha 1 (by norm_num)
  have hseq : (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, ((k:ℝ) ^ (-(1:ℝ))) * Real.sin (2*π*a*k))
            = (fun n : ℕ => ∑ k ∈ Finset.range (n+1), Real.sin (2*π*(k:ℝ)*a) / (k:ℝ)) := by
    funext n
    rw [show Finset.Icc 0 n = Finset.range (n+1) by
      ext k; rw [Finset.mem_Icc, Finset.mem_range]; omega]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Real.rpow_neg_one, show 2*π*a*(k:ℝ) = 2*π*(k:ℝ)*a by ring]
    ring
  rw [hseq] at h1
  have hsaw' : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n+1), Real.sin (2*π*(k:ℝ)*a) / (k:ℝ))
      atTop (𝓝 (π * (1/2 - a))) :=
    (CyclotomicNT.Sawtooth.tendsto_sum_sin_div a ha).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique h1 hsaw'

/-- **Dominated convergence in `s`.**  As `s → 1⁺`, the boundary integral
`∫₁^∞ (d/dt t^{-s})·D(⌊t⌋) dt` converges to its value at `s = 1`.  Dominating function: `2M·t^{-2}`
(`M = 1/sin(πa)` bounds the Dirichlet kernel `D` via `abs_sum_sin_le`). -/
theorem tendsto_integral_dc (a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1) :
    Tendsto (fun s : ℝ => ∫ t in Set.Ioi (1:ℝ), deriv (fun x : ℝ => x ^ (-s)) t *
              ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, Real.sin (2*π*a*k)) (𝓝[>] 1)
      (𝓝 (∫ t in Set.Ioi (1:ℝ), deriv (fun x : ℝ => x ^ (-(1:ℝ))) t *
              ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, Real.sin (2*π*a*k))) := by
  have hsin : 0 < Real.sin (π*a) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have := ha.1; positivity
    · have h2 := ha.2; nlinarith [Real.pi_pos]
  set M : ℝ := 1 / Real.sin (π*a) with hM_def
  have hM0 : 0 ≤ M := by rw [hM_def]; positivity
  have hker : ∀ n : ℕ, |∑ k ∈ Finset.Icc 0 n, Real.sin (2*π*a*k)| ≤ M := by
    intro n
    rw [show Finset.Icc 0 n = Finset.range (n+1) by
      ext k; rw [Finset.mem_Icc, Finset.mem_range]; omega]
    exact abs_sum_sin_le a ha (n+1)
  set D : ℝ → ℝ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, Real.sin (2*π*a*k) with hD_def
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun t => 2 * M * t ^ (-(2:ℝ)))
  · apply Filter.Eventually.of_forall
    intro s
    rw [Real.deriv_rpow_const' (-s)]
    apply AEStronglyMeasurable.mul
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      apply ContinuousOn.mul continuousOn_const
      intro t ht
      have ht0 : t ≠ 0 := by simp only [Set.mem_Ioi] at ht; linarith
      exact (Real.continuousAt_rpow_const t (-s-1) (Or.inl ht0)).continuousWithinAt
    · exact (Measurable.aestronglyMeasurable
        ((measurable_of_countable (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, Real.sin (2*π*a*k))).comp
          Nat.measurable_floor))
  · have hev : ∀ᶠ s : ℝ in 𝓝[>] 1, s < 2 := by
      have hIio : Set.Iio (2:ℝ) ∈ 𝓝 (1:ℝ) := Iio_mem_nhds (by norm_num)
      exact eventually_nhdsWithin_of_eventually_nhds
        (Filter.eventually_of_mem hIio (fun x hx => hx))
    filter_upwards [hev, self_mem_nhdsWithin] with s hs2 hs1
    rw [Set.mem_Ioi] at hs1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Set.mem_Ioi] at ht
    have ht0 : (0:ℝ) ≤ t := by linarith
    have ht1 : (1:ℝ) ≤ t := by linarith
    rw [Real.deriv_rpow_const' (-s)]
    have hrpow : (0:ℝ) ≤ t ^ (-s-1) := Real.rpow_nonneg ht0 _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos (by linarith : (0:ℝ) < s),
        abs_of_nonneg hrpow]
    calc s * t ^ (-s-1) * |D t|
        ≤ s * t ^ (-s-1) * M :=
          mul_le_mul_of_nonneg_left (hker ⌊t⌋₊) (by positivity)
      _ ≤ 2 * t ^ (-(2:ℝ)) * M := by
          apply mul_le_mul_of_nonneg_right _ hM0
          apply mul_le_mul (by linarith)
            (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) hrpow (by norm_num)
      _ = 2 * M * t ^ (-(2:ℝ)) := by ring
  · exact (integrableOn_Ioi_rpow_of_lt (show (-(2:ℝ)) < -1 by norm_num)
      (show (0:ℝ) < 1 by norm_num)).const_mul (2*M)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Set.mem_Ioi] at ht
    have ht0 : t ≠ 0 := by linarith
    simp only [Real.deriv_rpow_const']
    have key : Tendsto (fun s : ℝ => (-s) * t ^ (-s-1) * D t) (𝓝 (1:ℝ))
        (𝓝 ((-(1:ℝ)) * t ^ (-(1:ℝ)-1) * D t)) := by
      apply Tendsto.mul_const
      apply Tendsto.mul tendsto_id.neg
      have hinner : Tendsto (fun s : ℝ => -s-1) (𝓝 (1:ℝ)) (𝓝 (-(1:ℝ)-1)) :=
        (tendsto_id.neg.sub_const 1)
      exact ((Real.continuous_const_rpow ht0).tendsto _).comp hinner
    exact key.mono_left nhdsWithin_le_nhds

/-- **The Dirichlet–Abel boundary limit**.  As `s → 1⁺`,
`sinZeta a s → π(½ − a)`.  Chains `sinZeta_eq_ofReal` (s > 1), `tendsto_integral_dc` (the `s → 1`
limit of the integral), and `integral_eq_sawtooth` (its value). -/
theorem abelBoundaryLimit (a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1) :
    Tendsto (fun s : ℝ => sinZeta (↑a) (↑s : ℂ)) (𝓝[>] 1) (𝓝 (((π * (1/2 - a) : ℝ)) : ℂ)) := by
  have hsub : Tendsto (fun s : ℝ => (0 - ∫ t in Set.Ioi (1:ℝ), deriv (fun x : ℝ => x ^ (-s)) t *
              ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, Real.sin (2*π*a*k))) (𝓝[>] 1) (𝓝 (π * (1/2 - a))) := by
    have := (tendsto_const_nhds (x := (0:ℝ)) (f := 𝓝[>] (1:ℝ))).sub (tendsto_integral_dc a ha)
    rwa [integral_eq_sawtooth a ha] at this
  refine Filter.Tendsto.congr' ?_ ((Complex.continuous_ofReal.tendsto _).comp hsub)
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  exact (sinZeta_eq_ofReal a ha s hs).symm

/-- **`sinZeta a 1 = π(½ − a)`** for `a ∈ (0,1)`.  Uniqueness of limits applied to the continuity
limit (`tendsto_sinZeta_nhdsWithin`, → `sinZeta a 1`) and the Abel boundary limit
(`abelBoundaryLimit`, → `π(½−a)`). -/
theorem sinZeta_one_eq (a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1) :
    sinZeta (↑a) 1 = (((π * (1/2 - a) : ℝ)) : ℂ) :=
  tendsto_nhds_unique (tendsto_sinZeta_nhdsWithin a) (abelBoundaryLimit a ha)

/-- **`hurwitzZetaOdd a 0 = ½ − a`** for `a ∈ (0,1)`.  Combines `hurwitzZetaOdd_zero` (the
functional-equation half, `hurwitzZetaOdd a 0 = (1/π)·sinZeta a 1`) with `sinZeta_one_eq`.

This closes the sawtooth gap Mathlib's `hurwitzZeta_neg_nat` leaves open at `k = 0`, and supplies
the `h⁻` brick `L(0,χ) = −B_{1,χ}` for odd characters χ on the Iwasawa ladder toward
`realUnitKummer`. -/
theorem hurwitzZetaOdd_zero_eq (a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1) :
    hurwitzZetaOdd (↑a) 0 = (((1/2 - a : ℝ)) : ℂ) := by
  rw [hurwitzZetaOdd_zero, sinZeta_one_eq a ha]
  have hπ : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

end CyclotomicNT.DirichletAbel
