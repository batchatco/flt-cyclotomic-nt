import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The sawtooth Fourier series `∑ sin(2πnx)/n = π(½ − x)`

The conditionally-convergent core blocking `hurwitzZetaOdd(x,0)` (see
`CyclotomicNT/HurwitzOddZero.lean`).
Built from `∑_{n≥1} z₀ⁿ/n → −log(1−z₀)` for `z₀` on the unit circle, `z₀ ≠ 1`,
via Abel's limit theorem
(`Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`) + Dirichlet's test + the log series
(`hasSum_taylorSeries_neg_log`) — all on **sequential partial sums** (the
series is only conditionally
convergent, so `HasSum`/`tsum` do not apply).
-/

open Complex Finset Filter Topology
open scoped Real

namespace CyclotomicNT.Sawtooth

/-- Geometric partial sums on the unit circle are bounded: `‖∑_{i<N} z₀ⁱ‖ ≤ 2/‖z₀−1‖`. -/
theorem norm_geom_sum_le {z₀ : ℂ} (hz1 : z₀ ≠ 1) (hz : ‖z₀‖ = 1) (N : ℕ) :
    ‖∑ i ∈ range N, z₀ ^ i‖ ≤ 2 / ‖z₀ - 1‖ := by
  rw [geom_sum_eq hz1, norm_div]
  have hnum : ‖z₀ ^ N - 1‖ ≤ 2 := by
    calc ‖z₀ ^ N - 1‖ ≤ ‖z₀ ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
  gcongr

/-- The partial sums `∑_{n<N} z₀ⁿ/n` form a Cauchy sequence (Dirichlet's test), hence converge. -/
theorem exists_tendsto_sum_pow_div {z₀ : ℂ} (hz1 : z₀ ≠ 1) (hz : ‖z₀‖ = 1) :
    ∃ l : ℂ, Tendsto (fun N => ∑ n ∈ range N, z₀ ^ n / (n : ℂ)) atTop (𝓝 l) := by
  have hb : ∀ n, ‖∑ i ∈ range n, z₀ ^ (i + 1)‖ ≤ 2 / ‖z₀ - 1‖ := by
    intro n
    have he : ∑ i ∈ range n, z₀ ^ (i + 1) = z₀ * ∑ i ∈ range n, z₀ ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [pow_succ, mul_comm]
    rw [he, norm_mul, hz, one_mul]; exact norm_geom_sum_le hz1 hz n
  have hanti : Antitone (fun i : ℕ => 1 / (i + 1 : ℝ)) := fun i j hij =>
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hcauchy : CauchySeq (fun n => ∑ i ∈ range n, (1 / (i + 1 : ℝ)) • z₀ ^ (i + 1)) :=
    hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      tendsto_one_div_add_atTop_nhds_zero_nat hb
  -- rewrite the shifted smul-sum as `∑_{m<n+1} z₀^m/m`
  have hrw : (fun n => ∑ i ∈ range n, (1 / (i + 1 : ℝ)) • z₀ ^ (i + 1))
      = (fun n => ∑ m ∈ range (n + 1), z₀ ^ m / (m : ℂ)) := by
    funext n
    rw [Finset.sum_range_succ' (fun m => z₀ ^ m / (m : ℂ)) n]
    simp only [pow_zero, Nat.cast_zero, div_zero, add_zero]
    exact Finset.sum_congr rfl fun i _ => by rw [Complex.real_smul]; push_cast; ring
  rw [hrw] at hcauchy
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨l, (tendsto_add_atTop_iff_nat 1).mp hl⟩

/-- `1 − z₀ ∈ slitPlane` for `z₀` on the unit circle, `z₀ ≠ 1` (so `Complex.log`
is continuous there). -/
theorem one_sub_mem_slitPlane {z₀ : ℂ} (hz1 : z₀ ≠ 1) (hz : ‖z₀‖ = 1) :
    (1 - z₀) ∈ Complex.slitPlane := by
  rcases eq_or_ne z₀.im 0 with him | him
  · have hreal : z₀ = (z₀.re : ℂ) := Complex.ext rfl (by simp [him])
    have habs : |z₀.re| = 1 := by
      have h2 : ‖(z₀.re : ℂ)‖ = ‖z₀‖ := by rw [← hreal]
      rw [Complex.norm_real, Real.norm_eq_abs] at h2; rw [h2]; exact hz
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h1 | h1
    · exact absurd (by rw [hreal, h1, Complex.ofReal_one]) hz1
    · exact Or.inl (by simp only [Complex.sub_re, Complex.one_re, h1]; norm_num)
  · exact Or.inr (by simp only [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero]; exact him)

/-- **The key value identification.**  `∑_{n<N} z₀ⁿ/n → −log(1 − z₀)` for `z₀` on the unit circle,
`z₀ ≠ 1`.  Abel's theorem applied to `∑(z₀z)ⁿ/n = −log(1 − z₀z)` (`|z|<1`),
with the limit `z = ↑r → 1⁻`
identified by continuity of `log` at `1 − z₀ ∈ slitPlane`. -/
theorem tendsto_sum_pow_div {z₀ : ℂ} (hz1 : z₀ ≠ 1) (hz : ‖z₀‖ = 1) :
    Tendsto (fun N => ∑ n ∈ range N, z₀ ^ n / (n : ℂ)) atTop (𝓝 (-Complex.log (1 - z₀))) := by
  obtain ⟨l, hl⟩ := exists_tendsto_sum_pow_div hz1 hz
  suffices hval : l = -Complex.log (1 - z₀) by rwa [hval] at hl
  have hslit := one_sub_mem_slitPlane hz1 hz
  -- ∑' n, (z₀ⁿ/n)·zⁿ = −log(1 − z₀z) for ‖z‖<1
  have htsum : ∀ z : ℂ, ‖z‖ < 1 →
      (∑' n : ℕ, z₀ ^ n / (n : ℂ) * z ^ n) = -Complex.log (1 - z₀ * z) := by
    intro z hzn
    have hw : ‖z₀ * z‖ < 1 := by rw [norm_mul, hz, one_mul]; exact hzn
    rw [← (hasSum_taylorSeries_neg_log hw).tsum_eq]
    exact tsum_congr fun n => by rw [mul_pow]; ring
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := fun n => z₀ ^ n / (n : ℂ)) hl
  -- on the filter `↑r → 1⁻`, the Abel function equals `−log(1 − z₀·↑r)`
  have heq : (fun z : ℂ => ∑' n : ℕ, z₀ ^ n / (n : ℂ) * z ^ n)
      =ᶠ[(𝓝[<] (1 : ℝ)).map Complex.ofReal] (fun z => -Complex.log (1 - z₀ * z)) := by
    rw [Filter.eventuallyEq_map]
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    rw [Set.mem_Ioo] at hr
    exact htsum (r : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]; exact hr.2)
  -- and `−log(1 − z₀·↑r) → −log(1 − z₀)` by continuity
  have hcont : Tendsto (fun z : ℂ => -Complex.log (1 - z₀ * z))
      ((𝓝[<] (1 : ℝ)).map Complex.ofReal) (𝓝 (-Complex.log (1 - z₀))) := by
    have hg : ContinuousAt (fun z : ℂ => -Complex.log (1 - z₀ * z)) 1 := by
      refine ((continuousAt_clog ?_).comp (by fun_prop)).neg
      simpa using hslit
    have hofR : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
      simpa using (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    rw [tendsto_map'_iff]
    simpa using hg.tendsto.comp hofR
  exact tendsto_nhds_unique (habel.congr' heq) hcont

/-- The half-angle factorization `1 − e^{2πix} = 2·sin(πx)·e^{i(πx−π/2)}`. -/
theorem one_sub_exp_factor (x : ℝ) :
    1 - Complex.exp (((2 * π * x : ℝ) : ℂ) * Complex.I)
      = ((2 * Real.sin (π * x) : ℝ) : ℂ) * Complex.exp (((π * x - π / 2 : ℝ) : ℂ) * Complex.I) := by
  have hcs : Real.cos (π * x - π / 2) = Real.sin (π * x) := by
    rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hss : Real.sin (π * x - π / 2) = -Real.cos (π * x) := by
    rw [Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
    rw [hcs, show (2 * π * x : ℝ) = 2 * (π * x) by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (π * x)]
  · simp only [Complex.sub_im, Complex.one_im, Complex.exp_ofReal_mul_I_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, zero_mul, add_zero,
      zero_sub]
    rw [hss, show (2 * π * x : ℝ) = 2 * (π * x) by ring, Real.sin_two_mul]; ring

/-- **The sawtooth Fourier series** `∑_{n<N} sin(2πnx)/n → π(½ − x)` for `x ∈ (0,1)`. -/
theorem tendsto_sum_sin_div (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun N => ∑ n ∈ range N, Real.sin (2 * π * n * x) / n) atTop
      (𝓝 (π * (1 / 2 - x))) := by
  obtain ⟨hx0, hx1⟩ := hx
  set z₀ := Complex.exp (((2 * π * x : ℝ) : ℂ) * Complex.I) with hz₀
  have hznorm : ‖z₀‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hpx0 : 0 < π * x := mul_pos Real.pi_pos hx0
  have hpxπ : π * x < π := by nlinarith [Real.pi_pos]
  have hsinpos : 0 < Real.sin (π * x) := Real.sin_pos_of_pos_of_lt_pi hpx0 hpxπ
  -- z₀ ≠ 1 : if so then `sin(2πx)=0 ⟹ cos(πx)=0 ⟹ cos(2πx)=-1 ≠ 1 = re z₀`
  have hzne : z₀ ≠ 1 := by
    intro h
    have him : z₀.im = 0 := by rw [h]; rfl
    rw [hz₀, Complex.exp_ofReal_mul_I_im, show (2 * π * x : ℝ) = 2 * (π * x) by ring,
      Real.sin_two_mul] at him
    have hcos0 : Real.cos (π * x) = 0 := by
      rcases mul_eq_zero.mp him with h2 | h2
      · linarith [hsinpos]
      · exact h2
    have hre : z₀.re = 1 := by rw [h]; rfl
    rw [hz₀, Complex.exp_ofReal_mul_I_re, show (2 * π * x : ℝ) = 2 * (π * x) by ring,
      Real.cos_two_mul, hcos0] at hre
    norm_num at hre
  have hmain := tendsto_sum_pow_div hzne hznorm
  have harg : Complex.arg (1 - z₀) = π * x - π / 2 := by
    rw [hz₀, one_sub_exp_factor, Complex.arg_real_mul _ (by linarith [hsinpos]), Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hlogim : (-Complex.log (1 - z₀)).im = π * (1 / 2 - x) := by
    rw [Complex.neg_im, Complex.log_im, harg]; ring
  have himtend := (Complex.continuous_im.tendsto _).comp hmain
  rw [hlogim] at himtend
  refine himtend.congr fun N => ?_
  rw [Function.comp_apply, Complex.im_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hzn : z₀ ^ n = Complex.exp (((2 * π * n * x : ℝ) : ℂ) * Complex.I) := by
    rw [hz₀, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hzn, Complex.div_natCast_im, Complex.exp_ofReal_mul_I_im]

end CyclotomicNT.Sawtooth
