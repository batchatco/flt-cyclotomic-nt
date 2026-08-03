import Mathlib.NumberTheory.LSeries.HurwitzZeta

/-!
# `hurwitzZetaOdd a 0` and the sawtooth Fourier series

Toward `L(0,χ) = -B_{1,χ}` for **odd** characters χ (the minus-part / `h⁻` brick of the Iwasawa
ladder): for odd χ the even Hurwitz-zeta part cancels in `∑_j χ(j) hurwitzZeta(j/N,·)`, so `L(0,χ)`
needs only `hurwitzZetaOdd(x,0)`.

This file reduces `hurwitzZetaOdd(a,0)` to `sinZeta(a,1)` via the (entire) functional equation — the
clean, unconditional half.  The remaining `sinZeta(a,1) = π·(½ − a)` is the
**sawtooth Fourier series**
`∑_{n≥1} sin(2πna)/n = π(½ − a)` (conditionally convergent — must be handled with sequential partial
sums via Abel's theorem + Dirichlet's test + the log series, NOT `HasSum`);
that is the deep analytic
core Mathlib lacks (its `hurwitzZeta_neg_nat` excludes `k = 0` for exactly this reason).
-/

open Complex HurwitzZeta Real

/-- **The functional-equation half (unconditional).**  `hurwitzZetaOdd a 0 = (1/π)·sinZeta a 1`.
From `hurwitzZetaOdd_one_sub` at `s = 1` (valid since `1 ≠ -n`): the prefactor
`2·(2π)^{-1}·Γ(1)·sin(π/2) = 1/π`.  This isolates the value of `hurwitzZetaOdd` at `0` to the single
boundary value `sinZeta a 1` (the sawtooth). -/
theorem hurwitzZetaOdd_zero (a : UnitAddCircle) :
    hurwitzZetaOdd a 0 = (1 / (π : ℂ)) * sinZeta a 1 := by
  have hs : ∀ n : ℕ, (1 : ℂ) ≠ -n := by
    intro n h
    have : (1 : ℂ).re = (-(n : ℂ)).re := by rw [h]
    simp at this
    linarith [this, (Nat.cast_nonneg n : (0:ℝ) ≤ (n : ℝ))]
  have h := hurwitzZetaOdd_one_sub a hs
  rw [show (1 : ℂ) - 1 = 0 by ring] at h
  rw [h]
  rw [Complex.Gamma_one, show (π : ℂ) * 1 / 2 = π / 2 by ring, Complex.sin_pi_div_two,
    Complex.cpow_neg_one]
  rw [mul_one, mul_one]
  rw [show (2 * (π : ℂ))⁻¹ = (1 / (π : ℂ)) / 2 by
    rw [mul_comm, mul_inv]; ring]
  ring
