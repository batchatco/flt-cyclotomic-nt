import CyclotomicNT.DirichletAbel
import CyclotomicNT.GeneralizedBernoulli

/-!
# `L(0, χ) = −B_{1,χ}` for odd Dirichlet characters

`GeneralizedBernoulli.ZMod.LFunction_neg_nat` gives `L(−k, χ) = −B_{k+1,χ}/(k+1)` only for `k ≥ 1`,
because Mathlib's `hurwitzZeta_neg_nat` excludes `k = 0` (the conditionally-convergent sawtooth).

For the minus-part / `h⁻` of the analytic class-number formula one needs exactly the `k = 0` value
`L(0, χ) = −B_{1,χ}`, and only for **odd** characters χ.  For odd χ the even Hurwitz-zeta part
cancels (`ZMod.LFunction_def_odd`), so `L(0,χ) = ∑_j χ(j)·hurwitzZetaOdd(j/N, 0)`, and
`CyclotomicNT.DirichletAbel.hurwitzZetaOdd_zero_eq` supplies `hurwitzZetaOdd(j/N, 0) = ½ − j/N`.
Matching `∑_j χ(j)(½ − j/N) = −B_{1,χ}` (from `B₁(x) = x − ½`) closes the case.

This is the `h⁻` brick `L(0,χ) = −B_{1,χ}` (odd χ) on the Iwasawa ladder toward `realUnitKummer`.
-/

open Complex Finset Real HurwitzZeta
open CyclotomicNT.DirichletAbel DirichletCharacter

namespace CyclotomicNT

/-- **`L(0, χ) = −B_{1,χ}` for odd Dirichlet characters χ.**  The `k = 0` companion to
`ZMod.LFunction_neg_nat` (`L(−k,χ) = −B_{k+1,χ}/(k+1)`, `k ≥ 1`), valid for odd χ.  The even
Hurwitz part cancels (`ZMod.LFunction_def_odd`); the odd part is evaluated by the sawtooth value
`hurwitzZetaOdd_zero_eq`. -/
theorem LFunction_zero_odd {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hodd : (fun j => χ j).Odd) :
    ZMod.LFunction (fun j => χ j) 0 = - generalizedBernoulli χ 1 := by
  have hχ0 : χ (0 : ZMod N) = 0 := by
    have h := hodd 0; rw [neg_zero] at h; exact CharZero.eq_neg_self_iff.mp h
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [ZMod.LFunction_def_odd hodd 0, neg_zero, Complex.cpow_zero, one_mul,
      generalizedBernoulli_eq_sum_univ, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rcases eq_or_ne j 0 with hj | hj
  · subst hj; rw [hχ0, zero_mul, zero_mul, neg_zero]
  · have hval_pos : 0 < j.val :=
      Nat.pos_of_ne_zero (fun h => hj (by rw [← ZMod.natCast_zmod_val j, h, Nat.cast_zero]))
    have hval_lt : j.val < N := ZMod.val_lt j
    have hNpos : (0:ℝ) < N := by exact_mod_cast NeZero.pos N
    have ha : (j.val : ℝ)/N ∈ Set.Ioo (0:ℝ) 1 :=
      ⟨div_pos (by exact_mod_cast hval_pos) hNpos, by rw [div_lt_one hNpos]; exact_mod_cast hval_lt⟩
    have htac : ZMod.toAddCircle j = ((((j.val:ℝ)/N : ℝ)) : UnitAddCircle) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val j]
      rw [ZMod.toAddCircle_natCast]
    rw [htac, hurwitzZetaOdd_zero_eq _ ha, ← mul_neg]
    congr 1
    rw [Polynomial.bernoulli_one, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      pow_one, div_self hN, one_mul,
      show ((j.val:ℚ)/N - 2⁻¹) = -(1/2 - (j.val:ℚ)/N) by ring, map_neg, neg_neg,
      show algebraMap ℚ ℂ (1/2 - (j.val:ℚ)/N) = ((1/2 - (j.val:ℚ)/N : ℚ) : ℂ) by norm_cast]
    push_cast
    ring

end CyclotomicNT
