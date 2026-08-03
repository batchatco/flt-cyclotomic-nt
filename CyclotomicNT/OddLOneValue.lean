import CyclotomicNT.OddLValue
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# `L(1, χ)` for odd Dirichlet characters mod a prime

The minus part `h⁻` of the cyclotomic class number formula needs `L(1,χ)` for odd `χ`, but the
arithmetic lives at `s = 0` (`L(0,χ) = −B_{1,χ}`, `CyclotomicNT.LFunction_zero_odd`).  The
**functional equation** `IsPrimitive.completedLFunction_one_sub` bridges the two: at `s = 0`,

  `Λ(χ, 1) = N^{-1/2}·W(χ)·Λ(χ⁻¹, 0)`,    `Λ = completedLFunction`, `W = rootNumber`.

Dividing out the Archimedean Gamma factors (`Gammaℝ(1) = 1`, `Gammaℝ(2) = π⁻¹`, both for odd `χ`)
turns this into a relation between `L(1,χ)` and `L(0,χ⁻¹) = −B_{1,χ⁻¹}`:

  `L(1,χ) = π · N^{-1/2} · W(χ) · (−B_{1,χ⁻¹})`.

This is the analytic input that converts `∏_{χ odd} L(1,χ)` into `∏_{χ odd}
B_{1,χ}` (Washington 4.17,
`h⁻ = w·∏_{χ odd}(−½B_{1,χ})`).
-/

open Complex DirichletCharacter

namespace CyclotomicNT

variable {p : ℕ} [Fact p.Prime]

/-- Every nontrivial character mod a prime `p` is **primitive** (conductor
`= p`, since the conductor
divides `p` and is `1` only for the trivial character). -/
theorem isPrimitive_of_ne_one {χ : DirichletCharacter ℂ p} (hχ1 : χ ≠ 1) : χ.IsPrimitive := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [isPrimitive_def]
  rcases (Nat.dvd_prime Fact.out).mp (conductor_dvd_level χ) with h | h
  · exact absurd (eq_one_iff_conductor_eq_one.mpr h) hχ1
  · exact h

/-- The inverse of an odd character is odd: `χ⁻¹(-1) = (χ(-1))⁻¹ = (-1)⁻¹ = -1`. -/
theorem Odd.inv {χ : DirichletCharacter ℂ p} (hodd : χ.Odd) : χ⁻¹.Odd := by
  have h1 : (χ⁻¹ * χ) (-1) = 1 := by
    rw [inv_mul_cancel]; exact MulChar.one_apply (isUnit_one.neg)
  rw [MulChar.mul_apply] at h1
  show χ⁻¹ (-1) = -1
  rw [show χ (-1) = -1 from hodd] at h1
  linear_combination -h1

/-- `Gammaℝ 2 = π⁻¹` (`= π^{-1}·Γ(1)`). -/
theorem Gammaℝ_two : Gammaℝ (1 + 1) = (↑Real.pi : ℂ)⁻¹ := by
  rw [show (1 : ℂ) + 1 = 2 by norm_num, Gammaℝ_def, show (2 : ℂ) / 2 = 1 by norm_num,
    Complex.Gamma_one, mul_one, show (-(2 : ℂ)) / 2 = -1 by norm_num, Complex.cpow_neg,
    Complex.cpow_one]

/-- **`L(1, χ) = π·N^{-1/2}·W(χ)·(−B_{1,χ⁻¹})` for odd `χ` mod a prime `p`.**  Via the functional
equation at `s = 0`, the Gamma factors `Gammaℝ(1)=1` / `Gammaℝ(2)=π⁻¹`, and
`L(0,χ⁻¹)=−B_{1,χ⁻¹}`. -/
theorem LFunction_one_odd (χ : DirichletCharacter ℂ p) (hχ1 : χ ≠ 1) (hodd : χ.Odd) :
    DirichletCharacter.LFunction χ 1
      = ↑Real.pi * (p : ℂ) ^ (-(1 : ℂ) / 2) * DirichletCharacter.rootNumber χ
        * (- generalizedBernoulli χ⁻¹ 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  have hoddinv : χ⁻¹.Odd := Odd.inv hodd
  -- `χ⁻¹` is odd as a function (for `LFunction_zero_odd`)
  have hoddinvfun : (fun j => χ⁻¹ j).Odd := by
    intro a
    show χ⁻¹ (-a) = - χ⁻¹ a
    rw [show (-a : ZMod p) = (-1) * a by ring, map_mul, show χ⁻¹ (-1) = -1 from hoddinv]; ring
  -- `L(0,χ⁻¹) = −B_{1,χ⁻¹}`
  have hL0 : DirichletCharacter.LFunction χ⁻¹ 0 = - generalizedBernoulli χ⁻¹ 1 :=
    LFunction_zero_odd χ⁻¹ hoddinvfun
  -- functional equation at `s = 0`
  have hfe := (isPrimitive_of_ne_one hχ1).completedLFunction_one_sub 0
  rw [sub_zero, zero_sub] at hfe
  -- `completedLFunction χ⁻¹ 0 = L(0,χ⁻¹) · Gammaℝ 1 = L(0,χ⁻¹)`
  have hG1 : gammaFactor χ⁻¹ (0 : ℂ) = 1 := by rw [hoddinv.gammaFactor_def, zero_add, Gammaℝ_one]
  have hcomp0 : completedLFunction χ⁻¹ 0 = DirichletCharacter.LFunction χ⁻¹ 0 := by
    rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ 0 (Or.inr hp1), hG1, div_one]
  -- assemble: `L(1,χ) = completedLFunction χ 1 / Gammaℝ 2`
  rw [LFunction_eq_completed_div_gammaFactor χ 1 (Or.inl one_ne_zero), hodd.gammaFactor_def,
    Gammaℝ_two, hfe, hcomp0, hL0]
  have hπ : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

open scoped Classical in
/-- **The odd part of the class number formula in terms of Bernoulli numbers.**
`∏_{χ odd} L(1,χ) = (π·N^{-1/2})^{#odd} · (∏_{χ odd} W(χ)) · ∏_{χ odd}(−B_{1,χ⁻¹})` — applying
`LFunction_one_odd` to each factor and pulling out the constant.  The `∏_{χ odd}(−B_{1,χ⁻¹})` factor
is the `h⁻` Bernoulli content; the `W(χ)` Gauss sums and `π/N` powers fold into the class-number
constant. -/
theorem prod_LFunction_one_odd_eq :
    (∏ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Odd),
        DirichletCharacter.LFunction χ 1)
      = (↑Real.pi * (p : ℂ) ^ (-(1 : ℂ) / 2))
          ^ (Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Odd)).card
        * (∏ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Odd),
            DirichletCharacter.rootNumber χ)
        * (∏ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Odd),
            (- generalizedBernoulli χ⁻¹ 1)) := by
  have h1e : (1 : DirichletCharacter ℂ p).Even := MulChar.one_apply isUnit_one.neg
  have key : ∀ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Odd),
      DirichletCharacter.LFunction χ 1
        = (↑Real.pi * (p : ℂ) ^ (-(1 : ℂ) / 2))
          * (DirichletCharacter.rootNumber χ * (- generalizedBernoulli χ⁻¹ 1)) := by
    intro χ hχ
    have hodd := (Finset.mem_filter.mp hχ).2
    have hχ1 : χ ≠ 1 := by
      rintro rfl; exact (1 : DirichletCharacter ℂ p).not_even_and_odd ⟨h1e, hodd⟩
    rw [LFunction_one_odd χ hχ1 hodd]; ring
  rw [Finset.prod_congr rfl key, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_mul_distrib, mul_assoc]

open scoped Classical in
/-- Reindexing `∏_{χ odd}(−B_{1,χ⁻¹}) = ∏_{χ odd}(−B_{1,χ})` via the involution `χ ↦ χ⁻¹` on odd
characters (textbook form of the `h⁻` Bernoulli product). -/
theorem prod_neg_bernoulli_inv :
    (∏ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Odd),
        (- generalizedBernoulli χ⁻¹ 1))
      = ∏ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Odd),
          (- generalizedBernoulli χ 1) := by
  refine Finset.prod_nbij' (fun χ => χ⁻¹) (fun χ => χ⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
    exact Odd.inv hχ
  · intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
    exact Odd.inv hχ
  · intro χ _; exact inv_inv χ
  · intro χ _; exact inv_inv χ
  · intro χ _; rfl
