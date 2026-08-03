import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Generalized Bernoulli numbers

For a Dirichlet character `χ` of modulus `N`, the **generalized Bernoulli numbers** `B_{k,χ}`
are defined by the generating function
`∑_{a=1}^{N} χ(a) · t·e^{a t} / (e^{N t} − 1) = ∑_{k} B_{k,χ} · t^k / k!`,
equivalently (the form used here, via Bernoulli polynomials `B_k`):
`B_{k,χ} = N^{k-1} · ∑_{a=0}^{N-1} χ(a) · B_k(a/N)`.

These interpolate the values of Dirichlet `L`-functions at non-positive integers,
`L(1−k, χ) = −B_{k,χ}/k`, and are the objects the Kubota–Leopoldt `p`-adic `L`-function
`p`-adically interpolates. They connect to the Kubota–Leopoldt `p`-adic `L`-function and Iwasawa
theory; this file is written
in Mathlib style.

## Main definitions

* `DirichletCharacter.generalizedBernoulli χ k` — the `k`-th generalized Bernoulli number `B_{k,χ}`,
  valued in any `ℚ`-algebra `R` in which `χ` takes values.

-/

open Finset Polynomial

namespace DirichletCharacter

variable {R : Type*} [CommRing R] [Algebra ℚ R] {N : ℕ}

/-- The `k`-th **generalized Bernoulli number** `B_{k,χ}` of a Dirichlet character `χ` of modulus
`N`, via the Bernoulli polynomials: `B_{k,χ} = N^{k-1} · ∑_{a=0}^{N-1} χ(a) · B_k(a/N)`.
(The `a = 0` term vanishes since `χ 0 = 0`, so this agrees with the classical sum over
`1 ≤ a ≤ N`.) The factor `N^{k-1}` is written `N^k / N` to remain valid at `k = 0`. -/
noncomputable def generalizedBernoulli (χ : DirichletCharacter R N) (k : ℕ) : R :=
  ∑ a ∈ Finset.range N, χ (a : ZMod N) *
    algebraMap ℚ R ((N : ℚ) ^ k / N * (Polynomial.bernoulli k).eval ((a : ℚ) / N))

/-- `generalizedBernoulli` rewritten as a sum over all of `ZMod N` (rather than `range N`), the
form matching `ZMod.LFunction`. -/
theorem generalizedBernoulli_eq_sum_univ [NeZero N] (χ : DirichletCharacter R N) (k : ℕ) :
    generalizedBernoulli χ k = ∑ j : ZMod N, χ j *
      algebraMap ℚ R ((N : ℚ) ^ k / N * (Polynomial.bernoulli k).eval ((j.val : ℚ) / N)) := by
  rw [generalizedBernoulli]
  refine Finset.sum_nbij' (fun a => (a : ZMod N)) (fun j => j.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro j _; exact Finset.mem_range.mpr (ZMod.val_lt j)
  · intro a ha; exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
  · intro j _; exact ZMod.natCast_zmod_val j
  · intro a ha; rw [ZMod.val_cast_of_lt (Finset.mem_range.mp ha)]

end DirichletCharacter

/-! ### The bridge to Dirichlet `L`-function values at negative integers -/

