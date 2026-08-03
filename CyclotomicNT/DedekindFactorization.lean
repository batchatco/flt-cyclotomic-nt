import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Algebra.BigOperators.Field
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Dedekind zeta of `ℚ(ζ_p)` = product of Dirichlet `L`-functions — the local character identity

Toward Washington Thm 8.2 (`cyclotomic_unit_index`), the Dedekind zeta function of a cyclotomic
field factors as `ζ_{ℚ(ζ_p)}(s) = ∏_χ L(s,χ)`.  The algebraic heart of the
Euler-factor comparison at
a rational prime `q ≠ p` is the **local character identity**

  `∏_{χ mod p} (1 − χ(q)·t) = (1 − t^f)^g`,    `f = ord(q mod p)`, `g = (p−1)/f`,

matching the `q`-Euler factor of `∏_χ L(s,χ)` (left) with that of `ζ_K` (right, `f`/`g` = the
splitting of `q`).

**Done (here):** the roots-of-unity product (free from Mathlib's `pow_sub_pow_eq_prod_sub_mul`) and
`χ(a)^{ord a} = 1`.  The remaining content of the identity is the *counting* `|{χ : χ(a)=ζ}| = g`
for each `ζ ∈ μ_f` (fibers of `χ ↦ χ(a)` — a group hom onto `μ_f`).
-/

open Polynomial Finset

namespace CyclotomicNT.DedekindFactorization

variable {p : ℕ} [Fact p.Prime]

/-- **Roots-of-unity product** `∏_{ζ ∈ μ_n}(1 − ζ·t) = 1 − tⁿ` over `ℂ` — a direct specialization of
Mathlib's `IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul` (with `x = 1`). -/
theorem prod_one_sub_mul {n : ℕ} (hn : 0 < n) (t : ℂ) :
    ∏ ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ), (1 - ζ * t) = 1 - t ^ n := by
  have h : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn.ne'
  have key := IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul (x := (1 : ℂ)) (y := t) hn h
  simpa using key.symm

/-- Every value `χ(a)` of a Dirichlet character at a unit `a` is a `(ord a)`-th root of unity. -/
theorem dirichletChar_apply_pow_orderOf (χ : DirichletCharacter ℂ p) {a : ZMod p} :
    (χ a) ^ orderOf a = 1 := by
  rw [← map_pow, pow_orderOf_eq_one, map_one]

open scoped Classical in
/-- **Roots-of-unity orthogonality** in `ℂ`: for `w` an `f`-th root of unity, the indicator of
`w = 1` is `(1/f)·∑_{k<f} wᵏ`. -/
theorem indicator_eq_geom {f : ℕ} (hf : 0 < f) {w : ℂ} (hw : w ^ f = 1) :
    (if w = 1 then (1 : ℂ) else 0) = (∑ k ∈ range f, w ^ k) / f := by
  rcases eq_or_ne w 1 with rfl | hne
  · rw [if_pos rfl]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact (div_self (by exact_mod_cast hf.ne')).symm
  · rw [if_neg hne, geom_sum_eq hne, hw, sub_self]; simp

variable {a : ZMod p}

theorem orderOf_pos_of_isUnit (ha : IsUnit a) : 0 < orderOf a := by
  have hp2 := (Fact.out : p.Prime).two_le
  exact orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨p - 1, by omega, ZMod.pow_card_sub_one_eq_one ha.ne_zero⟩)

theorem orderOf_dvd_sub_one (ha : IsUnit a) : orderOf a ∣ (p - 1) :=
  orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one ha.ne_zero)

open scoped Classical in
/-- **Fiber count:** each `f`-th root of unity `ζ` is the value `χ(a)` for exactly `g = (p−1)/f`
Dirichlet characters `χ` — via `sum_characters_eq` and the orthogonality above. -/
theorem fiber_card (ha : IsUnit a) {ζ : ℂ} (hζ : ζ ∈ nthRootsFinset (orderOf a) (1 : ℂ)) :
    (univ.filter (fun χ : DirichletCharacter ℂ p => χ a = ζ)).card = (p - 1) / orderOf a := by
  haveI : NeZero ((Monoid.exponent (ZMod p)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  have hf := orderOf_pos_of_isUnit ha
  have hζ1 : ζ ^ orderOf a = 1 := by rw [mem_nthRootsFinset hf] at hζ; exact hζ
  have hζ0 : ζ ≠ 0 := fun h => by simp [h, hf.ne'] at hζ1
  have hfc : (orderOf a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hf.ne'
  have key : ∀ χ : DirichletCharacter ℂ p, ((if χ a = ζ then 1 else 0 : ℕ) : ℂ)
      = (∑ k ∈ range (orderOf a), (χ a * ζ⁻¹) ^ k) / orderOf a := by
    intro χ
    have hw : (χ a * ζ⁻¹) ^ orderOf a = 1 := by
      rw [mul_pow, dirichletChar_apply_pow_orderOf, inv_pow, hζ1, inv_one, one_mul]
    have hiff : (χ a * ζ⁻¹ = 1) ↔ (χ a = ζ) := mul_inv_eq_one₀ hζ0
    rw [← indicator_eq_geom hf hw]
    by_cases h : χ a = ζ
    · rw [if_pos h, if_pos (hiff.mpr h)]; norm_num
    · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh))]; norm_num
  apply Nat.cast_injective (R := ℂ)
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_congr rfl (fun χ _ => key χ),
    ← Finset.sum_div, Finset.sum_comm,
    Nat.cast_div (orderOf_dvd_sub_one ha) hfc]
  congr 1
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, Nat.totient_prime Fact.out]
  · intro k hk hk0
    rw [mem_range] at hk
    have hak : a ^ k ≠ 1 := fun h =>
      hk0 (Nat.eq_zero_of_dvd_of_lt (orderOf_dvd_iff_pow_eq_one.mpr h) hk)
    simp_rw [mul_pow]
    rw [← Finset.sum_mul]
    have hz : ∑ χ : DirichletCharacter ℂ p, (χ a) ^ k = 0 := by
      simp_rw [← map_pow]
      rw [DirichletCharacter.sum_characters_eq, if_neg hak]
    rw [hz, zero_mul]
  · intro h; exact absurd (mem_range.2 hf) h

open scoped Classical in
/-- **Local character identity** at a unit `a ∈ (ℤ/p)ˣ`:
`∏_{χ mod p} (1 − χ(a)·t) = (1 − t^f)^g`, with `f = ord(a)` and `g = (p−1)/f`.

Group the `(p−1)` characters by their value `ζ = χ(a)` (a group hom onto `μ_f`): each fiber has
`g` characters (`fiber_card`), so the product becomes `∏_{ζ ∈ μ_f}(1−ζt)^g = (1−t^f)^g` by the
roots-of-unity product `prod_one_sub_mul`.  This is the `q`-Euler factor of `∏_χ L(s,χ)` matched
against that of `ζ_{ℚ(ζ_p)}` (where `a = q`, `f`/`g` = the splitting of `q`). -/
theorem prod_char_one_sub (ha : IsUnit a) (t : ℂ) :
    ∏ χ : DirichletCharacter ℂ p, (1 - χ a * t) = (1 - t ^ orderOf a) ^ ((p - 1) / orderOf a) := by
  have hf := orderOf_pos_of_isUnit ha
  have hmaps : ∀ χ ∈ (univ : Finset (DirichletCharacter ℂ p)),
      χ a ∈ nthRootsFinset (orderOf a) (1 : ℂ) := fun χ _ =>
    (mem_nthRootsFinset hf (1 : ℂ)).2 (dirichletChar_apply_pow_orderOf χ)
  rw [← Finset.prod_fiberwise_of_maps_to hmaps (fun χ => 1 - χ a * t)]
  have hinner : ∀ ζ ∈ nthRootsFinset (orderOf a) (1 : ℂ),
      ∏ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ a = ζ), (1 - χ a * t)
        = (1 - ζ * t) ^ ((p - 1) / orderOf a) := by
    intro ζ hζ
    rw [Finset.prod_congr rfl (fun χ hχ => by rw [(Finset.mem_filter.1 hχ).2]),
      Finset.prod_const, fiber_card ha hζ]
  rw [Finset.prod_congr rfl hinner, Finset.prod_pow, prod_one_sub_mul hf]

open scoped Classical in
/-- **Unramified local Euler factor.**  At a prime `q ≠ p` (so `q` is a unit mod `p`), the inner
character product is the `ζ_K` Euler factor: `∏_χ (1 − χ(q)·t)⁻¹ = (1 − t^f)^{-g}` with
`f = ord(q mod p)`, `g = (p−1)/f` — the inverse of `prod_char_one_sub`
(`Finset.prod_inv_distrib`). -/
theorem prod_char_factor_prime {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (t : ℂ) :
    ∏ χ : DirichletCharacter ℂ p, (1 - χ (q : ZMod p) * t)⁻¹
      = ((1 - t ^ orderOf (q : ZMod p)) ^ ((p - 1) / orderOf (q : ZMod p)))⁻¹ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have ha : IsUnit (q : ZMod p) :=
    (ZMod.isUnit_iff_coprime q p).2 ((Nat.coprime_primes hq Fact.out).2 hqp)
  rw [Finset.prod_inv_distrib, prod_char_one_sub ha]

/-- **Ramified local factor.**  At `q = p` every character mod `p` vanishes
(`χ(p) = χ(0) = 0`), so the
inner product is `1`.  (The `ζ_K` Euler factor at `p` is instead supplied by
the imprimitivity of the
principal character: `L(s,χ₀) = ζ(s)·(1 − p^{-s})`.) -/
theorem prod_char_factor_ramified (t : ℂ) :
    ∏ χ : DirichletCharacter ℂ p, (1 - χ (p : ZMod p) * t)⁻¹ = 1 := by
  have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
  simp only [hp0, MulChar.map_zero, zero_mul, sub_zero, inv_one, Finset.prod_const_one]

open scoped LSeries.notation in
/-- **Product of Dirichlet L-functions as a single Euler product.**  For `Re s > 1`,
`∏_{χ mod p} L(s,χ) = ∏'_q ∏_{χ} (1 − χ(q)·q^{-s})⁻¹`, swapping the finite
character product with the
infinite Euler product over primes (each `L(s,χ)` is its own Euler product,
`LSeries_eulerProduct_tprod`;
the swap is `Multipliable.tprod_finsetProd`, justified by multipliability of each factor).

This is the structural reduction toward `ζ_{ℚ(ζ_p)} = ∏_χ L(s,χ)`: the inner local factor
`∏_χ (1 − χ(q)·q^{-s})⁻¹` is `prod_char_one_sub` (inverted) `= (1 −
q^{-sf})^{-g}`, the Euler factor of
`ζ_K` at an unramified `q` (`f = ord(q mod p)`, `g = (p−1)/f`). -/
theorem prod_dirichletL_eq_tprod {s : ℂ} (hs : 1 < s.re) :
    ∏ χ : DirichletCharacter ℂ p, (L ↗χ s)
      = ∏' q : Nat.Primes, ∏ χ : DirichletCharacter ℂ p, (1 - χ q * (q : ℂ) ^ (-s))⁻¹ := by
  have hmul : ∀ χ ∈ (univ : Finset (DirichletCharacter ℂ p)),
      Multipliable (fun q : Nat.Primes => (1 - χ q * (q : ℂ) ^ (-s))⁻¹) :=
    fun χ _ => (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable
  rw [Multipliable.tprod_finsetProd hmul]
  exact Finset.prod_congr rfl (fun χ _ => (DirichletCharacter.LSeries_eulerProduct_tprod χ hs).symm)

end CyclotomicNT.DedekindFactorization
