import CyclotomicNT.KPlusBasic
import CyclotomicNT.CyclotomicUnitGroup
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.Cyclotomic.Discriminant

/-!
# `|disc K⁺| = p^{(p−3)/2}` for `K⁺ = maximalRealSubfield ℚ(ζ_p)`

Via the tower-discriminant formula (Mathlib's
`natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`):

  `p^{p−2} = |disc K| = N(𝔡_{K/K⁺}) · |disc K⁺|²`.

The relative different `𝔡_{K/K⁺}` contains `δ = ζ − ζ⁻¹` (the derivative of the minimal
polynomial `X² − (ζ+ζ⁻¹)X + 1` of `ζ` over `K⁺`, Mathlib's
`aeval_derivative_mem_differentIdeal`), and `N_{K/ℚ}(ζ − ζ⁻¹) = ±p` (since
`ζ − ζ⁻¹ = ζ⁻¹(ζ²−1)` with `ζ²` again primitive), so `N(𝔡) ∣ p`.  `N(𝔡) = 1` is impossible by
parity (`p−2` is odd), hence `N(𝔡) = p` and `|disc K⁺|² = p^{p−3}`.
-/

open NumberField Polynomial

namespace CyclotomicNT

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ p)

section RealTrace

omit [IsCyclotomicExtension {p} ℚ K] in
/-- `ζ + ζ⁻¹` is fixed by complex conjugation, hence lies in `K⁺`. -/
theorem zeta_add_inv_mem (hζ : IsPrimitiveRoot ζ p) :
    ζ + ζ⁻¹ ∈ maximalRealSubfield K := by
  rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_add, map_inv₀,
    complexConj_zeta hζ, inv_inv, add_comm]

/-- The element `ζ + ζ⁻¹` of `K⁺`. -/
noncomputable def realTrace : maximalRealSubfield K := ⟨ζ + ζ⁻¹, zeta_add_inv_mem hζ⟩

omit [IsCyclotomicExtension {p} ℚ K] in
@[simp] theorem coe_realTrace :
    (algebraMap (maximalRealSubfield K) K) (realTrace hζ) = ζ + ζ⁻¹ := rfl

omit [IsCyclotomicExtension {p} ℚ K] in
include hζ in
/-- `ζ` is not real (`p ≠ 2`): `ζ ∉ K⁺`. -/
theorem zeta_not_mem_real (hp : p ≠ 2) : ζ ∉ (algebraMap (maximalRealSubfield K) K).range := by
  rintro ⟨y, hy⟩
  have hfix : NumberField.IsCMField.complexConj K ζ = ζ := by
    rw [← hy]
    exact NumberField.IsCMField.complexConj_apply_eq_self K y
  rw [complexConj_zeta hζ] at hfix
  have hz_ne : ζ ≠ 0 := hζ.ne_zero hpri.out.pos.ne'
  have hsq : ζ ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← hfix]
    exact inv_mul_cancel₀ hz_ne
  have hdvd := (hζ.pow_eq_one_iff_dvd 2).mp hsq
  have h2 := hpri.out.two_le
  have := Nat.le_of_dvd (by omega) hdvd
  omega

end RealTrace

section Minpoly

/-- The quadratic `X² − (ζ+ζ⁻¹)X + 1` over `K⁺`. -/
noncomputable def realQuadratic : Polynomial (maximalRealSubfield K) :=
  X ^ 2 + (-(C (realTrace hζ)) * X + 1)

omit [IsCyclotomicExtension {p} ℚ K] in
theorem realQuadratic_lin_degree_lt :
    (-(C (realTrace hζ)) * X + 1 : Polynomial (maximalRealSubfield K)).degree
      < ((2 : ℕ) : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
  · refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    have h1 : (-(C (realTrace hζ))).degree ≤ 0 := by
      rw [degree_neg]
      exact degree_C_le
    refine lt_of_le_of_lt (add_le_add h1 degree_X.le) ?_
    norm_num
  · refine lt_of_le_of_lt degree_one_le ?_
    norm_num

omit [IsCyclotomicExtension {p} ℚ K] in
theorem realQuadratic_monic : (realQuadratic hζ).Monic :=
  monic_X_pow_add (realQuadratic_lin_degree_lt hζ)

omit [IsCyclotomicExtension {p} ℚ K] in
theorem realQuadratic_natDegree : (realQuadratic hζ).natDegree = 2 := by
  have hdeg : (realQuadratic hζ).degree = ((2 : ℕ) : WithBot ℕ) := by
    rw [realQuadratic, degree_add_eq_left_of_degree_lt, degree_X_pow]
    rw [degree_X_pow]
    exact realQuadratic_lin_degree_lt hζ
  exact natDegree_eq_of_degree_eq_some hdeg

omit [IsCyclotomicExtension {p} ℚ K] in
theorem aeval_realQuadratic_zeta : aeval ζ (realQuadratic hζ) = 0 := by
  have hz_ne : ζ ≠ 0 := hζ.ne_zero hpri.out.pos.ne'
  simp only [realQuadratic, map_add, map_mul, map_neg, map_pow, aeval_X, aeval_C, map_one]
  rw [coe_realTrace]
  field_simp
  ring

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **The minimal polynomial of `ζ` over `K⁺`** is `X² − (ζ+ζ⁻¹)X + 1`. -/
theorem minpoly_zeta_real (hp : p ≠ 2) :
    minpoly (maximalRealSubfield K) ζ = realQuadratic hζ := by
  have hint : IsIntegral (maximalRealSubfield K) ζ :=
    Algebra.IsIntegral.isIntegral ζ
  have hdvd : minpoly (maximalRealSubfield K) ζ ∣ realQuadratic hζ :=
    minpoly.dvd _ _ (aeval_realQuadratic_zeta hζ)
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (realQuadratic_monic hζ)
    hdvd ?_).symm
  rw [realQuadratic_natDegree hζ]
  have hpos : 0 < (minpoly (maximalRealSubfield K) ζ).natDegree := minpoly.natDegree_pos hint
  have hne1 : (minpoly (maximalRealSubfield K) ζ).natDegree ≠ 1 := fun h =>
    zeta_not_mem_real hζ hp (minpoly.natDegree_eq_one_iff.mp h)
  omega

end Minpoly

section Different

omit [IsCyclotomicExtension {p} ℚ K] in
include hζ in
/-- `K = K⁺(ζ)`: the algebra adjoin of `ζ` over `K⁺` is everything (degree count). -/
theorem adjoin_zeta_eq_top (hp : p ≠ 2) :
    Algebra.adjoin (maximalRealSubfield K) ({ζ} : Set K) = ⊤ := by
  have hint : IsIntegral (maximalRealSubfield K) ζ := Algebra.IsIntegral.isIntegral ζ
  have hfr : Module.finrank (maximalRealSubfield K)
      (Algebra.adjoin (maximalRealSubfield K) ({ζ} : Set K)) = 2 := by
    rw [(Algebra.adjoin.powerBasis hint).finrank, Algebra.adjoin.powerBasis_dim hint,
      minpoly_zeta_real hζ hp, realQuadratic_natDegree hζ]
  have h2 : Module.finrank (maximalRealSubfield K) K = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ K
  apply Subalgebra.toSubmodule_injective
  rw [Algebra.top_toSubmodule]
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [Subalgebra.finrank_toSubmodule, hfr, h2]

/-- The derivative of the minimal polynomial of `ζ` over `𝓞 K⁺`, evaluated at `ζ` — the
generator of the different that we can compute. -/
noncomputable def diffElt : 𝓞 K :=
  aeval hζ.toInteger (derivative (minpoly (𝓞 (maximalRealSubfield K)) hζ.toInteger))

omit [IsCyclotomicExtension {p} ℚ K] in
/-- `diffElt ∈ 𝔡_{K/K⁺}` (Mathlib's `aeval_derivative_mem_differentIdeal`). -/
theorem diffElt_mem_differentIdeal (hp : p ≠ 2) :
    diffElt hζ ∈ differentIdeal (𝓞 (maximalRealSubfield K)) (𝓞 K) := by
  refine aeval_derivative_mem_differentIdeal (A := 𝓞 (maximalRealSubfield K))
    (maximalRealSubfield K) K hζ.toInteger ?_
  rw [show (algebraMap (𝓞 K) K) hζ.toInteger = ζ from hζ.coe_toInteger]
  exact adjoin_zeta_eq_top hζ hp

omit [IsCyclotomicExtension {p} ℚ K] in
/-- The `K`-value of `diffElt` is `ζ − ζ⁻¹`. -/
theorem coe_diffElt (hp : p ≠ 2) :
    (algebraMap (𝓞 K) K) (diffElt hζ) = ζ - ζ⁻¹ := by
  have hz_ne : ζ ≠ 0 := hζ.ne_zero hpri.out.pos.ne'
  have hintO : IsIntegral (𝓞 (maximalRealSubfield K)) hζ.toInteger :=
    Algebra.IsIntegral.isIntegral _
  -- the `𝓞K⁺`-minimal polynomial maps to the field one
  have hmp : minpoly (maximalRealSubfield K) ζ
      = (minpoly (𝓞 (maximalRealSubfield K)) hζ.toInteger).map
          (algebraMap (𝓞 (maximalRealSubfield K)) (maximalRealSubfield K)) := by
    have h := minpoly.isIntegrallyClosed_eq_field_fractions (maximalRealSubfield K) K
      (s := hζ.toInteger) hintO
    rwa [show (algebraMap (𝓞 K) K) hζ.toInteger = ζ from hζ.coe_toInteger] at h
  -- push `algebraMap (𝓞 K) K` through the evaluation
  have ht : (algebraMap (𝓞 K) K) hζ.toInteger = ζ := hζ.coe_toInteger
  rw [diffElt, ← Polynomial.aeval_algebraMap_apply K hζ.toInteger, ht,
    ← Polynomial.aeval_map_algebraMap (maximalRealSubfield K), ← derivative_map, ← hmp,
    minpoly_zeta_real hζ hp, realQuadratic]
  -- compute the derivative and evaluate
  simp only [derivative_add, derivative_mul, derivative_neg, derivative_C, derivative_X,
    derivative_one, derivative_X_pow]
  simp only [map_add, map_mul, map_neg, map_pow, aeval_X, aeval_C, map_one, map_ofNat,
    Nat.cast_ofNat, map_zero]
  rw [coe_realTrace]
  field_simp
  ring

end Different

section Norm

omit [NumberField K] [IsCMField K] in
include hζ in
/-- `N_{K/ℚ}(ζ − ζ⁻¹) = p`: factor as `ζ⁻¹(ζ²−1)` with `ζ²` again a primitive root. -/
theorem norm_zeta_sub_inv (hp : p ≠ 2) :
    Algebra.norm ℚ (ζ - ζ⁻¹) = (p : ℚ) := by
  have hz_ne : ζ ≠ 0 := hζ.ne_zero hpri.out.pos.ne'
  have hirr : Irreducible (Polynomial.cyclotomic p ℚ) :=
    Polynomial.cyclotomic.irreducible_rat hpri.out.pos
  have hfact : ζ - ζ⁻¹ = ζ⁻¹ * (ζ ^ 2 - 1) := by
    field_simp
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) p :=
    hζ.pow_of_coprime 2 ((Nat.coprime_primes Nat.prime_two hpri.out).mpr fun h => hp h.symm)
  have hn2 : Algebra.norm ℚ (ζ ^ 2 - 1) = (p : ℚ) := by
    rw [hζ2.sub_one_norm_isPrimePow hpri.out.isPrimePow hirr hp, hpri.out.minFac_eq]
  have hn1 : Algebra.norm ℚ ζ = 1 := hζ.norm_eq_one hp hirr
  have hninv : Algebra.norm ℚ ζ⁻¹ = 1 := by
    have h := congrArg (Algebra.norm ℚ) (inv_mul_cancel₀ hz_ne)
    rwa [map_mul, map_one, hn1, mul_one] at h
  rw [hfact, map_mul, hninv, one_mul, hn2]

/-- The principal ideal `(diffElt)` has absolute norm `p`. -/
theorem absNorm_span_diffElt (hp : p ≠ 2) :
    Ideal.absNorm (Ideal.span {diffElt hζ}) = p := by
  rw [Ideal.absNorm_span_singleton]
  have hcast : ((Algebra.norm ℤ (diffElt hζ) : ℤ) : ℚ)
      = Algebra.norm ℚ ((algebraMap (𝓞 K) K) (diffElt hζ)) := Algebra.coe_norm_int _
  rw [coe_diffElt hζ hp, norm_zeta_sub_inv hζ hp] at hcast
  have hZ : Algebra.norm ℤ (diffElt hζ) = (p : ℤ) := by exact_mod_cast hcast
  rw [hZ]
  exact Int.natAbs_natCast p

end Norm

section Tower

/-- **The tower-discriminant formula for `K/K⁺`**:
`p^{p−2} = N(𝔡_{K/K⁺}) · |disc K⁺|²`. -/
theorem pow_eq_absNorm_differentIdeal_mul_discr_sq :
    p ^ (p - 2) = Ideal.absNorm (differentIdeal (𝓞 (maximalRealSubfield K)) (𝓞 K))
      * (discr (maximalRealSubfield K)).natAbs ^ 2 := by
  haveI : Module.Finite (𝓞 (maximalRealSubfield K)) (𝓞 K) :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := maximalRealSubfield K) (𝒪 := 𝓞 (maximalRealSubfield K)) K (𝓞 K)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K] at h
  rw [← h, IsCyclotomicExtension.Rat.discr_prime p K, Int.natAbs_mul, Int.natAbs_pow,
    Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul, Int.natAbs_pow, Int.natAbs_natCast]

include hζ in
/-- **`|disc K⁺| = p^{(p−3)/2}`.** -/
theorem natAbs_discr_maximalRealSubfield (hp : p ≠ 2) :
    (discr (maximalRealSubfield K)).natAbs = p ^ ((p - 3) / 2) := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp)
  have hp3 : 3 ≤ p := by have := hpri.out.two_le; omega
  have htower := pow_eq_absNorm_differentIdeal_mul_discr_sq (K := K) (p := p)
  set d := (discr (maximalRealSubfield K)).natAbs with hd
  set N := Ideal.absNorm (differentIdeal (𝓞 (maximalRealSubfield K)) (𝓞 K)) with hN
  -- `N ∣ p` via `𝔡 ⊇ (ζ − ζ⁻¹)`
  have hNdvd : N ∣ p := by
    rw [← absNorm_span_diffElt hζ hp, hN]
    refine Ideal.absNorm_dvd_absNorm_of_le ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact SetLike.mem_coe.mpr (diffElt_mem_differentIdeal hζ hp)
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, pow_two, mul_zero, mul_zero] at htower
    exact absurd htower (by positivity)
  rcases (Nat.Prime.eq_one_or_self_of_dvd hpri.out N hNdvd) with hN1 | hNp
  · -- `N = 1` contradicts parity: `p−2` is odd but `v_p(d²)` is even
    exfalso
    rw [hN1, one_mul] at htower
    have hfac := congrArg (fun n => n.factorization p) htower
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hfac
    rw [Nat.Prime.factorization_self hpri.out] at hfac
    omega
  · -- `N = p`: `d² = p^{p−3}` and extract the square root
    rw [hNp] at htower
    have hd2 : d ^ 2 = p ^ (p - 3) := by
      refine Nat.eq_of_mul_eq_mul_left hpri.out.pos ?_
      rw [← htower, ← pow_succ']
      congr 1
      omega
    have hdvd : d ∣ p ^ (p - 3) := by
      rw [← hd2]
      exact dvd_pow_self d two_ne_zero
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow hpri.out).mp hdvd
    rw [hj, ← pow_mul] at hd2
    have h2j : j * 2 = p - 3 := Nat.pow_right_injective hpri.out.two_le hd2
    rw [hj]
    congr 1
    omega

end Tower

end CyclotomicNT
