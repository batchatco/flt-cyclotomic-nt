import CyclotomicNT.EvenCharBijection
import CyclotomicNT.EvenLOneValue

/-!
# The regulator eigenvalues are the even `L(1,χ)` values

The reduced-group-determinant eigenvalue at `k = k(χ)` (for an even `χ ≠ 1`) is

  `λ_k = ∑_{x ∈ ℤ/m} log‖1−e(g^x/p)‖·e(−kx/m) = −½·τ(χ⁻¹)·L(1,χ)`

— matching `CyclotomicRegulator`'s `∏‖λ_k‖` with the analytic data of
`gaussSum_mul_LFunction_one_even`.  Proof: the full character sum
`∑_{a mod p} χ⁻¹(a)·log‖1−e(a/p)‖` is supported on units; reindex the units by the generator
cycle `j ↦ g^j` (`j < p−1`); `χ⁻¹(g^j) = e(−kj/m)`; the two half-cycles `j` and `j+m`
contribute equally (`vFun` is `m`-periodic and `e(−k(j+m)/m) = e(−kj/m)`), giving twice the
`ℤ/m`-sum.
-/

open NumberField Finset

namespace CyclotomicNT

variable {p : ℕ} [hpri : Fact p.Prime] {g : (ZMod p)ˣ}

/-- Reindex a sum over `ℤ/p` of a function vanishing off the units by the generator cycle:
`∑_{a mod p} F a = ∑_{j < p−1} F(g^j)`. -/
theorem sum_zmod_eq_sum_range_generator (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g)
    (F : ZMod p → ℂ) (hF0 : F 0 = 0) :
    ∑ a : ZMod p, F a = ∑ j ∈ range (p - 1), F ((g ^ j : (ZMod p)ˣ) : ZMod p) := by
  have horder : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hpri.out]
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ (0 : ZMod p)), hF0, zero_add]
  refine (Finset.sum_bij (fun j _ => ((g ^ j : (ZMod p)ˣ) : ZMod p)) ?_ ?_ ?_ ?_).symm
  · intro j _
    exact Finset.mem_erase.mpr ⟨Units.ne_zero _, Finset.mem_univ _⟩
  · intro j hj j' hj' h
    have hu : (g ^ j : (ZMod p)ˣ) = g ^ j' := Units.ext h
    exact pow_injOn_Iio_orderOf (by rw [horder]; exact Set.mem_Iio.mpr (mem_range.mp hj))
      (by rw [horder]; exact Set.mem_Iio.mpr (mem_range.mp hj')) hu
  · intro a ha
    obtain ⟨ha0, -⟩ := Finset.mem_erase.mp ha
    have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha0
    obtain ⟨t, ht⟩ := mem_powers_iff_mem_zpowers.mpr (hgen hu.unit)
    refine ⟨t % (p - 1), mem_range.mpr (Nat.mod_lt _ ?_), ?_⟩
    · have := hpri.out.two_le
      omega
    · show ((g ^ (t % (p - 1)) : (ZMod p)ˣ) : ZMod p) = a
      have h1 : g ^ (t % (p - 1)) = g ^ t := by rw [← horder, pow_mod_orderOf]
      have h2 : g ^ t = hu.unit := ht
      rw [h1, h2, IsUnit.unit_spec]
  · intro j _
    rfl

/-- The inverse character along the cycle: `χ⁻¹(g^j) = e(−kj/m)` for `k = k(χ)`. -/
theorem inv_char_apply_pow [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2)
    (χ : {χ : DirichletCharacter ℂ p // χ.Even}) (j : ℕ) :
    χ.1⁻¹ ((g ^ j : (ZMod p)ˣ) : ZMod p)
      = ZMod.stdAddChar ((j : ZMod ((p - 1) / 2)) * (-(evenCharIdx hgen hp χ))) := by
  have hinv : χ.1⁻¹ ((g : ZMod p)) = ZMod.stdAddChar (-(evenCharIdx hgen hp χ)) := by
    rw [MulChar.inv_apply_eq_inv, ← stdAddChar_evenCharIdx hgen hp χ, Ring.inverse_eq_inv,
      ← AddChar.map_neg_eq_inv]
  rw [Units.val_pow_eq_pow_val, map_pow, hinv, stdAddChar_pow]

/-- **The eigenvalue–`L`-value identity**: for even `χ ≠ 1` with index `k = k(χ)`,
`λ_k = −½·τ(χ⁻¹)·L(1,χ)`. -/
theorem lam_eq_neg_half_gaussSum_mul_LFunction [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2)
    (χ : {χ : DirichletCharacter ℂ p // χ.Even}) (hχ1 : χ.1 ≠ 1) :
    ∑ x : ZMod ((p - 1) / 2), ((vIdx g x : ℝ) : ℂ)
        * (AddChar.mulShift ZMod.stdAddChar (evenCharIdx hgen hp χ)) (-x)
      = -(1 / 2) * (gaussSum χ.1⁻¹ ZMod.stdAddChar * DirichletCharacter.LFunction χ.1 1) := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp)
  have hp2 : 2 ≤ p := hpri.out.two_le
  -- the analytic input
  rw [gaussSum_mul_LFunction_one_even χ.1 hχ1 χ.2]
  -- kill the `a = 0` term and reindex by the generator cycle
  rw [sum_zmod_eq_sum_range_generator hgen _ (by
    rw [MulChar.map_nonunit _ (by simp), zero_mul])]
  -- per-term: `χ⁻¹(g^j)·(−log‖1−e(g^j/p)‖) = −(e(−kj/m)·vFun j)`
  have hterm : ∀ j : ℕ,
      χ.1⁻¹ ((g ^ j : (ZMod p)ˣ) : ZMod p)
          * (-((Real.log ‖1 - ZMod.stdAddChar ((g ^ j : (ZMod p)ˣ) : ZMod p)‖ : ℝ) : ℂ))
        = -(ZMod.stdAddChar ((j : ZMod ((p - 1) / 2)) * (-(evenCharIdx hgen hp χ)))
            * ((vFun g j : ℝ) : ℂ)) := by
    intro j
    rw [inv_char_apply_pow hgen hp χ j]
    simp only [vFun]
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_neg_distrib]
  -- split the cycle `range (p−1) = range m ∪ (m + range m)` into two equal halves
  have hsplit : ∑ j ∈ range (p - 1),
      ZMod.stdAddChar ((j : ZMod ((p - 1) / 2)) * (-(evenCharIdx hgen hp χ)))
        * ((vFun g j : ℝ) : ℂ)
      = 2 * ∑ j ∈ range ((p - 1) / 2),
          ZMod.stdAddChar ((j : ZMod ((p - 1) / 2)) * (-(evenCharIdx hgen hp χ)))
            * ((vFun g j : ℝ) : ℂ) := by
    have hpm : p - 1 = (p - 1) / 2 + (p - 1) / 2 := by omega
    rw [show range (p - 1) = range ((p - 1) / 2 + (p - 1) / 2) from congrArg _ hpm,
      Finset.sum_range_add]
    have hsecond : ∀ j : ℕ,
        ZMod.stdAddChar ((((p - 1) / 2 + j : ℕ) : ZMod ((p - 1) / 2))
              * (-(evenCharIdx hgen hp χ)))
            * ((vFun g ((p - 1) / 2 + j) : ℝ) : ℂ)
          = ZMod.stdAddChar ((j : ZMod ((p - 1) / 2)) * (-(evenCharIdx hgen hp χ)))
              * ((vFun g j : ℝ) : ℂ) := by
      intro j
      have hcast : (((p - 1) / 2 + j : ℕ) : ZMod ((p - 1) / 2)) = (j : ZMod ((p - 1) / 2)) := by
        push_cast
        rw [ZMod.natCast_self, zero_add]
      have hper : vFun g ((p - 1) / 2 + j) = vFun g j := by
        rw [add_comm]
        exact vFun_periodic hgen hp j
      rw [hcast, hper]
    rw [Finset.sum_congr rfl fun j _ => hsecond j]
    ring
  rw [hsplit]
  -- convert the `range m` sum to the `ℤ/m` sum
  have hzmod : ∑ j ∈ range ((p - 1) / 2),
      ZMod.stdAddChar ((j : ZMod ((p - 1) / 2)) * (-(evenCharIdx hgen hp χ)))
        * ((vFun g j : ℝ) : ℂ)
      = ∑ x : ZMod ((p - 1) / 2), ((vIdx g x : ℝ) : ℂ)
          * (AddChar.mulShift ZMod.stdAddChar (evenCharIdx hgen hp χ)) (-x) := by
    refine Finset.sum_bij (fun j _ => ((j : ZMod ((p - 1) / 2)))) ?_ ?_ ?_ ?_
    · intro j _
      exact Finset.mem_univ _
    · intro j hj j' hj' h
      have h1 := congrArg ZMod.val h
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hj),
        Nat.mod_eq_of_lt (mem_range.mp hj')] at h1
    · intro x _
      refine ⟨x.val, mem_range.mpr (ZMod.val_lt x), ?_⟩
      show ((x.val : ℕ) : ZMod ((p - 1) / 2)) = x
      rw [ZMod.natCast_val, ZMod.cast_id]
    · intro j hj
      rw [AddChar.mulShift_apply, vIdx_natCast hgen hp, mul_comm ((vFun g j : ℝ) : ℂ)]
      congr 2
      ring
  rw [hzmod]
  ring

section GaussSumNorm

/-- The conjugate Gauss sum: `conj τ(χ⁻¹) = gaussSum χ ψ⁻¹` (character values conjugate to
inverse values, `conj e(x/p) = e(−x/p)`). -/
theorem conj_gaussSum_inv (χ : DirichletCharacter ℂ p) :
    (starRingEnd ℂ) (gaussSum χ⁻¹ ZMod.stdAddChar) = gaussSum χ ZMod.stdAddChar⁻¹ := by
  rw [gaussSum, gaussSum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul]
  congr 1
  · have h := MulChar.star_apply' χ⁻¹ x
    rw [inv_inv] at h
    rw [← RCLike.star_def, h]
  · rw [conj_stdAddChar, AddChar.inv_apply]

/-- **The Gauss sum has absolute value `√p`**: `‖τ(χ⁻¹)‖ = √p` for `χ ≠ 1`. -/
theorem norm_gaussSum_inv (χ : DirichletCharacter ℂ p) (hχ1 : χ ≠ 1) :
    ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ = Real.sqrt p := by
  have hψ := ZMod.isPrimitive_stdAddChar p
  have hχinv : χ⁻¹ ≠ 1 := fun h => hχ1 (by rw [← inv_inv χ, h, inv_one])
  have hmul := gaussSum_mul_gaussSum_eq_card hχinv hψ
  rw [inv_inv, ZMod.card] at hmul
  have hconj : gaussSum χ⁻¹ ZMod.stdAddChar
        * (starRingEnd ℂ) (gaussSum χ⁻¹ ZMod.stdAddChar) = (p : ℂ) := by
    rw [conj_gaussSum_inv χ, hmul]
  rw [Complex.mul_conj] at hconj
  have hsq : ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 = (p : ℝ) := by
    have h2 : ((Complex.normSq (gaussSum χ⁻¹ ZMod.stdAddChar) : ℝ) : ℂ) = ((p : ℝ) : ℂ) := by
      rw [hconj]
      push_cast
      ring
    have h3 := Complex.ofReal_injective h2
    rwa [Complex.normSq_eq_norm_sq] at h3
  rw [← Real.sqrt_sq (norm_nonneg (gaussSum χ⁻¹ ZMod.stdAddChar)), hsq]

end GaussSumNorm

end CyclotomicNT
