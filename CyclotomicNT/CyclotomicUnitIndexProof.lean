import CyclotomicNT.ProductTransfer
import CyclotomicNT.KPlusEuler
import CyclotomicNT.KPlusDisc

/-!
# Washington Theorem 8.2: `[E : C] = h⁺` — the proof

The final assembly discharging `cyclotomic_unit_index`:

* `relIndex_mul_regulator_eq_prod_norm_LFunction` (ProductTransfer):
  `[E:C]·Reg(K⁺) = (√p/2)^{m−1}·∏_{χ even≠1}‖L(1,χ)‖`;
* `dedekindZeta_residue_real_eq_prod` (KPlusEuler):
  `Res ζ_{K⁺} = ∏_{χ even≠1} L(1,χ)`;
* `dedekindZeta_residue_maximalRealSubfield` (KPlusBasic):
  `Res = 2^{m−1}·Reg(K⁺)·h⁺/√|disc K⁺|`;
* `natAbs_discr_maximalRealSubfield` (KPlusDisc): `|disc K⁺| = p^{(p−3)/2}`.

The constants cancel exactly — `(√p/2)^{m−1}·2^{m−1} = (√p)^{m−1} = √(p^{(p−3)/2})` — leaving
`[E:C]·Reg(K⁺) = h⁺·Reg(K⁺)`, and `Reg(K⁺) > 0` finishes.
-/

open NumberField NumberField.Units Finset

namespace CyclotomicNT

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}

open scoped Classical in
/-- **Washington, Theorem 8.2**: the index of the cyclotomic unit group `C` in the real units
`E` of `ℚ(ζ_p)` is the class number `h⁺` of the maximal real subfield. -/
theorem cyclotomic_unit_index_proof (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) :
    (cyclotomicUnitGroup hζ).relIndex (NumberField.IsCMField.realUnits K) =
      Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K))) := by
  haveI : NeZero ((p - 1) / 2) := ⟨half_pred_ne_zero hp⟩
  obtain ⟨g, hgen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp)
  have hp3 : 3 ≤ p := by have := hpri.out.two_le; omega
  -- the geometric identity
  have hPT := relIndex_mul_regulator_eq_prod_norm_LFunction hζ hgen hp
  -- the analytic identity, normed
  have hRes := dedekindZeta_residue_real_eq_prod (K := K) hgen hp
  have hnorm := congrArg norm hRes
  rw [Complex.norm_real, Real.norm_eq_abs, norm_prod] at hnorm
  -- the residue is nonnegative
  have hreg_pos : (0 : ℝ) < regulator (maximalRealSubfield K) :=
    regulator_pos (maximalRealSubfield K)
  have hres_nonneg : 0 ≤ dedekindZeta_residue (maximalRealSubfield K) := by
    rw [dedekindZeta_residue_maximalRealSubfield hp]
    positivity
  rw [abs_of_nonneg hres_nonneg] at hnorm
  -- align the index sets
  rw [Finset.filter_erase] at hPT
  -- the discriminant value
  have hppos : (0 : ℝ) < p := by positivity
  have hdisc : |((discr (maximalRealSubfield K) : ℤ) : ℝ)| = (p : ℝ) ^ ((p - 3) / 2) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, natAbs_discr_maximalRealSubfield hζ hp]
    push_cast
    ring
  -- the constant collapse
  have hsq : Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) = Real.sqrt p ^ ((p - 3) / 2) := by
    rw [show (p : ℝ) ^ ((p - 3) / 2) = (Real.sqrt p ^ 2) ^ ((p - 3) / 2) by
        rw [Real.sq_sqrt hppos.le],
      ← pow_mul, mul_comm 2 ((p - 3) / 2), pow_mul, Real.sqrt_sq (by positivity)]
  have hm1 : (p - 1) / 2 - 1 = (p - 3) / 2 := by omega
  have hsqrt_pos : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr hppos
  have hconst : (Real.sqrt p / 2) ^ ((p - 1) / 2 - 1)
        * (2 ^ ((p - 1) / 2 - 1) * regulator (maximalRealSubfield K)
            * (classNumber (maximalRealSubfield K))
            / Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)))
      = (classNumber (maximalRealSubfield K) : ℝ) * regulator (maximalRealSubfield K) := by
    rw [hsq, hm1]
    have h1 : ((1 : ℝ) / 2) ^ ((p - 3) / 2) * 2 ^ ((p - 3) / 2) = 1 := by
      rw [← mul_pow]
      norm_num
    field_simp
    linear_combination (Real.sqrt p ^ ((p - 3) / 2)
      * (classNumber (maximalRealSubfield K) : ℝ)) * h1
  -- combine and cancel the regulator
  have key : ((cyclotomicUnitGroup hζ).relIndex (NumberField.IsCMField.realUnits K) : ℝ)
        * regulator (maximalRealSubfield K)
      = (classNumber (maximalRealSubfield K) : ℝ) * regulator (maximalRealSubfield K) := by
    rw [hPT, ← hnorm, dedekindZeta_residue_maximalRealSubfield hp, hdisc, hconst]
  have hfin := mul_right_cancel₀ hreg_pos.ne' key
  have hN : (cyclotomicUnitGroup hζ).relIndex (NumberField.IsCMField.realUnits K)
      = classNumber (maximalRealSubfield K) := Nat.cast_injective hfin
  rw [hN]
  rfl

end CyclotomicNT
