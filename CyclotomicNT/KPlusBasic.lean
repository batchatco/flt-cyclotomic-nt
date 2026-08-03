import CyclotomicNT.CyclotomicPlaceCycle
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Basic invariants of `K⁺ = maximalRealSubfield ℚ(ζ_p)`

The inputs to the class number formula for `K⁺`:

* `finrank ℚ K⁺ = m` and `nrRealPlaces K⁺ = m`, `nrComplexPlaces K⁺ = 0` (`m = (p−1)/2`);
* `torsionOrder K⁺ = 2` (any number field with a real place has torsion `{±1}` — the
  totally-real strengthening of Mathlib's `torsionOrder_eq_two_of_odd_finrank`);
* the explicit residue: `dedekindZeta_residue K⁺ = 2^{m−1}·Reg(K⁺)·h⁺/√|disc K⁺|`.
-/

open NumberField NumberField.InfinitePlace NumberField.Units

namespace CyclotomicNT

section RealTorsion

variable {F : Type*} [Field F] [NumberField F]

set_option backward.isDefEq.respectTransparency false in
/-- **Torsion of a field with a real place is `±1`** (a root of unity of order `> 2` kills all
real places) — Mathlib's `torsion_eq_one_or_neg_one_of_odd_finrank` with the
odd-degree hypothesis relaxed to the existence of a real place. -/
theorem torsion_eq_one_or_neg_one_of_nrRealPlaces_pos (h : 0 < nrRealPlaces F)
    (x : torsion F) : (x : (𝓞 F)ˣ) = 1 ∨ (x : (𝓞 F)ˣ) = -1 := by
  by_cases! hc : 2 < orderOf (x : (𝓞 F)ˣ)
  · rw [← orderOf_units, ← orderOf_submonoid] at hc
    linarith [IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc
      (IsPrimitiveRoot.orderOf (x.1 : F))]
  · interval_cases hi : orderOf (x : (𝓞 F)ˣ)
    · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]
    · exact Or.intro_left _ (orderOf_eq_one_iff.1 hi)
    · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, ← Units.val_inj, Units.val_neg, Units.val_one, hi]

/-- **`torsionOrder = 2` for a field with a real place.** -/
theorem torsionOrder_eq_two_of_nrRealPlaces_pos (h : 0 < nrRealPlaces F) :
    torsionOrder F = 2 := by
  classical
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact torsion_eq_one_or_neg_one_of_nrRealPlaces_pos h x

end RealTorsion

section KPlus

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

/-- `[K⁺ : ℚ] = (p−1)/2`. -/
theorem finrank_maximalRealSubfield (hp : p ≠ 2) :
    Module.finrank ℚ (maximalRealSubfield K) = (p - 1) / 2 := by
  have h2 : Module.finrank (maximalRealSubfield K) K = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ K
  have htower := Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K
  have hK : Module.finrank ℚ K = p - 1 := by
    rw [IsCyclotomicExtension.finrank (K := ℚ) (L := K)
      (Polynomial.cyclotomic.irreducible_rat hpri.out.pos), Nat.totient_prime hpri.out]
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp)
  rw [h2, hK] at htower
  omega

/-- `K⁺` has `(p−1)/2` real places and no complex places. -/
theorem nrRealPlaces_maximalRealSubfield (hp : p ≠ 2) :
    nrRealPlaces (maximalRealSubfield K) = (p - 1) / 2 := by
  have h0 : nrComplexPlaces (maximalRealSubfield K) = 0 :=
    IsTotallyReal.nrComplexPlaces_eq_zero _
  have hsum := card_add_two_mul_card_eq_rank (maximalRealSubfield K)
  rw [h0, finrank_maximalRealSubfield hp] at hsum
  omega

omit [IsCMField K] in
theorem nrComplexPlaces_maximalRealSubfield :
    nrComplexPlaces (maximalRealSubfield K) = 0 :=
  IsTotallyReal.nrComplexPlaces_eq_zero _

theorem torsionOrder_maximalRealSubfield (hp : p ≠ 2) :
    torsionOrder (maximalRealSubfield K) = 2 := by
  refine torsionOrder_eq_two_of_nrRealPlaces_pos ?_
  rw [nrRealPlaces_maximalRealSubfield hp]
  exact Nat.pos_of_ne_zero (half_pred_ne_zero hp)

/-- **The explicit residue of `ζ_{K⁺}`**:
`dedekindZeta_residue K⁺ = 2^{m−1}·Reg(K⁺)·h⁺/√|disc K⁺|` (`r₁ = m`, `r₂ = 0`, `w = 2`). -/
theorem dedekindZeta_residue_maximalRealSubfield (hp : p ≠ 2) :
    dedekindZeta_residue (maximalRealSubfield K)
      = 2 ^ ((p - 1) / 2 - 1) * regulator (maximalRealSubfield K)
          * classNumber (maximalRealSubfield K)
          / Real.sqrt |(discr (maximalRealSubfield K) : ℝ)| := by
  have hm : (1 : ℕ) ≤ (p - 1) / 2 := Nat.pos_of_ne_zero (half_pred_ne_zero hp)
  rw [dedekindZeta_residue, nrRealPlaces_maximalRealSubfield hp,
    nrComplexPlaces_maximalRealSubfield, torsionOrder_maximalRealSubfield hp]
  rw [pow_zero, mul_one, show ((p - 1) / 2 : ℕ) = ((p - 1) / 2 - 1) + 1 by omega, pow_succ]
  push_cast
  ring

end KPlus

end CyclotomicNT
