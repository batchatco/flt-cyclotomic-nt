import CyclotomicNT.EigenVector
import CyclotomicNT.PowerSumZMod

/-!
# Thm 8.14, piece 3a-iii (δ), steps 1–2 — `T(Ēᵢ) = ∑ a^{p−1−i}·v_{a·g}`

The eigenspace unit `Eᵢ` expands additively in `V` as `Ēᵢ = ∑_{a∈Icc 1 m} a^{p−1−i}·v_a`
(`eigenE_expand`), and applying `T` term-by-term (`galV_vc`) plus killing the constant `S·v_g` term
(`half_sum_pow_eq_zero`, since `S = ∑ a^{p−1−i} ≡ 0`) gives `T(Ēᵢ) = ∑ a^{p−1−i}·v_{a·g}`
(`galV_eigenE`).  Step δ-iii is the reindex `a ↦ (a·g reduced into [1,m])`. -/

namespace CyclotomicNT

open scoped NumberField
open NumberField NumberField.IsCMField Finset

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}

omit hpri [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
@[simp] theorem vOf_one : (vOf (1 : realUnits K) : ModN (Additive (realUnits K)) p) = 0 := by
  rw [vOf]; simp

omit hpri [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
theorem vOf_pow (u : realUnits K) (n : ℕ) :
    (vOf (u ^ n) : ModN (Additive (realUnits K)) p) = n • vOf u := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, vOf_mul, ih, succ_nsmul]

omit hpri [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
theorem vOf_prod {ι : Type*} (s : Finset ι) (f : ι → realUnits K) :
    (vOf (∏ a ∈ s, f a) : ModN (Additive (realUnits K)) p) = ∑ a ∈ s, vOf (f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih => rw [Finset.prod_insert ha, vOf_mul, Finset.sum_insert ha, ih]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- Step 1: the additive expansion `Ēᵢ = ∑_{a∈Icc 1 m} a^{p−1−i}·v_a` of the eigenspace unit. -/
theorem eigenE_expand (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (i : ℕ) :
    (vOf ⟨eigenCyclotomicUnit hζ i, eigenCyclotomicUnit_mem_realUnits hζ hp i⟩
      : ModN (Additive (realUnits K)) p)
      = ∑ a ∈ (Icc 1 ((p - 1) / 2)).attach,
          (a.1 ^ (p - 1 - i)) • vc hζ hp a.1 (coprime_of_mem_Icc a.2) := by
  have hsub : (⟨eigenCyclotomicUnit hζ i, eigenCyclotomicUnit_mem_realUnits hζ hp i⟩ : realUnits K)
      = ∏ a ∈ (Icc 1 ((p - 1) / 2)).attach,
          (⟨realCyclotomicUnit hζ a.1 (coprime_of_mem_Icc a.2),
            realCyclotomicUnit_mem_realUnits hζ hp _ _⟩ : realUnits K) ^ (a.1 ^ (p - 1 - i)) := by
    apply Subtype.ext
    simp only [eigenCyclotomicUnit, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow]
  rw [hsub, vOf_prod]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [vOf_pow, vc]

/-- Step 2: `T(Ēᵢ) = ∑_{a∈Icc 1 m} a^{p−1−i} • v_{a·g}` — the `−S·v_g` term vanishes since `S ≡
    0`. -/
theorem galV_eigenE (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (g : (ZMod p)ˣ) (i : ℕ)
    (hi : Even i) (h2 : 2 ≤ i) (h3 : i ≤ p - 3) :
    galV hζ g (vOf ⟨eigenCyclotomicUnit hζ i, eigenCyclotomicUnit_mem_realUnits hζ hp i⟩)
      = ∑ a ∈ (Icc 1 ((p - 1) / 2)).attach,
          (a.1 ^ (p - 1 - i)) • vc hζ hp (a.1 * (g : ZMod p).val)
            (Nat.coprime_mul_iff_left.mpr ⟨coprime_of_mem_Icc a.2, coprime_val g⟩) := by
  have hSvanish : (∑ a ∈ (Icc 1 ((p - 1) / 2)).attach,
      a.1 ^ (p - 1 - i) • vc hζ hp (g : ZMod p).val (coprime_val g)) = 0 := by
    rw [Finset.sum_congr rfl
        (fun a _ => (Nat.cast_smul_eq_nsmul (ZMod p) (a.1 ^ (p - 1 - i)) _).symm),
      ← Finset.sum_smul]
    have hcast : (∑ a ∈ (Icc 1 ((p - 1) / 2)).attach, ((a.1 ^ (p - 1 - i) : ℕ) : ZMod p)) = 0 := by
      rw [Finset.sum_attach (Icc 1 ((p - 1) / 2)) (fun a => ((a ^ (p - 1 - i) : ℕ) : ZMod p))]
      push_cast
      have heven : Even (p - 1) := by
        obtain ⟨k, hk⟩ := hpri.out.odd_of_ne_two hp; exact ⟨k, by omega⟩
      exact half_sum_pow_eq_zero p hp (p - 1 - i) (by omega) (by omega)
        ((Nat.even_sub (by omega)).mpr (iff_of_true heven hi))
    rw [hcast, zero_smul]
  rw [eigenE_expand hζ hp i]
  simp only [map_sum, map_nsmul, galV_vc]
  rw [Finset.sum_congr rfl (fun a _ => smul_sub (a.1 ^ (p - 1 - i)) _ _), Finset.sum_sub_distrib]
  exact sub_eq_self.mpr hSvanish

end CyclotomicNT
