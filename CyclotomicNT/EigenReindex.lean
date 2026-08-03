import CyclotomicNT.EigenSum

/-!
# Thm 8.14, piece 3a-iii (δ) step 3 — the reindex `a ↦ red(a·g)` (foundation)

To finish `T(Ēᵢ) = g^i·Ēᵢ` we reindex `∑ a^{p-1-i}·v_{a·g}` by `a ↦ red(a·g)`, where `red p n`
    reduces
`n` to its `±`-representative in `[1, (p-1)/2]`.  Here we set up `red` and prove `v_n = v_{red n}`
(`vc_red`, combining periodicity β and reflection α).  The bijection on `Icc 1 ((p-1)/2)` and the
coefficient congruence `a^{p-1-i} ≡ g^i·(red(a·g))^{p-1-i} (mod p)` come next. -/

namespace CyclotomicNT
open scoped NumberField
open NumberField NumberField.IsCMField Finset

/-- Reduce `n` to its representative in `[1, (p-1)/2]` under `±` mod `p`. -/
def red (p n : ℕ) : ℕ := if n % p ≤ (p - 1) / 2 then n % p else p - n % p

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}

theorem red_pos_lt (hp : p ≠ 2) (n : ℕ) (hn : n.Coprime p) :
    1 ≤ red p n ∧ red p n ≤ (p - 1) / 2 := by
  have hp1 : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp)
  have h2le : 2 ≤ p := hpri.out.two_le
  have hmod_pos : 1 ≤ n % p := by
    rcases Nat.eq_zero_or_pos (n % p) with h | h
    · exact absurd ((Nat.coprime_comm.mp hn).eq_one_of_dvd (Nat.dvd_of_mod_eq_zero h)) (by omega)
    · omega
  have hmod_lt : n % p < p := Nat.mod_lt _ (by omega)
  simp only [red]; split_ifs with h <;> omega

theorem red_coprime (hp : p ≠ 2) (n : ℕ) (hn : n.Coprime p) : (red p n).Coprime p := by
  obtain ⟨h1, h2⟩ := red_pos_lt hp n hn
  have h2le : 2 ≤ p := hpri.out.two_le
  refine (hpri.out.coprime_iff_not_dvd.mpr fun hdvd => ?_).symm
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

omit [IsCyclotomicExtension {p} ℚ K] in
theorem vc_congr (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) {j j' : ℕ} (h : j = j')
    (hj : j.Coprime p) (hj' : j'.Coprime p) : vc hζ hp j hj = vc hζ hp j' hj' := by
  subst h; rfl

omit [IsCyclotomicExtension {p} ℚ K] in
theorem vc_red (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (n : ℕ) (hn : n.Coprime p) :
    vc hζ hp n hn = vc hζ hp (red p n) (red_coprime hp n hn) := by
  have hmod : (n % p).Coprime p := by
    change Nat.gcd (n % p) p = 1; rw [← Nat.gcd_rec, Nat.gcd_comm]; exact hn
  rw [vc_periodic hζ hp n (n % p) (Nat.mod_modEq n p).symm hn hmod]
  have hlt : n % p < p := Nat.mod_lt _ hpri.out.pos
  by_cases h : n % p ≤ (p - 1) / 2
  · exact vc_congr hζ hp (show n % p = red p n by rw [red, if_pos h]) hmod (red_coprime hp n hn)
  · have hpx : (p - n % p).Coprime p := by
      refine (hpri.out.coprime_iff_not_dvd.mpr fun hd => ?_).symm
      have h2le := hpri.out.two_le
      have hp1 : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp)
      exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    exact (vc_reflect hζ hp (n % p) hlt hmod hpx).symm.trans
      (vc_congr hζ hp (show p - n % p = red p n by rw [red, if_neg h]) hpx (red_coprime hp n hn))

theorem red_spec (n : ℕ) :
    ((red p n : ℕ) : ZMod p) = (n : ZMod p) ∨ ((red p n : ℕ) : ZMod p) = -(n : ZMod p) := by
  have hmod : ((n % p : ℕ) : ZMod p) = (n : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_modEq n p)
  simp only [red]
  split_ifs with h
  · exact Or.inl hmod
  · refine Or.inr ?_
    rw [Nat.cast_sub (le_of_lt (Nat.mod_lt n hpri.out.pos)), ZMod.natCast_self, zero_sub, hmod]

theorem coeff_eq (hp : p ≠ 2) (g : (ZMod p)ˣ) (i : ℕ) (hi : Even i) (h3 : i ≤ p - 3)
    (a : ℕ) (_ha : a.Coprime p) :
    (((a ^ (p - 1 - i)) : ℕ) : ZMod p)
      = (g : ZMod p) ^ i * (((red p (a * (g : ZMod p).val)) ^ (p - 1 - i) : ℕ) : ZMod p) := by
  have h2le : 2 ≤ p := hpri.out.two_le
  have heven : Even (p - 1 - i) := by
    have hp1 : Even (p - 1) := by obtain ⟨k, hk⟩ := hpri.out.odd_of_ne_two hp; exact ⟨k, by omega⟩
    exact (Nat.even_sub (by omega)).mpr (iff_of_true hp1 hi)
  have hferm : (g : ZMod p) ^ (p - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one p g, Units.val_one]
  have hgval : (((g : ZMod p).val : ℕ) : ZMod p) = (g : ZMod p) := ZMod.natCast_rightInverse _
  have hredpow : ((red p (a * (g : ZMod p).val) : ℕ) : ZMod p) ^ (p - 1 - i)
      = ((a : ZMod p) * (g : ZMod p)) ^ (p - 1 - i) := by
    rcases red_spec (p := p) (a * (g : ZMod p).val) with h | h
    · rw [h]; push_cast [hgval]; ring
    · rw [h, heven.neg_pow]; push_cast [hgval]; ring
  push_cast
  rw [hredpow, mul_pow,
    show (g : ZMod p) ^ i * ((a : ZMod p) ^ (p - 1 - i) * (g : ZMod p) ^ (p - 1 - i))
      = (a : ZMod p) ^ (p - 1 - i) * ((g : ZMod p) ^ i * (g : ZMod p) ^ (p - 1 - i)) from by ring,
    ← pow_add, show i + (p - 1 - i) = p - 1 from by omega, hferm, mul_one]

theorem zmod_inj_on_Icc (hp : p ≠ 2) {x y : ℕ} (hx : x ∈ Icc 1 ((p - 1) / 2))
    (hy : y ∈ Icc 1 ((p - 1) / 2))
    (h : (x : ZMod p) = (y : ZMod p) ∨ (x : ZMod p) = -(y : ZMod p)) : x = y := by
  rw [mem_Icc] at hx hy
  have h2le := hpri.out.two_le
  have hp1 : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp)
  rcases h with h | h
  · have hxy : x % p = y % p := (ZMod.natCast_eq_natCast_iff x y p).mp h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hxy; exact hxy
  · have hz : ((x + y : ℕ) : ZMod p) = 0 := by push_cast; rw [h]; ring
    have hdvd : p ∣ (x + y) := (CharP.cast_eq_zero_iff (ZMod p) p (x + y)).mp hz
    have := Nat.le_of_dvd (by omega) hdvd
    omega

theorem red_red_inv (hp : p ≠ 2) (g : (ZMod p)ˣ) {a : ℕ} (ha : a ∈ Icc 1 ((p - 1) / 2))
    (hac : a.Coprime p) :
    red p (red p (a * (g : ZMod p).val) * ((g⁻¹ : (ZMod p)ˣ) : ZMod p).val) = a := by
  have hag : (a * (g : ZMod p).val).Coprime p := Nat.coprime_mul_iff_left.mpr ⟨hac, coprime_val g⟩
  set c := red p (a * (g : ZMod p).val) with hc
  have hcg : (c * ((g⁻¹ : (ZMod p)ˣ) : ZMod p).val).Coprime p :=
    Nat.coprime_mul_iff_left.mpr ⟨red_coprime hp _ hag, coprime_val g⁻¹⟩
  have hgv : (((g : ZMod p).val : ℕ) : ZMod p) = (g : ZMod p) := ZMod.natCast_rightInverse _
  have hginv : (((g⁻¹ : (ZMod p)ˣ) : ZMod p).val : ZMod p) = ((g⁻¹ : (ZMod p)ˣ) : ZMod p) :=
    ZMod.natCast_rightInverse _
  have hgg : (g : ZMod p) * ((g⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcval : (c : ZMod p) = (a : ZMod p) * (g : ZMod p)
      ∨ (c : ZMod p) = -((a : ZMod p) * (g : ZMod p)) := by
    rcases red_spec (p := p) (a * (g : ZMod p).val) with h | h
    · left; rw [hc, h]; push_cast [hgv]; ring
    · right; rw [hc, h]; push_cast [hgv]; ring
  have hcginv : ((c * ((g⁻¹ : (ZMod p)ˣ) : ZMod p).val : ℕ) : ZMod p) = (a : ZMod p)
      ∨ ((c * ((g⁻¹ : (ZMod p)ˣ) : ZMod p).val : ℕ) : ZMod p) = -(a : ZMod p) := by
    have key : ((c * ((g⁻¹ : (ZMod p)ˣ) : ZMod p).val : ℕ) : ZMod p)
        = (c : ZMod p) * ((g⁻¹ : (ZMod p)ˣ) : ZMod p) := by
      rw [Nat.cast_mul, hginv]
    rw [key]
    rcases hcval with h | h
    · left; rw [h, mul_assoc, hgg, mul_one]
    · right; rw [h, neg_mul, mul_assoc, hgg, mul_one]
  refine zmod_inj_on_Icc hp (mem_Icc.mpr (red_pos_lt hp _ hcg)) ha ?_
  rcases red_spec (p := p) (c * ((g⁻¹ : (ZMod p)ˣ) : ZMod p).val) with h | h <;>
      rcases hcginv with hc1 | hc1
  · exact Or.inl (by rw [h, hc1])
  · exact Or.inr (by rw [h, hc1])
  · exact Or.inr (by rw [h, hc1])
  · exact Or.inl (by rw [h, hc1, neg_neg])

omit [IsCyclotomicExtension {p} ℚ K] in
theorem eigen_summand (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (g : (ZMod p)ˣ) (i : ℕ)
    (hi : Even i) (h3 : i ≤ p - 3) (a : ℕ) (ha : a.Coprime p)
    (hcop : (a * (g : ZMod p).val).Coprime p) :
    (a ^ (p - 1 - i)) • vc hζ hp (a * (g : ZMod p).val) hcop
      = (g : ZMod p) ^ i • ((red p (a * (g : ZMod p).val)) ^ (p - 1 - i)
          • vc hζ hp (red p (a * (g : ZMod p).val)) (red_coprime hp _ hcop)) := by
  rw [vc_red hζ hp (a * (g : ZMod p).val) hcop, ← Nat.cast_smul_eq_nsmul (ZMod p) (a ^ (p - 1 - i)),
    coeff_eq hp g i hi h3 a ha, mul_smul, Nat.cast_smul_eq_nsmul]

/-- **Thm 8.14, piece 3a-iii (δ) — the eigenvector relation** `T(Ēᵢ) = g^i · Ēᵢ`. -/
theorem galV_eigen (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (g : (ZMod p)ˣ) (i : ℕ)
    (hi : Even i) (h2 : 2 ≤ i) (h3 : i ≤ p - 3) :
    galV hζ g (vOf ⟨eigenCyclotomicUnit hζ i, eigenCyclotomicUnit_mem_realUnits hζ hp i⟩)
      = (g : ZMod p) ^ i •
          vOf ⟨eigenCyclotomicUnit hζ i, eigenCyclotomicUnit_mem_realUnits hζ hp i⟩ := by
  rw [galV_eigenE hζ hp g i hi h2 h3, eigenE_expand hζ hp i, Finset.smul_sum]
  refine Finset.sum_nbij'
    (fun a => (⟨red p (a.1 * (g : ZMod p).val), mem_Icc.mpr (red_pos_lt hp _
        (Nat.coprime_mul_iff_left.mpr ⟨coprime_of_mem_Icc a.2, coprime_val g⟩))⟩ :
        ↥(Icc 1 ((p - 1) / 2))))
    (fun a => (⟨red p (a.1 * ((g⁻¹ : (ZMod p)ˣ) : ZMod p).val), mem_Icc.mpr (red_pos_lt hp _
        (Nat.coprime_mul_iff_left.mpr ⟨coprime_of_mem_Icc a.2, coprime_val g⁻¹⟩))⟩ :
        ↥(Icc 1 ((p - 1) / 2))))
    (fun a _ => mem_attach _ _) (fun a _ => mem_attach _ _)
    (fun a _ => Subtype.ext (red_red_inv hp g a.2 (coprime_of_mem_Icc a.2)))
    (fun a _ => Subtype.ext (by
      have := red_red_inv hp g⁻¹ a.2 (coprime_of_mem_Icc a.2); rwa [inv_inv] at this))
    (fun a _ => eigen_summand hζ hp g i hi h3 a.1 (coprime_of_mem_Icc a.2) _)

end CyclotomicNT
