import CyclotomicNT.CyclotomicPlaceCycle
import CyclotomicNT.CyclotomicUnitReduction
import CyclotomicNT.ReducedGroupDeterminant
import CyclotomicNT.UnitModP
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# The cyclotomic-unit index against the regulator of `K⁺` (Washington Thm 8.2, geometric half)

Assembles the archimedean bricks into

  `[E : C] · Reg(K⁺) = ∏_{k ≠ 0} ‖λ_k‖`,   `λ_k = ∑_{x ∈ ℤ/m} log‖1−e(g^x/p)‖·e(−kx/m)`

(`m = (p−1)/2`, `g` a generator of `(ℤ/p)ˣ`): the relative index of the cyclotomic unit group
`C` in the real units `E`, times the regulator of the maximal real subfield, equals the product
of the nontrivial character eigenvalues of the cyclotomic-unit group matrix.  The identification
of `∏‖λ_k‖` with `h⁺·Reg(K⁺)` via `L(1,χ)` and the class number formula for `K⁺` is the
remaining (analytic) half of `cyclotomic_unit_index`.

Route: `NumberField.Units.regOfFamily_div_regOfFamily` (covolume ratio = index, Mathlib) applied
to the cyclotomic family vs `IsCMField.realFundSystem`, whose `regOfFamily` is
`2^rank·Reg(K⁺)` (`regOfFamily_realFunSystem`); the determinant of the cyclotomic family is
computed by `norm_det_reduced_groupMatrix` through the cyclic place indexing of
`CyclotomicPlaceCycle`; torsion bookkeeping via the modular lattice law. -/

open NumberField NumberField.Units NumberField.IsCMField Finset

namespace CyclotomicNT

section Bookkeeping

variable {A : Type*} [CommGroup A]

/-- **Index bookkeeping**: for `C ≤ E` and `W ⊓ E ≤ C`, joining a common `W` does not change
the relative index: `[E⊔W : C⊔W] = [E : C]` (modular lattice law + second isomorphism). -/
theorem relIndex_sup_sup {C E W : Subgroup A} (hCE : C ≤ E) (hWE : W ⊓ E ≤ C) :
    (C ⊔ W).relIndex (E ⊔ W) = C.relIndex E := by
  have h1 : E ⊔ W = E ⊔ (C ⊔ W) := by rw [← sup_assoc, sup_eq_left.mpr hCE]
  rw [h1, Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right,
    sup_inf_assoc_of_le W hCE, sup_eq_left.mpr hWE]

end Bookkeeping

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ p) {g : (ZMod p)ˣ}

omit [CharZero K] [NumberField K] [IsCMField K] in
/-- `−1` is a torsion unit. -/
theorem neg_one_mem_torsion : (-1 : (𝓞 K)ˣ) ∈ torsion K :=
  (CommGroup.mem_torsion _).mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, by rw [neg_one_sq]⟩)

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Real torsion is `±1`, which lies in `C`**: `torsion K ⊓ realUnits K ≤ C`. -/
theorem torsion_inf_realUnits_le :
    torsion K ⊓ realUnits K ≤ cyclotomicUnitGroup hζ := by
  rintro u ⟨hut, hur⟩
  have hsq : u ^ 2 = 1 := realUnits_sq_eq_one hur hut
  have hcast : ((u : 𝓞 K) - 1) * ((u : 𝓞 K) + 1) = 0 := by
    have h2 : ((u ^ 2 : (𝓞 K)ˣ) : 𝓞 K) = 1 := by rw [hsq, Units.val_one]
    rw [Units.val_pow_eq_pow_val] at h2
    linear_combination h2
  rcases mul_eq_zero.mp hcast with h | h
  · have hu1 : u = 1 := Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h)
    rw [hu1]
    exact one_mem _
  · have hu1 : u = -1 := Units.ext (by
      rw [Units.val_neg, Units.val_one]
      linear_combination h)
    rw [hu1]
    exact Subgroup.subset_closure (Set.mem_union_left _ rfl)

omit [IsCMField K] in
omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- `ξ_1 = 1`. -/
theorem realCyclotomicUnit_one (h1 : (1 : ℕ).Coprime p) :
    realCyclotomicUnit hζ 1 h1 = 1 := by
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  have h := coe_realCyclotomicUnit hζ 1 h1
  simp only [Nat.cast_one, sub_self, zero_mul, zpow_zero, one_mul, range_one, sum_singleton,
    zpow_zero] at h
  rw [Units.val_one, map_one]
  exact h.trans (by simp)

omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/-- Unfold `cycUnitFun` along an identification of the unit `g^i`. -/
theorem cycUnitFun_eq_of_eq {i : ℕ} {x : (ZMod p)ˣ} (hx : g ^ i = x) :
    cycUnitFun hζ g i
      = realCyclotomicUnit hζ ((x : ZMod p)).val (ZMod.val_coe_unit_coprime x) := by
  subst hx
  rfl

omit [IsCMField K] in
omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- For `i ≡ 0 (mod m)`, the cycle unit `ξ_{g^i}` is torsion (`g^i = ±1`, `ξ_{±1} = ±1`). -/
theorem cycUnitFun_torsion_of_zero (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g)
    (hp : p ≠ 2) {i : ℕ} (hi : (i : ZMod ((p - 1) / 2)) = 0) :
    cycUnitFun hζ g i ∈ torsion K := by
  haveI : NeZero ((p - 1) / 2) := ⟨half_pred_ne_zero hp⟩
  obtain ⟨t, ht⟩ := (CharP.cast_eq_zero_iff (ZMod ((p - 1) / 2)) ((p - 1) / 2) i).mp hi
  have hgi : g ^ i = ((-1 : (ZMod p)ˣ)) ^ t := by
    rw [ht, pow_mul, generator_pow_half hgen hp]
  rcases Nat.even_or_odd t with he | ho
  · -- `g^i = 1`, `ξ_1 = 1`
    rw [he.neg_one_pow] at hgi
    rw [cycUnitFun_eq_of_eq hζ hgi]
    have hval : ((1 : (ZMod p)ˣ) : ZMod p).val = 1 := by
      rw [Units.val_one, ZMod.val_one]
    rw [realCyclotomicUnit_congr hζ hval _ (Nat.coprime_one_left p),
      realCyclotomicUnit_one hζ]
    exact one_mem _
  · -- `g^i = −1`, `ξ_{p−1} = −ξ_1 = −1`
    rw [ho.neg_one_pow] at hgi
    rw [cycUnitFun_eq_of_eq hζ hgi]
    have hmod : (((-1 : (ZMod p)ˣ) : ZMod p).val + 1) % p = 0 := by
      have hcast : ((((-1 : (ZMod p)ˣ) : ZMod p).val + 1 : ℕ) : ZMod p) = 0 := by
        push_cast [ZMod.natCast_val, ZMod.cast_id]
        simp
      exact Nat.dvd_iff_mod_eq_zero.mp ((CharP.cast_eq_zero_iff (ZMod p) p _).mp hcast)
    rw [realCyclotomicUnit_neg_modEq hζ hp hmod _ (Nat.coprime_one_left p),
      realCyclotomicUnit_one hζ]
    exact neg_one_mem_torsion

/-- The values of a unit and its negative sum to `0` mod `p`. -/
theorem val_neg_add_val (x : (ZMod p)ˣ) :
    ((((-x : (ZMod p)ˣ)) : ZMod p).val + ((x : ZMod p)).val) % p = 0 := by
  have hcast : ((((-x : (ZMod p)ˣ) : ZMod p).val + ((x : ZMod p)).val : ℕ) : ZMod p) = 0 := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    simp
  exact Nat.dvd_iff_mod_eq_zero.mp ((CharP.cast_eq_zero_iff (ZMod p) p _).mp hcast)

omit [IsCMField K] in
omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **Sign relation along the cycle**: `i ≡ i' (mod m)` makes `ξ_{g^i} = ±ξ_{g^{i'}}`. -/
theorem cycUnitFun_sign_modEq (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2)
    {i i' : ℕ} (h : i ≡ i' [MOD ((p - 1) / 2)]) :
    cycUnitFun hζ g i = cycUnitFun hζ g i'
      ∨ cycUnitFun hζ g i = - cycUnitFun hζ g i' := by
  -- one-sided step: `P (i' + t·m) i'`
  have step : ∀ (a t : ℕ), cycUnitFun hζ g (a + t * ((p - 1) / 2)) = cycUnitFun hζ g a
      ∨ cycUnitFun hζ g (a + t * ((p - 1) / 2)) = - cycUnitFun hζ g a := by
    intro a t
    have hpow : g ^ (a + t * ((p - 1) / 2)) = g ^ a * ((-1 : (ZMod p)ˣ)) ^ t := by
      rw [pow_add, pow_mul', generator_pow_half hgen hp]
    rcases Nat.even_or_odd t with he | ho
    · left
      rw [he.neg_one_pow, mul_one] at hpow
      rw [cycUnitFun_eq_of_eq hζ hpow]
      rfl
    · right
      rw [ho.neg_one_pow] at hpow
      have hneg : g ^ (a + t * ((p - 1) / 2)) = -(g ^ a) := by rw [hpow, mul_neg_one]
      rw [cycUnitFun_eq_of_eq hζ hneg,
        realCyclotomicUnit_neg_modEq hζ hp (val_neg_add_val (g ^ a)) _
          (ZMod.val_coe_unit_coprime _)]
      rfl
  -- reduce both sides to the common residue `r = i % m = i' % m`
  have hi : i % ((p - 1) / 2) + i / ((p - 1) / 2) * ((p - 1) / 2) = i := Nat.mod_add_div' _ _
  have hi' : i' % ((p - 1) / 2) + i' / ((p - 1) / 2) * ((p - 1) / 2) = i' :=
    Nat.mod_add_div' _ _
  have h1 := step (i % ((p - 1) / 2)) (i / ((p - 1) / 2))
  have h2 := step (i' % ((p - 1) / 2)) (i' / ((p - 1) / 2))
  rw [hi] at h1
  rw [hi', show i' % ((p - 1) / 2) = i % ((p - 1) / 2) from h.symm] at h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (h1.trans h2.symm)
  · exact Or.inr (by rw [h1, h2, neg_neg])
  · exact Or.inr (by rw [h1, h2])
  · exact Or.inl (by rw [h1, h2])

omit [IsCMField K] in
omit [CharZero K] [IsCyclotomicExtension {p} ℚ K] in
/-- **The cyclotomic unit group mod torsion is generated by the cycle family**:
`⟨range (ξ_{g^{(eFin i)}})⟩ ⊔ W = C ⊔ W` for any indexing `eFin` of the nonzero classes. -/
theorem closure_cycFamily_sup_torsion (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g)
    (hp : p ≠ 2) (eFin : Fin (rank K) ≃ {j : ZMod ((p - 1) / 2) // j ≠ 0}) :
    Subgroup.closure (Set.range (fun i => cycUnitFun hζ g ((eFin i).1.val))) ⊔ torsion K
      = cyclotomicUnitGroup hζ ⊔ torsion K := by
  haveI : NeZero ((p - 1) / 2) := ⟨half_pred_ne_zero hp⟩
  apply le_antisymm
  · refine sup_le_sup_right ?_ _
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact cycUnitFun_mem hζ g _
  · refine sup_le ?_ le_sup_right
    rw [cyclotomicUnitGroup, Subgroup.closure_le]
    rintro u (hu | ⟨a, ha, rfl⟩)
    · rw [Set.mem_singleton_iff] at hu
      subst hu
      exact SetLike.mem_coe.mpr (Subgroup.mem_sup_right neg_one_mem_torsion)
    · -- `ξ_a = ξ_{g^k}` for the discrete log `k` of `a`
      have hua : IsUnit (a : ZMod p) := (ZMod.isUnit_iff_coprime a p).mpr ha
      obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.mpr (hgen hua.unit)
      have hmodp : a ≡ ((g ^ k : (ZMod p)ˣ) : ZMod p).val [MOD p] := by
        have hk' : g ^ k = hua.unit := hk
        have hcoe : ((a : ℕ) : ZMod p) = ((g ^ k : (ZMod p)ˣ) : ZMod p) := by
          rw [hk', IsUnit.unit_spec]
        unfold Nat.ModEq
        rw [← ZMod.val_natCast, hcoe, Nat.mod_eq_of_lt (ZMod.val_lt _)]
      have hξ : realCyclotomicUnit hζ a ha = cycUnitFun hζ g k :=
        realCyclotomicUnit_modEq hζ hmodp ha _
      rw [SetLike.mem_coe, hξ]
      rcases eq_or_ne ((k : ZMod ((p - 1) / 2))) 0 with hj | hj
      · exact Subgroup.mem_sup_right (cycUnitFun_torsion_of_zero hζ hgen hp hj)
      · -- compare with the family member at the class of `k`
        have hkk : k ≡ ((eFin (eFin.symm ⟨_, hj⟩)).1.val) [MOD ((p - 1) / 2)] := by
          rw [Equiv.apply_symm_apply]
          unfold Nat.ModEq
          rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ dvd_rfl]
        have hmem : cycUnitFun hζ g ((eFin (eFin.symm ⟨_, hj⟩)).1.val)
            ∈ Subgroup.closure (Set.range (fun i => cycUnitFun hζ g ((eFin i).1.val)))
              ⊔ torsion K :=
          Subgroup.mem_sup_left (Subgroup.subset_closure ⟨eFin.symm ⟨_, hj⟩, rfl⟩)
        rcases cycUnitFun_sign_modEq hζ hgen hp hkk with hcase | hcase
        · rw [hcase]
          exact hmem
        · rw [hcase, show -(cycUnitFun hζ g ((eFin (eFin.symm ⟨_, hj⟩)).1.val))
              = (-1) * cycUnitFun hζ g ((eFin (eFin.symm ⟨_, hj⟩)).1.val) by
            rw [neg_one_mul]]
          exact mul_mem (Subgroup.mem_sup_right neg_one_mem_torsion) hmem

section Determinant

/-- The character family `ψ_j = e(j·−/m)` on `ℤ/m` is injective with trivial `ψ_0`. -/
theorem mulShift_stdAddChar_injective (m : ℕ) [NeZero m] :
    Function.Injective (fun j : ZMod m => AddChar.mulShift ZMod.stdAddChar j) := by
  intro j j' h
  have h1 := DFunLike.congr_fun h (1 : ZMod m)
  rw [AddChar.mulShift_apply, AddChar.mulShift_apply, mul_one, mul_one] at h1
  exact ZMod.injective_stdAddChar h1

omit [IsCMField K] in
/-- **The regulator of the cyclotomic cycle family**: `2^rank K` times the reduced group
determinant of the `vIdx` kernel over `ℤ/m` — by `regOfFamily_eq_det`, the cyclic place
indexing, the entry formula, and `norm_det_reduced_groupMatrix`. -/
theorem regOfFamily_cycFamily [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2)
    (eFin : Fin (rank K) ≃ {j : ZMod ((p - 1) / 2) // j ≠ 0}) :
    regOfFamily (fun i => cycUnitFun hζ g ((eFin i).1.val))
      = 2 ^ rank K * ∏ k : {j : ZMod ((p - 1) / 2) // j ≠ 0},
          ‖∑ x : ZMod ((p - 1) / 2), ((vIdx g x : ℂ))
            * (AddChar.mulShift ZMod.stdAddChar k.1) (-x)‖ := by
  classical
  -- the cyclic place indexing
  let b : ZMod ((p - 1) / 2) ≃ InfinitePlace K :=
    Equiv.ofBijective _ (cycPlaceIdx_bijective hζ hgen hp)
  set w₀ : InfinitePlace K := cycPlaceIdx hζ g 0 with hw₀
  let ePlace : {j : ZMod ((p - 1) / 2) // j ≠ 0} ≃ {w : InfinitePlace K // w ≠ w₀} :=
    b.subtypeEquiv fun j => not_iff_not.mpr ⟨fun h => by rw [h]; rfl, fun h => b.injective h⟩
  -- the regulator determinant at the base place `w₀`
  rw [regOfFamily_eq_det _ w₀ (ePlace.symm.trans eFin.symm)]
  -- identify the matrix with the reduced group matrix (rows/cols reindexed by `ePlace`)
  have hM : (Matrix.of fun i w : {w : InfinitePlace K // w ≠ w₀} =>
        (w.1.mult : ℝ) * Real.log (w.1 ((fun i => cycUnitFun hζ g ((eFin i).1.val))
          ((ePlace.symm.trans eFin.symm) i) : K)))
      = Matrix.reindex ePlace ePlace (Matrix.of
          fun j k : {j : ZMod ((p - 1) / 2) // j ≠ 0} =>
            (2 : ℝ) * (vIdx g (j.1 + k.1) - vIdx g k.1)) := by
    ext i w
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Matrix.of_apply]
    beta_reduce
    have hmult : (w.1.mult : ℝ) = 2 := by
      haveI : NumberField.IsTotallyComplex K :=
        IsCyclotomicExtension.Rat.isTotallyComplex (n := p) K
          (by have := hpri.out.two_le; omega)
      rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr
        (NumberField.IsTotallyComplex.isComplex w.1))]
      norm_num
    have hunit : (eFin ((ePlace.symm.trans eFin.symm) i)).1 = (ePlace.symm i).1 := by
      rw [Equiv.trans_apply, Equiv.apply_symm_apply]
    have hplace : w.1 = cycPlaceFun hζ g ((ePlace.symm w).1.val) := by
      conv_lhs => rw [show w = ePlace (ePlace.symm w) by rw [Equiv.apply_symm_apply]]
      rfl
    rw [hmult, hunit, hplace, log_cycPlaceFun_cycUnitFun hζ,
      vIdx_add hgen hp, vIdx]
  rw [hM, Matrix.det_reindex_self]
  -- pull the factor `2` out of every row
  have h2 : (Matrix.of fun j k : {j : ZMod ((p - 1) / 2) // j ≠ 0} =>
        (2 : ℝ) * (vIdx g (j.1 + k.1) - vIdx g k.1))
      = Matrix.of fun j k : {j : ZMod ((p - 1) / 2) // j ≠ 0} =>
          (fun _ : {j : ZMod ((p - 1) / 2) // j ≠ 0} => (2 : ℝ)) j
            * (Matrix.of fun j k : {j : ZMod ((p - 1) / 2) // j ≠ 0} =>
                (vIdx g (j.1 + k.1) - vIdx g k.1)) j k := rfl
  rw [h2, Matrix.det_mul_column, abs_mul, Finset.prod_const, abs_pow, abs_two]
  have hcardsub : Fintype.card {j : ZMod ((p - 1) / 2) // j ≠ 0} = rank K := by
    have h1 : Fintype.card {j : ZMod ((p - 1) / 2) // j ≠ 0}
        = Fintype.card (ZMod ((p - 1) / 2)) - 1 := by
      have h2 := Fintype.card_subtype_compl (fun j : ZMod ((p - 1) / 2) => j = 0)
      rw [Fintype.card_subtype_eq] at h2
      exact h2
    rw [h1, ZMod.card, rank, card_infinitePlace_eq hp]
  rw [Finset.card_univ, hcardsub]
  congr 1
  -- cast the real reduced determinant to `ℂ` and apply the reduced group determinant
  have hcast : |(Matrix.of fun j k : {j : ZMod ((p - 1) / 2) // j ≠ 0} =>
        (vIdx g (j.1 + k.1) - vIdx g k.1)).det|
      = ‖(Complex.ofRealHom.mapMatrix (Matrix.of
          fun j k : {j : ZMod ((p - 1) / 2) // j ≠ 0} =>
            (vIdx g (j.1 + k.1) - vIdx g k.1))).det‖ := by
    rw [← RingHom.map_det, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs]
  rw [hcast]
  have hmap : (Complex.ofRealHom.mapMatrix (Matrix.of
        fun j k : {j : ZMod ((p - 1) / 2) // j ≠ 0} =>
          (vIdx g (j.1 + k.1) - vIdx g k.1)))
      = Matrix.of fun j k : {j : ZMod ((p - 1) / 2) // j ≠ 0} =>
          (fun x : ZMod ((p - 1) / 2) => ((vIdx g x : ℝ) : ℂ)) (j.1 + k.1)
            - (fun x : ZMod ((p - 1) / 2) => ((vIdx g x : ℝ) : ℂ)) k.1 := by
    ext j k
    simp [Matrix.map_apply]
  rw [hmap, norm_det_reduced_groupMatrix (fun x => ((vIdx g x : ℝ) : ℂ))
    (fun j => AddChar.mulShift ZMod.stdAddChar j)
    (mulShift_stdAddChar_injective ((p - 1) / 2))
    (show AddChar.mulShift ZMod.stdAddChar (0 : ZMod ((p - 1) / 2)) = 0 by
      rw [AddChar.mulShift_zero]; rfl)]

end Determinant

section Assembly

omit [IsCMField K] in
/-- The nonzero classes of `ℤ/m` count the unit rank of `K`. -/
theorem card_ne_zero_eq_rank [NeZero ((p - 1) / 2)] (hp : p ≠ 2) :
    Fintype.card {j : ZMod ((p - 1) / 2) // j ≠ 0} = rank K := by
  have h2 := Fintype.card_subtype_compl (fun j : ZMod ((p - 1) / 2) => j = 0)
  rw [Fintype.card_subtype_eq] at h2
  have h1 : Fintype.card {j : ZMod ((p - 1) / 2) // j ≠ 0}
      = Fintype.card (ZMod ((p - 1) / 2)) - 1 := h2
  rw [h1, ZMod.card, rank, card_infinitePlace_eq hp]

/-- `realFundSystem` is of maximal rank: the subgroup it generates with torsion is
`realUnits ⊔ torsion`, of index `indexRealUnits K ∈ {1, 2}`. -/
theorem isMaxRank_realFundSystem : IsMaxRank (realFundSystem K) := by
  rw [isMaxRank_iff_closure_finiteIndex, finiteIndex_iff_sup_torsion_finiteIndex,
    closure_realFundSystem_sup_torsion]
  refine ⟨?_⟩
  change indexRealUnits K ≠ 0
  rcases indexRealUnits_eq_one_or_two K with h | h <;> rw [h] <;> omega

/-- **The cyclotomic-unit index times the regulator of `K⁺`** equals the product of the
nontrivial even-character eigenvalues `λ_k = ∑_x log‖1−e(g^x/p)‖·e(−kx/m)` of the
cyclotomic-unit group matrix (Washington Thm 8.2, geometric half).  The analytic half —
`∏‖λ_k‖ = h⁺·Reg(K⁺)` via `L(1,χ)` and the class number formula for `K⁺` — discharges
`cyclotomic_unit_index`. -/
theorem relIndex_cyclotomicUnitGroup_mul_regulator [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2) :
    (((cyclotomicUnitGroup hζ).relIndex (realUnits K) : ℝ))
        * regulator (maximalRealSubfield K)
      = ∏ k : {j : ZMod ((p - 1) / 2) // j ≠ 0},
          ‖∑ x : ZMod ((p - 1) / 2), ((vIdx g x : ℂ))
            * (AddChar.mulShift ZMod.stdAddChar k.1) (-x)‖ := by
  classical
  -- index the family by `Fin (rank K)`
  let eFin : Fin (rank K) ≃ {j : ZMod ((p - 1) / 2) // j ≠ 0} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, card_ne_zero_eq_rank (K := K) hp])
  -- the covolume-ratio theorem
  have h_le : Subgroup.closure (Set.range (fun i => cycUnitFun hζ g ((eFin i).1.val)))
        ⊔ torsion K
      ≤ Subgroup.closure (Set.range (realFundSystem K)) ⊔ torsion K := by
    rw [closure_cycFamily_sup_torsion hζ hgen hp eFin, closure_realFundSystem_sup_torsion]
    exact sup_le_sup_right (cyclotomicUnitGroup_le_realUnits hζ hp) _
  have key := regOfFamily_div_regOfFamily (isMaxRank_realFundSystem (K := K)) h_le
  rw [closure_cycFamily_sup_torsion hζ hgen hp eFin, closure_realFundSystem_sup_torsion,
    relIndex_sup_sup (cyclotomicUnitGroup_le_realUnits hζ hp) (torsion_inf_realUnits_le hζ),
    regOfFamily_realFunSystem, regOfFamily_cycFamily hζ hgen hp eFin] at key
  -- clear denominators
  have hreg : (0 : ℝ) < regulator (maximalRealSubfield K) :=
    regulator_pos (maximalRealSubfield K)
  have hne : (2 : ℝ) ^ rank K * regulator (maximalRealSubfield K) ≠ 0 := by positivity
  rw [div_eq_iff hne] at key
  apply mul_left_cancel₀ (show ((2 : ℝ) ^ rank K) ≠ 0 by positivity)
  rw [← mul_assoc, mul_comm ((2 : ℝ) ^ rank K), mul_assoc, ← key]

end Assembly

end CyclotomicNT
