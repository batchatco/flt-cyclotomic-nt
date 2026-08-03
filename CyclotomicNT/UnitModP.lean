import CyclotomicNT.GaloisRealUnits
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# Discharging `unitModP_finrank_le` — the `p`-rank bound

Goal: `finrank (ZMod p) (E/Eᵖ) ≤ (p−3)/2` for `E = realUnits K`, `K` a CM cyclotomic field.

Plan (four bricks):
1. **`units_rank_eq`** — `Units.rank K = (p−3)/2` (cyclotomic degree `p−1`, totally complex so
   `(p−1)/2` complex places, `rank = card places − 1`).  *(this file, done first)*
2. `finrank ℤ (Additive (realUnits K)) ≤ (p−3)/2` — `realUnits ⊆ E`, rank monotone.
3. `torsion (realUnits K) = {±1}` (the *real* roots of unity), order `2`, coprime to `p`.
4. `−1 = (−1)ᵖ` kills the `2`-torsion in `ModN`, so `finrank (ZMod p) (E/Eᵖ) = finrank ℤ E`. -/

open NumberField NumberField.IsCMField Module

namespace CyclotomicNT

variable {K : Type*} {p : ℕ} [Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

/-- **Brick 1: the unit rank of a CM cyclotomic field is `(p−3)/2`.**  `K = ℚ(ζ_p)` has degree
`p−1`; being totally complex (CM) it has `(p−1)/2` infinite places, so
`Units.rank K = (p−1)/2 − 1 = (p−3)/2`. -/
theorem units_rank_eq (hp : p ≠ 2) : NumberField.Units.rank K = (p - 3) / 2 := by
  have hpp : p.Prime := Fact.out
  have h3 : 3 ≤ p := by
    have h2 := hpp.two_le
    rcases hpp.eq_two_or_odd' with h | h
    · exact absurd h hp
    · omega
  have hfr : Module.finrank ℚ K = p - 1 := by
    rw [IsCyclotomicExtension.finrank (K := ℚ) (L := K)
      (Polynomial.cyclotomic.irreducible_rat hpp.pos), Nat.totient_prime hpp]
  have hcx : NumberField.InfinitePlace.nrComplexPlaces K = (p - 1) / 2 := by
    have h := IsTotallyComplex.finrank (K := K)
    rw [hfr] at h
    omega
  have hcard : Fintype.card (NumberField.InfinitePlace K) = (p - 1) / 2 := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, hcx]
  rw [NumberField.Units.rank, hcard]
  omega

/-- **Brick 3: real roots of unity are `±1`.**  A finite-order real unit squares to `1` — complex
conjugation inverts roots of unity (`complexConj_torsion`) yet fixes real units, so `u = u⁻¹`. -/
theorem realUnits_sq_eq_one {u : (𝓞 K)ˣ} (hu : u ∈ realUnits K) (hfin : IsOfFinOrder u) :
    u ^ 2 = 1 := by
  have htor : u ∈ NumberField.Units.torsion K := hfin
  have hc : complexConj K (u : K) = (u : K)⁻¹ := complexConj_torsion (K := K) ⟨u, htor⟩
  have hr : complexConj K (u : K) = (u : K) := (mem_realUnits_iff_complexConj u).mp hu
  have hinv : (u : K) = (u : K)⁻¹ := hr.symm.trans hc
  have hne : (u : K) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr (Units.ne_zero u)
  have hsq : (u : K) ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hinv]; exact mul_inv_cancel₀ hne
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  push_cast
  simp [hsq]

omit [CharZero K] [IsCMField K] in
/-- The torsion-free rank of the unit group is `Units.rank K`.  Proved via rank-nullity on the
**`logEmbedding`** (kernel = torsion, range = `unitLattice`), which avoids the awkward
`Additive (G ⧸ H)` quotient instance. -/
theorem finrank_additive_units :
    Module.finrank ℤ (Additive (𝓞 K)ˣ) = NumberField.Units.rank K := by
  set L := (NumberField.Units.logEmbedding K).toIntLinearMap with hL
  have hrn := Submodule.finrank_quotient_add_finrank (LinearMap.ker L)
  have hq : Module.finrank ℤ (Additive (𝓞 K)ˣ ⧸ LinearMap.ker L)
      = Module.finrank ℤ ↥(LinearMap.range L) := LinearEquiv.finrank_eq L.quotKerEquivRange
  have hrange : Module.finrank ℤ ↥(LinearMap.range L) = NumberField.Units.rank K := by
    have he : LinearMap.range L = NumberField.Units.unitLattice K := by
      rw [NumberField.Units.unitLattice, hL, Submodule.map_top]
    rw [he, NumberField.Units.unitLattice_rank]
  have hkerfin : Finite ↥(LinearMap.ker L) := by
    rw [hL, AddMonoidHom.coe_toIntLinearMap_ker,
      NumberField.Units.dirichletUnitTheorem.logEmbedding_ker]
    exact inferInstanceAs (Finite (Additive ↥(NumberField.Units.torsion K)))
  haveI : Module.Finite ℤ ↥(LinearMap.ker L) := Module.Finite.of_finite
  have htors : Module.IsTorsion ℤ ↥(LinearMap.ker L) := fun x => by
    have hpos : 0 < addOrderOf x := (isOfFinAddOrder_of_finite x).addOrderOf_pos
    refine ⟨⟨(addOrderOf x : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hpos.ne')⟩, ?_⟩
    change (addOrderOf x : ℤ) • x = 0
    rw [natCast_zsmul]
    exact addOrderOf_nsmul_eq_zero x
  have hker : Module.finrank ℤ ↥(LinearMap.ker L) = 0 :=
    Module.finrank_eq_zero_iff_isTorsion.mpr htors
  rw [hker, add_zero] at hrn
  exact hrn.symm.trans (hq.trans hrange)

/-- **Brick 2: the real unit group has free rank `≤ (p−3)/2`.**  `realUnits K ⊆ (𝓞 K)ˣ`, so its rank
is bounded by `Units.rank K = (p−3)/2`. -/
theorem realUnits_finrank_le (hp : p ≠ 2) :
    Module.finrank ℤ (Additive (realUnits K)) ≤ (p - 3) / 2 := by
  rw [← units_rank_eq (K := K) hp, ← finrank_additive_units (K := K)]
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (realUnits K).toAddSubgroup.subtype.toIntLinearMap) Subtype.val_injective

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Brick 4a: the torsion is killed by `p`.**  Every torsion element `t` of `Additive (realUnits
    K)`
satisfies `2 • t = 0` (brick 3), so since `p` is odd `t = p • t ∈ p·G`. -/
theorem realUnits_torsion_le_smul (hp : p ≠ 2) :
    Submodule.torsion ℤ (Additive (realUnits K))
      ≤ LinearMap.range (LinearMap.lsmul ℤ (Additive (realUnits K)) (p : ℤ)) := by
  have hpp : p.Prime := Fact.out
  have hodd : Odd p := hpp.odd_of_ne_two hp
  intro t ht
  rw [Submodule.mem_torsion_iff] at ht
  obtain ⟨a, ha⟩ := ht
  -- the underlying unit has finite order, so squares to 1 (brick 3)
  have hza : ((Additive.toMul t : realUnits K) : (𝓞 K)ˣ) ^ (a : ℤ) = 1 := by
    have h0 : (Additive.toMul t) ^ (a : ℤ) = 1 := by
      rw [← toMul_zsmul, show (a : ℤ) • t = 0 from ha]; rfl
    rw [← Subgroup.coe_zpow, h0, Subgroup.coe_one]
  have hfin : IsOfFinOrder ((Additive.toMul t : realUnits K) : (𝓞 K)ˣ) :=
    isOfFinOrder_iff_zpow_eq_one.mpr ⟨(a : ℤ), nonZeroDivisors.coe_ne_zero a, hza⟩
  have hsq1 : ((Additive.toMul t : realUnits K) : (𝓞 K)ˣ) ^ 2 = 1 :=
    realUnits_sq_eq_one (Additive.toMul t).2 hfin
  have h2 : (2 : ℤ) • t = 0 := by
    rw [← toMul_eq_one, toMul_zsmul]
    apply Subtype.ext
    rw [Subgroup.coe_zpow, Subgroup.coe_one]
    exact_mod_cast hsq1
  have hpt : (p : ℤ) • t = t := by
    obtain ⟨k, hk⟩ := hodd
    have hkk : (p : ℤ) - 1 = (k : ℤ) * 2 := by rw [hk]; push_cast; ring
    have hz : ((p : ℤ) - 1) • t = 0 := by rw [hkk, mul_smul, h2, smul_zero]
    rw [sub_smul, one_smul, sub_eq_zero] at hz
    exact hz
  exact ⟨t, by rw [LinearMap.lsmul_apply]; exact hpt⟩

/-- **Brick 4b + assembly: discharge of `unitModP_finrank_le`.**  Since the torsion `T` is killed by
`p` (brick 4a), `ModN G p ≅ ModN (G/T) p` (third isomorphism theorem); the latter is free of rank
`finrank ℤ (G/T) ≤ finrank ℤ G ≤ (p−3)/2` (bricks 2). -/
theorem unitModP_finrank_le_proof (hp : p ≠ 2) :
    finrank (ZMod p) (ModN (Additive (realUnits K)) p) ≤ (p - 3) / 2 := by
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  set G := Additive (realUnits K) with hG
  set T := Submodule.torsion ℤ G with hT
  have hple : T ≤ LinearMap.range (LinearMap.lsmul ℤ G (p : ℤ)) := realUnits_torsion_le_smul hp
  have hmap : (LinearMap.range (LinearMap.lsmul ℤ G (p : ℤ))).map T.mkQ
      = LinearMap.range (LinearMap.lsmul ℤ (G ⧸ T) (p : ℤ)) := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.lsmul_apply]
    constructor
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      exact ⟨T.mkQ z, (map_smul _ _ _).symm⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨z, rfl⟩ := T.mkQ_surjective w
      exact ⟨(p : ℤ) • z, ⟨z, rfl⟩, map_smul _ _ _⟩
  haveI : Module.Finite ℤ G :=
    Module.Finite.of_injective (realUnits K).toAddSubgroup.subtype.toIntLinearMap
      Subtype.val_injective
  haveI : Module.Finite ℤ (G ⧸ T) := Module.Finite.of_surjective T.mkQ T.mkQ_surjective
  haveI : Module.IsTorsionFree ℤ (G ⧸ T) := by
    rw [hT]; exact Submodule.QuotientTorsion.instIsTorsionFree
  haveI : Module.Free ℤ (G ⧸ T) := inferInstance
  haveI : Fintype (ZMod p) := ZMod.fintype p
  -- ModN G p ≅ ModN (G/T) p
  have e : ModN (G ⧸ T) p ≃ₗ[ℤ] ModN G p :=
    (Submodule.quotEquivOfEq _ _ hmap.symm).trans (Submodule.quotientQuotientEquivQuotient T _ hple)
  -- cardinalities
  haveI : Module.Finite ℤ (ModN G p) :=
    Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  haveI : Module.Finite (ZMod p) (ModN G p) := Module.Finite.of_restrictScalars_finite ℤ (ZMod p) _
  haveI : Finite (ModN G p) := Module.finite_of_finite (ZMod p)
  haveI : Fintype (ModN G p) := Fintype.ofFinite _
  have hcard : Nat.card (ModN G p) = p ^ Module.finrank ℤ (G ⧸ T) := by
    rw [← Nat.card_congr e.toEquiv, ModN.natCard_eq]
  have hcard2 : Nat.card (ModN G p) = p ^ finrank (ZMod p) (ModN G p) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card p]
  have heq : finrank (ZMod p) (ModN G p) = Module.finrank ℤ (G ⧸ T) :=
    Nat.pow_right_injective hpp.two_le (hcard2.symm.trans hcard)
  rw [heq]
  exact le_trans (Submodule.finrank_quotient_le T) (realUnits_finrank_le hp)

end CyclotomicNT
