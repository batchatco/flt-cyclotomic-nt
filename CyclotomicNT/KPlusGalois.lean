import CyclotomicNT.CyclotomicUnitGroup
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

/-!
# `K⁺/ℚ` is Galois, and complex conjugation is `−1 ∈ (ℤ/p)ˣ`

* `Gal(ℚ(ζ_p)/ℚ)` is abelian (it embeds in `(ℤ/p)ˣ` via `galEquivZMod`);
* `galEquivZMod (conj) = −1` (conjugation inverts `ζ`);
* `K⁺ = maximalRealSubfield K` is the fixed field of `⟨conj⟩`, hence Galois over `ℚ`
  (fixed field of a normal — here any, by commutativity — subgroup).

These feed the decomposition-group computation of the splitting of primes in `K⁺`
(`galEquivZMod_stabilizer` gives `D(Q) = ⟨q⟩`, so `f(Q/Q⁺) = 2 ⟺ −1 ∈ ⟨q⟩`).
-/

open NumberField IsCyclotomicExtension.Rat

namespace CyclotomicNT

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ p)

section AbelianGal

omit [NumberField.IsCMField K] in
include hpri in
/-- `Gal(ℚ(ζ_p)/ℚ)` is abelian. -/
theorem galCommutative : IsMulCommutative (K ≃ₐ[ℚ] K) :=
  ⟨⟨fun σ τ => (galEquivZMod p K).injective (by rw [map_mul, map_mul, mul_comm])⟩⟩

/-- Complex conjugation as a `ℚ`-automorphism of `K`. -/
noncomputable def conjGal : K ≃ₐ[ℚ] K :=
  (NumberField.IsCMField.complexConj K).restrictScalars ℚ

@[simp] theorem conjGal_apply (x : K) :
    conjGal (K := K) x = NumberField.IsCMField.complexConj K x := rfl

include hζ in
/-- The Galois–units dictionary sends conjugation to `−1`. -/
theorem galEquivZMod_conjGal : galEquivZMod p K (conjGal (K := K)) = -1 := by
  have h := galEquivZMod_apply_of_pow_eq p K (conjGal (K := K)) hζ.pow_eq_one
  rw [conjGal_apply, complexConj_zeta hζ] at h
  -- `ζ⁻¹ = ζ^{p−1}`
  have hz_ne : ζ ≠ 0 := hζ.ne_zero hpri.out.pos.ne'
  have hinv : ζ⁻¹ = ζ ^ (p - 1) := by
    have h2 := hpri.out.two_le
    field_simp
    rw [← pow_succ']
    rw [show p - 1 + 1 = p by omega]
    exact hζ.pow_eq_one.symm
  rw [hinv] at h
  -- exponents agree mod `p`
  rw [(hζ.isOfFinOrder hpri.out.ne_zero).pow_inj_mod, ← hζ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_val, ZMod.cast_id] at h
  apply Units.ext
  rw [← h, Units.val_neg, Units.val_one]
  have h2 := hpri.out.two_le
  push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
  rw [ZMod.natCast_self]
  ring

end AbelianGal

section FixedField

/-- `K⁺` as an intermediate field of `K/ℚ`. -/
noncomputable def realIF : IntermediateField ℚ K :=
  (maximalRealSubfield K).toIntermediateField fun q => by
    rw [eq_ratCast (algebraMap ℚ K) q]
    exact SubfieldClass.ratCast_mem _ q

omit [NumberField K] [NumberField.IsCMField K] in
@[simp] theorem mem_realIF (x : K) : x ∈ realIF (K := K) ↔ x ∈ maximalRealSubfield K :=
  Iff.rfl

/-- `K⁺` is the fixed field of `⟨conj⟩`. -/
theorem fixedField_zpowers_conjGal :
    IntermediateField.fixedField (Subgroup.zpowers (conjGal (K := K))) = realIF (K := K) := by
  ext x
  rw [IntermediateField.mem_fixedField_iff, mem_realIF]
  constructor
  · intro h
    exact (NumberField.IsCMField.complexConj_eq_self_iff K x).mp
      (h _ (Subgroup.mem_zpowers _))
  · intro hx σ hσ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
    have hfix : conjGal (K := K) x = x :=
      (NumberField.IsCMField.complexConj_eq_self_iff K x).mpr hx
    have hfix' : ((conjGal (K := K))⁻¹) x = x := by
      nth_rewrite 1 [← hfix]
      rw [AlgEquiv.aut_inv]
      exact (conjGal (K := K)).symm_apply_apply x
    -- any integer power of `conj` fixes `x`
    have hall : ∀ k : ℤ, ((conjGal (K := K)) ^ k) x = x := by
      intro k
      induction k with
      | zero => rfl
      | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, hfix, ih]
      | pred n ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hfix', ih]
    exact hall k

include hpri in
/-- **`K⁺/ℚ` is Galois** — the fixed field of the (normal, by commutativity) subgroup
`⟨conj⟩`. -/
theorem isGalois_realIF : IsGalois ℚ (realIF (K := K)) := by
  haveI := galCommutative (K := K) (hpri := hpri)
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  haveI : (Subgroup.zpowers (conjGal (K := K))).Normal :=
    Subgroup.normal_of_isMulCommutative _
  rw [← fixedField_zpowers_conjGal]
  exact IsGalois.of_fixedField_normal_subgroup _

include hpri in
/-- Transport: `IsGalois ℚ K⁺` for the `Subfield`-form `maximalRealSubfield K`. -/
theorem isGalois_maximalRealSubfield : IsGalois ℚ (maximalRealSubfield K) := by
  haveI := isGalois_realIF (K := K) (hpri := hpri)
  refine IsGalois.of_algEquiv (E := realIF (K := K)) ?_
  have hsub : (realIF (K := K)).toSubfield = maximalRealSubfield K := by
    ext x
    exact mem_realIF x
  exact AlgEquiv.ofRingEquiv (f := RingEquiv.subfieldCongr hsub) (fun q => rfl)

end FixedField

end CyclotomicNT
