import CyclotomicNT.HerbrandEigen

/-!
# Eigenspace projection of the class group mod `p`

The `F_p[Δ]`-idempotent decomposition of `Cl(ℚ(ζ_p))/p` (Δ = Gal ≅ (ℤ/p)ˣ), in multiplicative
form: for a class `cl` with `cl^p = 1`, the projection

  `eigenProj p k cl := ∏_a (σ_a⁻¹ cl)^{(a^k mod p)}`

is a weight-`k` eigenclass (`isEigenClass_eigenProj`), and the product of all projections over
`k < p−1` recovers `cl^{p−1}` (`prod_eigenProj`, via the geometric sum `∑_k a^k ≡ 0` for
`a ≠ 1`).  Consequently a nontrivial `cl` of order `p` has a nontrivial eigencomponent
(`exists_eigenProj_ne_one`) — the input to Herbrand's theorem. -/

open Finset NumberField IsCyclotomicExtension.Rat
open scoped Pointwise nonZeroDivisors

namespace CyclotomicNT

variable {p : ℕ} [hpri : Fact p.Prime] {k₀ : Type*} [Field k₀] [NumberField k₀]
  [IsCyclotomicExtension {p} ℚ k₀]

/-! ### The Galois action is multiplicative in the automorphism -/

theorem classGroupGalAct_one (cl : ClassGroup (𝓞 k₀)) :
    classGroupGalAct (1 : k₀ ≃ₐ[ℚ] k₀) cl = cl := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective cl
  rw [classGroupGalAct_mk0]
  congr 1
  exact Subtype.ext (one_smul _ _)

theorem classGroupGalAct_mul (σ τ : k₀ ≃ₐ[ℚ] k₀) (cl : ClassGroup (𝓞 k₀)) :
    classGroupGalAct σ (classGroupGalAct τ cl) = classGroupGalAct (σ * τ) cl := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective cl
  rw [classGroupGalAct_mk0, classGroupGalAct_mk0, classGroupGalAct_mk0]
  congr 1
  exact Subtype.ext (mul_smul σ τ (I : Ideal (𝓞 k₀))).symm

/-! ### Exponent arithmetic for order-`p` elements -/

omit hpri in
/-- For `x` with `x^p = 1`, exponents only matter mod `p`. -/
theorem pow_eq_pow_of_modEq_p {G : Type*} [Group G] {x : G} (hx : x ^ p = 1) {m n : ℕ}
    (h : m ≡ n [MOD p]) : x ^ m = x ^ n :=
  pow_eq_pow_iff_modEq.mpr (h.of_dvd (orderOf_dvd_of_pow_eq_one hx))

/-! ### The projection -/

variable (p) in
/-- The weight-`k` eigenprojection of a class: `∏_a (σ_a⁻¹ cl)^{(a^k mod p)}`
(the idempotent `ε_k` up to the unit `−1 = (p−1)⁻¹ mod p`, in multiplicative notation). -/
noncomputable def eigenProj (k : ℕ) (cl : ClassGroup (𝓞 k₀)) : ClassGroup (𝓞 k₀) :=
  ∏ a : (ZMod p)ˣ, (classGroupGalAct ((galEquivZMod p k₀).symm a)⁻¹ cl)
    ^ (((a ^ k : (ZMod p)ˣ) : ZMod p)).val

omit hpri [IsCyclotomicExtension {p} ℚ k₀] in
/-- The Galois action preserves `(·)^p = 1`. -/
theorem galAct_pow_p {cl : ClassGroup (𝓞 k₀)} (hclp : cl ^ p = 1) (σ : k₀ ≃ₐ[ℚ] k₀) :
    (classGroupGalAct σ cl) ^ p = 1 := by
  rw [← map_pow, hclp, map_one]

theorem eigenProj_pow_p {cl : ClassGroup (𝓞 k₀)} (hclp : cl ^ p = 1) (k : ℕ) :
    (eigenProj p k cl) ^ p = 1 := by
  rw [eigenProj, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [← pow_mul, mul_comm, pow_mul, galAct_pow_p hclp, one_pow]

/-- **The projection is an eigenclass**: `σ_b` acts on `eigenProj p k cl` by `b^k`. -/
theorem isEigenClass_eigenProj {cl : ClassGroup (𝓞 k₀)} (hclp : cl ^ p = 1) (k : ℕ) :
    IsEigenClass p k (eigenProj p k cl) := by
  intro b
  rw [eigenProj, map_prod]
  -- push the action into each factor and compose the automorphisms
  have hcomp : ∀ a : (ZMod p)ˣ,
      classGroupGalAct ((galEquivZMod p k₀).symm b)
        ((classGroupGalAct ((galEquivZMod p k₀).symm a)⁻¹ cl)
          ^ (((a ^ k : (ZMod p)ˣ) : ZMod p)).val)
      = (classGroupGalAct ((galEquivZMod p k₀).symm (a * b⁻¹))⁻¹ cl)
          ^ (((a ^ k : (ZMod p)ˣ) : ZMod p)).val := by
    intro a
    have hσ : (galEquivZMod p k₀).symm b * ((galEquivZMod p k₀).symm a)⁻¹
        = ((galEquivZMod p k₀).symm (a * b⁻¹))⁻¹ := by
      rw [← map_inv, ← map_inv, ← map_mul, mul_inv_rev, inv_inv]
    rw [map_pow, classGroupGalAct_mul, hσ]
  rw [Finset.prod_congr rfl fun a _ => hcomp a]
  -- reindex `a = a' * b`
  rw [← Equiv.prod_comp (Equiv.mulRight b) fun a =>
    (classGroupGalAct ((galEquivZMod p k₀).symm (a * b⁻¹))⁻¹ cl)
      ^ (((a ^ k : (ZMod p)ˣ) : ZMod p)).val]
  simp only [Equiv.coe_mulRight, mul_inv_cancel_right]
  -- collect the `b^k` exponent
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← pow_mul]
  refine pow_eq_pow_of_modEq_p (galAct_pow_p hclp _) ?_
  -- `val((ab)^k) ≡ val(a^k)·val(b^k) (mod p)`
  have : ((a * b) ^ k : (ZMod p)ˣ) = (a ^ k) * (b ^ k) := by rw [mul_pow]
  calc ((((a * b) ^ k : (ZMod p)ˣ) : ZMod p)).val
      = (((a ^ k : (ZMod p)ˣ) : ZMod p) * ((b ^ k : (ZMod p)ˣ) : ZMod p)).val := by
        rw [this, Units.val_mul]
    _ ≡ (((a ^ k : (ZMod p)ˣ) : ZMod p)).val * (((b ^ k : (ZMod p)ˣ) : ZMod p)).val [MOD p] := by
        rw [ZMod.val_mul]
        exact (Nat.mod_modEq _ p)

/-- **The decomposition recovers `cl^{p−1}`**: `∏_{k < p−1} eigenProj p k cl = cl^{p−1}`. -/
theorem prod_eigenProj {cl : ClassGroup (𝓞 k₀)} (hclp : cl ^ p = 1) :
    ∏ k ∈ Finset.range (p - 1), eigenProj p k cl = cl ^ (p - 1) := by
  classical
  haveI : Fact (1 < p) := ⟨hpri.out.one_lt⟩
  simp only [eigenProj]
  rw [Finset.prod_comm]
  have hgeom : ∀ a : (ZMod p)ˣ,
      ∏ k ∈ Finset.range (p - 1), (classGroupGalAct ((galEquivZMod p k₀).symm a)⁻¹ cl)
        ^ (((a ^ k : (ZMod p)ˣ) : ZMod p)).val
      = if a = 1 then cl ^ (p - 1) else 1 := by
    intro a
    rw [Finset.prod_pow_eq_pow_sum]
    by_cases ha : a = 1
    · subst ha
      rw [if_pos rfl]
      have hval : ∀ k ∈ Finset.range (p - 1), ((((1 : (ZMod p)ˣ) ^ k : (ZMod p)ˣ) : ZMod p)).val
          = 1 := fun k _ => by rw [one_pow, Units.val_one, ZMod.val_one]
      rw [Finset.sum_congr rfl hval, Finset.sum_const, Finset.card_range, smul_eq_mul,
        mul_one, map_one, inv_one, classGroupGalAct_one]
    · rw [if_neg ha]
      have hS : (∑ k ∈ Finset.range (p - 1), (((a ^ k : (ZMod p)ˣ) : ZMod p)).val) ≡ 0 [MOD p] := by
        have hcast : ((∑ k ∈ Finset.range (p - 1),
            (((a ^ k : (ZMod p)ˣ) : ZMod p)).val : ℕ) : ZMod p) = 0 := by
          rw [Nat.cast_sum,
            Finset.sum_congr rfl fun k _ => by
              rw [ZMod.natCast_val, ZMod.cast_id, Units.val_pow_eq_pow_val]]
          have hane : ((a : ZMod p)) ≠ 1 := fun h => ha (Units.ext h)
          rw [geom_sum_eq hane, ZMod.pow_card_sub_one_eq_one a.ne_zero, sub_self,
            zero_div]
        exact Nat.modEq_zero_iff_dvd.mpr ((ZMod.natCast_eq_zero_iff _ p).mp hcast)
      rw [pow_eq_pow_of_modEq_p (galAct_pow_p hclp _) hS, pow_zero]
  rw [Finset.prod_congr rfl fun a _ => hgeom a]
  simp

end CyclotomicNT
