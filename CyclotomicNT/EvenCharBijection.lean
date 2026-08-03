import CyclotomicNT.CyclotomicPlaceCycle
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# The even Dirichlet characters mod `p` are indexed by `ℤ/m`, `m = (p−1)/2`

For a generator `g` of `(ℤ/p)ˣ`, an even character `χ` satisfies `χ(g)^m = χ(−1) = 1`, so
`χ(g) = e(k/m)` for a unique `k : ℤ/m` — and `χ` is determined by `χ(g)`.  Counting
(via Mathlib's character duality `MulChar.subgroupOrderIsoSubgroupMulChar`: the even characters
are the dual subgroup of `{±1}`, of cardinality `[(ℤ/p)ˣ : {±1}] = m`) makes this assignment a
**bijection** `evenCharEquiv : {χ // χ.Even} ≃ ℤ/m`, with `χ = 1 ↔ k = 0`.

This is the index matching between the reduced-group-determinant eigenvalues `λ_k` of
`CyclotomicRegulator` and the even `L(1,χ)` values of `EvenLOneValue`.
-/

open NumberField Finset

namespace CyclotomicNT

variable {p : ℕ} [hpri : Fact p.Prime] {g : (ZMod p)ˣ}

section CharAtGenerator

/-- A Dirichlet character is determined by its value at a generator. -/
theorem dirichletChar_ext_of_generator (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g)
    {χ χ' : DirichletCharacter ℂ p} (h : χ (g : ZMod p) = χ' (g : ZMod p)) : χ = χ' := by
  refine MulChar.ext fun a => ?_
  obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hgen a)
  rw [Units.val_pow_eq_pow_val, map_pow, map_pow, h]

/-- For an even character, `χ(g)^m = χ(g^m) = χ(−1) = 1`. -/
theorem even_char_pow_half (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2)
    {χ : DirichletCharacter ℂ p} (hχ : χ.Even) :
    χ (g : ZMod p) ^ ((p - 1) / 2) = 1 := by
  rw [← map_pow, ← Units.val_pow_eq_pow_val, generator_pow_half hgen hp]
  have : ((-1 : (ZMod p)ˣ) : ZMod p) = (-1 : ZMod p) := by
    rw [Units.val_neg, Units.val_one]
  rw [this]
  exact hχ

/-- The index exists: `χ(g)` is an `m`-th root of unity, hence a `stdAddChar` value. -/
theorem exists_evenCharIdx [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2)
    (χ : {χ : DirichletCharacter ℂ p // χ.Even}) :
    ∃ k : ZMod ((p - 1) / 2), ZMod.stdAddChar k = χ.1 (g : ZMod p) := by
  obtain ⟨i, -, hi⟩ := (isPrimitiveRoot_stdAddChar_one
    (n := (p - 1) / 2)).eq_pow_of_pow_eq_one (even_char_pow_half hgen hp χ.2)
  exact ⟨(i : ZMod ((p - 1) / 2)), by rw [← hi, stdAddChar_pow, mul_one]⟩

/-- The index `k(χ) : ℤ/m` of an even character: the unique `k` with `χ(g) = e(k/m)`. -/
noncomputable def evenCharIdx [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2)
    (χ : {χ : DirichletCharacter ℂ p // χ.Even}) : ZMod ((p - 1) / 2) :=
  (exists_evenCharIdx hgen hp χ).choose

/-- The defining property of `evenCharIdx`: `e(k(χ)/m) = χ(g)`. -/
theorem stdAddChar_evenCharIdx [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2)
    (χ : {χ : DirichletCharacter ℂ p // χ.Even}) :
    ZMod.stdAddChar (evenCharIdx hgen hp χ) = χ.1 (g : ZMod p) :=
  (exists_evenCharIdx hgen hp χ).choose_spec

theorem evenCharIdx_injective [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2) :
    Function.Injective (evenCharIdx hgen hp) := by
  intro χ χ' h
  have hval : χ.1 (g : ZMod p) = χ'.1 (g : ZMod p) := by
    rw [← stdAddChar_evenCharIdx hgen hp, ← stdAddChar_evenCharIdx hgen hp, h]
  exact Subtype.ext (dirichletChar_ext_of_generator hgen hval)

end CharAtGenerator

section Counting

/-- **The number of even Dirichlet characters mod `p` is `(p−1)/2`** — they form the dual
subgroup of `{±1} ≤ (ℤ/p)ˣ` (Mathlib character duality), of cardinality the index of `{±1}`. -/
theorem card_even_dirichletChar (hp : p ≠ 2) :
    Nat.card {χ : DirichletCharacter ℂ p // χ.Even} = (p - 1) / 2 := by
  haveI : NeZero (Monoid.exponent (ZMod p)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hlt : 2 < p := by have := hpri.out.two_le; omega
  -- the even characters are the dual subgroup of `H = ⟨−1⟩`
  set H : Subgroup (ZMod p)ˣ := Subgroup.zpowers (-1 : (ZMod p)ˣ) with hH
  have hdual : ∀ χ : DirichletCharacter ℂ p,
      (χ ∈ (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod p) ℂ H).ofDual ↔ χ.Even) := by
    intro χ
    rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]
    constructor
    · intro h
      have := h (-1) (Subgroup.mem_zpowers _)
      rwa [Units.val_neg, Units.val_one] at this
    · intro hχ x hx
      obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hx
      rw [Units.val_pow_eq_pow_val, map_pow, Units.val_neg, Units.val_one, hχ, one_pow]
  -- counting: `card (dual H) = card ((ℤ/p)ˣ ⧸ H)` and `card H = 2`
  have hcardH : Nat.card H = 2 := by
    rw [hH, Nat.card_zpowers]
    haveI : Fact (2 < p) := ⟨hlt⟩
    refine orderOf_eq_prime (by rw [neg_one_sq]) ?_
    intro h
    exact ZMod.neg_one_ne_one (by
      have := congrArg (Units.val) h
      rwa [Units.val_neg, Units.val_one] at this)
  have hcardG : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hpri.out]
  have hquot : Nat.card ((ZMod p)ˣ ⧸ H) = (p - 1) / 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup H
    rw [hcardG, hcardH] at h
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp)
    omega
  rw [← hquot, ← MulChar.card_subgroupOrderIsoSubgroupMulChar (M := ZMod p) (R := ℂ) (H := H)]
  exact Nat.card_congr (Equiv.subtypeEquivRight hdual).symm

/-- **The even characters mod `p` biject with `ℤ/m`** via `χ ↦ k(χ)` (`χ(g) = e(k/m)`). -/
theorem evenCharIdx_bijective [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2) :
    Function.Bijective (evenCharIdx hgen hp) := by
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨evenCharIdx_injective hgen hp, ?_⟩
  rw [card_even_dirichletChar hp, Nat.card_eq_fintype_card (α := ZMod ((p - 1) / 2)), ZMod.card]

/-- The bijection `{χ even} ≃ ℤ/m`. -/
noncomputable def evenCharEquiv [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2) :
    {χ : DirichletCharacter ℂ p // χ.Even} ≃ ZMod ((p - 1) / 2) :=
  Equiv.ofBijective _ (evenCharIdx_bijective hgen hp)

/-- The trivial character corresponds to `k = 0`. -/
theorem evenCharIdx_eq_zero_iff [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2)
    (χ : {χ : DirichletCharacter ℂ p // χ.Even}) :
    evenCharIdx hgen hp χ = 0 ↔ χ.1 = 1 := by
  constructor
  · intro h
    have hval : χ.1 (g : ZMod p) = 1 := by
      rw [← stdAddChar_evenCharIdx hgen hp, h, AddChar.map_zero_eq_one]
    exact dirichletChar_ext_of_generator hgen (by
      rw [hval, MulChar.one_apply (Units.isUnit g)])
  · intro h
    have h1 : ZMod.stdAddChar (evenCharIdx hgen hp χ) = 1 := by
      rw [stdAddChar_evenCharIdx hgen hp, h, MulChar.one_apply (Units.isUnit g)]
    by_contra hne
    exact stdAddChar_ne_one hne h1

end Counting

end CyclotomicNT
