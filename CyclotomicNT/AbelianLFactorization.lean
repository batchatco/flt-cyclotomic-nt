import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Toward the abelian factorization `ζ_K = ∏_χ L(s,χ)`  (rung A of the Iwasawa ladder)

For an abelian number field `K` (here we care about `K = ℚ(ζ_N)`), the Dedekind zeta function
factors as a product of Dirichlet `L`-functions over the characters of `Gal(K/ℚ) ≅ (ℤ/N)ˣ`:
`ζ_K(s) = ∏_χ L(s,χ)`.  Combined with the (already-merged) Dirichlet class number formula
(`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) this yields the relative class number
formula `h⁻ = Q·w·∏_{χ odd}(-½ B_{1,χ})` — the minus-part that reflection ties to the
`realUnitKummer` obstruction in `CyclotomicNT`.

## Proof strategy (with the Mathlib building blocks that already exist)

1. **Local Euler-factor identity** (this file): for a unit `a` of order `d` in `(ℤ/N)ˣ`,
   `∏_χ (1 - χ(a)·X) = (1 - X^d)^{φ(N)/d}`.  Algebraic heart; uses:
   * the polynomial core `1 - X^d = ∏_{ω ∈ μ_d}(1 - ω·X)` — **`prod_one_sub_C_mul_X` below**,
     from `Polynomial.X_pow_sub_one_eq_prod`;
   * the character-group duality `MulChar.card_subgroupOrderIsoSubgroupMulChar` (each value of
     `χ ↦ χ(a)` in `μ_d` is attained `φ(N)/d` times) — via `Finset.prod_fiberwise_of_maps_to`.
2. **Euler product matching**: `ζ_K` and each `L(s,χ)` have Euler products
   (`riemannZeta_eulerProduct_tprod`, `dirichletLSeries_eulerProduct_tprod`); match local factors
   at each `p ∤ N` using (1), and handle `p ∣ N` separately.
3. **`ζ_K = ∏_χ L(s,χ)`**, then divide by `ζ_{K⁺} = ∏_{χ even} L` to get `∏_{χ odd} L`.
4. **`h⁻` formula**: residue/value comparison via the class number formula and
   `L(0,χ) = -B_{1,χ}` (`CyclotomicNT.GeneralizedBernoulli`, the `k = 0` value).
-/

open Polynomial Finset
open scoped Classical

/-- **Polynomial Euler-factor core.** Over a field with a primitive `d`-th root of unity `ζ`,
`∏_{ω ∈ μ_d}(1 - ω·X) = 1 - X^d` (the reciprocal of `X^d - 1 = ∏(X - ω)`). This is the
single-`d`-th-root local factor underlying `∏_χ(1 - χ(a)X) = (1 - X^d)^{φ(N)/d}`. -/
theorem prod_one_sub_C_mul_X {K : Type*} [Field K] {d : ℕ} (hd : 0 < d) {ζ : K}
    (h : IsPrimitiveRoot ζ d) :
    ∏ ω ∈ nthRootsFinset d (1 : K), (1 - C ω * X) = 1 - X ^ d := by
  have hω0 : ∀ ω ∈ nthRootsFinset d (1 : K), ω ≠ 0 := by
    intro ω hω
    rw [mem_nthRootsFinset hd] at hω
    rintro rfl
    rw [zero_pow hd.ne'] at hω
    exact zero_ne_one hω
  -- reindex `ω ↦ ω⁻¹` (a bijection of `μ_d`) and use `X^d - 1 = ∏ (X - C ω)`
  have hbij : ∏ ω ∈ nthRootsFinset d (1 : K), (X - C ω⁻¹)
      = ∏ ω ∈ nthRootsFinset d (1 : K), (X - C ω) := by
    refine Finset.prod_nbij' (fun ω => ω⁻¹) (fun ω => ω⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro ω hω
      rw [mem_nthRootsFinset hd] at hω ⊢; rw [inv_pow, hω, inv_one]
    · intro ω hω
      rw [mem_nthRootsFinset hd] at hω ⊢; rw [inv_pow, hω, inv_one]
    · intro ω hω; exact inv_inv ω
    · intro ω hω; exact inv_inv ω
    · intro ω _; rfl
  -- each factor: `1 - C ω * X = -C ω * (X - C ω⁻¹)`
  have hfac : ∀ ω ∈ nthRootsFinset d (1 : K), (1 - C ω * X) = -C ω * (X - C ω⁻¹) := by
    intro ω hω
    have hcc : C ω * C ω⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ (hω0 ω hω), map_one]
    linear_combination -hcc
  -- `∏ (-C ω) = -1`: it is the value at `X = 0` of `∏ (X - C ω) = X^d - 1`.
  have hconst : ∏ ω ∈ nthRootsFinset d (1 : K), (-C ω) = -1 := by
    have key : (∏ ω ∈ nthRootsFinset d (1 : K), (X - C ω)).eval 0 = (X ^ d - 1 : K[X]).eval 0 := by
      rw [X_pow_sub_one_eq_prod hd h]
    simp only [eval_prod, eval_sub, eval_X, eval_C, eval_pow, eval_one, zero_sub,
      zero_pow hd.ne'] at key
    calc ∏ ω ∈ nthRootsFinset d (1 : K), (-C ω)
        = C (∏ ω ∈ nthRootsFinset d (1 : K), (-ω)) := by rw [map_prod]; simp only [map_neg]
      _ = C (-1) := by rw [key]
      _ = -1 := by rw [map_neg, map_one]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, hbij, ← X_pow_sub_one_eq_prod hd h,
    hconst]
  ring

namespace MulChar

variable {M R : Type*} [CommMonoid M] [CommRing R] [IsDomain R]

/-- The value `χ(a)` of a multiplicative character at a unit `a` is a `(orderOf a)`-th root of
unity. (This is the "image ⊆ `μ_d`" half of the local Euler-factor identity.) -/
theorem apply_unit_mem_nthRootsFinset (χ : MulChar M R) {a : Mˣ} (hd : 0 < orderOf a) :
    χ (a : M) ∈ nthRootsFinset (orderOf a) (1 : R) := by
  rw [mem_nthRootsFinset hd, ← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one,
    Units.val_one, map_one]

end MulChar

namespace DirichletCharacter

section Kernel

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n]
  [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]

/-- **Kernel cardinality (the duality content).** The Dirichlet characters trivial at a unit `a`
are exactly the dual subgroup of `⟨a⟩`, whose order is `φ(n) / orderOf a`.  Stated
multiplicatively (`orderOf a · #{χ : χ(a)=1} = φ(n)`): each fiber of `χ ↦ χ(a)` has this size, so
the `orderOf a` distinct values are attained equally often. -/
theorem orderOf_mul_card_filter_apply_eq_one (a : (ZMod n)ˣ) :
    orderOf a * (Finset.univ.filter (fun χ : DirichletCharacter R n => χ (a : ZMod n) = 1)).card
      = n.totient := by
  classical
  set K := (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) R (Subgroup.zpowers a)).ofDual
    with hK
  -- the filter predicate is exactly membership in the dual subgroup `K`
  have hmem : ∀ χ : DirichletCharacter R n, χ (a : ZMod n) = 1 ↔ χ ∈ K := by
    intro χ
    rw [hK, MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]
    constructor
    · intro h m hm
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
      have hu : χ.toUnitHom a = 1 := Units.ext (by rw [MulChar.coe_toUnitHom]; exact h)
      rw [← MulChar.coe_toUnitHom, map_zpow, hu, one_zpow, Units.val_one]
    · intro h; exact h a (Subgroup.mem_zpowers a)
  -- so the filter has the cardinality of `K`, which duality identifies with `|(ZMod n)ˣ ⧸ ⟨a⟩|`
  have hcard : (Finset.univ.filter
      (fun χ : DirichletCharacter R n => χ (a : ZMod n) = 1)).card = Nat.card K := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight hmem)
  rw [hcard, hK, MulChar.card_subgroupOrderIsoSubgroupMulChar, ← ZMod.card_units_eq_totient,
    ← Nat.card_eq_fintype_card, ← Nat.card_zpowers (a := a)]
  exact Subgroup.card_mul_index (Subgroup.zpowers a)

end Kernel

section Field

variable {R : Type*} [Field R] {n : ℕ} [NeZero n]
  [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]

/-- **Fiber equidistribution.** For a unit `a` of order `d` and any `d`-th root of unity `ω`, the
number of Dirichlet characters with `χ(a)=ω` equals the number with `χ(a)=1` (`= φ(n)/d`).
Each fiber injects into the `ω=1` fiber (coset shift `χ ↦ χ·χ₀⁻¹`), and the fibers partition all
`φ(n) = d·(φ(n)/d)` characters across the `d` roots, forcing every fiber to the maximal size. -/
theorem card_filter_apply_eq (a : (ZMod n)ˣ) (hd : 0 < orderOf a) {ζ : R}
    (hζ : IsPrimitiveRoot ζ (orderOf a)) {ω : R}
    (hω : ω ∈ nthRootsFinset (orderOf a) (1 : R)) :
    (Finset.univ.filter (fun χ : DirichletCharacter R n => χ (a : ZMod n) = ω)).card
      = (Finset.univ.filter (fun χ : DirichletCharacter R n => χ (a : ZMod n) = 1)).card := by
  -- every fiber injects (coset shift) into the `ω = 1` fiber, so has card `≤ k`
  have hle : ∀ ω' ∈ nthRootsFinset (orderOf a) (1 : R),
      (Finset.univ.filter (fun χ : DirichletCharacter R n => χ (a : ZMod n) = ω')).card
        ≤ (Finset.univ.filter (fun χ : DirichletCharacter R n => χ (a : ZMod n) = 1)).card := by
    intro ω' hω'
    rcases (Finset.univ.filter
        (fun χ : DirichletCharacter R n => χ (a : ZMod n) = ω')).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.card_empty]; exact Nat.zero_le _
    · obtain ⟨χ₀, hχ₀⟩ := hne
      rw [Finset.mem_filter] at hχ₀
      have hω'0 : ω' ≠ 0 := by
        rw [mem_nthRootsFinset hd] at hω'
        rintro rfl; rw [zero_pow hd.ne'] at hω'; exact zero_ne_one hω'
      apply Finset.card_le_card_of_injOn (fun χ => χ * χ₀⁻¹)
      · intro χ hχ
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
        rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv', hχ, hχ₀.2]
        exact mul_inv_cancel₀ hω'0
      · intro χ₁ _ χ₂ _ h
        exact mul_right_cancel h
  -- the fibers partition all characters, giving `∑ = φ(n)`
  have hsum : ∑ ω' ∈ nthRootsFinset (orderOf a) (1 : R),
      (Finset.univ.filter (fun χ : DirichletCharacter R n => χ (a : ZMod n) = ω')).card
        = n.totient := by
    rw [← Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
          (t := nthRootsFinset (orderOf a) (1 : R))
          (f := fun χ : DirichletCharacter R n => χ (a : ZMod n))
          (fun χ _ => MulChar.apply_unit_mem_nthRootsFinset χ hd),
        Finset.card_univ, ← Nat.card_eq_fintype_card, card_eq_totient_of_hasEnoughRootsOfUnity]
  -- the constant `k`-sum also equals `d·k = φ(n)`, so the totals match and `≤` becomes `=`
  have hconst : ∑ _ω' ∈ nthRootsFinset (orderOf a) (1 : R),
      (Finset.univ.filter (fun χ : DirichletCharacter R n => χ (a : ZMod n) = 1)).card
        = n.totient := by
    rw [Finset.sum_const, hζ.card_nthRootsFinset, smul_eq_mul]
    exact orderOf_mul_card_filter_apply_eq_one a
  exact (Finset.sum_eq_sum_iff_of_le hle).mp (hsum.trans hconst.symm) ω hω

end Field

end DirichletCharacter
