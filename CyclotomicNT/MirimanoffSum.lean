import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Field.GeomSum

/-!
# The Mirimanoff sum `∑ j²tʲ` in `F_p` (Granville §4)

The endgame of the Kummer `B_{p−3}` criterion: the `n = 3` Mirimanoff sum has the closed form

  `∑_{j<p} j²·tʲ = t(1+t)/(1−t)²`  in `F_p`  (`t ≠ 1`, via Fermat `tᵖ = t`),

which vanishes only at `t ∈ {0, −1}`; and a Case I solution always provides a ratio
`t = −a/b ∉ {0, ±1}` among the three variable pairs.  Hence `ℓ₃(x+ξy) ≢ 0` for a suitable
arrangement, forcing (through the log-derivative dichotomy) the nonprincipality of `θ₃`, and
Herbrand then yields `p ∣ B_{p−3}`.

This file proves the two `ZMod p` facts; the log-derivative bridge is separate.
-/

open Finset

namespace CyclotomicNT

variable {p : ℕ} [hpri : Fact p.Prime]

/-- Units-to-full-sum bridge: a function of `ZMod p` vanishing at `0` sums equally over
units and over everything. -/
theorem sum_units_eq_sum_zmod {M : Type*} [AddCommMonoid M] (f : ZMod p → M) (h0 : f 0 = 0) :
    ∑ u : (ZMod p)ˣ, f u = ∑ x : ZMod p, f x := by
  classical
  have h1 : ∑ u : (ZMod p)ˣ, f u = ∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0), f x := by
    refine Finset.sum_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p)) ?_ ?_ ?_ ?_
    · exact fun u _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.ne_zero⟩
    · exact fun u _ v _ h => Units.ext h
    · intro x hx
      exact ⟨Units.mk0 x (Finset.mem_filter.mp hx).2, Finset.mem_univ _, rfl⟩
    · exact fun u _ => rfl
  rw [h1]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun x _ hx => ?_
  have hx0 : x = 0 := by
    by_contra h0x
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0x⟩)
  rw [hx0, h0]

/-- `∑_{j<p} tʲ = 1` in `F_p` for `t ≠ 1` (telescoping + Fermat `tᵖ = t`). -/
theorem sum_pow_eq_one {t : ZMod p} (ht : t ≠ 1) :
    ∑ j ∈ Finset.range p, t ^ j = 1 := by
  have hgeom := geom_sum_eq ht p
  rw [hgeom, ZMod.pow_card]
  exact div_self (sub_ne_zero.mpr ht)

/-- `(1−t)·∑_{j<p} j·tʲ = t` in `F_p` for `t ≠ 1`. -/
theorem one_sub_mul_sum_mul_pow {t : ZMod p} (ht : t ≠ 1) :
    (1 - t) * ∑ j ∈ Finset.range p, (j : ZMod p) * t ^ j = t := by
  have key : ∀ n : ℕ, (1 - t) * ∑ j ∈ Finset.range n, (j : ZMod p) * t ^ j
      = (∑ j ∈ Finset.range n, t ^ j) - 1 + t ^ n - (n : ZMod p) * t ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun j => t ^ j), mul_add, ih]
        push_cast
        ring
  have h := key p
  rw [sum_pow_eq_one ht, ZMod.pow_card, ZMod.natCast_self, zero_mul, sub_zero] at h
  rw [h]
  ring

/-- **The Mirimanoff `S₂` closed form**: `(1−t)²·∑_{j<p} j²·tʲ = t(1+t)` in `F_p`, `t ≠ 1`. -/
theorem one_sub_sq_mul_sum_sq_mul_pow {t : ZMod p} (ht : t ≠ 1) :
    (1 - t) ^ 2 * ∑ j ∈ Finset.range p, (j : ZMod p) ^ 2 * t ^ j = t * (1 + t) := by
  have key : ∀ n : ℕ, (1 - t) * ∑ j ∈ Finset.range n, (j : ZMod p) ^ 2 * t ^ j
      = 2 * (∑ j ∈ Finset.range n, (j : ZMod p) * t ^ j)
        - ((∑ j ∈ Finset.range n, t ^ j) - 1)
        - ((n : ZMod p) - 1) ^ 2 * t ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun j => (j : ZMod p) * t ^ j),
          Finset.sum_range_succ (f := fun j => t ^ j), mul_add, ih]
        push_cast
        ring
  have h := key p
  rw [sum_pow_eq_one ht, ZMod.pow_card, ZMod.natCast_self, sub_self, sub_zero, zero_sub,
    neg_one_sq, one_mul] at h
  have hB := one_sub_mul_sum_mul_pow ht
  calc (1 - t) ^ 2 * ∑ j ∈ Finset.range p, (j : ZMod p) ^ 2 * t ^ j
      = (1 - t) * ((1 - t) * ∑ j ∈ Finset.range p, (j : ZMod p) ^ 2 * t ^ j) := by ring
    _ = (1 - t) * (2 * (∑ j ∈ Finset.range p, (j : ZMod p) * t ^ j) - t) := by rw [h]
    _ = 2 * ((1 - t) * ∑ j ∈ Finset.range p, (j : ZMod p) * t ^ j) - t * (1 - t) := by ring
    _ = t * (1 + t) := by rw [hB]; ring

/-- **Nonvanishing of the `S₂` sum**: for `t ∉ {0, 1, −1}`, `∑_{j<p} j²·tʲ ≠ 0` in `F_p`. -/
theorem sum_sq_mul_pow_ne_zero {t : ZMod p} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm1 : t ≠ -1) :
    ∑ j ∈ Finset.range p, (j : ZMod p) ^ 2 * t ^ j ≠ 0 := by
  intro hzero
  have := one_sub_sq_mul_sum_sq_mul_pow h1
  rw [hzero, mul_zero] at this
  rcases mul_eq_zero.mp this.symm with h | h
  · exact h0 h
  · exact hm1 (by linear_combination h)

/-- **A Case I solution has a good Mirimanoff ratio**: if `x + y + z = 0` in `F_p` with
`x, y, z ≠ 0` and `p ≥ 5`, then one of the pairs `(a, b) ∈ {(x,y), (y,z), (z,x)}` has
`t := −a·b⁻¹ ∉ {0, 1, −1}`. -/
theorem exists_good_ratio (hp5 : 5 ≤ p) {x y z : ZMod p} (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) (hsum : x + y + z = 0) :
    ∃ a b : ZMod p, a ≠ 0 ∧ b ≠ 0 ∧ a + b ≠ 0 ∧
      ((a = x ∧ b = y) ∨ (a = y ∧ b = z) ∨ (a = z ∧ b = x)) ∧
      -a * b⁻¹ ≠ 0 ∧ -a * b⁻¹ ≠ 1 ∧ -a * b⁻¹ ≠ -1 := by
  -- `−a/b = 1 ⟺ a + b = 0`; `−a/b = −1 ⟺ a = b`; `−a/b = 0` impossible.
  -- if all three pairs are bad, then each pair is equal or opposite; case analysis kills it.
  have hchar : (p : ZMod p) = 0 := ZMod.natCast_self p
  have key : ∀ a b : ZMod p, a ≠ 0 → b ≠ 0 → a + b ≠ 0 → a ≠ b →
      -a * b⁻¹ ≠ 0 ∧ -a * b⁻¹ ≠ 1 ∧ -a * b⁻¹ ≠ -1 := by
    intro a b ha hb hab hne
    have hd : -a * b⁻¹ = -(a / b) := by rw [div_eq_mul_inv]; ring
    refine ⟨?_, ?_, ?_⟩
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact ha (neg_eq_zero.mp h)
      · exact hb (inv_eq_zero.mp h)
    · intro h
      rw [hd] at h
      have h2 : a / b = -1 := by linear_combination -h
      apply hab
      rw [div_eq_iff hb] at h2
      linear_combination h2
    · intro h
      rw [hd, neg_inj] at h
      exact hne ((div_eq_one_iff_eq hb).mp h)
  -- the three "badness" conditions: `a + b = 0` or `a = b`
  by_cases hxy : x + y = 0
  · -- then `z = 0`, contradiction
    exact absurd (by linear_combination hsum - hxy) hz
  · by_cases hxy' : x = y
    · by_cases hyz : y = z
      · -- `x = y = z` with `3x = 0`: impossible for `p ≥ 5`
        exfalso
        have h3 : (3 : ZMod p) * x = 0 := by
          rw [hxy', hyz] at hsum ⊢
          linear_combination hsum
        have h3ne : (3 : ZMod p) ≠ 0 := by
          have : ((3 : ℕ) : ZMod p) ≠ 0 := by
            rw [Ne, ZMod.natCast_eq_zero_iff]
            intro hd
            have := Nat.le_of_dvd (by norm_num) hd
            omega
          simpa using this
        rcases mul_eq_zero.mp h3 with h | h
        · exact h3ne h
        · exact hx h
      · -- pair `(y, z)`: `y + z = −x ≠ 0` and `y ≠ z`
        refine ⟨y, z, hy, hz, ?_, Or.inr (Or.inl ⟨rfl, rfl⟩), key y z hy hz ?_ hyz⟩
        · intro h
          exact hx (by linear_combination hsum - h)
        · intro h
          exact hx (by linear_combination hsum - h)
    · -- pair `(x, y)`: `x + y ≠ 0` and `x ≠ y`
      exact ⟨x, y, hx, hy, hxy, Or.inl ⟨rfl, rfl⟩, key x y hx hy hxy hxy'⟩

end CyclotomicNT
