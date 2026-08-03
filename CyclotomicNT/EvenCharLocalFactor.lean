import CyclotomicNT.EvenCharBijection
import CyclotomicNT.DedekindFactorization

/-!
# The even-character local factor `∏_{χ even}(1 − χ(a)t) = (1 − t^f)^{m/f}`

The even analogue of `DedekindFactorization.prod_char_one_sub`: at a unit `a = g^j` of `ℤ/p`,
the product of `1 − χ(a)t` over the **even** characters is `(1 − t^f)^{m/f}` where
`f = addOrderOf (j : ℤ/m)` (the order of the `±a` class) and `m = (p−1)/2`.

Via `evenCharEquiv` the product becomes `∏_{k ∈ ℤ/m}(1 − e(jk/m)t)`; the values `e(jk/m)` run
over the `f`-th roots of unity with constant fiber size `m/f` (additive-character
orthogonality), and `∏_{ζ ∈ μ_f}(1 − ζt) = 1 − t^f`.

This is the `q ≠ p` Euler factor of `∏_{χ even} L(s,χ)`, to be matched against the local factor
of `ζ_{K⁺}` (`f` = the residue degree of `q` in `K⁺`).
-/

open Finset Polynomial

namespace CyclotomicNT

section AddOrthogonality

variable {m : ℕ} [NeZero m]

/-- Additive-character orthogonality on `ℤ/m`: `∑_k e(ck/m) = m·[c = 0]`. -/
theorem sum_stdAddChar_mul (c : ZMod m) :
    ∑ k : ZMod m, ZMod.stdAddChar (c * k) = if c = 0 then (m : ℂ) else 0 := by
  have hψ : ∀ k : ZMod m, ZMod.stdAddChar (c * k)
      = (AddChar.mulShift ZMod.stdAddChar c) k := fun k => rfl
  rw [Finset.sum_congr rfl fun k _ => hψ k]
  rcases eq_or_ne c 0 with rfl | hc
  · rw [if_pos rfl]
    have h0 : AddChar.mulShift (ZMod.stdAddChar (N := m)) 0 = 0 := by
      rw [AddChar.mulShift_zero]; rfl
    rw [h0]
    simp [AddChar.zero_apply, ZMod.card]
  · rw [if_neg hc]
    refine AddChar.sum_eq_zero_iff_ne_zero.mpr fun h => stdAddChar_ne_one hc ?_
    have h1 := DFunLike.congr_fun h (1 : ZMod m)
    rwa [AddChar.mulShift_apply, AddChar.zero_apply, mul_one] at h1

/-- The values `e(jk/m)` are `addOrderOf j`-th roots of unity. -/
theorem stdAddChar_mul_pow_addOrderOf (j k : ZMod m) :
    ZMod.stdAddChar (j * k) ^ addOrderOf j = 1 := by
  rw [stdAddChar_pow, show ((addOrderOf j : ℕ) : ZMod m) * (j * k)
    = (((addOrderOf j : ℕ) : ZMod m) * j) * k by ring, ← nsmul_eq_mul,
    addOrderOf_nsmul_eq_zero, zero_mul, AddChar.map_zero_eq_one]

omit [NeZero m] in
/-- `addOrderOf j ∣ m` in `ℤ/m`. -/
theorem addOrderOf_dvd_card (j : ZMod m) : addOrderOf j ∣ m :=
  addOrderOf_dvd_of_nsmul_eq_zero (by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])

open scoped Classical in
/-- **Additive fiber count**: each `addOrderOf j`-th root of unity `ζ` arises as `e(jk/m)` for
exactly `m / addOrderOf j` values `k ∈ ℤ/m`. -/
theorem fiber_card_add {j : ZMod m} {ζ : ℂ}
    (hζ : ζ ∈ nthRootsFinset (addOrderOf j) (1 : ℂ)) :
    (univ.filter (fun k : ZMod m => ZMod.stdAddChar (j * k) = ζ)).card
      = m / addOrderOf j := by
  have hf : 0 < addOrderOf j := addOrderOf_pos j
  have hζ1 : ζ ^ addOrderOf j = 1 := by rwa [mem_nthRootsFinset hf] at hζ
  have hζ0 : ζ ≠ 0 := fun h => by simp [h, hf.ne'] at hζ1
  have hfc : (addOrderOf j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hf.ne'
  have key : ∀ k : ZMod m, ((if ZMod.stdAddChar (j * k) = ζ then 1 else 0 : ℕ) : ℂ)
      = (∑ r ∈ range (addOrderOf j), (ZMod.stdAddChar (j * k) * ζ⁻¹) ^ r) / addOrderOf j := by
    intro k
    have hw : (ZMod.stdAddChar (j * k) * ζ⁻¹) ^ addOrderOf j = 1 := by
      rw [mul_pow, stdAddChar_mul_pow_addOrderOf, inv_pow, hζ1, inv_one, one_mul]
    have hiff : (ZMod.stdAddChar (j * k) * ζ⁻¹ = 1) ↔ (ZMod.stdAddChar (j * k) = ζ) :=
      mul_inv_eq_one₀ hζ0
    rw [← DedekindFactorization.indicator_eq_geom hf hw]
    by_cases h : ZMod.stdAddChar (j * k) = ζ
    · rw [if_pos h, if_pos (hiff.mpr h)]; norm_num
    · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh))]; norm_num
  apply Nat.cast_injective (R := ℂ)
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_congr rfl (fun k _ => key k),
    ← Finset.sum_div, Finset.sum_comm, Nat.cast_div (addOrderOf_dvd_card j) hfc]
  congr 1
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ZMod.card]
  · intro r hr hr0
    have hrj : (r : ZMod m) * j ≠ 0 := fun h => hr0 (Nat.eq_zero_of_dvd_of_lt
      (addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by rw [nsmul_eq_mul]; exact h))
      (mem_range.mp hr))
    simp_rw [mul_pow]
    rw [← Finset.sum_mul]
    have hz : ∑ k : ZMod m, (ZMod.stdAddChar (j * k)) ^ r = 0 := by
      have hterm : ∀ k : ZMod m, (ZMod.stdAddChar (j * k)) ^ r
          = ZMod.stdAddChar (((r : ZMod m) * j) * k) := fun k => by
        rw [stdAddChar_pow]
        congr 1
        ring
      rw [Finset.sum_congr rfl fun k _ => hterm k, sum_stdAddChar_mul, if_neg hrj]
    rw [hz, zero_mul]
  · intro h
    exact absurd (mem_range.2 (addOrderOf_pos j)) h

open scoped Classical in
/-- `∏_{k ∈ ℤ/m}(1 − e(jk/m)·t) = (1 − t^f)^{m/f}`, `f = addOrderOf j`. -/
theorem prod_one_sub_stdAddChar_mul (j : ZMod m) (t : ℂ) :
    ∏ k : ZMod m, (1 - ZMod.stdAddChar (j * k) * t)
      = (1 - t ^ addOrderOf j) ^ (m / addOrderOf j) := by
  have hf : 0 < addOrderOf j := addOrderOf_pos j
  have hmaps : ∀ k ∈ (univ : Finset (ZMod m)),
      ZMod.stdAddChar (j * k) ∈ nthRootsFinset (addOrderOf j) (1 : ℂ) := fun k _ =>
    (mem_nthRootsFinset hf (1 : ℂ)).2 (stdAddChar_mul_pow_addOrderOf j k)
  rw [← Finset.prod_fiberwise_of_maps_to hmaps (fun k => 1 - ZMod.stdAddChar (j * k) * t)]
  have hinner : ∀ ζ ∈ nthRootsFinset (addOrderOf j) (1 : ℂ),
      ∏ k ∈ univ.filter (fun k : ZMod m => ZMod.stdAddChar (j * k) = ζ),
        (1 - ZMod.stdAddChar (j * k) * t) = (1 - ζ * t) ^ (m / addOrderOf j) := by
    intro ζ hζ
    rw [Finset.prod_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]),
      Finset.prod_const, fiber_card_add hζ]
  rw [Finset.prod_congr rfl hinner, Finset.prod_pow, DedekindFactorization.prod_one_sub_mul hf]

end AddOrthogonality

section EvenLocal

variable {p : ℕ} [hpri : Fact p.Prime] {g : (ZMod p)ˣ}

open scoped Classical in
/-- **The even-character local factor**: for a unit `a = g^j` mod `p`,
`∏_{χ even}(1 − χ(a)·t) = (1 − t^f)^{m/f}` with `f = addOrderOf (j : ℤ/m)` — the order of the
`±a` class — and `m = (p−1)/2`. -/
theorem prod_even_char_one_sub [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2)
    {a : (ZMod p)ˣ} {j : ℕ} (hj : g ^ j = a) (t : ℂ) :
    ∏ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even), (1 - χ (a : ZMod p) * t)
      = (1 - t ^ addOrderOf ((j : ZMod ((p - 1) / 2))))
          ^ (((p - 1) / 2) / addOrderOf ((j : ZMod ((p - 1) / 2)))) := by
  -- the value of an even character at `a` through its index
  have hval : ∀ c : {χ : DirichletCharacter ℂ p // χ.Even},
      c.1 (a : ZMod p) = ZMod.stdAddChar ((j : ZMod ((p - 1) / 2)) * evenCharIdx hgen hp c) := by
    intro c
    rw [← hj, Units.val_pow_eq_pow_val, map_pow, ← stdAddChar_evenCharIdx hgen hp c,
      stdAddChar_pow]
  -- pass to the subtype and transfer through `evenCharEquiv`
  rw [← Finset.prod_coe_sort (univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even))
    (fun χ => 1 - χ (a : ZMod p) * t)]
  let e0 : {χ : DirichletCharacter ℂ p //
        χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even)}
      ≃ {χ : DirichletCharacter ℂ p // χ.Even} :=
    Equiv.subtypeEquivRight fun χ => by simp [Finset.mem_filter]
  rw [← Equiv.prod_comp e0.symm (fun c : {χ : DirichletCharacter ℂ p //
    χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even)} => 1 - c.1 (a : ZMod p) * t)]
  have hstep : ∀ c : {χ : DirichletCharacter ℂ p // χ.Even},
      1 - (e0.symm c).1 (a : ZMod p) * t
        = 1 - ZMod.stdAddChar ((j : ZMod ((p - 1) / 2)) * evenCharIdx hgen hp c) * t := by
    intro c
    have : (e0.symm c).1 = c.1 := rfl
    rw [this, hval c]
  rw [Finset.prod_congr rfl fun c _ => hstep c]
  have hidx : ∀ c : {χ : DirichletCharacter ℂ p // χ.Even},
      evenCharIdx hgen hp c = evenCharEquiv hgen hp c := fun c => rfl
  rw [Finset.prod_congr rfl fun c _ => by rw [hidx c],
    Equiv.prod_comp (evenCharEquiv hgen hp)
      (fun k : ZMod ((p - 1) / 2) =>
        1 - ZMod.stdAddChar ((j : ZMod ((p - 1) / 2)) * k) * t)]
  exact prod_one_sub_stdAddChar_mul _ t

end EvenLocal

end CyclotomicNT
