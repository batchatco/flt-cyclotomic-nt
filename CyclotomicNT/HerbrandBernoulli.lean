import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Herbrand, step 2: the Faulhaber congruence `S_m ≡ p·B_m (mod p²)`

Elementary `ℚ`/`ℤ` arithmetic feeding Herbrand's theorem:

* `PInt p x`: `x : ℚ` is `p`-integral (`p ∤ x.den`), with closure under `+`, `*`, sums, and
  division by `p`-units;
* `not_dvd_den_bernoulli`: von Staudt–Clausen corollary — `p ∤ den B_m` when `(p−1) ∤ m`;
* `den_mul_sum_pow_modEq` (**Faulhaber mod `p²`**): for even `2 ≤ m ≤ p−3`,
  `den(B_m)·∑_{a<p} a^m ≡ p·num(B_m) (mod p²)` over `ℤ`;
* `sub_pmul_pow_modEq` (**binomial mod `p²`**): `(x − py)^e ≡ x^e − e·x^{e−1}·py (mod p²)`.
-/

open Finset

namespace CyclotomicNT

/-! ### `p`-integrality plumbing -/

/-- `x : ℚ` is `p`-integral: `p` does not divide its denominator. -/
def PInt (p : ℕ) (x : ℚ) : Prop := ¬ (p : ℕ) ∣ x.den

namespace PInt

variable {p : ℕ} [hpri : Fact p.Prime] {x y : ℚ}

theorem intCast (n : ℤ) : PInt p (n : ℚ) := by
  rw [PInt, Rat.den_intCast]
  exact fun h => hpri.out.ne_one (Nat.dvd_one.mp h)

theorem natCast (n : ℕ) : PInt p (n : ℚ) := by
  rw [show ((n : ℚ)) = ((n : ℤ) : ℚ) by push_cast; ring]
  exact intCast n

theorem one : PInt p 1 := by simpa using natCast 1

theorem add (hx : PInt p x) (hy : PInt p y) : PInt p (x + y) := fun h =>
  ((hpri.out.dvd_mul.mp (h.trans (Rat.add_den_dvd x y))).elim hx hy)

theorem mul (hx : PInt p x) (hy : PInt p y) : PInt p (x * y) := fun h =>
  ((hpri.out.dvd_mul.mp (h.trans (Rat.mul_den_dvd x y))).elim hx hy)

theorem sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, PInt p (f i)) :
    PInt p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intCast 0
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem pow (hx : PInt p x) (n : ℕ) : PInt p (x ^ n) := by
  induction n with
  | zero => simpa using one (p := p)
  | succ n ih => rw [pow_succ]; exact ih.mul hx

theorem div_nat (hx : PInt p x) {n : ℕ} (hn : ¬ (p : ℕ) ∣ n) : PInt p (x / n) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => hn (h ▸ dvd_zero p))
  rw [div_eq_mul_inv]
  refine hx.mul ?_
  rw [PInt, Rat.inv_natCast_den_of_pos hn0]
  exact hn

/-- **Extraction**: if `(N : ℚ) = p²·x` with `x` `p`-integral, then `p² ∣ N` in `ℤ`. -/
theorem sq_dvd_of_eq {N : ℤ} (h : (N : ℚ) = (p : ℚ) ^ 2 * x) (hx : PInt p x) :
    (p : ℤ) ^ 2 ∣ N := by
  have hp0 : ((p : ℚ) ^ 2) ≠ 0 := by
    have := hpri.out.pos
    positivity
  have hxN : x = (N : ℚ) / (p : ℚ) ^ 2 := by rw [h, mul_comm, mul_div_assoc, div_self hp0,
    mul_one]
  -- the denominator of `x` divides `p²`, and is coprime to `p`, hence is `1`
  have hden : x.den ∣ p ^ 2 := by
    have : x = ((N : ℚ)) / (((p ^ 2 : ℕ) : ℤ) : ℚ) := by rw [hxN]; push_cast; ring
    calc x.den ∣ (N : ℚ).den * (((((p ^ 2 : ℕ) : ℤ) : ℚ))⁻¹).den := by
          rw [this, div_eq_mul_inv]; exact Rat.mul_den_dvd _ _
      _ ∣ p ^ 2 := by
          rw [Rat.den_intCast, one_mul, show ((((p ^ 2 : ℕ) : ℤ)) : ℚ) = ((p ^ 2 : ℕ) : ℚ) by
            push_cast; ring, Rat.inv_natCast_den_of_pos (by have := hpri.out.pos; positivity)]
  have hcop : Nat.Coprime x.den p := Nat.coprime_comm.mp (hpri.out.coprime_iff_not_dvd.mpr hx)
  have hden1 : x.den = 1 := Nat.Coprime.eq_one_of_dvd (hcop.pow_right 2) hden
  obtain ⟨z, hz⟩ : ∃ z : ℤ, x = z := ⟨x.num, ((Rat.den_eq_one_iff x).mp hden1).symm⟩
  refine ⟨z, ?_⟩
  have : (N : ℚ) = ((p : ℤ) ^ 2 * z : ℤ) := by rw [h, hz]; push_cast; ring
  exact_mod_cast this

end PInt

/-! ### Von Staudt–Clausen corollary -/

variable {p : ℕ} [hpri : Fact p.Prime]

/-- The denominator of a finite sum divides the product of denominators. -/
theorem den_sum_dvd {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    (∑ i ∈ s, f i).den ∣ ∏ i ∈ s, (f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact (Rat.add_den_dvd _ _).trans (mul_dvd_mul_left _ ih)

/-- **Von Staudt–Clausen corollary**: if `(p−1) ∤ m` (and `p ≠ 2`), then `p ∤ den(B_m)`. -/
theorem not_dvd_den_bernoulli (hp2 : p ≠ 2) {m : ℕ} (hm : ¬ (p - 1) ∣ m) :
    ¬ (p : ℕ) ∣ (bernoulli m).den := by
  rcases Nat.even_or_odd m with hme | hmo
  · -- even case: von Staudt–Clausen
    obtain ⟨k, rfl⟩ := hme.exists_two_nsmul m
    rw [smul_eq_mul] at *
    obtain ⟨N, hN⟩ := Bernoulli.vonStaudt_clausen k
    have hB : bernoulli (2 * k)
        = (N : ℚ) - ∑ q ∈ Finset.range (2 * k + 2) with Nat.Prime q ∧ (q - 1) ∣ 2 * k,
            (1 : ℚ) / q := by
      linear_combination -hN
    intro hdvd
    rw [hB] at hdvd
    -- `p ∣ den (N − Σ) ∣ den Σ ∣ ∏ q`, all `q ≠ p`
    have h1 : ((N : ℚ) - ∑ q ∈ Finset.range (2 * k + 2) with Nat.Prime q ∧ (q - 1) ∣ 2 * k,
        (1 : ℚ) / q).den ∣ (∑ q ∈ Finset.range (2 * k + 2) with Nat.Prime q ∧ (q - 1) ∣ 2 * k,
        (1 : ℚ) / q).den := by
      rw [Rat.intCast_sub_den]
    have h2 := (hdvd.trans h1).trans (den_sum_dvd _ _)
    have h3 : ∀ q ∈ (Finset.range (2 * k + 2)).filter (fun q => Nat.Prime q ∧ (q - 1) ∣ 2 * k),
        ¬ (p : ℕ) ∣ ((1 : ℚ) / (q : ℚ)).den := by
      intro q hq
      obtain ⟨-, hqp, hqd⟩ := Finset.mem_filter.mp hq
      have hq0 : 0 < q := hqp.pos
      rw [one_div, Rat.inv_natCast_den_of_pos hq0]
      intro hpq
      exact hm ((Nat.prime_dvd_prime_iff_eq hpri.out hqp).mp hpq ▸ hqd)
    exact Finset.prod_induction _ (fun n => ¬ (p : ℕ) ∣ n)
      (fun a b ha hb h => (hpri.out.dvd_mul.mp h).elim ha hb)
      (fun h => hpri.out.ne_one (Nat.dvd_one.mp h)) h3 h2
  · -- odd case: `B_1 = −1/2` (`p ≠ 2`), `B_m = 0` for odd `m > 1`
    rcases eq_or_ne m 1 with rfl | hm1
    · have hden : (bernoulli 1).den = 2 := by
        have h12 : (-1 / 2 : ℚ) = -((2 : ℕ) : ℚ)⁻¹ := by norm_num
        rw [bernoulli_one, h12, Rat.neg_den, Rat.inv_natCast_den_of_pos two_pos]
      rw [hden]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpri.out Nat.prime_two).mp h)
    · have hlt : 1 < m := lt_of_le_of_ne hmo.pos (Ne.symm hm1)
      rw [bernoulli_eq_zero_of_odd hmo hlt]
      simpa using fun h => hpri.out.ne_one (Nat.dvd_one.mp h)

/-! ### The binomial congruence mod `p²` -/

/-! ### Faulhaber mod `p²` -/

/-- **Faulhaber mod `p²`**: for `1 ≤ m ≤ p−2`,
`den(B_m)·∑_{a<p} a^m ≡ p·num(B_m) (mod p²)` over `ℤ`. -/
theorem den_mul_sum_pow_modEq (hp2 : p ≠ 2) {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ p - 2) :
    ((bernoulli m).den : ℤ) * ∑ a ∈ Finset.range p, (a : ℤ) ^ m
      ≡ (p : ℤ) * (bernoulli m).num [ZMOD ((p : ℤ)) ^ 2] := by
  have hp3 : 3 ≤ p := by
    have := hpri.out.two_le
    omega
  -- Faulhaber over ℚ, with the top (`i = m`) term split off
  have hF := sum_range_pow p m
  rw [Finset.sum_range_succ] at hF
  have htop : bernoulli m * (((m + 1).choose m : ℕ) : ℚ) * (p : ℚ) ^ (m + 1 - m) / (m + 1)
      = bernoulli m * p := by
    have hm1q : ((m : ℚ) + 1) ≠ 0 := by positivity
    rw [Nat.choose_succ_self_right, show m + 1 - m = 1 by omega, pow_one]
    push_cast
    field_simp
  set R : ℚ := ∑ i ∈ Finset.range m,
    bernoulli i * (((m + 1).choose i : ℕ) : ℚ) * (p : ℚ) ^ (m - 1 - i) / (m + 1) with hR
  have hsplit : (∑ a ∈ Finset.range p, (a : ℚ) ^ m) = (p : ℚ) ^ 2 * R + bernoulli m * p := by
    rw [hF, htop, hR, Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => ?_) rfl
    have hilt : i < m := Finset.mem_range.mp hi
    have hexp : m + 1 - i = (m - 1 - i) + 2 := by omega
    rw [hexp, pow_add]
    ring
  -- `R` is `p`-integral
  have hPR : PInt p R := by
    refine PInt.sum _ _ fun i hi => ?_
    have hilt : i < m := Finset.mem_range.mp hi
    have hBi : PInt p (bernoulli i) := by
      rcases eq_or_ne i 0 with rfl | hi0
      · simpa [bernoulli_zero] using PInt.one (p := p)
      · exact not_dvd_den_bernoulli hp2
          (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hi0) (by omega))
    have hppow : PInt p ((p : ℚ) ^ (m - 1 - i)) := (PInt.natCast p).pow _
    have hcast : bernoulli i * (((m + 1).choose i : ℕ) : ℚ) * (p : ℚ) ^ (m - 1 - i) / ((m : ℚ) + 1)
        = bernoulli i * (((m + 1).choose i : ℕ) : ℚ) * (p : ℚ) ^ (m - 1 - i)
          / (((m + 1 : ℕ)) : ℚ) := by
      push_cast
      ring
    rw [hcast]
    exact ((hBi.mul (PInt.natCast _)).mul hppow).div_nat
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  -- extract the divisibility
  have hkey : (p : ℤ) ^ 2 ∣ ((bernoulli m).den : ℤ) * (∑ a ∈ Finset.range p, (a : ℤ) ^ m)
      - (p : ℤ) * (bernoulli m).num := by
    refine PInt.sq_dvd_of_eq (x := ((bernoulli m).den : ℚ) * R) ?_ ((PInt.natCast _).mul hPR)
    have hnum : ((bernoulli m).num : ℚ) = ((bernoulli m).den : ℚ) * bernoulli m :=
      (Rat.den_mul_eq_num _).symm
    push_cast
    rw [hsplit, hnum]
    ring
  rw [Int.modEq_iff_dvd]
  obtain ⟨z, hz⟩ := hkey
  exact ⟨-z, by linarith⟩

/-! ### The permutation lemma and the main congruence -/

omit hpri in
/-- Sums over `ZMod p` of functions of `val` are sums over `range p`. -/
theorem sum_val_eq_sum_range [NeZero p] {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ x : ZMod p, g x.val = ∑ a ∈ Finset.range p, g a :=
  Finset.sum_bij (fun (x : ZMod p) _ => x.val) (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x))
    (fun _ _ _ _ h => ZMod.val_injective p h) (fun a ha => ⟨(a : ZMod p), Finset.mem_univ _,
      ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)⟩) (fun _ _ => rfl)

/-- **Multiplication by a unit permutes residues**: summing any function of `(c·a) % p`
over `a < p` equals summing it over `a < p`. -/
theorem sum_fn_mod_mul_eq {M : Type*} [AddCommMonoid M] {c : ℕ} (hc : ¬ p ∣ c) (f : ℕ → M) :
    ∑ a ∈ Finset.range p, f ((c * a) % p) = ∑ a ∈ Finset.range p, f a := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  have hcu : (c : ZMod p) ≠ 0 := fun h => hc ((ZMod.natCast_eq_zero_iff c p).mp h)
  calc ∑ a ∈ Finset.range p, f ((c * a) % p)
      = ∑ x : ZMod p, f ((c * x.val) % p) := (sum_val_eq_sum_range _).symm
    _ = ∑ x : ZMod p, f (((c : ZMod p) * x).val) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
    _ = ∑ x : ZMod p, f x.val :=
        Fintype.sum_equiv (Equiv.mulLeft₀ (c : ZMod p) hcu) _ _ (fun x => rfl)
    _ = ∑ a ∈ Finset.range p, f a := sum_val_eq_sum_range f

omit hpri in
/-- In a ring where `π² = 0`, the binomial expansion of `(x − πy)^{e+1}` truncates exactly. -/
theorem sub_pow_of_sq_eq_zero {R : Type*} [CommRing R] {π : R} (hπ : π ^ 2 = 0)
    (x y : R) (e : ℕ) :
    (x - π * y) ^ (e + 1) = x ^ (e + 1) - (e + 1) * x ^ e * (π * y) := by
  induction e with
  | zero => ring
  | succ e ih =>
      have hsplit : (x - π * y) ^ (e + 1 + 1) = (x - π * y) ^ (e + 1) * (x - π * y) := by ring
      rw [hsplit, ih]
      push_cast
      linear_combination (((e : R) + 1) * x ^ e * y ^ 2) * hπ

/-- **The main analytic congruence** (Washington Lem. 6.9-style bookkeeping): for `p ∤ c` and
`m + 1 ≤ p − 2`,
`den(B_{m+1})·(m+1)·∑_a (ca)^m·⌊ca/p⌋ ≡ (c^{m+1} − 1)·num(B_{m+1}) (mod p)`. -/
theorem den_mul_sum_floor_modEq (hp2 : p ≠ 2) {m : ℕ} (hm : m + 1 ≤ p - 2) {c : ℕ}
    (hc : ¬ p ∣ c) :
    ((bernoulli (m + 1)).den : ℤ) * (m + 1)
        * ((∑ a ∈ Finset.range p, (c * a) ^ m * (c * a / p) : ℕ) : ℤ)
      ≡ ((c : ℤ) ^ (m + 1) - 1) * (bernoulli (m + 1)).num [ZMOD (p : ℤ)] := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  have hS1cast : ∑ a ∈ Finset.range p, (a : ℤ) ^ (m + 1)
      = ((∑ a ∈ Finset.range p, a ^ (m + 1) : ℕ) : ℤ) := by push_cast; rfl
  -- `π := p` squares to zero in `ZMod (p²)`
  have hπ : ((p : ZMod (p ^ 2))) ^ 2 = 0 := by
    rw [show ((p : ZMod (p ^ 2))) ^ 2 = ((p ^ 2 : ℕ) : ZMod (p ^ 2)) by push_cast; ring,
      ZMod.natCast_self]
  -- F1: Faulhaber mod `p²`, in `ZMod (p²)`
  have hF1 : ((bernoulli (m + 1)).den : ZMod (p ^ 2))
        * ((∑ a ∈ Finset.range p, a ^ (m + 1) : ℕ) : ZMod (p ^ 2))
      = (p : ZMod (p ^ 2)) * ((bernoulli (m + 1)).num : ZMod (p ^ 2)) := by
    have h := den_mul_sum_pow_modEq (p := p) hp2 (by omega : 1 ≤ m + 1) hm
    rw [hS1cast, show ((p : ℤ)) ^ 2 = ((p ^ 2 : ℕ) : ℤ) by push_cast; ring] at h
    have h2 := (ZMod.intCast_eq_intCast_iff _ _ _).mpr h
    push_cast at h2 ⊢
    exact h2
  -- F2: permutation + truncated binomial, in `ZMod (p²)`
  have hF2 : ((∑ a ∈ Finset.range p, a ^ (m + 1) : ℕ) : ZMod (p ^ 2))
      = (c : ZMod (p ^ 2)) ^ (m + 1)
          * ((∑ a ∈ Finset.range p, a ^ (m + 1) : ℕ) : ZMod (p ^ 2))
        - ((m : ZMod (p ^ 2)) + 1) * ((p : ZMod (p ^ 2))
          * ((∑ a ∈ Finset.range p, (c * a) ^ m * (c * a / p) : ℕ) : ZMod (p ^ 2))) := by
    have hperm := sum_fn_mod_mul_eq (p := p) hc (fun r => ((r : ZMod (p ^ 2))) ^ (m + 1))
    have hexp : ∀ a ∈ Finset.range p, (((c * a % p : ℕ)) : ZMod (p ^ 2)) ^ (m + 1)
        = ((c * a : ℕ) : ZMod (p ^ 2)) ^ (m + 1)
          - ((m : ZMod (p ^ 2)) + 1) * ((c * a : ℕ) : ZMod (p ^ 2)) ^ m
            * ((p : ZMod (p ^ 2)) * ((c * a / p : ℕ) : ZMod (p ^ 2))) := by
      intro a _
      have hd : p * (c * a / p) + c * a % p = c * a := Nat.div_add_mod (c * a) p
      have hmod : (((c * a % p : ℕ)) : ZMod (p ^ 2))
          = ((c * a : ℕ) : ZMod (p ^ 2))
            - (p : ZMod (p ^ 2)) * ((c * a / p : ℕ) : ZMod (p ^ 2)) := by
        have hcast : ((p * (c * a / p) + c * a % p : ℕ) : ZMod (p ^ 2))
            = ((c * a : ℕ) : ZMod (p ^ 2)) := by rw [hd]
        push_cast at hcast ⊢
        linear_combination hcast
      rw [hmod, sub_pow_of_sq_eq_zero hπ]
    calc ((∑ a ∈ Finset.range p, a ^ (m + 1) : ℕ) : ZMod (p ^ 2))
        = ∑ a ∈ Finset.range p, ((a : ZMod (p ^ 2))) ^ (m + 1) := by push_cast; rfl
      _ = ∑ a ∈ Finset.range p, (((c * a % p : ℕ)) : ZMod (p ^ 2)) ^ (m + 1) := by
          rw [hperm]
      _ = ∑ a ∈ Finset.range p, (((c * a : ℕ) : ZMod (p ^ 2)) ^ (m + 1)
            - ((m : ZMod (p ^ 2)) + 1) * ((c * a : ℕ) : ZMod (p ^ 2)) ^ m
              * ((p : ZMod (p ^ 2)) * ((c * a / p : ℕ) : ZMod (p ^ 2)))) :=
          Finset.sum_congr rfl hexp
      _ = _ := by
          rw [Finset.sum_sub_distrib]
          congr 1
          · push_cast
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun a _ => by ring
          · push_cast
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun a _ => by ring
  -- combine and cancel one `p`
  have hkey : ((p : ZMod (p ^ 2)))
      * (((((c : ℤ) ^ (m + 1) - 1) * (bernoulli (m + 1)).num
          - ((bernoulli (m + 1)).den : ℤ) * (m + 1)
            * ((∑ a ∈ Finset.range p, (c * a) ^ m * (c * a / p) : ℕ) : ℤ) : ℤ)) : ZMod (p ^ 2))
      = 0 := by
    push_cast [-Nat.cast_sum]
    linear_combination (1 - (c : ZMod (p ^ 2)) ^ (m + 1)) * hF1
      - ((bernoulli (m + 1)).den : ZMod (p ^ 2)) * hF2
  -- `p² ∣ p·D ⟹ p ∣ D`
  have hdvd : ((p ^ 2 : ℕ) : ℤ) ∣ (p : ℤ) * ((((c : ℤ) ^ (m + 1) - 1) * (bernoulli (m + 1)).num
      - ((bernoulli (m + 1)).den : ℤ) * (m + 1)
        * ((∑ a ∈ Finset.range p, (c * a) ^ m * (c * a / p) : ℕ) : ℤ))) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [-Nat.cast_sum]
    push_cast [-Nat.cast_sum] at hkey
    exact hkey
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpri.out.ne_zero
  rw [Int.modEq_iff_dvd]
  refine (mul_dvd_mul_iff_left hp0).mp ?_
  rwa [show ((p ^ 2 : ℕ) : ℤ) = (p : ℤ) * (p : ℤ) by push_cast; ring] at hdvd

end CyclotomicNT
