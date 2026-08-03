import CyclotomicNT.DedekindCounting
import CyclotomicNT.LocalFactor
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# The local ideal count for unramified primes in a cyclotomic field

Specializing `CyclotomicNT.idealCount_prime_pow` to `K = ℚ(ζ_m)`.  For a rational prime `p` **not**
dividing the conductor `m` (the unramified case), Mathlib's
`IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd` says *every* prime above `p` has residue degree
`f = ord(p mod m)` — exactly the constant-degree hypothesis `hdeg` of `idealCount_prime_pow`.  Hence

  `idealCount K (pᵉ) = if f ∣ e then C(e/f + g−1, g−1) else 0`,   `f = ord(p mod m)`, `g = #{𝔭 ∣
      p}`,

the number-theoretic input (`hcount`) consumed by `LocalFactor.tsum_dedekindSummand_prime_pow` to
produce the `ζ_K` Euler factor `(1 − p^{-sf})^{-g}`. -/

open NumberField Ideal IsCyclotomicExtension.Rat

namespace CyclotomicNT

/-- **Number of primes above an unramified `p` in `ℚ(ζ_m)`:** `g = φ(m) / ord(p mod m)`.  From the
Galois fundamental identity `g · (e · f) = [K:ℚ] = φ(m)` with `e = ramificationIdxIn = 1`
    (unramified)
and `f = inertiaDegIn = ord(p mod m)`. -/
theorem ncard_primesOver_eq_of_not_dvd {m : ℕ} [NeZero m] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] {p : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)).ncard = m.totient / orderOf (p : ZMod m) := by
  haveI := Fact.mk hp
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have hpb : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  have hord : 0 < orderOf (p : ZMod m) := by
    have hu : IsUnit (p : ZMod m) := (ZMod.isUnit_iff_coprime p m).2 (hp.coprime_iff_not_dvd.2 hm)
    obtain ⟨u, hu'⟩ := hu
    rw [← hu', orderOf_units]; exact orderOf_pos u
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hpb (𝓞 K) Gal(K/ℚ)
  rw [ramificationIdxIn_eq_of_not_dvd p K hm, inertiaDegIn_eq_of_not_dvd p K hm, one_mul,
    IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K, finrank m K] at h_main
  exact (Nat.div_eq_of_eq_mul_left hord h_main.symm).symm

variable {m : ℕ} [NeZero m] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K]

/-- **Local ideal count at an unramified prime `p ∤ m` in `ℚ(ζ_m)`.**  `idealCount K (pᵉ)` is the
multichoose `C(e/f + g−1, g−1)` (when `f ∣ e`, else `0`), with `f = ord(p mod m)` the common residue
degree and `g` the number of primes above `p`.  Via `idealCount_prime_pow` and
`IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`. -/
theorem idealCount_cyclotomic_of_not_dvd {p : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) (e : ℕ) :
    idealCount K (p ^ e) =
      if orderOf (p : ZMod m) ∣ e then
        (e / orderOf (p : ZMod m) +
          (Nat.card (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) - 1)).choose
          (Nat.card (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) - 1)
      else 0 := by
  haveI := Fact.mk hp
  haveI hMmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  refine idealCount_prime_pow hp ?_ ?_ ?_ rfl
  · -- `0 < ord(p mod m)`: `p` is a unit mod `m` (coprime), so it has finite multiplicative order
    have hu : IsUnit (p : ZMod m) := (ZMod.isUnit_iff_coprime p m).2 (hp.coprime_iff_not_dvd.2 hm)
    obtain ⟨u, hu'⟩ := hu
    rw [← hu', orderOf_units]
    exact orderOf_pos u
  · -- `0 < #{𝔭 ∣ p}`: there is a prime above `p`
    haveI : Nonempty ↥(primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) :=
      (Ideal.span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
    exact Nat.card_pos
  · -- constant residue degree: every prime above `p` has `inertiaDeg = ord(p mod m)`
    rintro Q ⟨hQP, hQlo⟩
    haveI := hQP; haveI := hQlo
    exact IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p K Q hm

/-- **The `ζ_{ℚ(ζ_m)}` local Euler factor at an unramified prime `p ∤ m`.**  Feeding the cyclotomic
ideal count into `tsum_dedekindSummand_prime_pow`:
`∑'_e dedekindSummand(pᵉ) = 1 / (1 − (p^{-s})^f)^g`, with `f = ord(p mod m)` and `g = #{𝔭 ∣ p}`.
This is the `ζ_K`-side local factor to be matched against the `q`-Euler factor `(1 − q^{-sf})^{-g}`
    of
`∏_χ L(s,χ)` (the L-side `DedekindFactorization.prod_char_factor_prime`). -/
theorem tsum_dedekindSummand_cyclotomic_unramified (s : ℂ) {p : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m)
    (hY : ‖(p : ℂ) ^ (-s)‖ < 1) :
    ∑' e : ℕ, dedekindSummand K s (p ^ e)
      = 1 / (1 - ((p : ℂ) ^ (-s)) ^ orderOf (p : ZMod m))
          ^ Nat.card (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) := by
  haveI := Fact.mk hp
  refine tsum_dedekindSummand_prime_pow K s p hY (orderOf (p : ZMod m))
    (Nat.card (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K))) ?_ ?_
    (fun e => idealCount_cyclotomic_of_not_dvd hp hm e)
  · -- `0 < ord(p mod m)`
    have hu : IsUnit (p : ZMod m) := (ZMod.isUnit_iff_coprime p m).2 (hp.coprime_iff_not_dvd.2 hm)
    obtain ⟨u, hu'⟩ := hu
    rw [← hu', orderOf_units]
    exact orderOf_pos u
  · -- `1 ≤ #{𝔭 ∣ p}`
    haveI hMmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    haveI : Nonempty ↥(primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) :=
      (Ideal.span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
    exact Nat.card_pos

/-- **`ζ_{ℚ(ζ_m)}` local Euler factor at unramified `p`, splitting data made explicit:**
`∑'_e dedekindSummand(pᵉ) = 1 / (1 − (p^{-s})^f)^{φ(m)/f}`, `f = ord(p mod m)`.  This is the exact
form (with `m = p₀` the FLT prime, `φ(p₀) = p₀−1`) of the inverted L-side local factor
`DedekindFactorization.prod_char_factor_prime` — the two Euler factors of `ζ_K` and `∏_χ L`
    coincide. -/
theorem tsum_dedekindSummand_cyclotomic_unramified' (s : ℂ) {p : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m)
    (hY : ‖(p : ℂ) ^ (-s)‖ < 1) :
    ∑' e : ℕ, dedekindSummand K s (p ^ e)
      = 1 / (1 - ((p : ℂ) ^ (-s)) ^ orderOf (p : ZMod m))
          ^ (m.totient / orderOf (p : ZMod m)) := by
  have hg : Nat.card (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K))
      = m.totient / orderOf (p : ZMod m) := by
    rw [Nat.card_coe_set_eq]; exact ncard_primesOver_eq_of_not_dvd hp hm
  rw [tsum_dedekindSummand_cyclotomic_unramified s hp hm hY, hg]

end CyclotomicNT
