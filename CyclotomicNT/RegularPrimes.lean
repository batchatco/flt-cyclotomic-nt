import FltRegular.NumberTheory.RegularPrimes
import FltRegular.NumberTheory.KummersLemma.KummersLemma
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import CyclotomicNT.GroupAux
import CyclotomicNT.ClassGroupMap

/-!
# Weaker hypotheses than regularity

This file introduces the two hypotheses under which the Varma–Washington extension of
Kummer's proof handles FLT at irregular primes (e.g. `p = 37`), both *strictly weaker*
than `IsRegularPrime p`:

* `MaximalRealCyclotomic p` — the maximal real subfield `Q(ζ_p)⁺` of the `p`-th
  cyclotomic field, as a number field.
* `IsVandiverPrime p` — `p` does not divide the class number of `Q(ζ_p)⁺`.
  (`IsRegularPrime p` asks for `p` coprime to the class number of the *full* field
  `Q(ζ_p)`; since `h⁺_p ∣ h_p`, regularity implies this.)
* `KummerUnitProperty p` — the cyclotomic-unit assumption: every unit of `O_{K⁺}`
  congruent to a rational integer mod `p` is a `p`-th power. At regular primes this is
  Kummer's lemma restricted to the real subfield.

References:
* I. Varma, *Kummer, Regular Primes, and Fermat's Last Theorem*, §7.
* L. Washington, *Introduction to Cyclotomic Fields*, Ch. 9. -/

open NumberField

open scoped NumberField

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (p : ℕ)

/-- The maximal real subfield `Q(ζ_p)⁺` of the `p`-th cyclotomic field, as a number field.

Concretely this is `Q(ζ_p + ζ_p⁻¹)`; Mathlib realises it as `maximalRealSubfield`, the
subfield of elements fixed by every complex embedding's conjugation (equivalently, by the
complex-conjugation automorphism `ζ ↦ ζ⁻¹`). As a subfield of a number field it is itself
a number field, via `NumberField.of_subfield`. -/
abbrev MaximalRealCyclotomic : Type :=
  maximalRealSubfield (CyclotomicField p ℚ)

/-- A prime `p` is a **Vandiver prime** if `p` does not divide the class number of the
maximal real subfield `Q(ζ_p)⁺`, i.e. `p` is coprime to `|Cl(O_{K⁺})|`.

This mirrors `IsRegularPrime` (which uses the full cyclotomic field `Q(ζ_p)`) but on the
real subfield only. Vandiver's conjecture asserts this holds for every odd prime; it has
been verified computationally for all `p < 2 · 10⁹`. For this project we discharge it
numerically at each specific prime (e.g. `p = 37`, where `h⁺_37 = 1`). -/
def IsVandiverPrime [Fact p.Prime] : Prop :=
  p.Coprime <| Fintype.card <| ClassGroup (𝓞 (MaximalRealCyclotomic p))

/-- The **Kummer unit property** for `p`: every unit `u` of `O_{K⁺}` that is congruent to a
rational integer modulo `p` is a `p`-th power of a unit of `O_{K⁺}`.

⚠ **This hypothesis is MIS-SPECIFIED for the project's goal (irregular primes).** It is exactly
Kummer's Lemma (Washington, *Introduction to Cyclotomic Fields*, **Lemma 5.36**), stated there
only for **regular** primes. It is a classical fact that Kummer's Lemma **FAILS at irregular
primes** (the `p`-adic regulator of the cyclotomic units is `≡ ∏ B_{2i} ≡ 0 (mod p)` when `p`
is irregular, producing a unit `≡ 1 (mod p)` that is not a `p`-th power). So
`KummerUnitProperty p` is almost certainly **false** at `p = 37` (and other irregular targets)
and cannot be discharged numerically.

Washington's actual second-case theorem (**Thm 9.4**, verified against the 1982 text) instead
assumes Vandiver (`p ∤ h⁺`) plus a **Bernoulli congruence** `p³ ∤ B_{pi}` (even `i`,
`2 ≤ i ≤ p−3`; index `p·i`); the unit step is **Corollary 8.23** (the refined Kummer's lemma),
not this `mod p` version.
`IsRegularPrime.kummerUnitProperty` below is still a correct theorem (regular primes *do*
satisfy this — it is Washington's Thm 9.3 route via Lemma 5.36), but the property is only
useful in the regular case. -/
def KummerUnitProperty [Fact p.Prime] : Prop :=
  ∀ u : (𝓞 (MaximalRealCyclotomic p))ˣ,
    (∃ n : ℤ, (p : 𝓞 (MaximalRealCyclotomic p)) ∣ ((u : 𝓞 (MaximalRealCyclotomic p)) - n)) →
    ∃ v : (𝓞 (MaximalRealCyclotomic p))ˣ, u = v ^ p

variable {p}

/-- A Vandiver prime has no nontrivial `p`-torsion in the class group of `K⁺`: if `a ^ p = 1`
then `a = 1`. (Since `p ∤ h⁺`, the order of `a` divides `gcd(p, h⁺) = 1`.)

This is the form consumed by `CyclotomicNT.eq_one_of_pow_eq_one_of_image_sq` — the
plus-part triviality at the heart of the Case II principality step. -/
theorem IsVandiverPrime.pow_eq_one_eq_one [Fact p.Prime] (hvand : IsVandiverPrime p)
    {a : ClassGroup (𝓞 (MaximalRealCyclotomic p))} (ha : a ^ p = 1) : a = 1 := by
  have hg : Nat.gcd p (Fintype.card (ClassGroup (𝓞 (MaximalRealCyclotomic p)))) = 1 := hvand
  have hdvd : orderOf a ∣ 1 :=
    hg ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha) orderOf_dvd_card
  rwa [Nat.dvd_one, orderOf_eq_one_iff] at hdvd

/-- `[Frac (𝓞 K) : Frac (𝓞 K⁺)] = 2` for odd `p`: reduce the fraction-field degree to the
ring-of-integers degree to `[K : K⁺] = 2` (`IsCMField`, valid as `2 < p`). -/
theorem finrank_fractionRing_eq_two [hp : Fact p.Prime] (hodd : p ≠ 2) :
    Module.finrank (FractionRing (𝓞 (MaximalRealCyclotomic p)))
      (FractionRing (𝓞 (CyclotomicField p ℚ))) = 2 := by
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  haveI : IsCMField (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.Rat.isCMField (CyclotomicField p ℚ) (S := {p})
      ⟨p, Set.mem_singleton p, lt_of_le_of_ne hp.out.two_le (Ne.symm hodd)⟩
  exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (MaximalRealCyclotomic p))
      (FractionRing (𝓞 (MaximalRealCyclotomic p))) (𝓞 (CyclotomicField p ℚ))
      (FractionRing (𝓞 (CyclotomicField p ℚ)))).trans <|
    ((Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (MaximalRealCyclotomic p))
      (MaximalRealCyclotomic p) (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)).symm).trans
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _)

/-- **Number-theoretic core of "regular ⇒ Vandiver".**

For an odd prime `p`, the extension-of-ideals map `Cl(O_{K⁺}) → Cl(O_K)` and the relative-norm
map `Cl(O_K) → Cl(O_{K⁺})` compose to squaring, since
`N_{K/K⁺}(I · O_K) = I^{[K:K⁺]} = I²` (as `[K : K⁺] = 2` for the CM extension `K/K⁺`).

Built from `CyclotomicNT.classGroupExtend` / `classGroupNorm` and
`classGroupNorm_classGroupExtend` (`= a ^ finrank (Frac O_{K⁺}) (Frac O_K)`), with the
`finrank` computed to be `2` by `finrank_fractionRing_eq_two`. -/
theorem exists_classGroup_norm_extend_sq [hp : Fact p.Prime] (hodd : p ≠ 2) :
    ∃ (f : ClassGroup (𝓞 (MaximalRealCyclotomic p)) →* ClassGroup (𝓞 (CyclotomicField p ℚ)))
      (g : ClassGroup (𝓞 (CyclotomicField p ℚ)) →* ClassGroup (𝓞 (MaximalRealCyclotomic p))),
      ∀ a, g (f a) = a ^ 2 := by
  have hinj : Function.Injective
      (algebraMap (𝓞 (MaximalRealCyclotomic p)) (𝓞 (CyclotomicField p ℚ))) :=
    RingOfIntegers.algebraMap.injective (MaximalRealCyclotomic p) (CyclotomicField p ℚ)
  exact ⟨CyclotomicNT.classGroupExtend hinj, CyclotomicNT.classGroupNorm, fun a => by
    rw [CyclotomicNT.classGroupNorm_classGroupExtend hinj a, finrank_fractionRing_eq_two hodd]⟩

/-- The class number of the real subfield `Q(ζ_2)⁺ = Q` is `1`, so `2` is trivially Vandiver.
`CyclotomicField 2 ℚ` has degree `φ(2) = 1` over `ℚ`, hence is totally real (so its maximal
real subfield is everything), and its ring of integers (`≅ ℤ`) is a PID. -/
theorem isVandiverPrime_two : IsVandiverPrime 2 := by
  haveI : IsCyclotomicExtension {2} ℚ (CyclotomicField 2 ℚ) :=
    CyclotomicField.isCyclotomicExtension 2 ℚ
  have hfr : Module.finrank ℚ (CyclotomicField 2 ℚ) = 1 := by
    rw [IsCyclotomicExtension.Rat.finrank 2 (CyclotomicField 2 ℚ)]; decide
  have hbij := Module.Free.bijective_algebraMap_of_finrank_eq_one (R := ℚ)
    (S := CyclotomicField 2 ℚ) hfr
  haveI : IsTotallyReal (CyclotomicField 2 ℚ) :=
    IsTotallyReal.ofRingEquiv (RingEquiv.ofBijective (algebraMap ℚ (CyclotomicField 2 ℚ)) hbij)
  have htop : maximalRealSubfield (CyclotomicField 2 ℚ) = ⊤ :=
    IsTotallyReal.maximalRealSubfield_eq_top
  let e : MaximalRealCyclotomic 2 ≃+* CyclotomicField 2 ℚ :=
    (RingEquiv.subfieldCongr htop).trans Subfield.topEquiv
  let e𝓞 : 𝓞 (MaximalRealCyclotomic 2) ≃+* 𝓞 (CyclotomicField 2 ℚ) :=
    RingOfIntegers.mapRingEquiv e
  haveI : IsPrincipalIdealRing (𝓞 (MaximalRealCyclotomic 2)) :=
    IsPrincipalIdealRing.of_surjective e𝓞.symm.toRingHom e𝓞.symm.surjective
  have hcard : Fintype.card (ClassGroup (𝓞 (MaximalRealCyclotomic 2))) = 1 :=
    card_classGroup_eq_one_iff.mpr inferInstance
  rw [IsVandiverPrime, hcard]
  exact Nat.coprime_one_right 2

/-- A regular prime is a Vandiver prime: `p ∤ h ⇒ p ∤ h⁺`.

For odd `p` this follows from `CyclotomicNT.coprime_card_of_sq` applied to the
extension/norm pair of `exists_classGroup_norm_extend_sq`, whose composite is squaring:
the kernel of the extension map is killed by `2`, so the odd part of `h⁺` divides `h`. The
prime `p = 2` is the degenerate `isVandiverPrime_two`. -/
theorem IsRegularPrime.isVandiverPrime [hp : Fact p.Prime]
    (hreg : IsRegularPrime p) : IsVandiverPrime p := by
  rcases eq_or_ne p 2 with rfl | hodd
  · exact isVandiverPrime_two
  · obtain ⟨f, g, hfg⟩ := exists_classGroup_norm_extend_sq hodd
    have hB : p.Coprime (Nat.card (ClassGroup (𝓞 (CyclotomicField p ℚ)))) := by
      rw [Nat.card_eq_fintype_card]; exact hreg
    have hA := CyclotomicNT.coprime_card_of_sq hfg hp.out hodd hB
    rw [IsVandiverPrime, ← Nat.card_eq_fintype_card]
    exact hA

