import FltRegular.NumberTheory.Unramified
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Galois descent of ideals coprime to the ramified primes

This file generalizes flt-regular's `comap_map_eq_of_isUnramified` (which requires the extension
`S/R` to be unramified at *every* prime) to a **localized** version: a `Gal(L/K)`-fixed ideal `I`
is extended from `R` (`(I ∩ R)·S = I`) provided `S/R` is unramified only at the primes dividing
`I ∩ R`. This is what is needed for ideals coprime to the (finitely many) ramified primes — e.g.
in `ℚ(ζ_p)/ℚ(ζ_p)⁺`, an ideal coprime to `(p)` avoids the sole ramified prime `(1-ζ)`.

The proofs are flt-regular's, with the single use of the global `[IsUnramified R S]` instance
(via `prod_primesOverFinset_of_isUnramified`) replaced by a per-prime hypothesis.
-/

open UniqueFactorizationMonoid Ideal Polynomial

attribute [local instance] FractionRing.liftAlgebra

variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]

/-- Compatibility shim: flt-regular's former `IsUnramifiedAt S p` predicate (unramified at the
single base prime `p`), which upstream removed in favor of mathlib's `Algebra.IsUnramifiedAt`.
The localized descent below is stated against this per-base-prime form. -/
def IsUnramifiedAt {R} (S : Type*) [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) : Prop :=
  ∀ P ∈ Ideal.primesOver p S, Ideal.ramificationIdx p P = 1

/-- Compatibility shim: flt-regular's former `IsUnramified R S` class (unramified at every nonzero
base prime). -/
class IsUnramified (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  isUnramifiedAt : ∀ (p : Ideal R) [p.IsPrime] (_ : p ≠ ⊥), IsUnramifiedAt S p

/-- Bridge from Mathlib's per-top-prime `Algebra.IsUnramifiedAt` to the per-base-prime shim
`IsUnramifiedAt`: unramifiedness at every prime of `S` over `p` gives unramifiedness at `p`
(each `ramificationIdx p P` equals `P.ramificationIdx' R`, which is `1`). -/
lemma isUnramifiedAt_of_forall_isUnramifiedAt {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDedekindDomain S] [Module.IsTorsionFree R S] [Algebra.EssFiniteType R S]
    {p : Ideal R} (hp : p ≠ ⊥)
    (h : ∀ (P : Ideal S) [P.IsPrime], P.LiesOver p → Algebra.IsUnramifiedAt R P) :
    IsUnramifiedAt S p := by
  rintro P ⟨hPprime, hPover⟩
  letI : P.IsPrime := hPprime
  letI : P.LiesOver p := hPover
  haveI := h P hPover
  rw [Ideal.ramificationIdx_eq_ramificationIdx' p P hp]
  exact Ideal.ramificationIdx'_eq_one P R

/-- Mathlib's global `Algebra.Unramified R S` implies the shim class `IsUnramified R S`. -/
lemma IsUnramified.of_unramified {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDedekindDomain S] [Module.IsTorsionFree R S] [Algebra.EssFiniteType R S]
    [Algebra.FiniteType R S] [Algebra.Unramified R S] : IsUnramified R S := by
  refine ⟨fun p _ hp => isUnramifiedAt_of_forall_isUnramifiedAt hp ?_⟩
  intro P hPp _
  haveI := hPp
  exact Algebra.unramified_iff_forall.mp ‹Algebra.Unramified R S› ⟨P, hPp⟩

/-- The shim class `IsUnramified R S` implies Mathlib's `Algebra.Unramified R S`, for a Dedekind
domain finite over a char-0 number-ring-like base (every `e(q|R)=1`, plus the generic fibre). -/
lemma IsUnramified.toUnramified {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDedekindDomain S] [Module.IsTorsionFree R S]
    [Algebra.EssFiniteType R S] [Algebra.FiniteType R S]
    [Module.Finite ℤ R] [CharZero R] [Algebra.IsIntegral R S]
    [IsUnramified R S] : Algebra.Unramified R S := by
  rw [Algebra.unramified_iff_forall]
  rintro ⟨q, hq⟩
  haveI := hq
  by_cases hbot : q = ⊥
  · subst hbot; exact isUnramifiedAt_bot
  · rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hbot]
    haveI : (q.under R).IsPrime := Ideal.IsPrime.under R q
    exact IsUnramified.isUnramifiedAt (q.under R) (Ideal.under_ne_bot R hbot) q ⟨hq, inferInstance⟩

variable {R} {S}

/-- Localized form of `prod_primesOverFinset_of_isUnramified`: the product of the primes over `p`
equals `p·S`, given only that `S/R` is unramified *at `p`* (not everywhere). -/
lemma prod_primesOverFinset_of_unramifiedAt [IsDedekindDomain S]
    [Module.IsTorsionFree R S] (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥)
    (hunram : IsUnramifiedAt S p) :
    ∏ P ∈ IsDedekindDomain.primesOverFinset p S, P = p.map (algebraMap R S) := by
  classical
  have hpbot' : p.map (algebraMap R S) ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective
      (Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance)).not.mpr hp
  rw [← associated_iff_eq.mp (factors_pow_count_prod hpbot')]
  apply Finset.prod_congr rfl
  intros P hP
  convert (pow_one _).symm
  have : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp ‹_›
  rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hp] at hP
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count hpbot' hP.1
    (ne_bot_of_mem_primesOver hp hP)]
  exact hunram _ hP

/-- Localized form of `comap_map_eq_of_isUnramified`: a `Gal(L/K)`-fixed ideal `I` of `S` is
extended from `R`, provided `S/R` is unramified at every prime of `R` dividing `I ∩ R`. -/
lemma comap_map_eq_of_unramifiedAtFactors [IsGalois K L] (I : Ideal S)
    (hI : ∀ σ : L ≃ₐ[K] L, I.comap (galRestrict R K L S σ) = I)
    (hunram : ∀ q : Ideal R, q.IsPrime → I.comap (algebraMap R S) ≤ q → IsUnramifiedAt S q) :
    (I.comap (algebraMap R S)).map (algebraMap R S) = I := by
  classical
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have := IsIntegralClosure.isDedekindDomain R K L S
  have hRS : Function.Injective (algebraMap R S) := by
    refine Function.Injective.of_comp (f := algebraMap S L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
  have := Module.isTorsionFree_iff_algebraMap_injective.mpr hRS
  by_cases hIbot : I = ⊥
  · rw [hIbot, Ideal.comap_bot_of_injective _ hRS, Ideal.map_bot]
  have h1 : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R L
  have hIbot' : I.comap (algebraMap R S) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hIbot
  have : ∀ p, (p.IsPrime ∧ I.comap (algebraMap R S) ≤ p) → ∃ P ≥ I, P ∈ primesOver p S := by
    intro p ⟨hp₁, hp₂⟩
    obtain ⟨P, hP1, hP2, hP3⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ _ hp₂
    exact ⟨P, hP1, hP2, ⟨hP3.symm⟩⟩
  choose 𝔓 h𝔓 h𝔓' using this
  suffices I = ∏ p ∈ (factors (I.comap <| algebraMap R S)).toFinset,
    (p.map (algebraMap R S)) ^ (if h : _ then (factors I).count (𝔓 p h) else 0) by
    simp_rw [← Ideal.mapHom_apply, ← map_pow, ← map_prod, Ideal.mapHom_apply] at this
    rw [this, Ideal.map_comap_map]
  conv_lhs => rw [← associated_iff_eq.mp (factors_pow_count_prod hIbot)]
  rw [← Finset.prod_fiberwise_of_maps_to (g := (Ideal.comap (algebraMap R S) : Ideal S → Ideal R))
    (t := (factors (I.comap (algebraMap R S))).toFinset)]
  · apply Finset.prod_congr rfl
    intros p hp
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot'] at hp
    have hpbot : p ≠ ⊥ := fun hp' ↦ hIbot' (eq_bot_iff.mpr (hp.2.trans_eq hp'))
    have hpbot' : p.map (algebraMap R S) ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective hRS).not.mpr
      hpbot
    have := hp.1
    rw [← prod_primesOverFinset_of_unramifiedAt p hpbot (hunram p hp.1 hp.2), ← Finset.prod_pow]
    have : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hpbot this
    apply Finset.prod_congr
    · ext P
      rw [factors_eq_normalizedFactors, Finset.mem_filter, Multiset.mem_toFinset,
        Ideal.mem_normalizedFactors_iff hIbot, ← Finset.mem_coe,
          IsDedekindDomain.coe_primesOverFinset hpbot S]
      refine ⟨fun H ↦ ⟨H.1.1, ⟨H.2.symm⟩⟩, fun H ↦ ⟨⟨H.1, ?_⟩, ?_⟩⟩
      · have ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K L S (h𝔓' _ hp) H
        rw [← hσ, ← hI σ]
        exact Ideal.comap_mono (h𝔓 _ hp)
      · have := H.2.1
        rw [Ideal.under_def] at this
        exact this.symm
    · intro P hP
      rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hpbot S] at hP
      congr
      rw [dif_pos hp, ← Nat.cast_inj (R := ENat), ← normalize_eq P, factors_eq_normalizedFactors,
        ← emultiplicity_eq_count_normalizedFactors
          (prime_of_mem_primesOver hpbot hP).irreducible hIbot,
        ← normalize_eq (𝔓 p hp), ← emultiplicity_eq_count_normalizedFactors
          (prime_of_mem_primesOver hpbot <| h𝔓' p hp).irreducible hIbot,
          emultiplicity_eq_emultiplicity_iff]
      intro n
      have ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K L S (h𝔓' _ hp) hP
      rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le]
      conv_lhs => rw [← hI σ, ← hσ,
        Ideal.comap_le_iff_le_map _ (AlgEquiv.bijective _), Ideal.map_pow,
        Ideal.map_comap_of_surjective _ (AlgEquiv.surjective _)]
  · intro P hP
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot] at hP
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot']
    exact ⟨hP.1.comap _, Ideal.comap_mono hP.2⟩

/-- The monic quadratic `X² - bX + 1` over a field is separable when its discriminant `b² - 4`
is nonzero. Proof: the explicit Bézout identity `(2X-b)·f' - 4·f = b² - 4` exhibits `f` and its
derivative as coprime. This is the separability step for the descent's unramified criterion
(`isUnramifiedAt_of_Separable_minpoly` with the minpoly `X² - (ζ+ζ⁻¹)X + 1` of `ζ` over `K⁺`,
whose discriminant is `(ζ-ζ⁻¹)²`, a unit modulo any prime away from `p`). -/
lemma separable_quadratic_of_disc_ne_zero {F : Type*} [Field F] (b : F)
    (hb : b ^ 2 - 4 ≠ 0) : (X ^ 2 - C b * X + 1 : F[X]).Separable := by
  have hd : derivative (X ^ 2 - C b * X + 1 : F[X]) = C 2 * X - C b := by
    simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_C_mul, derivative_X,
      derivative_one, mul_one, add_zero, Nat.cast_ofNat]
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  have hu : (b ^ 2 - 4)⁻¹ * (b ^ 2 - 4) = 1 := inv_mul_cancel₀ hb
  rw [Polynomial.separable_def]
  refine ⟨C (-4 * (b ^ 2 - 4)⁻¹), C (b ^ 2 - 4)⁻¹ * (C 2 * X - C b), ?_⟩
  rw [hd]
  have key : ((C 2 * X - C b) ^ 2 - 4 * (X ^ 2 - C b * X + 1) : F[X]) = C (b ^ 2 - 4) := by
    simp only [map_sub, map_pow, map_ofNat]; ring
  have expand : C (-4 * (b ^ 2 - 4)⁻¹) * (X ^ 2 - C b * X + 1)
      + C (b ^ 2 - 4)⁻¹ * (C 2 * X - C b) * (C 2 * X - C b)
      = C (b ^ 2 - 4)⁻¹ * ((C 2 * X - C b) ^ 2 - 4 * (X ^ 2 - C b * X + 1)) := by
    simp only [map_mul, map_neg, map_ofNat]; ring
  rw [expand, key, ← C_mul, hu, C_1]
