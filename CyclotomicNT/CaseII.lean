import CyclotomicNT.RegularPrimes
import CyclotomicNT.UnramifiedDescent
import CyclotomicNT.PrimitiveRootUnit
import Mathlib.NumberTheory.NumberField.CMField

/-!
# Case II of FLT under the Vandiver + Kummer-unit hypotheses

This file states **Case II** (`p ∣ abc`) of Fermat's Last Theorem under `IsVandiverPrime p`
and `KummerUnitProperty p`, the analogue of `FltRegular.caseII` with regularity weakened. This
is the main work of the Varma–Washington generalisation ("generalisation of the second case",
Varma §7).

## Where regularity enters Case II (and how the two hypotheses replace it)

flt-regular's `caseII` reduces (via `not_exists_Int_solution'` → `not_exists_solution'` →
`not_exists_solution`) to the descent step `FltRegular.CaseII.exists_solution'` in
`CaseII/InductionStep.lean`. That step uses regularity in exactly two conceptually distinct
places, matching the two hypotheses here:

1. **Ideal principality** — `isPrincipal_a_div_a_zero` calls
   `isPrincipal_of_isPrincipal_pow_of_Coprime'` (i.e. `p ∤ h`), for the class `[𝔞 η₁ / 𝔞 η₂]`
   with `(𝔞 η)^p = 𝔠 η` the coprime part of `(x + y·η)`.

   ⚠ **In `InductionStep.lean`, `x, y, z` are GENERAL cyclotomic integers (not real), so
   `[𝔞 η₁/𝔞 η₂]` is NOT Galois-symmetric and the plus-part / extended-class argument does
   NOT apply to it.** flt-regular genuinely needs full `p ∤ h` here. The Varma–Washington
   Vandiver proof uses a *different* descent that keeps the relevant classes in the plus part;
   reproducing it is a from-scratch construction, not a copy-modify of flt-regular.

   The class-group infrastructure here (`eq_one_of_pow_eq_one_of_image_sq` in `GroupAux.lean`,
   `IsVandiverPrime.pow_eq_one_eq_one` in `RegularPrimes.lean`, the `ι`/`N` maps and Galois
   action in `ClassGroupMap.lean`, and the criteria `isOne_of_pow_eq_one_of_extend_norm_eq_sq`
   / `isOne_of_pow_eq_one_of_extended` below) is correct and reusable, but it only discharges
   principality for `j`-fixed / `ι`-extended classes — which the descent must first be
   rearranged to produce.

2. **Kummer's lemma** — `exists_solution'` calls
   `eq_pow_prime_of_unit_of_congruent hp hreg` ("this is Kummers") to show a unit `V'` of
   `𝓞 K` is a `p`-th power. Under Vandiver one shows `V'` is (a root of unity times) a *real*
   unit, reducing to `KummerUnitProperty p`. (Varma §7 "Step 2".)

Everything else in `InductionStep.lean` (the factorisations, coprimality of the `𝔠 η`, the
`formula`, the multiplicity bookkeeping in `not_exists_solution'`) is regularity-free and
reusable essentially verbatim. -/

open NumberField

open scoped NumberField nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace CyclotomicNT

variable {p : ℕ}

/-- **Case II principality criterion (plus-part triviality), proved.**

A `p`-torsion ideal class `c` of `Cl(𝓞 K)` (`K = Q(ζ_p)`) that is *fixed by complex
conjugation* — concretely, one for which `extend (norm c) = c²` (since `ι (N c) = c^{1+j}` and
`j` fixes `c`) — is trivial, under `IsVandiverPrime p` and `p ≠ 2`.

This is the principality step of the Case II descent (Varma §7 "Step 1"), packaged as a
ready-to-use lemma: it reduces that step to the single remaining fact
`extend (norm c) = c²`, i.e. the `ι ∘ N = (1 + j)` relation evaluated at the `j`-fixed
Galois-symmetric ideals `𝔞 η / 𝔞 η₀`. It is `eq_one_of_pow_eq_one_of_image_sq` applied to
`classGroupExtend` / `classGroupNorm`, with `IsVandiverPrime.pow_eq_one_eq_one` supplying the
`p`-torsion-freeness of `Cl(𝓞 K⁺)`. -/
theorem isOne_of_pow_eq_one_of_extend_norm_eq_sq [hp : Fact p.Prime] (hvand : IsVandiverPrime p)
    (hodd : p ≠ 2) {c : ClassGroup (𝓞 (CyclotomicField p ℚ))} (hcp : c ^ p = 1)
    (hsq : classGroupExtend
        (RingOfIntegers.algebraMap.injective (MaximalRealCyclotomic p) (CyclotomicField p ℚ))
        (classGroupNorm c) = c ^ 2) :
    c = 1 :=
  eq_one_of_pow_eq_one_of_image_sq _ _ hp.out hodd
    (fun _ ha => hvand.pow_eq_one_eq_one ha) hcp hsq

/-- **Principality for classes extended from `K⁺`, proved unconditionally** (no
conjugate-product needed). If a class `c = ι a` *in the image of* `classGroupExtend` (i.e.
extended from `Cl(𝓞 K⁺)`) is `p`-torsion, then `c = 1`, under `IsVandiverPrime p` and `p ≠ 2`.

The point: for `c = ι a`, the required `extend (norm c) = c²` is *automatic* from the proved
`classGroupNorm_classGroupExtend` (`N ∘ ι = ·²`, since `[K:K⁺] = 2`):
`ι (N (ι a)) = ι (a²) = (ι a)²`. So this avoids the still-missing `ι ∘ N = (1+j)` identity
entirely. It reduces the Case II principality step to showing the relevant Galois-symmetric
class lies in the image of `ι` (extension from the real subfield). -/
theorem isOne_of_pow_eq_one_of_extended [hp : Fact p.Prime] (hvand : IsVandiverPrime p)
    (hodd : p ≠ 2) {a : ClassGroup (𝓞 (MaximalRealCyclotomic p))}
    (hcp : (classGroupExtend
        (RingOfIntegers.algebraMap.injective (MaximalRealCyclotomic p) (CyclotomicField p ℚ))
        a) ^ p = 1) :
    classGroupExtend
      (RingOfIntegers.algebraMap.injective (MaximalRealCyclotomic p) (CyclotomicField p ℚ)) a
      = 1 := by
  apply isOne_of_pow_eq_one_of_extend_norm_eq_sq hvand hodd hcp
  rw [classGroupNorm_classGroupExtend, finrank_fractionRing_eq_two hodd, map_pow]

/-- **§9.1 principality step (ideal level), PROVED.** If `I` is an ideal of `𝓞 K⁺` whose
extension `I·𝓞 K` to `𝓞 K` has *principal `p`-th power*, then `I·𝓞 K` is itself principal —
under `IsVandiverPrime p` and `p ≠ 2`. This is exactly how Washington's descent makes the real
ideal `B_0` (which "arises from `ℤ[λ] = 𝓞 K⁺`") principal from `p ∤ h⁺`. It reduces to the
class-group lemma `isOne_of_pow_eq_one_of_extended` (no Stickelberger). -/
theorem isPrincipal_map_of_pow_isPrincipal [Fact p.Prime] (hvand : IsVandiverPrime p)
    (hodd : p ≠ 2) {I : Ideal (𝓞 (MaximalRealCyclotomic p))}
    (hpow : (I.map (algebraMap (𝓞 (MaximalRealCyclotomic p))
        (𝓞 (CyclotomicField p ℚ))) ^ p).IsPrincipal) :
    (I.map (algebraMap (𝓞 (MaximalRealCyclotomic p)) (𝓞 (CyclotomicField p ℚ)))).IsPrincipal := by
  have hinj : Function.Injective
      (algebraMap (𝓞 (MaximalRealCyclotomic p)) (𝓞 (CyclotomicField p ℚ))) :=
    RingOfIntegers.algebraMap.injective _ _
  rcases eq_or_ne I 0 with rfl | hI
  · simp only [Ideal.zero_eq_bot, Ideal.map_bot]; exact bot_isPrincipal
  · have hImem : I ∈ (Ideal (𝓞 (MaximalRealCyclotomic p)))⁰ :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hI
    have hJmem : I.map (algebraMap _ _) ∈ (Ideal (𝓞 (CyclotomicField p ℚ)))⁰ :=
      mem_nonZeroDivisors_iff_ne_zero.mpr
        (fun h => hI ((Ideal.map_eq_bot_iff_of_injective hinj).mp h))
    have hJpmem : (I.map (algebraMap _ _)) ^ p ∈ (Ideal (𝓞 (CyclotomicField p ℚ)))⁰ :=
      pow_mem hJmem p
    have key : classGroupExtend hinj (ClassGroup.mk0 ⟨I, hImem⟩)
        = ClassGroup.mk0 ⟨I.map (algebraMap _ _), hJmem⟩ := by
      rw [classGroupExtend_mk0]; congr 1
    have hp1 : (classGroupExtend hinj (ClassGroup.mk0 ⟨I, hImem⟩)) ^ p = 1 := by
      rw [key, ← map_pow,
        show (⟨I.map (algebraMap _ _), hJmem⟩ : (Ideal (𝓞 (CyclotomicField p ℚ)))⁰) ^ p
          = ⟨(I.map (algebraMap _ _)) ^ p, hJpmem⟩ from Subtype.ext (by push_cast; ring)]
      exact (ClassGroup.mk0_eq_one_iff hJpmem).mpr hpow
    rw [← ClassGroup.mk0_eq_one_iff hJmem, ← key]
    exact isOne_of_pow_eq_one_of_extended hvand hodd hp1

set_option maxHeartbeats 1000000 in -- heavy ramification/finrank elaboration
/-- The discriminant `a² − 4` of the minimal polynomial `X² − a·X + 1` of `ζ` (where
`algebraMap a = ζ + ζ⁻¹`) is not in a prime `q` of `𝓞 K⁺` lying under a prime `Q` of `𝓞 K`
with `p ∉ q`. Equivalently, `ζ − ζ⁻¹` (which generates the prime above `p`) avoids `Q`. This is
the discriminant-nonvanishing fact behind `hunram`'s separability step. -/
lemma disc_not_mem [Fact p.Prime] [NeZero p]
    [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] [IsCMField (CyclotomicField p ℚ)]
    (hp : 2 < p) {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {q : Ideal (𝓞 (MaximalRealCyclotomic p))} {Q : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hQ_prime : Q.IsPrime)
    (hQ_over : Q.comap (algebraMap (𝓞 (MaximalRealCyclotomic p)) (𝓞 (CyclotomicField p ℚ))) = q)
    (hp_not : (p : 𝓞 (MaximalRealCyclotomic p)) ∉ q)
    {a : 𝓞 (MaximalRealCyclotomic p)}
    (ha : algebraMap (𝓞 (MaximalRealCyclotomic p)) (CyclotomicField p ℚ) a = ζ + ζ⁻¹) :
    a ^ 2 - 4 ∉ q := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne p)
  intro hmem_q
  have hmem_Q : (algebraMap (𝓞 (MaximalRealCyclotomic p)) (𝓞 (CyclotomicField p ℚ))) (a ^ 2 - 4)
      ∈ Q := Ideal.mem_comap.mp (hQ_over.symm ▸ hmem_q)
  set δ : 𝓞 (CyclotomicField p ℚ) :=
    (hζ.unit' : 𝓞 (CyclotomicField p ℚ)) - (↑hζ.unit'⁻¹ : 𝓞 (CyclotomicField p ℚ)) with hδdef
  have hu2 : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
      (↑hζ.unit'⁻¹ : 𝓞 (CyclotomicField p ℚ)) = ζ⁻¹ := rfl
  have hιδ : (algebraMap (𝓞 (MaximalRealCyclotomic p)) (𝓞 (CyclotomicField p ℚ))) (a ^ 2 - 4)
      = δ ^ 2 := by
    apply IsFractionRing.injective (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
    rw [← IsScalarTower.algebraMap_apply, map_sub, map_pow, map_ofNat, ha, hδdef, map_pow,
      map_sub, hu2]
    change (ζ + ζ⁻¹) ^ 2 - 4 = (ζ - ζ⁻¹) ^ 2
    field_simp
    ring
  rw [hιδ] at hmem_Q
  have hδ_Q : δ ∈ Q := hQ_prime.mem_of_pow_mem 2 hmem_Q
  have hassoc : Associated δ ((hζ.unit' : 𝓞 (CyclotomicField p ℚ)) - 1) := by
    have hinv : (↑hζ.unit'⁻¹ : 𝓞 (CyclotomicField p ℚ)) * (↑hζ.unit' : 𝓞 (CyclotomicField p ℚ))
        = 1 := by rw [← Units.val_mul, inv_mul_cancel]; rfl
    have hδeq : δ = (↑hζ.unit'⁻¹ : 𝓞 (CyclotomicField p ℚ))
        * ((hζ.unit' : 𝓞 (CyclotomicField p ℚ)) ^ 2 - 1) := by
      rw [hδdef]; linear_combination (-(hζ.unit' : 𝓞 (CyclotomicField p ℚ))) * hinv
    have hcop2 : Nat.Coprime 2 p :=
      Nat.coprime_two_left.mpr ((Fact.out : p.Prime).odd_of_ne_two (by omega))
    have h2 : Associated ((hζ.unit' : 𝓞 (CyclotomicField p ℚ)) - 1)
        ((hζ.unit' : 𝓞 (CyclotomicField p ℚ)) ^ 2 - 1) :=
      hζ.unit'_coe.associated_sub_one_pow_sub_one_of_coprime hcop2
    rw [hδeq]
    exact (associated_unit_mul_left _ _ (hζ.unit'⁻¹).isUnit).trans h2.symm
  have h1ζ_Q : (hζ.unit' : 𝓞 (CyclotomicField p ℚ)) - 1 ∈ Q := by
    obtain ⟨u, hu⟩ := hassoc
    rw [← hu]; exact Ideal.mul_mem_right _ Q hδ_Q
  have hp_Q : (p : 𝓞 (CyclotomicField p ℚ)) ∈ Q :=
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h1ζ_Q)) hζ.p_mem_one_sub_zeta
  apply hp_not
  rw [← hQ_over, Ideal.mem_comap]
  simpa using hp_Q

set_option maxHeartbeats 4000000 in -- monolithic Hilbert-94-style descent inside one proof
open Polynomial IsCMField in
/-- A conjugation-fixed ideal `B` of `𝓞 K` (`K = ℚ(ζ_p)`) coprime to `(p)` is extended from
`𝓞 K⁺`. This applies `comap_map_eq_of_unramifiedAtFactors` (the localized Galois ideal-descent
lemma — flt-regular's `comap_map_eq_of_isUnramified` weakened to per-prime unramifiedness) to
`𝓞 K⁺ → 𝓞 K`, taking `A := B.comap ι`. All the tower / integral-closure / fraction-ring /
Galois instances resolve automatically, reducing the proof to two facts (both **PROVED**):
* **`hI`** — `B.comap` is fixed by the whole Galois action `Gal(K/K⁺)`: from `hfix` (`B` is
  `complexConj`-fixed) and `Gal(K/K⁺) = {1, complexConj}` (order two, `zpowers_complexConj_eq_top`),
  identifying `galRestrict complexConj` with `ringOfIntegersComplexConj`.
* **`hunram`** — every prime `q` of `𝓞 K⁺` dividing `B ∩ 𝓞 K⁺` is unramified in `𝓞 K`. Since
  `hcop` gives `q ∤ (p)`, `q` avoids the sole ramified prime `(1-ζ)`; discharged via
  `isUnramifiedAt_of_Separable_minpoly` with `x = ζ`: the minpoly of `ζ` over `K⁺` is the quadratic
  `X² - (ζ+ζ⁻¹)X + 1` (proved here), its reduction is separable by
  `separable_quadratic_of_disc_ne_zero` since the discriminant `(ζ-ζ⁻¹)²` is a unit mod `q`
  (`disc_not_mem`, via the prime above `p`).

This lemma is axiom-clean (`#print axioms` shows only `propext`/`Classical.choice`/`Quot.sound`),
so `isPrincipal_of_conjFixed_of_pow` is too, and `caseII_94_of_descent` is clean modulo
`refinedKummer`. `set_option maxHeartbeats 4000000` is needed only because the whole proof is one
declaration over the `maximalRealSubfield` carrier; the individual steps are cheap. -/
lemma isExtended_of_conjFixed_of_coprime [Fact p.Prime] (hp : 2 < p)
    [IsCMField (CyclotomicField p ℚ)]
    {B : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hfix : B.map (NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) = B)
    (hcop : IsCoprime B (Ideal.span {(p : 𝓞 (CyclotomicField p ℚ))})) :
    ∃ A : Ideal (𝓞 (MaximalRealCyclotomic p)),
      B = A.map (algebraMap (𝓞 (MaximalRealCyclotomic p)) (𝓞 (CyclotomicField p ℚ))) := by
  refine ⟨B.comap (algebraMap (𝓞 (MaximalRealCyclotomic p)) (𝓞 (CyclotomicField p ℚ))),
    (comap_map_eq_of_unramifiedAtFactors (MaximalRealCyclotomic p) (CyclotomicField p ℚ) B
      ?hI ?hunram).symm⟩
  case hI =>
    have hinv : ∀ x : 𝓞 (CyclotomicField p ℚ),
        (NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField p ℚ)
            : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ))
          ((NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField p ℚ)
            : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) x) = x := by
      intro x
      apply IsFractionRing.injective (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
      simp only [RingHom.coe_coe, IsCMField.coe_ringOfIntegersComplexConj,
        IsCMField.complexConj_apply_apply]
    have hcomap : B.comap (NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField p ℚ)
        : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) = B := by
      apply le_antisymm
      · intro x hx
        rw [Ideal.mem_comap] at hx
        have h2 := Ideal.mem_map_of_mem
          (NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField p ℚ)
            : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) hx
        rw [hfix, hinv] at h2; exact h2
      · intro x hx
        rw [Ideal.mem_comap]
        have h2 := Ideal.mem_map_of_mem
          (NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField p ℚ)
            : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) hx
        rwa [hfix] at h2
    have hgr : (galRestrict (𝓞 (MaximalRealCyclotomic p)) (MaximalRealCyclotomic p)
        (CyclotomicField p ℚ) (𝓞 (CyclotomicField p ℚ))
        (IsCMField.complexConj (CyclotomicField p ℚ))
        : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ))
        = (NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField p ℚ)
            : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) := by
      ext x
      simp only [RingHom.coe_coe, algebraMap_galRestrict_apply,
        IsCMField.coe_ringOfIntegersComplexConj]
    have hc2 : IsCMField.complexConj (CyclotomicField p ℚ) ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast,
        ← IsCMField.orderOf_complexConj (CyclotomicField p ℚ)]
      exact pow_orderOf_eq_one _
    intro σ
    have hdisj : σ = 1 ∨ σ = IsCMField.complexConj (CyclotomicField p ℚ) := by
      have hmem : σ ∈ Subgroup.zpowers (IsCMField.complexConj (CyclotomicField p ℚ)) :=
        IsCMField.zpowers_complexConj_eq_top (CyclotomicField p ℚ) ▸ Subgroup.mem_top σ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · left; rw [show m + m = 2 * m by ring, zpow_mul, hc2, one_zpow]
      · right; rw [zpow_add, zpow_mul, hc2, one_zpow, one_mul, zpow_one]
    rcases hdisj with rfl | rfl
    · rw [map_one]; exact Ideal.comap_id B
    · change B.comap ((galRestrict (𝓞 (MaximalRealCyclotomic p)) (MaximalRealCyclotomic p)
          (CyclotomicField p ℚ) (𝓞 (CyclotomicField p ℚ))
          (IsCMField.complexConj (CyclotomicField p ℚ)))
          : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) = B
      rw [hgr]; exact hcomap
  case hunram =>
    intro q hq_prime hq_le
    haveI := hq_prime
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
      CyclotomicField.isCyclotomicExtension p ℚ
    set ζ : CyclotomicField p ℚ := IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) with hζdef
    have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
    have hζint : IsIntegral (𝓞 (MaximalRealCyclotomic p)) ζ :=
      (hζ.isIntegral (by positivity)).tower_top
    -- (A) B ≠ ⊥: else `hcop` forces `p` to be a unit, but `p` lies in the proper prime `(1-ζ)`.
    have hB_ne : B ≠ ⊥ := by
      intro hBbot
      rw [hBbot, bot_eq_zero, isCoprime_zero_left] at hcop
      have hsp_top : Ideal.span {(p : 𝓞 (CyclotomicField p ℚ))} = ⊤ := Ideal.isUnit_iff.mp hcop
      have hp_mem : (p : 𝓞 (CyclotomicField p ℚ)) ∈
          Ideal.span {(hζ.unit' - 1 : 𝓞 (CyclotomicField p ℚ))} := hζ.p_mem_one_sub_zeta
      have hle : Ideal.span {(p : 𝓞 (CyclotomicField p ℚ))} ≤
          Ideal.span {(hζ.unit' - 1 : 𝓞 (CyclotomicField p ℚ))} :=
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp_mem)
      rw [hsp_top, top_le_iff] at hle
      exact hζ.isPrime_one_sub_zeta.ne_top hle
    have hqbot : q ≠ ⊥ := fun h =>
      Ideal.IsIntegral.comap_ne_bot (𝓞 (MaximalRealCyclotomic p)) hB_ne (le_bot_iff.mp (h ▸ hq_le))
    obtain ⟨Q, hBQ, hQ_prime, hQ_over⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral q B hq_le
    -- (C) ζ generates K over K⁺: it already generates K over ℚ ⊆ K⁺.
    have hadjoin : Algebra.adjoin (MaximalRealCyclotomic p) {ζ} = ⊤ := by
      have h1 : Algebra.adjoin ℚ {ζ} = ⊤ := IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
      have h2 : Algebra.adjoin ℚ {ζ} ≤
          (Algebra.adjoin (MaximalRealCyclotomic p) {ζ}).restrictScalars ℚ := by
        apply Algebra.adjoin_le
        simp only [Set.singleton_subset_iff, SetLike.mem_coe, Subalgebra.mem_restrictScalars]
        exact Algebra.self_mem_adjoin_singleton _ ζ
      rw [h1, top_le_iff] at h2
      apply Subalgebra.restrictScalars_injective ℚ
      rw [h2, Subalgebra.restrictScalars_top]
    -- (D) separability of the reduced minimal polynomial.
    have hsep : ((minpoly (𝓞 (MaximalRealCyclotomic p)) ζ).map
        (Ideal.Quotient.mk q)).Separable := by
      have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne p)
      have hconj_zeta : complexConj (CyclotomicField p ℚ) ζ = ζ⁻¹ := by
        have hfin : IsOfFinOrder hζ.unit' :=
          isOfFinOrder_iff_pow_eq_one.mpr ⟨p, NeZero.pos p, hζ.unit'_pow⟩
        have hmem : hζ.unit' ∈ NumberField.Units.torsion (CyclotomicField p ℚ) := hfin
        have huval : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) ↑hζ.unit' = ζ := rfl
        simpa [huval] using IsCMField.complexConj_torsion (CyclotomicField p ℚ) ⟨hζ.unit', hmem⟩
      obtain ⟨a, ha⟩ : ∃ a : 𝓞 (MaximalRealCyclotomic p),
          algebraMap (𝓞 (MaximalRealCyclotomic p)) (CyclotomicField p ℚ) a = ζ + ζ⁻¹ := by
        have hα_fixed : complexConj (CyclotomicField p ℚ) (ζ + ζ⁻¹) = ζ + ζ⁻¹ := by
          rw [map_add, map_inv₀, hconj_zeta, inv_inv, add_comm]
        set xK : 𝓞 (CyclotomicField p ℚ) := (hζ.unit' : 𝓞 (CyclotomicField p ℚ))
          + (↑hζ.unit'⁻¹ : 𝓞 (CyclotomicField p ℚ)) with hxKdef
        have hxK_coe : (xK : CyclotomicField p ℚ) = ζ + ζ⁻¹ := by rw [hxKdef]; push_cast; rfl
        have hxK_fixed : complexConj (CyclotomicField p ℚ) xK = xK := by
          rw [show ((xK : CyclotomicField p ℚ)) = ζ + ζ⁻¹ from hxK_coe]; exact hα_fixed
        obtain ⟨a, ha⟩ :=
          (RingOfIntegers.complexConj_eq_self_iff (CyclotomicField p ℚ) xK).mp hxK_fixed
        exact ⟨a, ha.trans hxK_coe⟩
      have hmp : minpoly (𝓞 (MaximalRealCyclotomic p)) ζ = X ^ 2 - C a * X + 1 := by
        have hroot : (aeval ζ) (X ^ 2 - C a * X + 1 : (𝓞 (MaximalRealCyclotomic p))[X]) = 0 := by
          rw [map_add, map_sub, map_pow, map_mul, aeval_X, aeval_C, map_one, ha, add_mul,
            inv_mul_cancel₀ hζ0]
          ring
        have hPmonic : (X ^ 2 - C a * X + 1 : (𝓞 (MaximalRealCyclotomic p))[X]).Monic := by
          monicity!
        have hPdeg : (X ^ 2 - C a * X + 1 : (𝓞 (MaximalRealCyclotomic p))[X]).natDegree = 2 := by
          compute_degree!
        have hdvd := minpoly.isIntegrallyClosed_dvd hζint hroot
        have h2le : 2 ≤ (minpoly (𝓞 (MaximalRealCyclotomic p)) ζ).natDegree := by
          rw [minpoly.two_le_natDegree_iff hζint]
          rintro ⟨a', ha'⟩
          have hfix : complexConj (CyclotomicField p ℚ) ζ = ζ := by
            rw [← ha', IsScalarTower.algebraMap_apply (𝓞 (MaximalRealCyclotomic p))
              (MaximalRealCyclotomic p) (CyclotomicField p ℚ)]
            exact complexConj_apply_eq_self (CyclotomicField p ℚ) _
          rw [hconj_zeta] at hfix
          have hsq : ζ ^ 2 = 1 := by
            rw [pow_two]; nth_rewrite 2 [← hfix]; exact mul_inv_cancel₀ hζ0
          exact absurd (Nat.le_of_dvd (by norm_num) ((hζ.pow_eq_one_iff_dvd 2).mp hsq)) (by omega)
        exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hζint) hPmonic hdvd
          (by rw [hPdeg]; exact h2le)).symm
      haveI : q.IsMaximal := hq_prime.isMaximal hqbot
      letI : Field (𝓞 (MaximalRealCyclotomic p) ⧸ q) := Ideal.Quotient.field q
      rw [hmp, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_C, Polynomial.map_X, Polynomial.map_one]
      apply separable_quadratic_of_disc_ne_zero
      have hp_not : (p : 𝓞 (MaximalRealCyclotomic p)) ∉ q := by
        intro hpq
        have hpQ : (algebraMap (𝓞 (MaximalRealCyclotomic p)) (𝓞 (CyclotomicField p ℚ)))
            (p : 𝓞 (MaximalRealCyclotomic p)) ∈ Q := Ideal.mem_comap.mp (hQ_over.symm ▸ hpq)
        have hsup : B ⊔ Ideal.span {(p : 𝓞 (CyclotomicField p ℚ))} ≤ Q :=
          sup_le hBQ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (by simpa using hpQ)))
        rw [Ideal.isCoprime_iff_sup_eq.mp hcop] at hsup
        exact hQ_prime.ne_top (top_le_iff.mp hsup)
      intro hcontra
      apply disc_not_mem hp hζ hQ_prime hQ_over hp_not ha
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_ofNat]
      exact hcontra
    apply isUnramifiedAt_of_forall_isUnramifiedAt hqbot
    intro 𝔔 h𝔔prime h𝔔over
    letI := h𝔔prime
    letI : 𝔔.LiesOver q := h𝔔over
    refine isUnramifiedAt_of_Separable_minpoly (MaximalRealCyclotomic p) (CyclotomicField p ℚ)
      𝔔 (Ideal.ne_bot_of_liesOver_of_ne_bot hqbot 𝔔) ζ hζint hadjoin ?_
    rw [show 𝔔.under (𝓞 (MaximalRealCyclotomic p)) = q from h𝔔over.over.symm]
    exact hsep

/-- §9.1 Washington's descent produces an ideal `B` fixed by complex conjugation,
coprime to `p`, with `B^p` principal. `p ∤ h⁺` makes `B` principal.
Note: `[IsCMField (CyclotomicField p ℚ)]` is required for `ringOfIntegersComplexConj`;
it mathematically follows from `hp : 2 < p` (via `IsCyclotomicExtension.Rat.isCMField`). -/
theorem isPrincipal_of_conjFixed_of_pow [Fact p.Prime] (hp : 2 < p)
    (hvand : IsVandiverPrime p)
    [IsCMField (CyclotomicField p ℚ)]
    {B : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hfix : B.map (NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) = B)
    (hcop : IsCoprime B (Ideal.span {(p : 𝓞 (CyclotomicField p ℚ))}))
    (hpow : (B ^ p).IsPrincipal) :
    B.IsPrincipal := by
  have h_ext := isExtended_of_conjFixed_of_coprime hp hfix hcop
  rcases h_ext with ⟨A, rfl⟩
  exact isPrincipal_map_of_pow_isPrincipal hvand (ne_of_gt hp) hpow

end CyclotomicNT
