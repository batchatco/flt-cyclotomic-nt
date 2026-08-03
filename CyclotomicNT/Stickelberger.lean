import CyclotomicNT.StkBridge
import CyclotomicNT.ClassGroupMap

/-!
# Stickelberger's theorem for the class group of `ℚ(ζ_p)`

The class-group form of Stickelberger's annihilation theorem, **proved** (no axiom): for every
`c : ℕ` the integral Stickelberger element `β_c = ∑_{a ∈ (ℤ/p)ˣ} ⌊c·a/p⌋·σ_a⁻¹ ∈ ℤ[Gal]`
annihilates the ideal class group of any model `k₀` of `ℚ(ζ_p)`:

  `∏_a (σ_a⁻¹ · [I])^{⌊c·a/p⌋} = 1`.

The ideal-theoretic content is `stickelberger_annihilates_ideal` from our standalone, independent
`Stickelberger` library — a clean-room formalization of the Gauss-sum factorization and the
integral Stickelberger relation following Washington, *Introduction to Cyclotomic Fields*
(2nd ed.), Ch. 6, built only on Mathlib (`sorry`-free).
This file is pure glue: the Galois action on the class group (`classGroupMapEquiv`, from
`ClassGroupMap.lean`) matches the pointwise ideal action, and "class of product is trivial"
matches "product is principal" (`ClassGroup.mk0_eq_one_iff`). -/

open NumberField Ideal IsCyclotomicExtension.Rat
open scoped NumberField Pointwise nonZeroDivisors

namespace CyclotomicNT

variable {p : ℕ} [hpri : Fact p.Prime] {k₀ : Type*} [Field k₀] [NumberField k₀]
  [IsCyclotomicExtension {p} ℚ k₀]

/-- The Galois action of `σ ∈ Gal(k₀/ℚ)` on the class group of `𝓞 k₀`, `[I] ↦ [σ(I)]` —
`classGroupMapEquiv` applied to the induced ring-of-integers automorphism. -/
noncomputable def classGroupGalAct (σ : k₀ ≃ₐ[ℚ] k₀) :
    ClassGroup (𝓞 k₀) →* ClassGroup (𝓞 k₀) :=
  classGroupMapEquiv (RingOfIntegers.mapRingEquiv σ.toRingEquiv)

/-- The pointwise ideal action preserves nonzeroness. -/
theorem smul_mem_nonZeroDivisors (σ : k₀ ≃ₐ[ℚ] k₀) (I : (Ideal (𝓞 k₀))⁰) :
    σ • (I : Ideal (𝓞 k₀)) ∈ (Ideal (𝓞 k₀))⁰ := by
  rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.pointwise_smul_def, Ne, Ideal.zero_eq_bot,
    Ideal.map_eq_bot_iff_of_injective
      (show Function.Injective ⇑(MulSemiringAction.toRingHom _ (𝓞 k₀) σ) from
        MulAction.injective σ)]
  rw [← Ideal.zero_eq_bot]
  exact mem_nonZeroDivisors_iff_ne_zero.mp I.2

/-- **The Galois action on `mk0` is the pointwise ideal action**: the two vocabularies
(`classGroupMapEquiv ∘ mapRingEquiv` here, `σ • I` in the `Stickelberger` library) agree. -/
theorem classGroupGalAct_mk0 (σ : k₀ ≃ₐ[ℚ] k₀) (I : (Ideal (𝓞 k₀))⁰) :
    classGroupGalAct σ (ClassGroup.mk0 I)
      = ClassGroup.mk0 ⟨σ • (I : Ideal (𝓞 k₀)), smul_mem_nonZeroDivisors σ I⟩ := by
  rw [classGroupGalAct, classGroupMapEquiv_mk0]
  refine congrArg ClassGroup.mk0 (Subtype.ext ?_)
  rw [idealMapEquiv_coe]
  change _ = σ • (I : Ideal (𝓞 k₀))
  rw [Ideal.pointwise_smul_def]
  congr 1

/-- **Stickelberger's theorem, class-group form** (Washington, *Cyclotomic Fields*,
Thm 6.10 / Lemma 6.9, integral version): for every `c : ℕ`, the integral Stickelberger element
`β_c = ∑_a ⌊c·a/p⌋·σ_a⁻¹` annihilates every ideal class of `ℚ(ζ_p)`.

Proved via the clean-room `Stickelberger` library (`stickelberger_annihilates_ideal`). -/
theorem stickelberger_annihilates (c : ℕ) (cl : ClassGroup (𝓞 k₀)) :
    ∏ a : (ZMod p)ˣ,
      (classGroupGalAct (((galEquivZMod p k₀).symm a)⁻¹) cl) ^ (c * (a : ZMod p).val / p)
      = 1 := by
  classical
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective cl
  have hI : (I : Ideal (𝓞 k₀)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  calc ∏ a : (ZMod p)ˣ,
      (classGroupGalAct (((galEquivZMod p k₀).symm a)⁻¹) (ClassGroup.mk0 I))
        ^ (c * (a : ZMod p).val / p)
      = ∏ a : (ZMod p)ˣ,
          (ClassGroup.mk0 (⟨((galEquivZMod p k₀).symm a)⁻¹ • (I : Ideal (𝓞 k₀)),
            smul_mem_nonZeroDivisors _ I⟩ : (Ideal (𝓞 k₀))⁰)) ^ (c * (a : ZMod p).val / p) :=
        Finset.prod_congr rfl fun a _ => by rw [classGroupGalAct_mk0]
    _ = ClassGroup.mk0 (∏ a : (ZMod p)ˣ,
          (⟨((galEquivZMod p k₀).symm a)⁻¹ • (I : Ideal (𝓞 k₀)),
            smul_mem_nonZeroDivisors _ I⟩ : (Ideal (𝓞 k₀))⁰) ^ (c * (a : ZMod p).val / p)) := by
        rw [map_prod]
        exact Finset.prod_congr rfl fun a _ => (map_pow _ _ _).symm
    _ = 1 := by
        refine (ClassGroup.mk0_eq_one_iff (∏ a : (ZMod p)ˣ,
          (⟨((galEquivZMod p k₀).symm a)⁻¹ • (I : Ideal (𝓞 k₀)),
            smul_mem_nonZeroDivisors _ I⟩ : (Ideal (𝓞 k₀))⁰)
              ^ (c * (a : ZMod p).val / p)).2).mpr ?_
        have hcoe : ((∏ a : (ZMod p)ˣ,
            (⟨((galEquivZMod p k₀).symm a)⁻¹ • (I : Ideal (𝓞 k₀)),
              smul_mem_nonZeroDivisors _ I⟩ : (Ideal (𝓞 k₀))⁰)
                ^ (c * (a : ZMod p).val / p) : (Ideal (𝓞 k₀))⁰) : Ideal (𝓞 k₀))
            = ∏ a : (ZMod p)ˣ,
              (((galEquivZMod p k₀).symm a)⁻¹ • (I : Ideal (𝓞 k₀)))
                ^ (c * (a : ZMod p).val / p) := by
          push_cast
          rfl
        rw [hcoe]
        exact stickelberger_annihilates_ideal c (I : Ideal (𝓞 k₀)) hI

end CyclotomicNT
