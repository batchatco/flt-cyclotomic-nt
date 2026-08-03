import CyclotomicNT.CyclotomicUnitGalois

/-!
# Thm 8.14, piece 3b (foundation) — `σ_g` preserves the real units

To descend the Galois operator `σ_g` to `V = E/E^p` we first show it maps `E = realUnits K` into
itself.  This holds because `Gal(K/ℚ)` is abelian (cyclotomic), so `σ_g` commutes with complex
conjugation; hence it preserves the fixed field `K⁺` and its units.

* `galAut_complexConj`: `σ_g ∘ conj = conj ∘ σ_g` (checked on `ζ`, where both send `ζ ↦ ζ^{∓g}`);
* `mem_realUnits_iff_complexConj`: `u ∈ realUnits K ↔ conj` fixes `u`;
* `galUnit_mem_realUnits`: `σ_g` maps `realUnits K` into itself. -/

namespace CyclotomicNT

open scoped NumberField
open NumberField NumberField.IsCMField

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}

/-- `σ_g` commutes with complex conjugation — both lie in the abelian group `Gal(K/ℚ)`.  Verified on
the generator `ζ`, where `σ_g(conj ζ) = σ_g(ζ⁻¹) = ζ^{−g} = conj(ζ^g) = conj(σ_g ζ)`. -/
theorem galAut_complexConj (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) (x : K) :
    galAut hζ g (complexConj K x) = complexConj K (galAut hζ g x) := by
  have key : (galAut hζ g).toAlgHom.comp ((complexConj K).restrictScalars ℚ).toAlgHom
      = ((complexConj K).restrictScalars ℚ).toAlgHom.comp (galAut hζ g).toAlgHom := by
    apply (hζ.powerBasis ℚ).algHom_ext
    simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom,
      AlgEquiv.restrictScalars_apply, IsPrimitiveRoot.powerBasis_gen]
    rw [complexConj_zeta hζ, map_inv₀, galAut_zeta, map_pow, complexConj_zeta hζ, inv_pow]
  have hx := AlgHom.ext_iff.mp key x
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_algHom,
    AlgEquiv.restrictScalars_apply] using hx

/-- A unit of `𝓞 K` is a real unit iff it is fixed by complex conjugation. -/
theorem mem_realUnits_iff_complexConj (u : (𝓞 K)ˣ) :
    u ∈ realUnits K ↔ complexConj K (u : K) = (u : K) := by
  rw [mem_realUnits_iff, Units.complexConj_eq_self_iff]
  refine exists_congr fun v => ?_
  rw [IsScalarTower.algebraMap_apply (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) K]
  exact (FaithfulSMul.algebraMap_injective (𝓞 K) K).eq_iff.symm

/-- `σ_g` maps the real units into themselves (it preserves `K⁺`). -/
theorem galUnit_mem_realUnits (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) (u : (𝓞 K)ˣ)
    (hu : u ∈ realUnits K) : galUnit hζ g u ∈ realUnits K := by
  rw [mem_realUnits_iff_complexConj] at hu ⊢
  simp only [coe_galUnit]
  rw [← galAut_complexConj, hu]

end CyclotomicNT
