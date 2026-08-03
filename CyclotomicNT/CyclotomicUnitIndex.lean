import CyclotomicNT.CyclotomicUnitIndexProof
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Washington Thm 8.2 — the cyclotomic-unit index `[E : C] = h⁺`

The computation of the regulator of the cyclotomic units as `∏_{χ even} L(1,χ)` compared against
the analytic class number formula for `K⁺`, proved by
`CyclotomicNT.cyclotomic_unit_index_proof` (CyclotomicUnitIndexProof.lean), the capstone of the
chain: archimedean regulator geometry (CyclotomicEmbedding/PlaceCycle/Regulator + the reduced
group determinant), the even-character bijection and `λ_k = −½τ(χ⁻¹)L(1,χ)`
(EvenCharBijection/EigenvalueLValue/ProductTransfer), the splitting of primes in `K⁺` and the
Euler factorization `ζ_{K⁺}(s)(1−p^{−s}) = ∏_{χ even}L(s,χ)` (KPlusGalois/KPlusSplitting/
KPlusEuler), `|disc K⁺| = p^{(p−3)/2}` (KPlusDisc), and the class number formula (KPlusBasic).

`E = realUnits K` (the units of `K⁺`, via `NumberField.IsCMField.realUnits`), `C =
    cyclotomicUnitGroup hζ`
(proven `C ≤ E` in `cyclotomicUnitGroup_le_realUnits`), and `h⁺ = |Cl(𝓞 K⁺)|`.  Both `E` and `C`
    carry
the same torsion `{±1}`, so the full-group index equals the index of the free parts, which Thm 8.2
identifies with `h⁺`.

When instantiated at `K = CyclotomicField p ℚ` we have `maximalRealSubfield K =
    MaximalRealCyclotomic p`,
so the right-hand side is exactly the class number appearing in `CyclotomicNT.IsVandiverPrime`. -/

namespace CyclotomicNT

open scoped NumberField
open NumberField.IsCMField

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}

/-- **Washington, *Introduction to Cyclotomic Fields*, Theorem 8.2**.  The index
of the cyclotomic unit group `C` in the real unit group `E = realUnits K` equals the class number
`h⁺` of the maximal real subfield `K⁺`. -/
theorem cyclotomic_unit_index (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) :
    (cyclotomicUnitGroup hζ).relIndex (realUnits K) =
      Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K))) :=
  cyclotomic_unit_index_proof hζ hp

end CyclotomicNT
