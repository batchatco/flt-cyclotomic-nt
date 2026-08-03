import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# Compatibility shim: `IsPrimitiveRoot.unit'`

Old Mathlib exposed `IsPrimitiveRoot.unit'`, sending a primitive root `ζ : K` of a number field to
the corresponding unit of its ring of integers `(𝓞 K)ˣ`, together with `unit'_coe` witnessing that
this unit is again a primitive root in `𝓞 K`. Both were removed upstream in favor of `toInteger`.
This file restores them (as thin wrappers over `IsPrimitiveRoot.toInteger`) so the Case II descent
files compile unchanged. By construction `(hζ.unit' : 𝓞 K) = hζ.toInteger = ⟨ζ, _⟩`
definitionally. -/

open NumberField

namespace IsPrimitiveRoot

variable {K : Type*} [Field K] [NumberField K] {ζ : K}

/-- A primitive `k`-th root of unity of a number field, as a unit of its ring of integers.
Both `(hζ.unit' : 𝓞 K) = hζ.toInteger` and `(↑hζ.unit'⁻¹ : 𝓞 K) = hζ.inv.toInteger` hold by `rfl`
(so `algebraMap … ↑hζ.unit'⁻¹ = ζ⁻¹` definitionally — matching old Mathlib's `unit'`). -/
noncomputable def unit' {k : ℕ} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : (𝓞 K)ˣ where
  val := hζ.toInteger
  inv := hζ.inv.toInteger
  val_inv := by
    apply NumberField.RingOfIntegers.coe_injective
    push_cast [IsPrimitiveRoot.coe_toInteger]
    exact mul_inv_cancel₀ (hζ.ne_zero (NeZero.ne k))
  inv_val := by
    apply NumberField.RingOfIntegers.coe_injective
    push_cast [IsPrimitiveRoot.coe_toInteger]
    exact inv_mul_cancel₀ (hζ.ne_zero (NeZero.ne k))

omit [NumberField K] in
/-- The unit `hζ.unit'` is again a primitive `k`-th root of unity, now in `𝓞 K`. -/
lemma unit'_coe {k : ℕ} [NeZero k] (hζ : IsPrimitiveRoot ζ k) :
    IsPrimitiveRoot (hζ.unit' : 𝓞 K) k :=
  hζ.toInteger_isPrimitiveRoot

omit [NumberField K] in
/-- `(hζ.unit' : 𝓞 K) = hζ.toInteger`, holding by `rfl`. Not a global `simp` lemma (the descent
files state results in the `unit'` form); used to bridge to Mathlib lemmas phrased via
`toInteger`. -/
lemma coe_unit' {k : ℕ} [NeZero k] (hζ : IsPrimitiveRoot ζ k) :
    (hζ.unit' : 𝓞 K) = hζ.toInteger := rfl

omit [NumberField K] in
/-- `hζ.unit' ^ k = 1` (the unit `hζ.unit'` is a `k`-th root of unity). -/
lemma unit'_pow {k : ℕ} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : hζ.unit' ^ k = 1 := by
  ext
  simpa [coe_unit'] using hζ.pow_eq_one

omit [NumberField K] in
/-- flt-regular's `η` (`(hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne k)).unit`) equals our
`hζ.unit'` (same value `hζ.toInteger`). A `simp` lemma so goals stated via flt-regular's `η`
normalize to the `unit'` form the descent files are written against. -/
lemma toInteger_isUnit_unit {k : ℕ} [NeZero k] (hζ : IsPrimitiveRoot ζ k) :
    (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne k)).unit = hζ.unit' := Units.ext rfl

end IsPrimitiveRoot
