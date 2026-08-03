import CyclotomicNT.EigenOperator

/-!
# Thm 8.14, piece 3a-iii (δ) — towards the eigenvector relation `T(Ēᵢ) = g^i·Ēᵢ`

Working in `V = E/E^p` with the class map `vc a := [ξ_a]`, this collects the `V`-level consequences
    of
the element identities: `vc` is `p`-periodic (β) and reflection-invariant (α), the latter because
`ξ_{p−x} = −ξ_x` and `−1 = (−1)^p ∈ E^p` so `[−1] = 0`.  These let the reindex `a ↦ (a·g reduced
    into
[1,(p−1)/2])` be carried out in `V`. -/

namespace CyclotomicNT

open scoped NumberField
open NumberField NumberField.IsCMField

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}

/-- `−1` is a real unit. -/
theorem neg_one_mem_realUnits : (-1 : (𝓞 K)ˣ) ∈ realUnits K := by
  rw [mem_realUnits_iff_complexConj]; push_cast; rw [map_neg, map_one]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- `[−1] = 0` in `V = E/E^p`, since `−1 = (−1)^p ∈ E^p` (`p` odd). -/
theorem vOf_neg_one (hp2 : p ≠ 2) :
    (vOf ⟨(-1 : (𝓞 K)ˣ), neg_one_mem_realUnits⟩ : ModN (Additive (realUnits K)) p) = 0 := by
  have hp1 : Odd p := hpri.out.odd_of_ne_two hp2
  rw [vOf]
  refine (Submodule.Quotient.mk_eq_zero _).mpr
    ⟨Additive.ofMul (⟨-1, neg_one_mem_realUnits⟩ : realUnits K), ?_⟩
  change p • Additive.ofMul (⟨(-1 : (𝓞 K)ˣ), neg_one_mem_realUnits⟩ : realUnits K) = _
  rw [← ofMul_pow]
  congr 1
  ext
  exact hp1.neg_one_pow

/-- The class `v_a = [ξ_a] ∈ V` of the real cyclotomic unit. -/
noncomputable def vc (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (a : ℕ) (ha : a.Coprime p) :
    ModN (Additive (realUnits K)) p :=
  vOf ⟨realCyclotomicUnit hζ a ha, realCyclotomicUnit_mem_realUnits hζ hp a ha⟩

omit [IsCyclotomicExtension {p} ℚ K] in
/-- `v_a` depends only on `a (mod p)` (periodicity β). -/
theorem vc_periodic (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (j j' : ℕ) (hjj' : j ≡ j' [MOD p])
    (hj : j.Coprime p) (hj' : j'.Coprime p) : vc hζ hp j hj = vc hζ hp j' hj' := by
  rw [vc, vc]
  congr 1
  exact Subtype.ext (realCyclotomicUnit_periodic hζ j j' hjj' hj hj')

omit [IsCyclotomicExtension {p} ℚ K] in
/-- `v_{p−x} = v_x` in `V` (reflection α, with `[−1] = 0`). -/
theorem vc_reflect (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (x : ℕ) (hxlt : x < p)
    (hx : x.Coprime p) (hpx : (p - x).Coprime p) : vc hζ hp (p - x) hpx = vc hζ hp x hx := by
  have hsub : (⟨realCyclotomicUnit hζ (p - x) hpx,
        realCyclotomicUnit_mem_realUnits hζ hp (p - x) hpx⟩ : realUnits K)
      = (⟨-1, neg_one_mem_realUnits⟩ : realUnits K)
        * ⟨realCyclotomicUnit hζ x hx, realCyclotomicUnit_mem_realUnits hζ hp x hx⟩ :=
    Subtype.ext (show realCyclotomicUnit hζ (p - x) hpx
        = (-1 : (𝓞 K)ˣ) * realCyclotomicUnit hζ x hx by
      rw [realCyclotomicUnit_reflect hζ hp x hxlt hx hpx, neg_one_mul])
  rw [vc, vc, hsub, vOf_mul, vOf_neg_one hp, zero_add]

/-- **The per-unit eigenvector step**: `T(v_a) = v_{a·g} − v_g` in `V`, from the Galois identity
`σ_g(ξ_a) = ξ_{a·g}·ξ_g⁻¹` (3a-ii) made additive via `vOf_mul`/`vOf_inv`. -/
theorem galV_vc (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (g : (ZMod p)ˣ) (a : ℕ) (ha : a.Coprime p) :
    galV hζ g (vc hζ hp a ha)
      = vc hζ hp (a * (g : ZMod p).val) (Nat.coprime_mul_iff_left.mpr ⟨ha, coprime_val g⟩)
        - vc hζ hp (g : ZMod p).val (coprime_val g) := by
  rw [vc, galV_vOf]
  have hsub : galUnitReal hζ g ⟨realCyclotomicUnit hζ a ha,
        realCyclotomicUnit_mem_realUnits hζ hp a ha⟩
      = (⟨realCyclotomicUnit hζ (a * (g : ZMod p).val)
            (Nat.coprime_mul_iff_left.mpr ⟨ha, coprime_val g⟩),
          realCyclotomicUnit_mem_realUnits hζ hp _ _⟩ : realUnits K)
        * (⟨realCyclotomicUnit hζ (g : ZMod p).val (coprime_val g),
            realCyclotomicUnit_mem_realUnits hζ hp _ _⟩ : realUnits K)⁻¹ :=
    Subtype.ext (show galUnit hζ g (realCyclotomicUnit hζ a ha)
        = realCyclotomicUnit hζ (a * (g : ZMod p).val) _
          * (realCyclotomicUnit hζ (g : ZMod p).val _)⁻¹ from
      galUnit_realCyclotomicUnit hζ g a ha)
  rw [hsub, vOf_mul, vOf_inv, vc, vc, sub_eq_add_neg]

end CyclotomicNT
