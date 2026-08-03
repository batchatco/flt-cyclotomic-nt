import CyclotomicNT.CyclotomicUnitGroup
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Archimedean side of `ℚ(ζ_p)` — the embeddings `σ_b`, the places `w_b`, and `w_b(ξ_a)`

First brick of the `cyclotomic_unit_index` (Washington Thm 8.2) regulator computation.  For
`b ∈ (ℤ/p)ˣ` we construct the complex embedding `σ_b : K → ℂ` determined by `ζ ↦ e(b/p)`
(`e(x) = exp(2πix)`, i.e. `ZMod.stdAddChar b` — the SAME normalization as the analytic
`L(1,χ)` formulas in `EvenLOneValue.lean`), show `b ↦ σ_b` is a bijection onto the embeddings
with `conj ∘ σ_b = σ_{-b}`, and define the infinite places `w_b = InfinitePlace.mk σ_b`
(`w_b = w_{b'}` iff `b' = ±b`, and every place is some `w_b`).

The payoff is the **regulator entry**: for Washington's real cyclotomic unit
`ξ_a = ζ^{(1−a)/2}·(ζ^a−1)/(ζ−1)`,

  `w_b(ξ_a) = ‖1 − e(ab/p)‖ / ‖1 − e(b/p)‖`, so
  `log w_b(ξ_a) = log‖1 − e(ab/p)‖ − log‖1 − e(b/p)‖`,

matching the entries `log‖1 − ζ^a‖` of `gaussSum_mul_LFunction_one_even` exactly.
-/

namespace CyclotomicNT

open NumberField Finset

section StdAddChar

-- The `stdAddChar` facts hold for any modulus `n ≠ 0` (used at both `n = p` and `n = (p−1)/2`).
variable {n : ℕ} [NeZero n]

/-- `ZMod.stdAddChar 1 = e(1/n) = exp(2πi/n)` is a primitive `n`-th root of unity. -/
theorem isPrimitiveRoot_stdAddChar_one :
    IsPrimitiveRoot (ZMod.stdAddChar (1 : ZMod n)) n := by
  have h := ZMod.stdAddChar_coe (N := n) 1
  rw [Int.cast_one] at h
  rw [h]
  simpa using Complex.isPrimitiveRoot_exp n (NeZero.ne n)

/-- Powers of `stdAddChar` values: `e(x/n)^k = e(kx/n)`. -/
theorem stdAddChar_pow (x : ZMod n) (k : ℕ) :
    ZMod.stdAddChar x ^ k = ZMod.stdAddChar ((k : ZMod n) * x) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]

/-- For a unit `b ∈ (ℤ/n)ˣ`, `e(b/n)` is a primitive `n`-th root of unity. -/
theorem isPrimitiveRoot_stdAddChar_unit (b : (ZMod n)ˣ) :
    IsPrimitiveRoot (ZMod.stdAddChar (b : ZMod n)) n := by
  have hb : ZMod.stdAddChar ((b : ZMod n)) = ZMod.stdAddChar (1 : ZMod n) ^ (b : ZMod n).val := by
    rw [stdAddChar_pow, mul_one, ZMod.natCast_val, ZMod.cast_id]
  rw [hb]
  exact isPrimitiveRoot_stdAddChar_one.pow_of_coprime _ (ZMod.val_coe_unit_coprime b)

/-- `stdAddChar` values lie on the unit circle. -/
theorem norm_stdAddChar (x : ZMod n) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

/-- `e(x/n) ≠ 1` for `x ≠ 0` — nonvanishing of the regulator-entry denominators. -/
theorem stdAddChar_ne_one {x : ZMod n} (hx : x ≠ 0) : ZMod.stdAddChar x ≠ 1 := fun h =>
  hx (ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one _).symm))

/-- Complex conjugation inverts `stdAddChar` values: `conj e(x/n) = e(−x/n)`. -/
theorem conj_stdAddChar (x : ZMod n) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (norm_stdAddChar x)]

end StdAddChar

variable {p : ℕ} [hpri : Fact p.Prime]

variable {K : Type*} [Field K] [CharZero K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- **The complex embedding `σ_b`** of `K = ℚ(ζ_p)` determined by `ζ ↦ e(b/p)`, `b ∈ (ℤ/p)ˣ`
(via `IsPrimitiveRoot.embeddingsEquivPrimitiveRoots`). -/
noncomputable def cycEmbedding (b : (ZMod p)ˣ) : K →+* ℂ :=
  ((hζ.embeddingsEquivPrimitiveRoots ℂ
      (Polynomial.cyclotomic.irreducible_rat hpri.out.pos)).symm
    ⟨ZMod.stdAddChar (b : ZMod p), (mem_primitiveRoots hpri.out.pos).mpr
      (isPrimitiveRoot_stdAddChar_unit b)⟩).toRingHom

/-- The defining property: `σ_b ζ = e(b/p)`. -/
@[simp] theorem cycEmbedding_apply_zeta (b : (ZMod p)ˣ) :
    cycEmbedding hζ b ζ = ZMod.stdAddChar (b : ZMod p) := by
  have h := hζ.embeddingsEquivPrimitiveRoots_apply_coe ℂ
    (Polynomial.cyclotomic.irreducible_rat hpri.out.pos)
    ((hζ.embeddingsEquivPrimitiveRoots ℂ
        (Polynomial.cyclotomic.irreducible_rat hpri.out.pos)).symm
      ⟨ZMod.stdAddChar (b : ZMod p), (mem_primitiveRoots hpri.out.pos).mpr
        (isPrimitiveRoot_stdAddChar_unit b)⟩)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

include hζ in
/-- Two complex embeddings of `K = ℚ(ζ_p)` agreeing at `ζ` are equal (power-basis rigidity). -/
theorem cycEmbedding_ext {φ ψ : K →+* ℂ} (h : φ ζ = ψ ζ) : φ = ψ := by
  have h2 : φ.toRatAlgHom = ψ.toRatAlgHom :=
    (hζ.powerBasis ℚ).algHom_ext (by rw [IsPrimitiveRoot.powerBasis_gen ℚ hζ]; exact h)
  ext x
  exact DFunLike.congr_fun h2 x

theorem cycEmbedding_injective : Function.Injective (cycEmbedding hζ) := fun b c h => by
  have hbc : ZMod.stdAddChar (b : ZMod p) = ZMod.stdAddChar (c : ZMod p) := by
    rw [← cycEmbedding_apply_zeta hζ b, ← cycEmbedding_apply_zeta hζ c, h]
  exact Units.ext (ZMod.injective_stdAddChar hbc)

/-- Every complex embedding of `K = ℚ(ζ_p)` is `σ_b` for some `b ∈ (ℤ/p)ˣ` — `φ ζ` is a primitive
root `e(1/p)^i = e(i/p)` with `i` coprime to `p`. -/
theorem cycEmbedding_surjective : Function.Surjective (cycEmbedding hζ) := fun φ => by
  have hφζ : IsPrimitiveRoot (φ ζ) p := hζ.map_of_injective φ.injective
  obtain ⟨i, -, hicop, hi⟩ :=
    (isPrimitiveRoot_stdAddChar_one (n := p)).isPrimitiveRoot_iff.mp hφζ
  refine ⟨ZMod.unitOfCoprime i hicop, cycEmbedding_ext hζ ?_⟩
  rw [cycEmbedding_apply_zeta, ZMod.coe_unitOfCoprime, ← hi, stdAddChar_pow, mul_one]

/-- Complex conjugation acts on the embeddings by `b ↦ −b`: `conj ∘ σ_b = σ_{−b}`. -/
theorem conjugate_cycEmbedding (b : (ZMod p)ˣ) :
    ComplexEmbedding.conjugate (cycEmbedding hζ b) = cycEmbedding hζ (-b) := by
  refine cycEmbedding_ext hζ ?_
  rw [ComplexEmbedding.conjugate_coe_eq, cycEmbedding_apply_zeta, cycEmbedding_apply_zeta,
    conj_stdAddChar, Units.val_neg]

/-- **The infinite place `w_b`** of `K = ℚ(ζ_p)` attached to `σ_b`. -/
noncomputable def cycPlace (b : (ZMod p)ˣ) : InfinitePlace K :=
  InfinitePlace.mk (cycEmbedding hζ b)

theorem cycPlace_apply (b : (ZMod p)ˣ) (x : K) :
    cycPlace hζ b x = ‖cycEmbedding hζ b x‖ :=
  InfinitePlace.apply _ _

/-- The places pair up under negation: `w_{−b} = w_b` (conjugate embeddings). -/
@[simp] theorem cycPlace_neg (b : (ZMod p)ˣ) : cycPlace hζ (-b) = cycPlace hζ b := by
  rw [cycPlace, cycPlace, ← conjugate_cycEmbedding hζ b, InfinitePlace.mk_conjugate_eq]

/-- Every infinite place of `ℚ(ζ_p)` is `w_b` for some `b ∈ (ℤ/p)ˣ`. -/
theorem cycPlace_surjective : Function.Surjective (cycPlace hζ) := fun w => by
  obtain ⟨b, hb⟩ := cycEmbedding_surjective hζ (InfinitePlace.embedding w)
  exact ⟨b, by rw [cycPlace, hb, InfinitePlace.mk_embedding]⟩

section RegulatorEntry

variable [NumberField K]

omit [NumberField K] in
/-- **The archimedean value of the real cyclotomic unit `ξ_a`** (the regulator-entry numerator/
denominator): `‖σ_b(ξ_a)‖ = ‖1 − e(ab/p)‖ / ‖1 − e(b/p)‖`.  The `ζ`-power prefactor of `ξ_a` has
modulus `1` and the geometric sum `∑_{i<a} ζ^i` maps to `(e(ab/p) − 1)/(e(b/p) − 1)`. -/
theorem norm_cycEmbedding_realCyclotomicUnit (b : (ZMod p)ˣ) (a : ℕ) (ha : a.Coprime p) :
    ‖cycEmbedding hζ b (realCyclotomicUnit hζ a ha : K)‖
      = ‖1 - ZMod.stdAddChar ((a : ZMod p) * (b : ZMod p))‖
        / ‖1 - ZMod.stdAddChar (b : ZMod p)‖ := by
  set z : ℂ := ZMod.stdAddChar ((b : ZMod p)) with hz
  have hz_ne_one : z ≠ 1 := stdAddChar_ne_one (b.ne_zero)
  -- map the field value of ξ_a through σ_b
  have hmap : cycEmbedding hζ b (realCyclotomicUnit hζ a ha : K)
      = z ^ ((1 - (a : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ)) * ∑ i ∈ range a, z ^ (i : ℤ) := by
    rw [coe_realCyclotomicUnit, map_mul, map_zpow₀, map_sum, cycEmbedding_apply_zeta, ← hz]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [map_zpow₀, cycEmbedding_apply_zeta, ← hz]
  -- the prefactor has modulus 1; the geometric sum gives the ratio
  have hgeom : ∑ i ∈ range a, z ^ (i : ℤ) = (z ^ a - 1) / (z - 1) := by
    rw [← geom_sum_eq hz_ne_one]
    exact Finset.sum_congr rfl fun i _ => by rw [zpow_natCast]
  rw [hmap, norm_mul, norm_zpow, hz, norm_stdAddChar, one_zpow, one_mul, hgeom, norm_div,
    norm_sub_rev (z ^ a), norm_sub_rev z, ← hz, stdAddChar_pow]

omit [NumberField K] in
/-- The place value `w_b(ξ_a) = ‖1 − e(ab/p)‖ / ‖1 − e(b/p)‖`. -/
theorem cycPlace_realCyclotomicUnit (b : (ZMod p)ˣ) (a : ℕ) (ha : a.Coprime p) :
    cycPlace hζ b (realCyclotomicUnit hζ a ha : K)
      = ‖1 - ZMod.stdAddChar ((a : ZMod p) * (b : ZMod p))‖
        / ‖1 - ZMod.stdAddChar (b : ZMod p)‖ := by
  rw [cycPlace_apply, norm_cycEmbedding_realCyclotomicUnit]

omit [NumberField K] in
/-- **The logarithmic regulator entry**:
`log w_b(ξ_a) = log‖1 − e(ab/p)‖ − log‖1 − e(b/p)‖` — the circulant-matrix entries (in the
variable `ab`) minus a per-row constant, exactly the shape fed to `det_circulant_eq_prod` and
matched against `gaussSum_mul_LFunction_one_even`. -/
theorem log_cycPlace_realCyclotomicUnit (b : (ZMod p)ˣ) (a : ℕ) (ha : a.Coprime p) :
    Real.log (cycPlace hζ b (realCyclotomicUnit hζ a ha : K))
      = Real.log ‖1 - ZMod.stdAddChar ((a : ZMod p) * (b : ZMod p))‖
        - Real.log ‖1 - ZMod.stdAddChar (b : ZMod p)‖ := by
  have hb_ne : (1 : ℂ) - ZMod.stdAddChar (b : ZMod p) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (stdAddChar_ne_one b.ne_zero))
  have hab_ne : (1 : ℂ) - ZMod.stdAddChar ((a : ZMod p) * (b : ZMod p)) ≠ 0 := by
    refine sub_ne_zero.mpr (Ne.symm (stdAddChar_ne_one ?_))
    have ha0 : (a : ZMod p) ≠ 0 := by
      intro h0
      have hdvd : p ∣ a := (CharP.cast_eq_zero_iff (ZMod p) p a).mp h0
      have h1 : p ∣ Nat.gcd a p := Nat.dvd_gcd hdvd dvd_rfl
      rw [ha.gcd_eq_one] at h1
      exact hpri.out.ne_one (Nat.dvd_one.mp h1)
    exact mul_ne_zero ha0 b.ne_zero
  rw [cycPlace_realCyclotomicUnit, Real.log_div (norm_ne_zero_iff.mpr hab_ne)
    (norm_ne_zero_iff.mpr hb_ne)]

end RegulatorEntry

end CyclotomicNT
