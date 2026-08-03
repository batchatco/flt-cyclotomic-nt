import CyclotomicNT.KummerLogDeriv
import CyclotomicNT.HerbrandBernoulli
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.Algebra.CharP.Quotient
import Mathlib.NumberTheory.NumberField.Norm

/-!
# The reduction `π : F_p[ℤ/p] → 𝓞/p` for `ℚ(ζ_p)`

The ring homomorphism `π : P → 𝓞 k₀ ⧸ (p)` sending `Xᵏ ↦ ζ̄ᵏ`, connecting the group-algebra
log-derivative machinery (`KummerLogDeriv`) to the arithmetic of `ℚ(ζ_p)`:

* `CharP (𝓞/p) p` (so `𝓞/p` is an `F_p`-algebra);
* `piRed` with `piRed_single : π(Xᵏ·c) = c·ζ̄^{k.val}`;
* `piRed_nelt : π(N) = 0` (since `∑_{j<p} ζʲ = 0`). -/

open Finset NumberField AddMonoidAlgebra CyclotomicNT.KummerLog

namespace CyclotomicNT

namespace KummerLog

variable {p : ℕ} [hpri : Fact p.Prime] {k₀ : Type*} [Field k₀] [NumberField k₀]
  [IsCyclotomicExtension {p} ℚ k₀] {ζ : k₀} (hζ : IsPrimitiveRoot ζ p)

/-- `p` is not a unit in `𝓞 k₀` (its norm is `p^{p−1} ≠ ±1`). -/
theorem natCast_p_nonunit : (p : 𝓞 k₀) ∈ nonunits (𝓞 k₀) := by
  intro hu
  haveI := IsCyclotomicExtension.numberField {p} ℚ k₀
  rw [NumberField.isUnit_iff_norm, RingOfIntegers.coe_norm] at hu
  have hcast : ((p : 𝓞 k₀) : k₀) = algebraMap ℚ k₀ (p : ℚ) := by push_cast; rfl
  rw [hcast, Algebra.norm_algebraMap] at hu
  have hrank : 0 < Module.finrank ℚ k₀ := Module.finrank_pos
  have hgt : (1 : ℚ) < (p : ℚ) ^ Module.finrank ℚ k₀ := by
    have hp1 : (1 : ℚ) < p := by exact_mod_cast hpri.out.one_lt
    calc (1 : ℚ) < p := hp1
      _ ≤ (p : ℚ) ^ Module.finrank ℚ k₀ := le_self_pow₀ hp1.le (by omega)
  rw [abs_of_pos (by positivity)] at hu
  exact absurd hu hgt.ne'

variable (k₀) in
/-- The mod-`p` ring of integers. -/
abbrev OmodP (p : ℕ) := 𝓞 k₀ ⧸ (Ideal.span {(p : 𝓞 k₀)})

instance : CharP (OmodP k₀ p) p := CharP.quotient _ p natCast_p_nonunit

noncomputable instance : Algebra (ZMod p) (OmodP k₀ p) :=
  (ZMod.castHom dvd_rfl (OmodP k₀ p)).toAlgebra

/-- `ζ̄ ∈ 𝓞/p`. -/
noncomputable def zetaBar : OmodP k₀ p := Ideal.Quotient.mk _ hζ.toInteger

omit [NumberField k₀] [IsCyclotomicExtension {p} ℚ k₀] in
theorem zetaBar_pow_p : (zetaBar (k₀ := k₀) hζ) ^ p = 1 := by
  rw [zetaBar, ← map_pow, ← map_one (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 k₀)}))]
  congr 1
  apply FaithfulSMul.algebraMap_injective (𝓞 k₀) k₀
  have ht : algebraMap (𝓞 k₀) k₀ hζ.toInteger = ζ := hζ.coe_toInteger
  rw [map_pow, map_one, ht]
  exact hζ.pow_eq_one

omit hpri in
/-- Exponents of `p`-th roots of unity only matter mod `p`. -/
theorem pow_val_mod {M : Type*} [Monoid M] {x : M} (hx : x ^ p = 1) (m : ℕ) :
    x ^ (m % p) = x ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m p]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

/-- `k ↦ ζ̄^{k.val}` as a monoid hom `Multiplicative (ℤ/p) →* 𝓞/p`. -/
noncomputable def zetaPowHom : Multiplicative (ZMod p) →* OmodP k₀ p where
  toFun k := (zetaBar hζ) ^ (Multiplicative.toAdd k).val
  map_one' := by
    change (zetaBar hζ) ^ (0 : ZMod p).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' k l := by
    change (zetaBar hζ) ^ ((Multiplicative.toAdd k + Multiplicative.toAdd l : ZMod p)).val
      = (zetaBar hζ) ^ (Multiplicative.toAdd k).val * (zetaBar hζ) ^ (Multiplicative.toAdd l).val
    rw [ZMod.val_add, pow_val_mod (zetaBar_pow_p hζ), pow_add]

/-- **The reduction** `π : F_p[ℤ/p] → 𝓞/p`, `Xᵏ ↦ ζ̄ᵏ`. -/
noncomputable def piRed : P p →ₐ[ZMod p] OmodP k₀ p :=
  AddMonoidAlgebra.lift (ZMod p) (OmodP k₀ p) (ZMod p) (zetaPowHom hζ)

@[simp] theorem piRed_single (k c : ZMod p) :
    piRed hζ (single k c) = c • (zetaBar hζ) ^ k.val := by
  rw [piRed, AddMonoidAlgebra.lift_single]
  rfl

omit [NumberField k₀] [IsCyclotomicExtension {p} ℚ k₀] in
/-- The geometric relation in `𝓞/p`: `∑_{k} ζ̄^{k.val} = 0`. -/
theorem sum_zetaBar_pow : (∑ k : ZMod p, (zetaBar (k₀ := k₀) hζ) ^ k.val) = 0 := by
  rw [sum_val_eq_sum_range (p := p) (fun j => (zetaBar hζ) ^ j)]
  have hgeom : (∑ j ∈ Finset.range p, hζ.toInteger ^ j) = 0 :=
    hζ.toInteger_isPrimitiveRoot.geom_sum_eq_zero hpri.out.one_lt
  calc (∑ j ∈ Finset.range p, (zetaBar (k₀ := k₀) hζ) ^ j)
      = Ideal.Quotient.mk _ (∑ j ∈ Finset.range p, hζ.toInteger ^ j) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [zetaBar, ← map_pow]
    _ = 0 := by rw [hgeom, map_zero]

/-- `π` of an arbitrary element as a full sum. -/
theorem piRed_eq_sum (d : P p) :
    piRed hζ d = ∑ k : ZMod p, d k • (zetaBar (k₀ := k₀) hζ) ^ k.val := by
  conv_lhs => rw [support_decomp d]
  rw [map_sum, Finset.sum_congr rfl fun k _ => piRed_single hζ k (d k)]
  refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
  rw [Finsupp.notMem_support_iff.mp hk, zero_smul]

/-- **The kernel of `π` is `F_p·N`**: an element mapping to `0` is the constant multiple of
the norm element given by its `(−1)`-coefficient. -/
theorem eq_smul_nelt_of_piRed_eq_zero {d : P p} (hd : piRed hζ d = 0) :
    d = (d (-1)) • nelt := by
  classical
  set c := d (-1) with hc
  -- the centered coefficients sum to zero against the powers of ζ̄
  have hsum : (∑ k : ZMod p, (d k - c) • (zetaBar (k₀ := k₀) hζ) ^ k.val) = 0 := by
    have h1 : (∑ k : ZMod p, d k • (zetaBar (k₀ := k₀) hζ) ^ k.val) = 0 := by
      rw [← piRed_eq_sum hζ d, hd]
    have h2 : (∑ k : ZMod p, c • (zetaBar (k₀ := k₀) hζ) ^ k.val) = 0 := by
      rw [← Finset.smul_sum, sum_zetaBar_pow hζ, smul_zero]
    rw [Finset.sum_congr rfl fun k _ => sub_smul (d k) c ((zetaBar (k₀ := k₀) hζ) ^ k.val),
      Finset.sum_sub_distrib, h1, h2, sub_zero]
  -- coefficients away from `−1` vanish, via the integral power basis
  have hcoords : ∀ k : ZMod p, k ≠ -1 → d k - c = 0 := by
    intro k₀' hk₀
    -- the integer lift over the erased sum
    set E : 𝓞 k₀ := ∑ k ∈ Finset.univ.erase (-1 : ZMod p),
      (((d k - c).val : ℤ)) • hζ.toInteger ^ k.val with hE
    have hmkE : Ideal.Quotient.mk (Ideal.span {(p : 𝓞 k₀)}) E = 0 := by
      rw [hE, map_sum]
      have hterm : ∀ k : ZMod p,
          Ideal.Quotient.mk (Ideal.span {(p : 𝓞 k₀)})
            ((((d k - c).val : ℤ)) • hζ.toInteger ^ k.val)
          = (d k - c) • (zetaBar (k₀ := k₀) hζ) ^ k.val := by
        intro k
        rw [map_zsmul, zsmul_eq_mul, Algebra.smul_def]
        congr 1
        · change ((((d k - c).val : ℤ)) : OmodP k₀ p) = algebraMap (ZMod p) (OmodP k₀ p) (d k - c)
          rw [show algebraMap (ZMod p) (OmodP k₀ p) (d k - c)
              = ZMod.castHom dvd_rfl (OmodP k₀ p) (d k - c) from rfl, ZMod.castHom_apply,
            ZMod.cast_eq_val]
          push_cast
          rfl
      rw [Finset.sum_congr rfl fun k _ => hterm k]
      -- extend the erased sum: the `−1` term has coefficient `c − c = 0`
      have hext : (∑ k ∈ Finset.univ.erase (-1 : ZMod p),
          (d k - c) • (zetaBar (k₀ := k₀) hζ) ^ k.val)
          = ∑ k : ZMod p, (d k - c) • (zetaBar (k₀ := k₀) hζ) ^ k.val := by
        refine Finset.sum_subset (Finset.erase_subset _ _) fun k _ hk => ?_
        have hkm : k = -1 := by
          by_contra h
          exact hk (Finset.mem_erase.mpr ⟨h, Finset.mem_univ k⟩)
        rw [hkm, ← hc, sub_self, zero_smul]
      rw [hext]
      exact hsum
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmkE
    obtain ⟨y, hy⟩ := hmkE
    set pb := hζ.integralPowerBasis with hpb
    have hdim : pb.dim = p - 1 := by
      rw [hpb, hζ.integralPowerBasis_dim, Nat.totient_prime hpri.out]
    have hneg1 : ((-1 : ZMod p)).val = p - 1 := by
      have he : (-1 : ZMod p) = ((p - 1 : ℕ) : ZMod p) := by
        have h0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
        push_cast [Nat.cast_sub hpri.out.one_le, h0]
        ring
      rw [he, ZMod.val_natCast_of_lt (by have := hpri.out.one_lt; omega)]
    have hvalne : ∀ k : ZMod p, k ≠ -1 → k.val < p - 1 := by
      intro k hk
      have h1 := ZMod.val_lt k
      have h2 : k.val ≠ p - 1 := by
        intro h
        apply hk
        apply ZMod.val_injective
        rw [h, hneg1]
      omega
    have hk0lt : k₀'.val < pb.dim := by
      rw [hdim]
      exact hvalne k₀' hk₀
    have hterm2 : ∀ k ∈ Finset.univ.erase (-1 : ZMod p),
        pb.basis.repr ((((d k - c).val : ℤ)) • hζ.toInteger ^ k.val) ⟨k₀'.val, hk0lt⟩
        = if k = k₀' then (((d k - c).val : ℤ)) else 0 := by
      intro k hk
      have hklt : k.val < pb.dim := by
        rw [hdim]
        exact hvalne k (Finset.mem_erase.mp hk).1
      have hgen : hζ.toInteger ^ k.val = pb.basis ⟨k.val, hklt⟩ := by
        rw [pb.coe_basis]
        change hζ.toInteger ^ k.val = pb.gen ^ k.val
        rw [hpb, hζ.integralPowerBasis_gen]
      rw [map_smul, hgen, pb.basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
      by_cases hkk : k = k₀'
      · rw [if_pos (Fin.mk_eq_mk.mpr (by rw [hkk])), if_pos hkk, smul_eq_mul, mul_one]
      · have hne : (⟨k.val, hklt⟩ : Fin pb.dim) ≠ ⟨k₀'.val, hk0lt⟩ := by
          intro h
          exact hkk (ZMod.val_injective p (Fin.mk_eq_mk.mp h))
        rw [if_neg hne, if_neg hkk, smul_zero]
    have hreprE : pb.basis.repr E ⟨k₀'.val, hk0lt⟩ = (((d k₀' - c).val : ℤ)) := by
      rw [hE, map_sum, Finsupp.finsetSum_apply, Finset.sum_congr rfl hterm2,
        Finset.sum_ite_eq' (Finset.univ.erase (-1 : ZMod p)) k₀',
        if_pos (Finset.mem_erase.mpr ⟨hk₀, Finset.mem_univ _⟩)]
    have hdvd : (p : ℤ) ∣ (((d k₀' - c).val : ℤ)) := by
      have hyz : E = ((p : ℤ)) • y := by
        rw [hy, zsmul_eq_mul]
        push_cast
        ring
      rw [← hreprE, hyz, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact ⟨_, rfl⟩
    have hval0 : (d k₀' - c).val = 0 := by
      have hd2 : p ∣ (d k₀' - c).val := by exact_mod_cast hdvd
      exact Nat.eq_zero_of_dvd_of_lt hd2 (ZMod.val_lt _)
    rwa [ZMod.val_eq_zero] at hval0
  -- conclude `d = c • N` coefficientwise
  ext m
  change d m = c * (nelt : P p) m
  rw [nelt_apply, mul_one]
  by_cases hm : m = -1
  · rw [hm, hc]
  · have h := hcoords m hm
    linear_combination h

/-- **Two `π`-preimages differ by a multiple of `N`** — with `ell_eq_of_val_eq_add_smul_N`,
the `ℓ_n` are well-defined on `π`-images. -/
theorem exists_smul_nelt_of_piRed_eq {f g : P p} (h : piRed hζ f = piRed hζ g) :
    ∃ c : ZMod p, f = g + c • nelt := by
  have hd : piRed hζ (f - g) = 0 := by rw [map_sub, h, sub_self]
  exact ⟨(f - g) (-1), by linear_combination eq_smul_nelt_of_piRed_eq_zero hζ hd⟩

/-- **`ℓ_n` descends through `π`**: units of `P` with equal images in `𝓞/p` have equal
logarithmic derivatives. -/
theorem ell_eq_of_piRed_eq {n : ℕ} (hn : 2 ≤ n)
    (h1d : ¬ (p - 1) ∣ (n - 1)) (h2d : ¬ (p - 1) ∣ n)
    {γ γ' : (P p)ˣ} (h : piRed hζ ((γ : P p)) = piRed hζ ((γ' : P p))) :
    ell n γ = ell n γ' := by
  obtain ⟨c, hc⟩ := exists_smul_nelt_of_piRed_eq hζ h.symm
  exact (ell_eq_of_val_eq_add_smul_N hn h1d h2d γ γ' c hc).symm

end KummerLog

end CyclotomicNT
