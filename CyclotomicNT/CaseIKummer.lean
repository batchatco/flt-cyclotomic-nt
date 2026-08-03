import CyclotomicNT.KummerReduction
import CyclotomicNT.EigenProjection
import CyclotomicNT.Herbrand
import CyclotomicNT.KPlusGalois
import CyclotomicNT.PrimitiveRootUnit
import FltRegular.CaseI.Statement

/-!
# Case I via Kummer's criterion: the assembly

The endgame of the Kummer–Wieferich–Skula route — A. Granville, "The
Kummer–Wieferich–Skula approach to the first case of Fermat's Last Theorem",
in *Advances in Number Theory* (Gouvêa–Yui, eds.), Oxford Univ. Press 1993,
479–498; see also Granville–Powell, "On Sophie Germain type criteria for
Fermat's Last Theorem", Acta Arith. 50 (1988), 265–277, and cf. Sitaraman,
"Vandiver revisited", J. Number Theory 57 (1996), 122–129.
For a Case I solution and `p ∤ B_{p−3}`, the
weight-3 eigencomponent of the class of `I` (where `(x+ζy) = Iᵖ`) must be nontrivial — else
the Stickelberger relation forces `ℓ₃(x+ζy) = 0`, contradicting the Mirimanoff evaluation.
Herbrand then yields `p ∣ B_{p−3}`, contradiction. -/

open Finset NumberField AddMonoidAlgebra IsCyclotomicExtension.Rat
open scoped Pointwise nonZeroDivisors

namespace CyclotomicNT

namespace KummerLog

variable {p : ℕ} [hpri : Fact p.Prime] {k₀ : Type*} [Field k₀] [NumberField k₀]
  [IsCyclotomicExtension {p} ℚ k₀] {ζ : k₀} (hζ : IsPrimitiveRoot ζ p)

/-! ### The descended Galois action on `𝓞/p` and `π`-equivariance -/

/-- The Galois action descends to `𝓞/p`. -/
noncomputable def galBar (a : (ZMod p)ˣ) : OmodP k₀ p →+* OmodP k₀ p :=
  Ideal.quotientMap (Ideal.span {(p : 𝓞 k₀)})
    (MulSemiringAction.toRingHom _ (𝓞 k₀) ((galEquivZMod p k₀).symm a))
    (by
      rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      rw [SetLike.mem_coe, Ideal.mem_comap,
        show (MulSemiringAction.toRingHom _ (𝓞 k₀) ((galEquivZMod p k₀).symm a))
            ((p : ℕ) : 𝓞 k₀) = ((p : ℕ) : 𝓞 k₀) from map_natCast _ p]
      exact Ideal.subset_span rfl)

@[simp] theorem galBar_mk (a : (ZMod p)ˣ) (x : 𝓞 k₀) :
    galBar a (Ideal.Quotient.mk _ x)
      = Ideal.Quotient.mk _ (((galEquivZMod p k₀).symm a) • x) :=
  Ideal.quotientMap_mk

/-- `σ̄_a(ζ̄) = ζ̄^{a.val}`. -/
theorem galBar_zetaBar (a : (ZMod p)ˣ) :
    galBar a (zetaBar (k₀ := k₀) hζ) = (zetaBar hζ) ^ ((a : ZMod p)).val := by
  rw [zetaBar, galBar_mk]
  have hpow : hζ.toInteger ^ p = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 k₀) k₀
    have ht : algebraMap (𝓞 k₀) k₀ hζ.toInteger = ζ := hζ.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζ.pow_eq_one
  have h := galEquivZMod_smul_of_pow_eq p k₀ ((galEquivZMod p k₀).symm a) hpow
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, map_pow]

/-- `galBar` fixes the `ZMod p`-scalars. -/
theorem galBar_smul (a : (ZMod p)ˣ) (c : ZMod p) (x : OmodP k₀ p) :
    galBar a (c • x) = c • galBar a x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  change galBar a ((ZMod.castHom dvd_rfl (OmodP k₀ p)) c) = (ZMod.castHom dvd_rfl (OmodP k₀ p)) c
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast]

/-- **`π` intertwines `σ_a` with `σ̄_a`.** -/
theorem piRed_sigma (a : (ZMod p)ˣ) (f : P p) :
    piRed hζ (sigma a f) = galBar a (piRed hζ f) := by
  conv_lhs => rw [support_decomp f]
  conv_rhs => rw [support_decomp f]
  rw [map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sigma_single, piRed_single, piRed_single, galBar_smul]
  congr 1
  rw [map_pow, galBar_zetaBar, ← pow_mul, ZMod.val_mul,
    pow_val_mod (zetaBar_pow_p hζ)]

/-! ### The `(1−ζ)`-residue criterion and unit lifts -/

omit [NumberField k₀] [IsCyclotomicExtension {p} ℚ k₀] in
/-- Our `toInteger` is flt-regular's `unit'`. -/
theorem unit'_val_eq_toInteger : ((hζ.unit' : (𝓞 k₀)ˣ) : 𝓞 k₀) = hζ.toInteger :=
  Subtype.ext rfl

omit [NumberField k₀] [IsCyclotomicExtension {p} ℚ k₀] in
/-- `(p) ⊆ (ζ−1)`. -/
theorem span_p_le_span_zeta_sub_one :
    Ideal.span {((p : ℕ) : 𝓞 k₀)} ≤ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
  rw [Ideal.span_le]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  exact_mod_cast hζ.p_mem_one_sub_zeta

/-- The residue field at `(ζ−1)` has characteristic `p` (Bézout against `𝔭 ≠ ⊤`). -/
theorem charP_resid :
    CharP (𝓞 k₀ ⧸ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀))) p := by
  constructor
  intro n
  rw [show ((n : ℕ) : 𝓞 k₀ ⧸ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)))
      = Ideal.Quotient.mk _ ((n : ℕ) : 𝓞 k₀) from (map_natCast _ n).symm,
    Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hn
    by_contra hpn
    -- Bézout: `1 = a·p + b·n` lands in `𝔭`, contradicting primality
    have hcop : IsCoprime ((p : ℕ) : ℤ) ((n : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.Prime.coprime_iff_not_dvd hpri.out).mpr hpn
    obtain ⟨a, b, hab⟩ := hcop
    have h1 : (1 : 𝓞 k₀) ∈ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
      have hmem : ((a * (p : ℕ) + b * (n : ℕ) : ℤ) : 𝓞 k₀)
          ∈ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
        push_cast
        exact Ideal.add_mem _
          (Ideal.mul_mem_left _ _ (by exact_mod_cast hζ.p_mem_one_sub_zeta))
          (Ideal.mul_mem_left _ _ hn)
      rw [hab] at hmem
      simpa using hmem
    have hprime := hζ.isPrime_one_sub_zeta
    exact hprime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · rintro ⟨m, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ (by exact_mod_cast hζ.p_mem_one_sub_zeta)

/-- The canonical map `ZMod p → 𝓞/(ζ−1)`. -/
noncomputable def chiRes : ZMod p →+* 𝓞 k₀ ⧸ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) :=
  haveI := charP_resid hζ
  ZMod.castHom dvd_rfl _

/-- The composite `P → 𝓞/p → 𝓞/(ζ−1)` is the augmentation. -/
theorem factor_piRed (f : P p) :
    Ideal.Quotient.factor (span_p_le_span_zeta_sub_one hζ) (piRed hζ f)
      = chiRes hζ (eps f) := by
  haveI := charP_resid hζ
  have hζ1 : Ideal.Quotient.mk (Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)))
      hζ.toInteger = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      ← unit'_val_eq_toInteger hζ]
    exact Ideal.subset_span rfl
  conv_lhs => rw [support_decomp f]
  rw [map_sum, map_sum]
  have hterm : ∀ k ∈ f.support,
      Ideal.Quotient.factor (span_p_le_span_zeta_sub_one hζ) (piRed hζ (single k (f k)))
      = chiRes hζ (f k) := by
    intro k _
    rw [piRed_single, Algebra.smul_def, map_mul]
    have h2 : Ideal.Quotient.factor (span_p_le_span_zeta_sub_one hζ)
        ((zetaBar (k₀ := k₀) hζ) ^ k.val) = 1 := by
      rw [map_pow, zetaBar,
        show Ideal.Quotient.factor (span_p_le_span_zeta_sub_one hζ)
          (Ideal.Quotient.mk _ hζ.toInteger)
          = Ideal.Quotient.mk _ hζ.toInteger from Ideal.Quotient.factor_mk _ _,
        hζ1, one_pow]
    rw [h2, mul_one]
    change Ideal.Quotient.factor (span_p_le_span_zeta_sub_one hζ)
        ((ZMod.castHom dvd_rfl (OmodP k₀ p)) (f k)) = chiRes hζ (f k)
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast, chiRes, ZMod.castHom_apply,
      ZMod.cast_eq_val]
  rw [Finset.sum_congr rfl hterm, ← map_sum, eps_apply]

/-- The residue criterion: a lift of `mk α` with `α ∉ (ζ−1)` has nonzero augmentation. -/
theorem eps_ne_zero_of_lift {f : P p} {α : 𝓞 k₀}
    (hf : piRed hζ f = Ideal.Quotient.mk _ α)
    (hα : α ∉ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀))) : eps f ≠ 0 := by
  intro h0
  have h1 := factor_piRed hζ f
  rw [h0, map_zero, hf,
    show Ideal.Quotient.factor (span_p_le_span_zeta_sub_one hζ) (Ideal.Quotient.mk _ α)
      = Ideal.Quotient.mk _ α from Ideal.Quotient.factor_mk _ _] at h1
  exact hα (Ideal.Quotient.eq_zero_iff_mem.mp h1)

/-- **Unit-lift existence**: every residue away from `(ζ−1)` lifts to a `P`-unit. -/
theorem exists_unit_lift {α : 𝓞 k₀}
    (hα : α ∉ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀))) :
    ∃ γ : (P p)ˣ, piRed hζ ((γ : P p)) = Ideal.Quotient.mk _ α := by
  classical
  set pb := hζ.integralPowerBasis with hpb
  have hdimlt : pb.dim < p := by
    rw [hpb, hζ.integralPowerBasis_dim, Nat.totient_prime hpri.out]
    have := hpri.out.two_le
    omega
  set f₀ : P p := ∑ i : Fin pb.dim,
    single (((i : ℕ) : ZMod p)) (((pb.basis.repr α i : ℤ) : ZMod p)) with hf₀
  have hπ : piRed hζ f₀ = Ideal.Quotient.mk _ α := by
    rw [hf₀, map_sum]
    have hterm : ∀ i : Fin pb.dim,
        piRed hζ (single (((i : ℕ) : ZMod p)) (((pb.basis.repr α i : ℤ) : ZMod p)))
        = Ideal.Quotient.mk (Ideal.span {((p : ℕ) : 𝓞 k₀)})
            ((pb.basis.repr α i : ℤ) • hζ.toInteger ^ (i : ℕ)) := by
      intro i
      rw [piRed_single,
        show (((i : ℕ) : ZMod p)).val = (i : ℕ) from
          ZMod.val_natCast_of_lt (lt_trans i.isLt hdimlt),
        Algebra.smul_def]
      change (ZMod.castHom dvd_rfl (OmodP k₀ p)) (((pb.basis.repr α i : ℤ) : ZMod p))
          * (zetaBar hζ) ^ (i : ℕ) = _
      rw [show ((ZMod.castHom dvd_rfl (OmodP k₀ p)) (((pb.basis.repr α i : ℤ) : ZMod p)))
          = (((pb.basis.repr α i : ℤ)) : OmodP k₀ p) from
        eq_intCast ((ZMod.castHom dvd_rfl (OmodP k₀ p)).comp (Int.castRingHom (ZMod p)))
          (pb.basis.repr α i)]
      rw [map_zsmul, zsmul_eq_mul]
      congr 1
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← map_sum]
    congr 1
    have hbasis : ∀ i : Fin pb.dim, hζ.toInteger ^ (i : ℕ) = pb.basis i := by
      intro i
      rw [pb.coe_basis]
      change hζ.toInteger ^ (i : ℕ) = pb.gen ^ (i : ℕ)
      rw [show pb.gen = hζ.toInteger from hζ.integralPowerBasis_gen]
    rw [Finset.sum_congr rfl fun i _ => by rw [hbasis i]]
    exact pb.basis.sum_repr α
  have hε : eps f₀ ≠ 0 := eps_ne_zero_of_lift hζ hπ hα
  exact ⟨(isUnit_of_eps_ne_zero hε).unit, by rw [IsUnit.unit_spec]; exact hπ⟩

/-! ### `ℓ₃`-vanishing on lifted units -/

omit hpri in
theorem not_dvd_two (hp5 : 5 ≤ p) : ¬ (p - 1) ∣ 2 := fun h => by
  have := Nat.le_of_dvd (by norm_num) h
  omega

omit hpri in
theorem not_dvd_three (hp5 : 5 ≤ p) : ¬ (p - 1) ∣ 3 := fun h => by
  have := Nat.le_of_dvd (by norm_num) h
  omega

/-- **Conj-invariant residues have `ℓ₃ = 0`** (the σ₋₁-trick, lift-free). -/
theorem ell_three_eq_zero_of_conj_inv (hp5 : 5 ≤ p) {w : 𝓞 k₀} {γ : (P p)ˣ}
    (hγ : piRed hζ ((γ : P p)) = Ideal.Quotient.mk _ w)
    (hw : ((galEquivZMod p k₀).symm (-1)) • w = w) :
    ell 3 γ = 0 := by
  have hπeq : piRed hζ ((sigmaU (-1) γ : (P p)ˣ) : P p) = piRed hζ ((γ : P p)) := by
    rw [sigmaU_val, piRed_sigma, hγ, galBar_mk, hw]
  have heq := ell_eq_of_piRed_eq hζ (by norm_num) (by
      rw [show (3 : ℕ) - 1 = 2 from rfl]
      exact not_dvd_two hp5) (not_dvd_three hp5) hπeq
  rw [ell_sigmaU 3 (by norm_num)] at heq
  have hcoe : (((-1 : (ZMod p)ˣ) : ZMod p)) ^ 3 = -1 := by
    rw [Units.val_neg, Units.val_one]
    ring
  rw [hcoe] at heq
  have h2 : (2 : ZMod p) * ell 3 γ = 0 := by linear_combination -heq
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h2' : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    simpa using h2'
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h h2ne
  · exact h

/-! ### Kummer's unit lemma: `ℓ₃` vanishes on unit residues -/

open NumberField.IsCMField in
include hζ in
/-- The `σ₋₁`-action is integral complex conjugation. -/
theorem galSymm_neg_one_smul (hp2 : 2 < p) (x : 𝓞 k₀) :
    haveI : NumberField.IsCMField k₀ := IsCyclotomicExtension.Rat.isCMField (S := {p}) (K := k₀)
        ⟨p, rfl, hp2⟩
    ((galEquivZMod p k₀).symm (-1)) • x = ringOfIntegersComplexConj k₀ x := by
  haveI : NumberField.IsCMField k₀ := IsCyclotomicExtension.Rat.isCMField (S := {p}) (K := k₀) ⟨p,
      rfl, hp2⟩
  have hgal : (galEquivZMod p k₀).symm (-1) = conjGal (K := k₀) := by
    rw [← galEquivZMod_conjGal hζ]
    exact (galEquivZMod p k₀).symm_apply_apply _
  apply FaithfulSMul.algebraMap_injective (𝓞 k₀) k₀
  rw [show (algebraMap (𝓞 k₀) k₀) (ringOfIntegersComplexConj k₀ x)
      = complexConj k₀ (algebraMap (𝓞 k₀) k₀ x) from coe_ringOfIntegersComplexConj k₀ x]
  rw [hgal]
  rfl

open NumberField.IsCMField in
/-- Conjugation inverts `ζ` at the unit level. -/
theorem unitsComplexConj_unit' (hp2 : 2 < p) :
    haveI : NumberField.IsCMField k₀ := IsCyclotomicExtension.Rat.isCMField (S := {p}) (K := k₀)
        ⟨p, rfl, hp2⟩
    unitsComplexConj k₀ hζ.unit' = (hζ.unit')⁻¹ := by
  haveI : NumberField.IsCMField k₀ := IsCyclotomicExtension.Rat.isCMField (S := {p}) (K := k₀) ⟨p,
      rfl, hp2⟩
  refine Units.ext ?_
  apply FaithfulSMul.algebraMap_injective (𝓞 k₀) k₀
  rw [show ((unitsComplexConj k₀ hζ.unit' : (𝓞 k₀)ˣ) : 𝓞 k₀)
      = ringOfIntegersComplexConj k₀ ((hζ.unit' : (𝓞 k₀)ˣ) : 𝓞 k₀) from rfl,
    show (algebraMap (𝓞 k₀) k₀) (ringOfIntegersComplexConj k₀ ((hζ.unit' : (𝓞 k₀)ˣ) : 𝓞 k₀))
      = complexConj k₀ (algebraMap (𝓞 k₀) k₀ ((hζ.unit' : (𝓞 k₀)ˣ) : 𝓞 k₀)) from
    coe_ringOfIntegersComplexConj k₀ _]
  rw [unit'_val_eq_toInteger hζ]
  have ht : algebraMap (𝓞 k₀) k₀ hζ.toInteger = ζ := hζ.coe_toInteger
  rw [ht, complexConj_zeta hζ]
  rfl

open NumberField.IsCMField in
/-- **`ℓ₃` vanishes on lifts of unit residues** (Kummer: `u = ζᵐ·(conj-invariant)`). -/
theorem ell_three_eq_zero_of_unit (hp5 : 5 ≤ p) (u : (𝓞 k₀)ˣ) {γ : (P p)ˣ}
    (hγ : piRed hζ ((γ : P p)) = Ideal.Quotient.mk _ ((u : 𝓞 k₀))) :
    ell 3 γ = 0 := by
  classical
  have hp2 : 2 < p := by omega
  haveI : NumberField.IsCMField k₀ := IsCyclotomicExtension.Rat.isCMField (S := {p}) (K := k₀) ⟨p,
      rfl, hp2⟩
  obtain ⟨m, hm⟩ := unit_inv_conj_is_root_of_unity hζ u hp2
  set w : (𝓞 k₀)ˣ := ((hζ.unit')⁻¹) ^ m * u with hw
  have hcu : unitsComplexConj k₀ u = ((hζ.unit' ^ m) ^ 2)⁻¹ * u := by
    -- `hm` is phrased with flt-regular's `(…).unit` form of the root of unity; bridge it to our
    -- `hζ.unit'` (same underlying value `hζ.toInteger`, so `Units.ext rfl`).
    have hm' : (hζ.unit' ^ m) ^ 2 = u * (unitsComplexConj k₀ u)⁻¹ := by
      rw [hm]; congr 2; exact Units.ext rfl
    rw [hm']
    group
  have hconjw : unitsComplexConj k₀ w = w := by
    rw [hw, map_mul, map_pow, map_inv, unitsComplexConj_unit' hζ hp2, hcu]
    group
  have hu_eq : u = (hζ.unit') ^ m * w := by
    rw [hw]
    group
  have hwnot : ((w : (𝓞 k₀)ˣ) : 𝓞 k₀)
      ∉ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
    intro hmem
    exact (hζ.isPrime_one_sub_zeta).ne_top (Ideal.eq_top_of_isUnit_mem _ hmem w.isUnit)
  obtain ⟨γw, hγw⟩ := exists_unit_lift hζ hwnot
  have hconjw' : ((galEquivZMod p k₀).symm (-1)) • ((w : (𝓞 k₀)ˣ) : 𝓞 k₀)
      = ((w : (𝓞 k₀)ˣ) : 𝓞 k₀) := by
    rw [galSymm_neg_one_smul hζ hp2,
      show ringOfIntegersComplexConj k₀ ((w : (𝓞 k₀)ˣ) : 𝓞 k₀)
        = ((unitsComplexConj k₀ w : (𝓞 k₀)ˣ) : 𝓞 k₀) from rfl, hconjw]
  have hℓw : ell 3 γw = 0 := ell_three_eq_zero_of_conj_inv hζ hp5 hγw hconjw'
  set δu := singleUnit (((m : ℕ) : ZMod p)) (1 : ZMod p) one_ne_zero with hδu
  have hπδ : piRed hζ ((δu : (P p)ˣ) : P p) = Ideal.Quotient.mk _ (hζ.toInteger ^ m) := by
    change piRed hζ (single (((m : ℕ) : ZMod p)) (1 : ZMod p)) = _
    rw [piRed_single, one_smul, ZMod.val_natCast, pow_val_mod (zetaBar_pow_p hζ), zetaBar,
      map_pow]
  have hpieq : piRed hζ ((δu * γw : (P p)ˣ) : P p) = piRed hζ ((γ : P p)) := by
    rw [Units.val_mul, map_mul, hπδ, hγw, hγ, ← map_mul]
    congr 1
    rw [hu_eq, Units.val_mul, ← unit'_val_eq_toInteger hζ]
    congr 1
  have heq := ell_eq_of_piRed_eq hζ (by norm_num) (by
      rw [show (3 : ℕ) - 1 = 2 from rfl]
      exact not_dvd_two hp5) (not_dvd_three hp5) hpieq
  rw [ell_mul, show ell 3 δu = 0 from ell_singleUnit 3 (by norm_num) _ _ _, hℓw,
    add_zero] at heq
  exact heq.symm

/-! ### The η₃-relation from a trivial eigencomponent -/

open Ideal in
/-- If the weight-3 eigencomponent of `[I]` is trivial, then the `η₃`-twisted product of the
conjugates of `β` is a unit times a `p`-th power. -/
theorem eta_three_relation {β : 𝓞 k₀} (_hβ0 : β ≠ 0) {Iid : Ideal (𝓞 k₀)}
    (hI : Ideal.span {β} = Iid ^ p) (hIne : Iid ≠ 0)
    (htriv : eigenProj p 3 (ClassGroup.mk0
      ⟨Iid, mem_nonZeroDivisors_iff_ne_zero.mpr hIne⟩) = 1) :
    ∃ (u : (𝓞 k₀)ˣ) (z : 𝓞 k₀),
      (∏ b : (ZMod p)ˣ, ((((galEquivZMod p k₀).symm b) • β : 𝓞 k₀))
          ^ (((b⁻¹ ^ 3 : (ZMod p)ˣ) : ZMod p)).val)
        = (u : 𝓞 k₀) * z ^ p
      ∧ Ideal.span {z} = ∏ b : (ZMod p)ˣ,
          ((((galEquivZMod p k₀).symm b) • Iid : Ideal (𝓞 k₀)))
            ^ (((b⁻¹ ^ 3 : (ZMod p)ˣ) : ZMod p)).val := by
  classical
  set Isub : (Ideal (𝓞 k₀))⁰ := ⟨Iid, mem_nonZeroDivisors_iff_ne_zero.mpr hIne⟩ with hIsub
  -- the eigenprojection ideal is principal
  have hprin : Submodule.IsPrincipal (∏ a : (ZMod p)ˣ,
      ((((galEquivZMod p k₀).symm a)⁻¹ • Iid : Ideal (𝓞 k₀)))
        ^ (((a ^ 3 : (ZMod p)ˣ) : ZMod p)).val) := by
    have h1 : eigenProj p 3 (ClassGroup.mk0 Isub)
        = ClassGroup.mk0 (∏ a : (ZMod p)ˣ,
          (⟨((galEquivZMod p k₀).symm a)⁻¹ • Iid,
            smul_mem_nonZeroDivisors _ Isub⟩ : (Ideal (𝓞 k₀))⁰)
              ^ (((a ^ 3 : (ZMod p)ˣ) : ZMod p)).val) := by
      rw [eigenProj, map_prod]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [map_pow]
      congr 1
      exact classGroupGalAct_mk0 _ Isub
    rw [h1] at htriv
    have h2 := (ClassGroup.mk0_eq_one_iff (∏ a : (ZMod p)ˣ,
      (⟨((galEquivZMod p k₀).symm a)⁻¹ • Iid,
        smul_mem_nonZeroDivisors _ Isub⟩ : (Ideal (𝓞 k₀))⁰)
          ^ (((a ^ 3 : (ZMod p)ˣ) : ZMod p)).val).2).mp htriv
    have hcoe : ((∏ a : (ZMod p)ˣ,
        (⟨((galEquivZMod p k₀).symm a)⁻¹ • Iid,
          smul_mem_nonZeroDivisors _ Isub⟩ : (Ideal (𝓞 k₀))⁰)
            ^ (((a ^ 3 : (ZMod p)ˣ) : ZMod p)).val : (Ideal (𝓞 k₀))⁰) : Ideal (𝓞 k₀))
        = ∏ a : (ZMod p)ˣ, ((((galEquivZMod p k₀).symm a)⁻¹ • Iid : Ideal (𝓞 k₀)))
            ^ (((a ^ 3 : (ZMod p)ˣ) : ZMod p)).val := by
      push_cast
      rfl
    rwa [hcoe] at h2
  -- reindex `a := b⁻¹`
  have hreidx : (∏ a : (ZMod p)ˣ,
      ((((galEquivZMod p k₀).symm a)⁻¹ • Iid : Ideal (𝓞 k₀)))
        ^ (((a ^ 3 : (ZMod p)ˣ) : ZMod p)).val)
      = ∏ b : (ZMod p)ˣ, ((((galEquivZMod p k₀).symm b) • Iid : Ideal (𝓞 k₀)))
          ^ (((b⁻¹ ^ 3 : (ZMod p)ˣ) : ZMod p)).val := by
    rw [← Equiv.prod_comp (Equiv.inv (ZMod p)ˣ) fun b =>
      ((((galEquivZMod p k₀).symm b) • Iid : Ideal (𝓞 k₀)))
        ^ (((b⁻¹ ^ 3 : (ZMod p)ˣ) : ZMod p)).val]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [show Equiv.inv (ZMod p)ˣ a = a⁻¹ from rfl, ← map_inv, inv_inv]
  rw [hreidx] at hprin
  obtain ⟨z, hz⟩ := hprin.principal
  rw [Ideal.submodule_span_eq] at hz
  have hpow : Ideal.span {z ^ p}
      = Ideal.span {(∏ b : (ZMod p)ˣ, ((((galEquivZMod p k₀).symm b) • β : 𝓞 k₀))
          ^ (((b⁻¹ ^ 3 : (ZMod p)ˣ) : ZMod p)).val)} := by
    rw [← Ideal.span_singleton_pow, ← hz, ← Ideal.prod_span_singleton, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun b _ => ?_
    have hsmulpow : (((galEquivZMod p k₀).symm b) • Iid : Ideal (𝓞 k₀)) ^ p
        = ((galEquivZMod p k₀).symm b) • (Iid ^ p) := by
      rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def, Ideal.map_pow]
    have hsmulspan : (((galEquivZMod p k₀).symm b) • (Ideal.span {β}) : Ideal (𝓞 k₀))
        = Ideal.span {(((galEquivZMod p k₀).symm b) • β : 𝓞 k₀)} := by
      rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
      rfl
    rw [← pow_mul, mul_comm, pow_mul, hsmulpow, ← hI, hsmulspan, Ideal.span_singleton_pow]
  rw [Ideal.span_singleton_eq_span_singleton] at hpow
  obtain ⟨u, hu⟩ := hpow
  exact ⟨u, z, by rw [← hu]; ring, hz.symm⟩

/-! ### The core dichotomy -/

include hζ in
/-- Bézout: an integer whose image lies in `(ζ−1)` is divisible by `p`. -/
theorem intCast_mem_zeta_sub_one {n : ℤ}
    (hn : ((n : ℤ) : 𝓞 k₀) ∈ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀))) :
    (p : ℤ) ∣ n := by
  by_contra hpn
  have hcop : IsCoprime ((p : ℕ) : ℤ) n :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hpri.out)).mpr hpn
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : 𝓞 k₀) ∈ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
    have hmem : ((a * (p : ℕ) + b * n : ℤ) : 𝓞 k₀)
        ∈ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
      push_cast
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (by exact_mod_cast hζ.p_mem_one_sub_zeta))
        (Ideal.mul_mem_left _ _ hn)
    rw [hab] at hmem
    simpa using hmem
  exact (hζ.isPrime_one_sub_zeta).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

open Ideal in
include hζ in
/-- **The core dichotomy** (Granville, KWS 1993): a factorization `(x+ζy) = Iᵖ` whose Mirimanoff
ratio `t = −y/x` avoids `{0, 1, −1}` forces `p − 3` to be an irregular index. -/
theorem isIrregular_of_span_eq_pow (hp5 : 5 ≤ p) {x y : ℤ} {Iid : Ideal (𝓞 k₀)}
    (hI : Ideal.span {((x : ℤ) : 𝓞 k₀) + hζ.toInteger * ((y : ℤ) : 𝓞 k₀)} = Iid ^ p)
    (hx : ((x : ℤ) : ZMod p) ≠ 0)
    (hsum : ((x : ℤ) : ZMod p) + ((y : ℤ) : ZMod p) ≠ 0)
    (ht0 : -((y : ℤ) : ZMod p) * (((x : ℤ) : ZMod p))⁻¹ ≠ 0)
    (ht1 : -((y : ℤ) : ZMod p) * (((x : ℤ) : ZMod p))⁻¹ ≠ 1)
    (htm1 : -((y : ℤ) : ZMod p) * (((x : ℤ) : ZMod p))⁻¹ ≠ -1) :
    QiCert.IsIrregularIndex p (p - 3) := by
  classical
  set β : 𝓞 k₀ := ((x : ℤ) : 𝓞 k₀) + hζ.toInteger * ((y : ℤ) : 𝓞 k₀) with hβ
  -- `β ∉ (ζ−1)` since `x + y ≢ 0 (mod p)`
  have hβp : β ∉ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
    intro hmem
    have hxy : (((x + y : ℤ)) : 𝓞 k₀)
        ∈ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
      have hdecomp : (((x + y : ℤ)) : 𝓞 k₀)
          = β - ((y : ℤ) : 𝓞 k₀) * (hζ.unit' - 1 : 𝓞 k₀) := by
        rw [hβ, ← unit'_val_eq_toInteger hζ]
        push_cast
        ring
      rw [hdecomp]
      exact Ideal.sub_mem _ hmem (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
    have := intCast_mem_zeta_sub_one hζ hxy
    apply hsum
    have hcast : (((x + y : ℤ)) : ZMod p) = 0 := by
      rcases this with ⟨m, hm⟩
      rw [hm]
      push_cast
      rw [ZMod.natCast_self]
      ring
    push_cast at hcast
    linear_combination hcast
  have hβ0 : β ≠ 0 := fun h => hβp (h ▸ Ideal.zero_mem _)
  have hIne : Iid ≠ 0 := by
    intro h
    rw [h, zero_pow hpri.out.ne_zero] at hI
    exact hβ0 (Ideal.span_singleton_eq_bot.mp hI)
  by_cases htriv : eigenProj p 3 (ClassGroup.mk0
      ⟨Iid, mem_nonZeroDivisors_iff_ne_zero.mpr hIne⟩) = 1
  case neg =>
    -- Herbrand fires
    have hclp : (ClassGroup.mk0
        (⟨Iid, mem_nonZeroDivisors_iff_ne_zero.mpr hIne⟩ : (Ideal (𝓞 k₀))⁰)) ^ p = 1 := by
      rw [← map_pow]
      refine (ClassGroup.mk0_eq_one_iff
        ((⟨Iid, mem_nonZeroDivisors_iff_ne_zero.mpr hIne⟩ : (Ideal (𝓞 k₀))⁰) ^ p).2).mpr ?_
      have hcoe : (((⟨Iid, mem_nonZeroDivisors_iff_ne_zero.mpr hIne⟩ : (Ideal (𝓞 k₀))⁰) ^ p :
          (Ideal (𝓞 k₀))⁰) : Ideal (𝓞 k₀)) = Iid ^ p := by
        push_cast
        rfl
      rw [hcoe, ← hI]
      exact ⟨⟨β, by rw [hβ, Ideal.submodule_span_eq]⟩⟩
    exact herbrand_eigenProj (by decide) (by norm_num) (by omega) hclp htriv
  case pos =>
    exfalso
    obtain ⟨u, z, hA, hzspan⟩ := eta_three_relation hβ0 hI hIne htriv
    -- `z ∉ (ζ−1)`: the prime-divisibility chase
    have hzp : z ∉ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
      intro hmem
      have h𝔭ne : Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) ≠ ⊥ := by
        intro h
        have h1 := Ideal.span_singleton_eq_bot.mp h
        rw [sub_eq_zero, unit'_val_eq_toInteger hζ] at h1
        have h2 : ζ = 1 := by
          have hc := congrArg (algebraMap (𝓞 k₀) k₀) h1
          have ht : algebraMap (𝓞 k₀) k₀ hζ.toInteger = ζ := hζ.coe_toInteger
          rwa [ht, map_one] at hc
        exact (hζ.ne_one hpri.out.one_lt) h2
      have hprime : Prime (Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀))) :=
        Ideal.prime_of_isPrime h𝔭ne (hζ.isPrime_one_sub_zeta)
      have hdvd1 : Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) ∣ Ideal.span {z} := by
        rw [Ideal.dvd_iff_le]
        exact (Ideal.span_singleton_le_iff_mem _).mpr hmem
      rw [hzspan] at hdvd1
      obtain ⟨b, _, hdvd2⟩ := hprime.exists_mem_finset_dvd hdvd1
      have hdvd3 := hprime.dvd_of_dvd_pow hdvd2
      obtain ⟨C, hC⟩ := hdvd3
      have hdvd4 : ((galEquivZMod p k₀).symm b)⁻¹
          • (Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀))) ∣ Iid := by
        refine ⟨((galEquivZMod p k₀).symm b)⁻¹ • C, ?_⟩
        have := congrArg (fun J => ((galEquivZMod p k₀).symm b)⁻¹ • J) hC
        simpa [smul_smul, smul_mul'] using this
      have h𝔭fix : ((galEquivZMod p k₀).symm b)⁻¹
          • (Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)))
          = Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
        rw [← map_inv]
        rw [show ((galEquivZMod p k₀).symm b⁻¹)
            • (Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)))
            = Ideal.span {(((galEquivZMod p k₀).symm b⁻¹) • (hζ.unit' - 1 : 𝓞 k₀) : 𝓞 k₀)} from by
          rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
          rfl]
        have hpow : hζ.toInteger ^ p = 1 := by
          apply FaithfulSMul.algebraMap_injective (𝓞 k₀) k₀
          have ht : algebraMap (𝓞 k₀) k₀ hζ.toInteger = ζ := hζ.coe_toInteger
          rw [map_pow, map_one, ht]
          exact hζ.pow_eq_one
        have hsm : (((galEquivZMod p k₀).symm b⁻¹) • (hζ.unit' - 1 : 𝓞 k₀) : 𝓞 k₀)
            = hζ.toInteger ^ (((b⁻¹ : (ZMod p)ˣ) : ZMod p)).val - 1 := by
          rw [show (hζ.unit' - 1 : 𝓞 k₀) = hζ.toInteger - 1 from by
            rw [← unit'_val_eq_toInteger hζ], smul_sub]
          congr 1
          · have h := galEquivZMod_smul_of_pow_eq p k₀ ((galEquivZMod p k₀).symm b⁻¹) hpow
            rw [MulEquiv.apply_symm_apply] at h
            exact h
          · exact map_one (MulSemiringAction.toRingHom _ (𝓞 k₀) ((galEquivZMod p k₀).symm b⁻¹))
        rw [hsm, show Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀))
            = Ideal.span {(hζ.toInteger - 1 : 𝓞 k₀)} from by
          rw [← unit'_val_eq_toInteger hζ]]
        exact Ideal.span_singleton_eq_span_singleton.mpr
          (associated_sub_one_pow_sub_one hζ.toInteger_isPrimitiveRoot hpri.out.two_le
            (ZMod.val_coe_unit_coprime b⁻¹)).symm
      rw [h𝔭fix] at hdvd4
      have hdvd5 : Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) ∣ Ideal.span {β} := by
        rw [hI]
        exact dvd_pow hdvd4 hpri.out.ne_zero
      exact hβp (Ideal.le_of_dvd hdvd5 (Ideal.subset_span rfl))
    -- lifts of `u` and `z`
    have hup : ((u : (𝓞 k₀)ˣ) : 𝓞 k₀)
        ∉ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := fun hmem =>
      (hζ.isPrime_one_sub_zeta).ne_top (Ideal.eq_top_of_isUnit_mem _ hmem u.isUnit)
    obtain ⟨γu, hγu⟩ := exists_unit_lift hζ hup
    obtain ⟨γz, hγz⟩ := exists_unit_lift hζ hzp
    -- the base unit `V = x̄·(1−tX)`, of value `x̄ + ȳX`
    set t : ZMod p := -((y : ℤ) : ZMod p) * (((x : ℤ) : ZMod p))⁻¹ with hT
    set V : (P p)ˣ := singleUnit 0 (((x : ℤ) : ZMod p)) hx * geomUnit t ht1 with hV
    have hVval : ((V : (P p)ˣ) : P p)
        = single 0 (((x : ℤ) : ZMod p)) + single 1 (((y : ℤ) : ZMod p)) := by
      rw [hV, Units.val_mul]
      change (single (0 : ZMod p) (((x : ℤ) : ZMod p)) : P p) * (1 - single 1 t) = _
      rw [mul_sub, mul_one, single_mul_single, zero_add]
      have hxt : (((x : ℤ) : ZMod p)) * t = -(((y : ℤ) : ZMod p)) := by
        rw [hT]
        field_simp
      rw [hxt]
      have hneg : (single (1 : ZMod p) (-(((y : ℤ) : ZMod p))) : P p)
          = -single 1 (((y : ℤ) : ZMod p)) := by
        classical
        ext m
        change (single (1 : ZMod p) (-(((y : ℤ) : ZMod p))) : P p) m
            = -((single (1 : ZMod p) (((y : ℤ) : ZMod p)) : P p) m)
        rw [AddMonoidAlgebra.single_apply, AddMonoidAlgebra.single_apply]
        split_ifs <;> ring
      rw [hneg]
      ring
    -- `π` of the conjugates of `V` are the conjugates of `β`
    have hpow : hζ.toInteger ^ p = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 k₀) k₀
      have ht2 : algebraMap (𝓞 k₀) k₀ hζ.toInteger = ζ := hζ.coe_toInteger
      rw [map_pow, map_one, ht2]
      exact hζ.pow_eq_one
    have hsmul_int : ∀ (n : ℤ) (w : OmodP k₀ p),
        (((n : ℤ) : ZMod p)) • w = (((n : ℤ)) : OmodP k₀ p) * w := by
      intro n w
      rw [Algebra.smul_def]
      congr 1
      exact eq_intCast ((ZMod.castHom dvd_rfl (OmodP k₀ p)).comp (Int.castRingHom (ZMod p))) n
    have hπV : ∀ b : (ZMod p)ˣ,
        piRed hζ (sigma b ((V : (P p)ˣ) : P p))
          = Ideal.Quotient.mk _ ((((galEquivZMod p k₀).symm b) • β : 𝓞 k₀)) := by
      intro b
      rw [hVval, map_add, map_add, sigma_single, sigma_single, piRed_single, piRed_single,
        mul_zero, mul_one, ZMod.val_zero, pow_zero, hsmul_int, hsmul_int, mul_one]
      have hsm : (((galEquivZMod p k₀).symm b) • β : 𝓞 k₀)
          = ((x : ℤ) : 𝓞 k₀)
            + hζ.toInteger ^ (((b : (ZMod p)ˣ) : ZMod p)).val * ((y : ℤ) : 𝓞 k₀) := by
        rw [hβ, smul_add, smul_mul']
        have hx2 : (((galEquivZMod p k₀).symm b) • (((x : ℤ)) : 𝓞 k₀) : 𝓞 k₀)
            = (((x : ℤ)) : 𝓞 k₀) :=
          map_intCast (MulSemiringAction.toRingHom _ (𝓞 k₀) _) x
        have hy2 : (((galEquivZMod p k₀).symm b) • (((y : ℤ)) : 𝓞 k₀) : 𝓞 k₀)
            = (((y : ℤ)) : 𝓞 k₀) :=
          map_intCast (MulSemiringAction.toRingHom _ (𝓞 k₀) _) y
        have hz2 : (((galEquivZMod p k₀).symm b) • hζ.toInteger : 𝓞 k₀)
            = hζ.toInteger ^ (((b : (ZMod p)ˣ) : ZMod p)).val := by
          have h := galEquivZMod_smul_of_pow_eq p k₀ ((galEquivZMod p k₀).symm b) hpow
          rw [MulEquiv.apply_symm_apply] at h
          exact h
        rw [hx2, hy2, hz2]
      rw [hsm, map_add, map_mul, map_pow, map_intCast, map_intCast, zetaBar]
      ring
    -- the twisted product and its `π`-image
    set bigProd : (P p)ˣ := ∏ b : (ZMod p)ˣ,
      (sigmaU b V) ^ (((b⁻¹ ^ 3 : (ZMod p)ˣ) : ZMod p)).val with hbigProd
    have hcoeProd : ((bigProd : (P p)ˣ) : P p)
        = ∏ b : (ZMod p)ˣ, (sigma b ((V : (P p)ˣ) : P p))
            ^ (((b⁻¹ ^ 3 : (ZMod p)ˣ) : ZMod p)).val := by
      rw [hbigProd, show (((∏ b : (ZMod p)ˣ,
          (sigmaU b V) ^ (((b⁻¹ ^ 3 : (ZMod p)ˣ) : ZMod p)).val) : (P p)ˣ) : P p)
          = ∏ b : (ZMod p)ˣ, (((sigmaU b V) ^ (((b⁻¹ ^ 3 : (ZMod p)ˣ) : ZMod p)).val
              : (P p)ˣ) : P p) from map_prod (Units.coeHom (P p)) _ _]
      exact Finset.prod_congr rfl fun b _ => by
        rw [show (((sigmaU b V) ^ (((b⁻¹ ^ 3 : (ZMod p)ˣ) : ZMod p)).val : (P p)ˣ) : P p)
            = ((sigmaU b V : (P p)ˣ) : P p) ^ (((b⁻¹ ^ 3 : (ZMod p)ˣ) : ZMod p)).val from
          Units.val_pow_eq_pow_val _ _, sigmaU_val]
    have hRHS : piRed hζ ((γu * γz ^ p : (P p)ˣ) : P p)
        = Ideal.Quotient.mk _ (((u : (𝓞 k₀)ˣ) : 𝓞 k₀) * z ^ p) := by
      rw [Units.val_mul, map_mul, show ((γz ^ p : (P p)ˣ) : P p) = ((γz : (P p)ˣ) : P p) ^ p from
        Units.val_pow_eq_pow_val _ _, map_pow, hγu, hγz, ← map_pow, ← map_mul]
    have hpiProd : piRed hζ ((bigProd : (P p)ˣ) : P p)
        = piRed hζ ((γu * γz ^ p : (P p)ˣ) : P p) := by
      rw [hcoeProd, map_prod, Finset.prod_congr rfl fun b _ => by
        rw [map_pow, hπV b, ← map_pow], ← map_prod, hA, hRHS]
    -- the `ℓ₃`-contradiction
    have h3 := ell_eq_of_piRed_eq hζ (by norm_num) (by
        rw [show (3 : ℕ) - 1 = 2 from rfl]
        exact not_dvd_two hp5) (not_dvd_three hp5) hpiProd
    rw [hbigProd, ell_etaProd 3 (by norm_num) V] at h3
    have hru : ell 3 (γu * γz ^ p) = 0 := by
      rw [ell_mul, ell_pow_p, ell_three_eq_zero_of_unit hζ hp5 u hγu, add_zero]
    rw [hru, neg_eq_zero] at h3
    have hVell : ell 3 V = ell 3 (geomUnit t ht1) := by
      rw [hV, ell_mul, ell_singleUnit 3 (by norm_num), zero_add]
    rw [hVell] at h3
    exact ell_three_geomUnit_ne_zero ht0 ht1 htm1 h3

/-! ### The Kummer criterion for Case I -/

omit hpri in
/-- A triple covering `{a,b,c}` up to signs inherits coprimality. -/
theorem gcd_triple_of_cover {x y z a b c : ℤ}
    (hcov : ∀ w ∈ ({a, b, c} : Finset ℤ),
      w ∈ ({x, y, z} : Finset ℤ) ∨ -w ∈ ({x, y, z} : Finset ℤ))
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) :
    ({x, y, z} : Finset ℤ).gcd id = 1 := by
  classical
  have hdvd : ({x, y, z} : Finset ℤ).gcd id ∣ 1 := by
    rw [← hgcd]
    refine Finset.dvd_gcd fun w hw => ?_
    rcases hcov w hw with h | h
    · exact Finset.gcd_dvd (f := (id : ℤ → ℤ)) h
    · have h2 := Finset.gcd_dvd (f := (id : ℤ → ℤ)) h
      simp only [id] at h2 ⊢
      exact (dvd_neg.mp h2)
  have hnn : 0 ≤ ({x, y, z} : Finset ℤ).gcd id := Finset.Int.finsetGcd_nonneg
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
  · exact h
  · omega

end KummerLog

open KummerLog IsCyclotomicExtension in
/-- **Kummer's criterion (1857)**: if `p ∤ B_{p−3}`, the first case of Fermat's Last Theorem
holds at `p`. -/
theorem caseI_of_not_irregular {p : ℕ} [hpri : Fact p.Prime] (hp5 : 5 ≤ p)
    (hirr : ¬ QiCert.IsIrregularIndex p (p - 3))
    {a b c : ℤ} (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬ ↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p := by
  intro H
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have hζK : IsPrimitiveRoot (zeta p ℚ (CyclotomicField p ℚ)) p :=
    zeta_spec p ℚ (CyclotomicField p ℚ)
  have hpodd : Odd p := hpri.out.odd_of_ne_two (by omega)
  -- the ζ-membership for `exists_ideal`
  have hζmem : hζK.toInteger
      ∈ Polynomial.nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
    rw [Polynomial.mem_nthRootsFinset hpri.out.pos]
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
    have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) hζK.toInteger
        = zeta p ℚ (CyclotomicField p ℚ) := hζK.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζK.pow_eq_one
  -- `p` divides none of `a, b, c`
  have hpa : ¬ (p : ℤ) ∣ a := fun h => caseI ((h.mul_right b).mul_right c)
  have hpb : ¬ (p : ℤ) ∣ b := fun h => caseI ((h.mul_left a).mul_right c)
  have hpc : ¬ (p : ℤ) ∣ c := fun h => caseI (h.mul_left (a * b))
  have haz : ((a : ZMod p)) ≠ 0 := fun h => hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have hbz : ((b : ZMod p)) ≠ 0 := fun h => hpb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h)
  have hcz : ((c : ZMod p)) ≠ 0 := fun h => hpc ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp h)
  -- the triple sums to zero mod `p`
  have hsum0 : ((a : ZMod p)) + ((b : ZMod p)) + (-((c : ZMod p))) = 0 := by
    have hH := congrArg (fun n : ℤ => ((n : ZMod p))) H
    push_cast at hH
    rw [ZMod.pow_card, ZMod.pow_card, ZMod.pow_card] at hH
    linear_combination hH
  obtain ⟨A, B, hA, hB, hAB, hmem, ht0, ht1, htm1⟩ :=
    exists_good_ratio hp5 haz hbz (neg_ne_zero.mpr hcz) hsum0
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- pair `(ā, b̄)`: integer pair `(x, y) := (b, a)`
    obtain ⟨Iid, hIid⟩ := FltRegular.exists_ideal hp5
      (show b ^ p + a ^ p = c ^ p by linarith) (gcd_triple_of_cover (by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
        rcases hw with rfl | rfl | rfl
        · exact Or.inl (Or.inr (Or.inl rfl))
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr (Or.inr rfl))) hgcd)
      (by
        intro h
        exact caseI (by
          have : b * a * c = a * b * c := by ring
          rwa [this] at h)) hζmem
    exact hirr (isIrregular_of_span_eq_pow hζK hp5 (x := b) (y := a) hIid hB
      (by rw [add_comm]; exact hAB) ht0 ht1 htm1)
  · -- pair `(b̄, −c̄)`: integer pair `(x, y) := (−c, b)`
    obtain ⟨Iid, hIid⟩ := FltRegular.exists_ideal hp5
      (show (-c) ^ p + b ^ p = (-a) ^ p by
        rw [hpodd.neg_pow, hpodd.neg_pow]
        linarith) (gcd_triple_of_cover (by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
        rcases hw with rfl | rfl | rfl
        · exact Or.inr (by right; right; rfl)
        · exact Or.inl (Or.inr (Or.inl rfl))
        · exact Or.inr (by left; rfl)) hgcd)
      (by
        intro h
        exact caseI (by
          have h2 : (-c) * b * (-a) = a * b * c := by ring
          rwa [h2] at h)) hζmem
    refine hirr (isIrregular_of_span_eq_pow hζK hp5 (x := -c) (y := b) hIid ?_ ?_ ?_ ?_ ?_)
    · push_cast
      exact hB
    · push_cast
      rw [add_comm]
      exact hAB
    · push_cast
      exact ht0
    · push_cast
      exact ht1
    · push_cast
      exact htm1
  · -- pair `(−c̄, ā)`: integer pair `(x, y) := (a, −c)`
    obtain ⟨Iid, hIid⟩ := FltRegular.exists_ideal hp5
      (show a ^ p + (-c) ^ p = (-b) ^ p by
        rw [hpodd.neg_pow, hpodd.neg_pow]
        linarith) (gcd_triple_of_cover (by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
        rcases hw with rfl | rfl | rfl
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr (by right; right; rfl)
        · exact Or.inr (by right; left; rfl)) hgcd)
      (by
        intro h
        exact caseI (by
          have h2 : a * (-c) * (-b) = a * b * c := by ring
          rwa [h2] at h)) hζmem
    refine hirr (isIrregular_of_span_eq_pow hζK hp5 (x := a) (y := -c) hIid hB ?_ ?_ ?_ ?_)
    · push_cast
      rw [add_comm]
      exact hAB
    · push_cast
      exact ht0
    · push_cast
      exact ht1
    · push_cast
      exact htm1

end CyclotomicNT
