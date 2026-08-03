module

public import CyclotomicNT.StkAnnihilation
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Stickelberger.Descent

@[expose] public section

/-!
# Discharging the hypotheses of the Stickelberger machinery

This file constructs the standing hypotheses of the Gauss-sum development for a concrete
arithmetic situation, towards the final integral Stickelberger annihilation statement.

* `rootsOfUnity_mapQuot_bijective`: the reduction map `μ_n(𝓞 K) → (𝓞 K ⧸ P)ˣ` is bijective
  when `K` contains the `n`-th roots of unity, `absNorm P` is coprime to `n`, and the residue
  field has exactly `n + 1` elements. Injectivity is Mathlib's
  `Ideal.rootsOfUnityMapQuot_injective`; surjectivity is a cardinality count.
* `rootsOfUnity_mapQuot_bijective_of_liesOver`: the instantiation for `K = ℚ(ζ_{p^f-1})` and
  `P` a maximal ideal over `p`, discharging the `hbij` hypothesis of the Stickelberger files.
-/

noncomputable section

open Ideal NumberField IntermediateField Pointwise IsCyclotomicExtension.Rat

attribute [local instance] Ideal.Quotient.field

/-! ### Transport of the twisted product along an isomorphism of cyclotomic fields -/

section Transport

variable {m : ℕ} [NeZero m] {k₀ k : Type*} [Field k₀] [Field k] [NumberField k₀] [NumberField k]
  [IsCyclotomicExtension {m} ℚ k₀] [IsCyclotomicExtension {m} ℚ k] (φ : k₀ ≃ₐ[ℚ] k)

/-- Conjugation by an isomorphism of cyclotomic fields preserves the cyclotomic character. -/
theorem galEquivZMod_autCongr (σ : k₀ ≃ₐ[ℚ] k₀) :
    galEquivZMod m k (AlgEquiv.autCongr φ σ) = galEquivZMod m k₀ σ := by
  have hζ₀ := IsCyclotomicExtension.zeta_spec m ℚ k₀
  have hζ : IsPrimitiveRoot (φ (IsCyclotomicExtension.zeta m ℚ k₀)) m :=
    hζ₀.map_of_injective φ.injective
  have h1 : σ (IsCyclotomicExtension.zeta m ℚ k₀) =
      (IsCyclotomicExtension.zeta m ℚ k₀) ^ (galEquivZMod m k₀ σ).val.val :=
    galEquivZMod_apply_of_pow_eq m k₀ σ hζ₀.pow_eq_one
  have h2 : (AlgEquiv.autCongr φ σ) (φ (IsCyclotomicExtension.zeta m ℚ k₀)) =
      (φ (IsCyclotomicExtension.zeta m ℚ k₀)) ^
        (galEquivZMod m k (AlgEquiv.autCongr φ σ)).val.val :=
    galEquivZMod_apply_of_pow_eq m k _ (by rw [← map_pow, hζ₀.pow_eq_one, map_one])
  have h3 : (AlgEquiv.autCongr φ σ) (φ (IsCyclotomicExtension.zeta m ℚ k₀)) =
      (φ (IsCyclotomicExtension.zeta m ℚ k₀)) ^ (galEquivZMod m k₀ σ).val.val := by
    rw [show (AlgEquiv.autCongr φ σ) (φ (IsCyclotomicExtension.zeta m ℚ k₀)) =
        φ (σ (φ.symm (φ (IsCyclotomicExtension.zeta m ℚ k₀)))) from rfl,
      φ.symm_apply_apply, h1, map_pow]
  have h4 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h2.symm.trans h3)
  exact Units.ext (ZMod.val_injective m h4)

/-- The ring-of-integers transport intertwines the Galois actions on ideals. -/
theorem map_smul_eq_autCongr_smul_map (σ : k₀ ≃ₐ[ℚ] k₀) (I : Ideal (𝓞 k₀)) :
    Ideal.map (RingOfIntegers.mapRingEquiv φ.toRingEquiv) (σ • I) =
      (AlgEquiv.autCongr φ σ) • Ideal.map (RingOfIntegers.mapRingEquiv φ.toRingEquiv) I := by
  have key : ∀ y : 𝓞 k₀, (RingOfIntegers.mapRingEquiv φ.toRingEquiv) (σ • y) =
      (AlgEquiv.autCongr φ σ) • (RingOfIntegers.mapRingEquiv φ.toRingEquiv) y := by
    intro y
    apply FaithfulSMul.algebraMap_injective (𝓞 k) k
    rw [algebraMap.smul' (B := 𝓞 k) (C := k), AlgEquiv.smul_def,
      ← RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.mapRingEquiv_apply,
      ← RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.mapRingEquiv_apply,
      RingOfIntegers.coe_eq_algebraMap, algebraMap.smul' (B := 𝓞 k₀) (C := k₀),
      AlgEquiv.smul_def]
    change φ (σ (y : k₀)) = (AlgEquiv.autCongr φ σ) (φ (y : k₀))
    rw [show (AlgEquiv.autCongr φ σ) (φ (y : k₀)) = φ (σ (φ.symm (φ (y : k₀)))) from rfl,
      φ.symm_apply_apply]
  have hcoe : ∀ J : Ideal (𝓞 k₀), Ideal.map (RingOfIntegers.mapRingEquiv φ.toRingEquiv) J =
      Ideal.map ((RingOfIntegers.mapRingEquiv φ.toRingEquiv :
        𝓞 k₀ ≃+* 𝓞 k) : 𝓞 k₀ →+* 𝓞 k) J := fun _ ↦ rfl
  rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def, hcoe, hcoe, Ideal.map_map,
    Ideal.map_map]
  congr 1
  exact RingHom.ext fun x ↦ key x

/-- Principality of the twisted Stickelberger product transports along an isomorphism of
cyclotomic fields. -/
theorem isPrincipal_prod_smul_pow_congr (E : (ZMod m)ˣ → ℕ) (𝔮 : Ideal (𝓞 k₀))
    (h : Submodule.IsPrincipal (∏ a : (ZMod m)ˣ, (((galEquivZMod m k).symm a)⁻¹ •
        Ideal.map (RingOfIntegers.mapRingEquiv φ.toRingEquiv) 𝔮) ^ E a : Ideal (𝓞 k))) :
    Submodule.IsPrincipal
      (∏ a : (ZMod m)ˣ, (((galEquivZMod m k₀).symm a)⁻¹ • 𝔮) ^ E a : Ideal (𝓞 k₀)) := by
  have hmap : Ideal.map (RingOfIntegers.mapRingEquiv φ.toRingEquiv)
      (∏ a : (ZMod m)ˣ, (((galEquivZMod m k₀).symm a)⁻¹ • 𝔮) ^ E a) =
      ∏ a : (ZMod m)ˣ, (((galEquivZMod m k).symm a)⁻¹ •
        Ideal.map (RingOfIntegers.mapRingEquiv φ.toRingEquiv) 𝔮) ^ E a := by
    rw [← Ideal.mapHom_apply, map_prod]
    refine Fintype.prod_congr _ _ fun a ↦ ?_
    have hsymm : AlgEquiv.autCongr φ ((galEquivZMod m k₀).symm a) =
        (galEquivZMod m k).symm a := by
      apply (galEquivZMod m k).injective
      rw [galEquivZMod_autCongr, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rw [map_pow, Ideal.mapHom_apply, map_smul_eq_autCongr_smul_map, _root_.map_inv, hsymm]
  obtain ⟨g, hg⟩ := h.principal
  rw [← hmap] at hg
  refine ⟨⟨(RingOfIntegers.mapRingEquiv φ.toRingEquiv).symm g, ?_⟩⟩
  have h2 := congrArg (Ideal.map (((RingOfIntegers.mapRingEquiv φ.toRingEquiv).symm :
    𝓞 k ≃+* 𝓞 k₀) : 𝓞 k →+* 𝓞 k₀)) hg
  have hcoe : ∀ J : Ideal (𝓞 k₀), Ideal.map (RingOfIntegers.mapRingEquiv φ.toRingEquiv) J =
      Ideal.map ((RingOfIntegers.mapRingEquiv φ.toRingEquiv :
        𝓞 k₀ ≃+* 𝓞 k) : 𝓞 k₀ →+* 𝓞 k) J := fun _ ↦ rfl
  rw [hcoe, Ideal.map_map, Ideal.map_span, Set.image_singleton,
    show ((((RingOfIntegers.mapRingEquiv φ.toRingEquiv).symm : 𝓞 k ≃+* 𝓞 k₀) :
        𝓞 k →+* 𝓞 k₀)).comp (((RingOfIntegers.mapRingEquiv φ.toRingEquiv) :
        𝓞 k₀ ≃+* 𝓞 k) : 𝓞 k₀ →+* 𝓞 k) = RingHom.id _ from
      RingHom.ext fun x ↦ (RingOfIntegers.mapRingEquiv φ.toRingEquiv).symm_apply_apply x,
    Ideal.map_id] at h2
  exact h2

end Transport

/-! ### The per-prime instantiation -/

section PerPrime

variable {p : ℕ} [hpp : Fact p.Prime] {k₀ : Type*} [Field k₀] [NumberField k₀]
  [IsCyclotomicExtension {p} ℚ k₀]

open IsCyclotomicExtension in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- Instantiating the Gauss-sum machinery over `L = ℚ(ζ_{ℓ(ℓ^f-1)})` is a heavy elaboration that
-- exceeds the default heartbeat budget.
/-- **The Stickelberger elements annihilate primes of `ℚ(ζ_p)`** away from `2p`: for any model
`k₀` of `ℚ(ζ_p)` and any nonzero prime `𝔮` coprime to `2p`, both `𝔮^{pθ} = ∏ₐ (σₐ⁻¹𝔮)^{a}`
and, for every unit `c` mod `p`, `𝔮^{β_c} = ∏ₐ (σₐ⁻¹𝔮)^{⌊c·a/p⌋}` are principal. This
instantiates the Gauss-sum machinery over `L = ℚ(ζ_{ℓ(ℓ^f-1)})`, `ℓ` the residue
characteristic of `𝔮`. -/
theorem stickelberger_annihilates_prime_of_coprime (𝔮 : Ideal (𝓞 k₀)) [𝔮.IsPrime]
    (h𝔮 : 𝔮 ≠ 0) (hcop : 𝔮 ⊔ span {((2 * p : ℕ) : 𝓞 k₀)} = ⊤) :
    Submodule.IsPrincipal (∏ a : (ZMod p)ˣ,
      (((galEquivZMod p k₀).symm a)⁻¹ • 𝔮) ^ (a : ZMod p).val : Ideal (𝓞 k₀)) ∧
    ∀ c : (ZMod p)ˣ, Submodule.IsPrincipal (∏ a : (ZMod p)ˣ,
      (((galEquivZMod p k₀).symm a)⁻¹ • 𝔮) ^ (c.val.val * a.val.val / p) : Ideal (𝓞 k₀)) := by
  classical
  haveI : NeZero p := ⟨hpp.out.ne_zero⟩
  haveI h𝔮max : 𝔮.IsMaximal := (inferInstance : 𝔮.IsPrime).isMaximal h𝔮
  -- the residue characteristic `ℓ` of `𝔮`
  obtain ⟨l₀, hl₀⟩ := (IsPrincipalIdealRing.principal (𝔮.under ℤ)).principal
  rw [Ideal.submodule_span_eq] at hl₀
  have hunder0 : 𝔮.under ℤ ≠ ⊥ := by
    intro h0
    have h1 : ((Ideal.absNorm 𝔮 : ℤ)) ∈ 𝔮.under ℤ :=
      Ideal.mem_comap.mpr (by exact_mod_cast Ideal.absNorm_mem 𝔮)
    rw [h0, Ideal.mem_bot, Int.natCast_eq_zero] at h1
    exact h𝔮 (Ideal.absNorm_eq_zero_iff.mp h1)
  have hl₀0 : l₀ ≠ 0 := by
    rintro rfl
    rw [show (span {(0 : ℤ)} : Ideal ℤ) = ⊥ by simp] at hl₀
    exact hunder0 hl₀
  have hl₀p : Prime l₀ := by
    rw [← Ideal.span_singleton_prime hl₀0, ← hl₀]
    infer_instance
  set ℓ : ℕ := l₀.natAbs with hℓdef
  have hℓprime : ℓ.Prime := Int.prime_iff_natAbs_prime.mp hl₀p
  haveI : Fact ℓ.Prime := ⟨hℓprime⟩
  have hspan : 𝔮.under ℤ = span {(ℓ : ℤ)} := by
    rw [hl₀]
    exact Ideal.span_singleton_eq_span_singleton.mpr (Int.associated_natAbs l₀)
  haveI h𝔮over : 𝔮.LiesOver (span {(ℓ : ℤ)}) := ⟨hspan.symm⟩
  -- `ℓ` does not divide `2p`
  have hℓmem : ((ℓ : ℕ) : 𝓞 k₀) ∈ 𝔮 := by
    have h2 : ((ℓ : ℤ)) ∈ 𝔮.under ℤ := by
      rw [hspan]
      exact Ideal.subset_span rfl
    rw [Ideal.mem_comap] at h2
    exact_mod_cast h2
  have hℓ2p : ¬ ℓ ∣ 2 * p := by
    rintro ⟨t, ht⟩
    have h2 : ((2 * p : ℕ) : 𝓞 k₀) ∈ 𝔮 := by
      rw [ht]
      push_cast
      exact Ideal.mul_mem_right _ _ (by exact_mod_cast hℓmem)
    have h3 : span {((2 * p : ℕ) : 𝓞 k₀)} ≤ 𝔮 := by
      rwa [Ideal.span_singleton_le_iff_mem]
    rw [sup_eq_left.mpr h3] at hcop
    exact h𝔮max.ne_top hcop
  have hℓ2 : ℓ ≠ 2 := fun h ↦ hℓ2p (h ▸ Dvd.intro p rfl)
  have hℓp : ℓ ≠ p := fun h ↦ hℓ2p (h ▸ Dvd.intro_left 2 rfl)
  haveI : Fact (Odd ℓ) := ⟨hℓprime.odd_of_ne_two hℓ2⟩
  -- the inertia order `f` and the cofactor `d`
  have hcoprime : ℓ.Coprime p := (Nat.coprime_primes hℓprime hpp.out).mpr hℓp
  set f : ℕ := orderOf (ℓ : ZMod p) with hfdef
  have hfpos : 0 < f := by
    rw [hfdef, show ((ℓ : ZMod p)) = ((ZMod.unitOfCoprime ℓ hcoprime : (ZMod p)ˣ) : ZMod p)
      from (ZMod.coe_unitOfCoprime _ _).symm, orderOf_units]
    exact orderOf_pos _
  haveI : NeZero f := ⟨hfpos.ne'⟩
  have hmf : orderOf (ℓ : ZMod p) = f := rfl
  have hℓf1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓprime.pos
  have hpdvd : p ∣ ℓ ^ f - 1 := by
    have h1 : ((ℓ : ZMod p)) ^ f = 1 := pow_orderOf_eq_one _
    have h2 : (((ℓ ^ f - 1 : ℕ)) : ZMod p) = 0 := by
      push_cast [hℓf1]
      rw [h1]
      ring
    exact (ZMod.natCast_eq_zero_iff _ _).mp h2
  set d : ℕ := (ℓ ^ f - 1) / p with hddef
  have hdm : ℓ ^ f - 1 = d * p := (Nat.div_mul_cancel hpdvd).symm
  haveI : NeZero (ℓ ^ f - 1) := ⟨by
    have h2 : 2 ≤ ℓ := hℓprime.two_le
    have h3 : 2 ≤ ℓ ^ f := le_trans h2 (Nat.le_self_pow hfpos.ne' ℓ)
    omega⟩
  -- the ambient cyclotomic field `L = ℚ(ζ_{ℓ(ℓ^f-1)})` and its subfields
  haveI : NeZero (ℓ * (ℓ ^ f - 1)) := ⟨Nat.mul_ne_zero hℓprime.ne_zero (NeZero.ne _)⟩
  let L : Type _ := CyclotomicField (ℓ * (ℓ ^ f - 1)) ℚ
  haveI : IsCyclotomicExtension {ℓ * (ℓ ^ f - 1)} ℚ L :=
    CyclotomicField.isCyclotomicExtension (ℓ * (ℓ ^ f - 1)) ℚ
  haveI : NumberField L := IsCyclotomicExtension.numberField {ℓ * (ℓ ^ f - 1)} ℚ L
  -- kL = ℚ(ζ_p)
  set kL : IntermediateField ℚ L := Stickelberger.kSubR (L := L) (p := ℓ) (f := f) p with hkLdef
  haveI : IsCyclotomicExtension {p} ℚ kL :=
    Stickelberger.isCyclotomic_kSubR (L := L) (p := ℓ) (f := f) (r := p) hpp.out.pos hpdvd
  -- transport `𝔮` to the model `kL`
  let φ : k₀ ≃ₐ[ℚ] kL := IsCyclotomicExtension.algEquiv {p} ℚ k₀ kL
  set 𝔭 : Ideal (𝓞 kL) := Ideal.map (RingOfIntegers.mapRingEquiv φ.toRingEquiv) 𝔮 with h𝔭def
  have hcoe : Ideal.map (RingOfIntegers.mapRingEquiv φ.toRingEquiv) 𝔮 =
      Ideal.comap ((RingOfIntegers.mapRingEquiv φ.toRingEquiv).symm) 𝔮 := by
    rw [show Ideal.map (RingOfIntegers.mapRingEquiv φ.toRingEquiv) 𝔮 =
        Ideal.map (((RingOfIntegers.mapRingEquiv φ.toRingEquiv) :
          𝓞 k₀ ≃+* 𝓞 kL) : 𝓞 k₀ →+* 𝓞 kL) 𝔮 from rfl]
    exact Ideal.map_comap_of_equiv _
  haveI h𝔭prime : 𝔭.IsPrime := by
    rw [h𝔭def, hcoe]
    exact Ideal.IsPrime.comap _
  have h𝔭0 : 𝔭 ≠ 0 := by
    intro h0
    apply h𝔮
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    intro x hx
    have h1 : (RingOfIntegers.mapRingEquiv φ.toRingEquiv) x ∈ 𝔭 :=
      Ideal.mem_map_of_mem _ hx
    rw [h0, Ideal.zero_eq_bot, Ideal.mem_bot] at h1
    rw [Ideal.mem_bot]
    exact (RingOfIntegers.mapRingEquiv φ.toRingEquiv).injective (by simpa using h1)
  have hψZ : ∀ x : ℤ, (RingOfIntegers.mapRingEquiv φ.toRingEquiv) (algebraMap ℤ (𝓞 k₀) x) =
      algebraMap ℤ (𝓞 kL) x := fun x ↦ RingHom.congr_fun (Subsingleton.elim
        ((((RingOfIntegers.mapRingEquiv φ.toRingEquiv) : 𝓞 k₀ ≃+* 𝓞 kL) :
          𝓞 k₀ →+* 𝓞 kL).comp (algebraMap ℤ (𝓞 k₀))) (algebraMap ℤ (𝓞 kL))) x
  haveI h𝔭over : 𝔭.LiesOver (span {(ℓ : ℤ)}) := by
    constructor
    rw [← hspan]
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap]
    constructor
    · intro hx
      have h1 : (RingOfIntegers.mapRingEquiv φ.toRingEquiv) (algebraMap ℤ (𝓞 k₀) x) ∈ 𝔭 :=
        Ideal.mem_map_of_mem _ hx
      rwa [hψZ x] at h1
    · intro hx
      rw [h𝔭def, Ideal.mem_map_iff_of_surjective _
        (RingOfIntegers.mapRingEquiv φ.toRingEquiv).surjective] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      have h3 : y = algebraMap ℤ (𝓞 k₀) x :=
        (RingOfIntegers.mapRingEquiv φ.toRingEquiv).injective (by rw [hxy, hψZ x])
      rwa [← h3]
  -- a maximal ideal of `𝓞 L` over `𝔭`, and its trace `P` on `K`
  obtain ⟨𝓟, h𝓟max, h𝓟over⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral 𝔭 (S := 𝓞 L)
  haveI := h𝓟max
  haveI := h𝓟over
  haveI h𝓟prime : 𝓟.IsPrime := h𝓟max.isPrime
  haveI h𝓟overl : 𝓟.LiesOver (span {(ℓ : ℤ)}) := Ideal.LiesOver.trans 𝓟 𝔭 (span {(ℓ : ℤ)})
  have hspanl0 : (span {(ℓ : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [ne_eq, span_singleton_eq_bot]
    exact_mod_cast hℓprime.ne_zero
  haveI : NeZero 𝓟 := ⟨Ideal.ne_bot_of_liesOver_of_ne_bot hspanl0 𝓟⟩
  -- apply the clean-room Stickelberger machinery over `L` and transport back
  have hq3 : 3 ≤ ℓ ^ f := le_trans (by have := hℓprime.two_le; omega) (Nat.le_self_pow hfpos.ne' ℓ)
  have hP0 : 𝓟.under (𝓞 kL) = 𝔭 := (Ideal.LiesOver.over (p := 𝔭) (P := 𝓟)).symm
  haveI : IsGalois ℚ kL := IsCyclotomicExtension.isGalois {p} ℚ kL
  constructor
  · have hmain := Stickelberger.stickelberger_isPrincipal_of_descent (P := 𝓟) (m := p)
      hpp.out.two_le hfpos hq3 hpdvd hcoprime hmf hP0
    simp only [Stickelberger.conjugatePrime_eq_galEquivZMod] at hmain
    rw [show (Stickelberger.galMulSemiringAction : MulSemiringAction (kL ≃ₐ[ℚ] kL) (𝓞 kL))
        = _ from Stickelberger.galMul_eq_canonical] at hmain
    exact isPrincipal_prod_smul_pow_congr φ (fun a : (ZMod p)ˣ ↦ a.val.val) 𝔮 hmain
  · intro c
    have hmain := Stickelberger.stickelbergerProd_prime_isPrincipal_of_descent (P := 𝓟) (m := p)
      hpp.out.two_le hfpos hq3 hpdvd hcoprime hmf c.val.val (ZMod.val_coe_unit_coprime c) hP0
    simp only [Stickelberger.stickelbergerProd, Stickelberger.galZMod, map_inv] at hmain
    rw [show (Stickelberger.galMulSemiringAction : MulSemiringAction (kL ≃ₐ[ℚ] kL) (𝓞 kL))
        = _ from Stickelberger.galMul_eq_canonical] at hmain
    exact isPrincipal_prod_smul_pow_congr φ (fun a ↦ c.val.val * a.val.val / p) 𝔮 hmain

end PerPrime

section PerPrime

variable {p : ℕ} [hpp : Fact p.Prime] {k₀ : Type*} [Field k₀] [NumberField k₀]
  [IsCyclotomicExtension {p} ℚ k₀]

/-- **The integral Stickelberger annihilation theorem** for any model `k₀` of `ℚ(ζ_p)`:
for every `c : ℕ` and every nonzero ideal `I` of `𝓞 k₀`, the twisted product
`∏ₐ (σₐ⁻¹ I)^{⌊c·a/p⌋}` is principal. In class-group terms this says that the integral
Stickelberger element `β_c = ∑ₐ ⌊c·a/p⌋ σₐ⁻¹` annihilates the class group of `ℚ(ζ_p)`;
it is the ideal-theoretic form of flt-vandiver's `stickelberger_annihilates` axiom. -/
theorem stickelberger_annihilates_ideal (c : ℕ) (I : Ideal (𝓞 k₀)) (hI : I ≠ 0) :
    Submodule.IsPrincipal (∏ a : (ZMod p)ˣ,
      (((galEquivZMod p k₀).symm a)⁻¹ • I) ^ (c * (a : ZMod p).val / p) : Ideal (𝓞 k₀)) := by
  classical
  haveI : NeZero p := ⟨hpp.out.ne_zero⟩
  have hM : (span {((2 * p : ℕ) : 𝓞 k₀)} : Ideal (𝓞 k₀)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, span_singleton_eq_bot]
    exact_mod_cast Nat.mul_ne_zero two_ne_zero hpp.out.ne_zero
  refine isPrincipal_prod_smul_pow_of_forall_prime p
    (fun a : (ZMod p)ˣ ↦ c * (a : ZMod p).val / p) (M := span {((2 * p : ℕ) : 𝓞 k₀)})
    (fun J hJ ↦ Ideal.exists_span_mul_eq_span_mul_coprime hM hJ) ?_ I hI
  intro 𝔮 h𝔮prime h𝔮0 h𝔮cop
  haveI := h𝔮prime
  obtain ⟨hθ, hβ⟩ := stickelberger_annihilates_prime_of_coprime 𝔮 h𝔮0 h𝔮cop
  rw [prod_pow_mul_val_div (fun a ↦ ((galEquivZMod p k₀).symm a)⁻¹ • 𝔮) c]
  obtain ⟨A, hA⟩ := hθ.principal
  rcases Nat.eq_zero_or_pos (c % p) with hc0 | hcpos
  · rw [hc0]
    simp only [Nat.zero_mul, Nat.zero_div, pow_zero, Finset.prod_const_one, mul_one]
    exact ⟨⟨A ^ (c / p), by rw [hA, Ideal.span_singleton_pow]⟩⟩
  · have hndvd : ¬ p ∣ c % p := fun hdvd ↦
      Nat.lt_irrefl _ (lt_of_lt_of_le (Nat.mod_lt c hpp.out.pos) (Nat.le_of_dvd hcpos hdvd))
    have hcop' : (c % p).Coprime p := Nat.Coprime.symm (hpp.out.coprime_iff_not_dvd.mpr hndvd)
    have hβu := hβ (ZMod.unitOfCoprime (c % p) hcop')
    have hu : ((ZMod.unitOfCoprime (c % p) hcop' : (ZMod p)ˣ) : ZMod p).val = c % p := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (Nat.mod_lt c hpp.out.pos)
    rw [hu] at hβu
    obtain ⟨B, hB⟩ := hβu.principal
    exact ⟨⟨A ^ (c / p) * B, by
      rw [hA, hB, Ideal.span_singleton_pow, span_singleton_mul_span_singleton]⟩⟩

end PerPrime
