module

public import Mathlib

@[expose] public section

/-!
# The Stickelberger element annihilates ideal classes

This file derives, from the basic Stickelberger prime annihilation
(`Stickelberger.stickelberger_isPrincipal_of_descent`, i.e. the orbit factorization
`Stickelberger.orbit_factorization`), the *integral* form of
Stickelberger's theorem (Washington, *Introduction to Cyclotomic Fields*, Lemma 6.9/Thm 6.10):
for `c` coprime to `m`, the integral Stickelberger element
`β_c = ∑_{a ∈ (ZMod m)ˣ} ⌊c·a.val/m⌋ σ_a⁻¹` annihilates the class of every prime `𝔭` of
`ℚ(ζ_m)` lying over a rational prime `ℓ ∤ m`, i.e. `∏_a (σ_a⁻¹ 𝔭)^{⌊c·a.val/m⌋}` is principal.

The element-level mechanism: with `Γ` the descended Gauss-sum power (`(Γ) = ∏_a (σ_a⁻¹𝔭)^{a.val}`,
see `Stickelberger.orbit_factorization`), we have `σ_c(Γ) ∣ Γ^c` in `𝓞 ℚ(ζ_m)` because the
exponents satisfy `(c·a).val ≤ c·a.val` prime-by-prime; the quotient `γ` then satisfies
`(γ)^m = (∏_a (σ_a⁻¹𝔭)^{⌊c·a.val/m⌋})^m` by the identity `c·a.val = (c·a).val + m·⌊c·a.val/m⌋`,
and `m`-th roots of ideals are unique in a Dedekind domain.
-/

noncomputable section

open Ideal NumberField IntermediateField Pointwise IsCyclotomicExtension.Rat

variable {p f : ℕ} [NeZero (p ^ f - 1)]

local notation3 "𝒑" => span {(p : ℤ)}

variable {L : Type*} [Field L] [NumberField L] {k : IntermediateField ℚ L}

variable (m : ℕ) (𝔭 : Ideal (𝓞 k))

/-- The elementary exponent identity behind `(c - σ_c)·mθ = m·β_c`. -/
theorem val_add_mul_div (c a : (ZMod m)ˣ) [NeZero m] :
    (c * a : (ZMod m)ˣ).val.val + m * (c.val.val * a.val.val / m) =
      c.val.val * a.val.val := by
  have h1 : ((c * a : (ZMod m)ˣ) : ZMod m).val = c.val.val * a.val.val % m := by
    rw [Units.val_mul, ZMod.val_mul]
  rw [h1]
  exact Nat.mod_add_div _ _

/-- Reindexing: the action of `σ_c` on the Stickelberger product permutes the factors,
replacing the exponent `a.val` by `(a·c).val`. -/
theorem smul_stickelberger_prod [IsCyclotomicExtension {m} ℚ k] [NeZero m] (c : (ZMod m)ˣ) :
    (galEquivZMod m k).symm c •
        ∏ a : (ZMod m)ˣ, (((galEquivZMod m k).symm a)⁻¹ • 𝔭) ^ a.val.val =
      ∏ a : (ZMod m)ˣ, (((galEquivZMod m k).symm a)⁻¹ • 𝔭) ^ (a * c : (ZMod m)ˣ).val.val := by
  rw [Finset.smul_prod']
  simp_rw [smul_pow']
  rw [← Equiv.prod_comp (Equiv.mulRight c⁻¹)
    (fun a ↦ (((galEquivZMod m k).symm a)⁻¹ • 𝔭) ^ (a * c : (ZMod m)ˣ).val.val)]
  refine Fintype.prod_congr _ _ fun a ↦ ?_
  have hgrp : (c * a⁻¹ : (ZMod m)ˣ) = (a * c⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv, mul_comm]
  have h2 : (galEquivZMod m k).symm c • ((galEquivZMod m k).symm a)⁻¹ • 𝔭 =
      ((galEquivZMod m k).symm (a * c⁻¹))⁻¹ • 𝔭 := by
    rw [smul_smul, ← _root_.map_inv, ← _root_.map_mul, hgrp, _root_.map_inv]
  rw [show ((Equiv.mulRight c⁻¹) a : (ZMod m)ˣ) = a * c⁻¹ from rfl, h2,
    inv_mul_cancel_right]

variable {F K : IntermediateField ℚ L}

/-- Splitting an arbitrary integral Stickelberger element: for any `c`, the exponent vector of
`β_c` is `(c / m)·(mθ) + β_{c % m}`. Consequently, annihilation for arbitrary `c : ℕ` (the form
of flt-vandiver's `stickelberger_annihilates` axiom) reduces to the coprime case `c % m`
together with the principality of `𝔭^{mθ}` (`Stickelberger.stickelberger_isPrincipal_of_descent`),
since `c % m` is either `0` or
coprime to a prime `m`. -/
theorem prod_pow_mul_val_div {M : Type*} [CommMonoid M] {m : ℕ} [NeZero m]
    (x : (ZMod m)ˣ → M) (c : ℕ) :
    (∏ a : (ZMod m)ˣ, x a ^ (c * (a : ZMod m).val / m)) =
      (∏ a : (ZMod m)ˣ, x a ^ (a : ZMod m).val) ^ (c / m) *
        ∏ a : (ZMod m)ˣ, x a ^ (c % m * (a : ZMod m).val / m) := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Fintype.prod_congr _ _ fun a ↦ ?_
  rw [← pow_mul, ← pow_add]
  congr 1
  conv_lhs => rw [← Nat.div_add_mod c m]
  rw [add_mul, mul_assoc, Nat.mul_add_div (Nat.pos_of_ne_zero (NeZero.ne m)),
    mul_comm ((a : ZMod m).val) (c / m)]

/-! ### Class-level transfer: the twisted product `∏ₐ (σₐ⁻¹ I)^{E a}` -/

section PhiTransfer

variable {k' : Type*} [Field k'] [NumberField k'] [IsCyclotomicExtension {m} ℚ k'] [NeZero m]
  (E : (ZMod m)ˣ → ℕ)

/-- The twisted product is multiplicative in the ideal. -/
theorem prod_smul_pow_mul (I J : Ideal (𝓞 k')) :
    (∏ a : (ZMod m)ˣ, (((galEquivZMod m k').symm a)⁻¹ • (I * J)) ^ E a) =
      (∏ a : (ZMod m)ˣ, (((galEquivZMod m k').symm a)⁻¹ • I) ^ E a) *
        ∏ a : (ZMod m)ˣ, (((galEquivZMod m k').symm a)⁻¹ • J) ^ E a := by
  simp_rw [smul_mul', mul_pow, Finset.prod_mul_distrib]

/-- The twisted product of a principal ideal is principal. -/
theorem isPrincipal_prod_smul_pow_span (x : 𝓞 k') :
    Submodule.IsPrincipal
      (∏ a : (ZMod m)ˣ, (((galEquivZMod m k').symm a)⁻¹ • span {x}) ^ E a : Ideal (𝓞 k')) := by
  refine ⟨⟨∏ a : (ZMod m)ˣ, ((((galEquivZMod m k').symm a)⁻¹ • x) ^ E a), ?_⟩⟩
  simp_rw [Ideal.smul_closure, Set.smul_set_singleton, Ideal.span_singleton_pow,
    Ideal.prod_span_singleton]

/-- The twisted product of a nonzero principal ideal is nonzero. -/
theorem prod_smul_pow_span_ne_zero {x : 𝓞 k'} (hx : x ≠ 0) :
    (∏ a : (ZMod m)ˣ, (((galEquivZMod m k').symm a)⁻¹ • span {x}) ^ E a : Ideal (𝓞 k')) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro a _
  refine pow_ne_zero _ fun h0 ↦ ?_
  have h1 : (span {x} : Ideal (𝓞 k')) = 0 := by
    simpa using congrArg ((((galEquivZMod m k').symm a)) • ·) h0
  rw [Ideal.zero_eq_bot, span_singleton_eq_bot] at h1
  exact hx h1

/-- Transfer of twisted-product principality along the class equivalence `(x)·I = (y)·J`. -/
theorem isPrincipal_prod_smul_pow_of_span_mul_eq {I J : Ideal (𝓞 k')} {x y : 𝓞 k'} (hx : x ≠ 0)
    (h : span {x} * I = span {y} * J)
    (hJ : Submodule.IsPrincipal
      (∏ a : (ZMod m)ˣ, (((galEquivZMod m k').symm a)⁻¹ • J) ^ E a : Ideal (𝓞 k'))) :
    Submodule.IsPrincipal
      (∏ a : (ZMod m)ˣ, (((galEquivZMod m k').symm a)⁻¹ • I) ^ E a : Ideal (𝓞 k')) := by
  obtain ⟨X, hX⟩ := (isPrincipal_prod_smul_pow_span m E x).principal
  obtain ⟨Y, hY⟩ := (isPrincipal_prod_smul_pow_span m E y).principal
  obtain ⟨Z, hZ⟩ := hJ.principal
  have hX0 : X ≠ 0 := by
    intro h0
    apply prod_smul_pow_span_ne_zero m E hx
    rw [hX, h0, Ideal.zero_eq_bot, span_singleton_eq_bot]
  have h2 := congrArg (fun I : Ideal (𝓞 k') ↦
    ∏ a : (ZMod m)ˣ, (((galEquivZMod m k').symm a)⁻¹ • I) ^ E a) h
  simp only [prod_smul_pow_mul] at h2
  rw [hX, hY, hZ, span_singleton_mul_span_singleton] at h2
  have h3 : X ∣ Y * Z := by
    have h4 : (span {Y * Z} : Ideal (𝓞 k')) ≤ span {X} := by
      rw [← h2]
      exact Ideal.mul_le_right
    exact Ideal.span_singleton_le_span_singleton.mp h4
  obtain ⟨t, ht⟩ := h3
  refine ⟨⟨t, ?_⟩⟩
  have h5 : (span {X} : Ideal (𝓞 k')) *
      (∏ a : (ZMod m)ˣ, (((galEquivZMod m k').symm a)⁻¹ • I) ^ E a) =
      span {X} * span {t} := by
    rw [h2, span_singleton_mul_span_singleton, ← ht]
  refine mul_left_cancel₀ ?_ h5
  rw [ne_eq, Ideal.zero_eq_bot, span_singleton_eq_bot]
  exact hX0

/-- **Class-level transfer**: if the twisted product `∏ₐ (σₐ⁻¹𝔮)^{E a}` is principal for every
nonzero prime `𝔮` coprime to a modulus `M`, and every class has a representative coprime to `M`
(the hypothesis `hmove`, the classical "moving lemma"), then the twisted product of *every*
nonzero ideal is principal. -/
theorem isPrincipal_prod_smul_pow_of_forall_prime {M : Ideal (𝓞 k')}
    (hmove : ∀ I : Ideal (𝓞 k'), I ≠ 0 → ∃ (x y : 𝓞 k') (J : Ideal (𝓞 k')),
      x ≠ 0 ∧ J ≠ 0 ∧ span {x} * I = span {y} * J ∧ J ⊔ M = ⊤)
    (hprime : ∀ 𝔮 : Ideal (𝓞 k'), 𝔮.IsPrime → 𝔮 ≠ 0 → 𝔮 ⊔ M = ⊤ →
      Submodule.IsPrincipal
        (∏ a : (ZMod m)ˣ, (((galEquivZMod m k').symm a)⁻¹ • 𝔮) ^ E a : Ideal (𝓞 k')))
    (I : Ideal (𝓞 k')) (hI : I ≠ 0) :
    Submodule.IsPrincipal
      (∏ a : (ZMod m)ˣ, (((galEquivZMod m k').symm a)⁻¹ • I) ^ E a : Ideal (𝓞 k')) := by
  obtain ⟨x, y, J, hx, hJ0, heq, hcop⟩ := hmove I hI
  refine isPrincipal_prod_smul_pow_of_span_mul_eq m E hx heq ?_
  clear heq hI hx I x y
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ0
  | h₂ u hu =>
      rw [Ideal.isUnit_iff] at hu
      rw [hu, ← Ideal.span_singleton_one]
      exact isPrincipal_prod_smul_pow_span m E 1
  | h₃ J q hJ' hq ih =>
      have hsup_q : q ⊔ M = ⊤ := by
        rw [eq_top_iff, ← hcop]
        exact sup_le_sup_right Ideal.mul_le_right M
      have hsup_J : J ⊔ M = ⊤ := by
        rw [eq_top_iff, ← hcop]
        exact sup_le_sup_right Ideal.mul_le_left M
      rw [prod_smul_pow_mul]
      obtain ⟨A, hA⟩ := (hprime q (Ideal.isPrime_of_prime hq) hq.ne_zero hsup_q).principal
      obtain ⟨B, hB⟩ := (ih hJ' hsup_J).principal
      exact ⟨⟨A * B, by rw [hA, hB, span_singleton_mul_span_singleton]⟩⟩

end PhiTransfer
/-! ### The moving lemma: coprime class representatives in Dedekind domains -/

open UniqueFactorizationMonoid in
/-- In a Dedekind domain, every nonzero ideal `I` admits a nonzero `J` in the *inverse* ideal
class with `J` coprime to a given nonzero modulus `M`: `(x) = I * J`. -/
theorem Ideal.exists_span_eq_mul_coprime {R : Type*} [CommRing R] [IsDedekindDomain R]
    {M : Ideal R} (hM : M ≠ 0) {I : Ideal R} (hI : I ≠ 0) :
    ∃ (x : R) (J : Ideal R), x ≠ 0 ∧ J ≠ 0 ∧ span {x} = I * J ∧ J ⊔ M = ⊤ := by
  classical
  have hT : I * M ≠ 0 := mul_ne_zero hI hM
  set S : Finset (Ideal R) := (normalizedFactors (I * M)).toFinset with hS
  rcases S.eq_empty_or_nonempty with hSe | ⟨𝔮₀, h𝔮₀⟩
  · -- no prime factors: `I = ⊤`
    have h1 : (normalizedFactors (I * M)) = 0 := by
      rwa [← Multiset.toFinset_eq_empty]
    have h2 : IsUnit (I * M) := by
      have h := prod_normalizedFactors hT
      rw [h1, Multiset.prod_zero] at h
      exact associated_one_iff_isUnit.mp h.symm
    have hItop : I = ⊤ := by
      rw [eq_top_iff, ← Ideal.isUnit_iff.mp h2]
      exact Ideal.mul_le_right
    exact ⟨1, ⊤, one_ne_zero, top_ne_bot, by rw [hItop, Ideal.span_singleton_one, top_mul],
      top_sup_eq M⟩
  set e : Ideal R → ℕ := fun 𝔮 ↦ (normalizedFactors I).count 𝔮 with he
  have hprimeS : ∀ 𝔮 ∈ S, Prime 𝔮 := fun 𝔮 h ↦
    prime_of_normalized_factor 𝔮 (Multiset.mem_toFinset.mp h)
  choose z hz1 hz2 using fun (i : {i // i ∈ S}) ↦
    Ideal.exists_mem_pow_notMem_pow_succ (i : Ideal R)
      (hprimeS i i.2).ne_zero (Ideal.IsPrime.ne_top (Ideal.isPrime_of_prime (hprimeS i i.2)))
      (e i)
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun 𝔮 ↦ 𝔮)
    (fun 𝔮 ↦ e 𝔮 + 1) hprimeS (fun i _ j _ h ↦ h) z
  have hxmem : ∀ 𝔮 (h𝔮 : 𝔮 ∈ S), x ∈ 𝔮 ^ e 𝔮 := by
    intro 𝔮 h𝔮
    have h3 : x = z ⟨𝔮, h𝔮⟩ + (x - z ⟨𝔮, h𝔮⟩) := by ring
    rw [h3]
    exact Ideal.add_mem _ (hz1 ⟨𝔮, h𝔮⟩)
      (Ideal.pow_le_pow_right (Nat.le_succ _) (hx 𝔮 h𝔮))
  have hxnot : ∀ 𝔮 (h𝔮 : 𝔮 ∈ S), x ∉ 𝔮 ^ (e 𝔮 + 1) := by
    intro 𝔮 h𝔮 hmem
    refine hz2 ⟨𝔮, h𝔮⟩ ?_
    have h3 : z ⟨𝔮, h𝔮⟩ = x - (x - z ⟨𝔮, h𝔮⟩) := by ring
    rw [h3]
    exact Ideal.sub_mem _ hmem (hx 𝔮 h𝔮)
  have hx0 : x ≠ 0 := fun h0 ↦ hxnot 𝔮₀ h𝔮₀ (h0 ▸ zero_mem _)
  have hsx0 : (span {x} : Ideal R) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, span_singleton_eq_bot]
    exact hx0
  -- `I` divides `(x)`
  have hIdvd : I ∣ span {x} := by
    rw [dvd_iff_emultiplicity_le hI]
    intro q hq
    by_cases hqI : q ∣ I
    · have hqS : q ∈ S := Multiset.mem_toFinset.mpr
        ((Ideal.mem_normalizedFactors_iff hT).mpr ⟨Ideal.isPrime_of_prime hq,
          Ideal.dvd_iff_le.mp (hqI.trans (dvd_mul_right I M))⟩)
      have h4 : emultiplicity q I = e q := by
        rw [he, emultiplicity_eq_count_normalizedFactors hq.irreducible hI, normalize_eq]
      rw [h4]
      have h5 : q ^ e q ∣ span {x} := Ideal.dvd_span_singleton.mpr (hxmem q hqS)
      exact pow_dvd_iff_le_emultiplicity.mp h5
    · rw [emultiplicity_eq_zero.mpr hqI]
      exact zero_le
  obtain ⟨J, hJ⟩ := hIdvd
  have hJ0 : J ≠ 0 := fun h0 ↦ hsx0 (by rw [hJ, h0, mul_zero])
  refine ⟨x, J, hx0, hJ0, hJ, ?_⟩
  -- coprimality of `J` and `M`
  by_contra hsup
  obtain ⟨𝔪, h𝔪max, h𝔪⟩ := Ideal.exists_le_maximal _ hsup
  have h𝔪prime : Prime 𝔪 := Ideal.prime_of_isPrime
    (fun h0 ↦ hM (eq_bot_iff.mpr (h0 ▸ (le_sup_right.trans h𝔪)))) h𝔪max.isPrime
  have h𝔪J : 𝔪 ∣ J := Ideal.dvd_iff_le.mpr (le_sup_left.trans h𝔪)
  have h𝔪M : 𝔪 ∣ M := Ideal.dvd_iff_le.mpr (le_sup_right.trans h𝔪)
  have h𝔪S : 𝔪 ∈ S := Multiset.mem_toFinset.mpr
    ((Ideal.mem_normalizedFactors_iff hT).mpr ⟨Ideal.isPrime_of_prime h𝔪prime,
      Ideal.dvd_iff_le.mp (h𝔪M.mul_left I)⟩)
  -- the valuation of `(x)` at `𝔪` exceeds `e 𝔪`
  have h6 : emultiplicity 𝔪 I = e 𝔪 := by
    rw [he, emultiplicity_eq_count_normalizedFactors h𝔪prime.irreducible hI, normalize_eq]
  have h7 : 1 ≤ emultiplicity 𝔪 J := by
    exact pow_dvd_iff_le_emultiplicity.mp (by rwa [pow_one])
  have h8 : ((e 𝔪 + 1 : ℕ) : ℕ∞) ≤ emultiplicity 𝔪 (span {x}) := by
    rw [hJ, emultiplicity_mul h𝔪prime, h6]
    push_cast
    exact add_le_add le_rfl h7
  have h9 : 𝔪 ^ (e 𝔪 + 1) ∣ span {x} := pow_dvd_iff_le_emultiplicity.mpr h8
  exact hxnot 𝔪 h𝔪S (Ideal.dvd_span_singleton.mp h9)

/-- **The moving lemma**: in a Dedekind domain, every nonzero ideal `I` is equivalent, in the
ideal class group, to a nonzero ideal `J` coprime to a given nonzero modulus `M`. -/
theorem Ideal.exists_span_mul_eq_span_mul_coprime {R : Type*} [CommRing R] [IsDedekindDomain R]
    {M : Ideal R} (hM : M ≠ 0) {I : Ideal R} (hI : I ≠ 0) :
    ∃ (x y : R) (J : Ideal R), x ≠ 0 ∧ J ≠ 0 ∧ span {x} * I = span {y} * J ∧ J ⊔ M = ⊤ := by
  obtain ⟨y, J1, hy, hJ1, hspan1, hcop1⟩ := Ideal.exists_span_eq_mul_coprime hM hI
  obtain ⟨x, J, hx, hJ, hspan2, hcop2⟩ := Ideal.exists_span_eq_mul_coprime hM hJ1
  refine ⟨x, y, J, hx, hJ, ?_, hcop2⟩
  rw [hspan2, hspan1]
  ring
