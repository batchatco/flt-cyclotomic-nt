import CyclotomicNT.DedekindEulerProduct
import Mathlib.Data.Sym.Card

/-!
# Counting ideals of prime-power norm (toward the local Euler factor's ideal count)

The Euler matching `ζ_K = ∏_χ L` needs `idealCount K (pᵉ) = C(e/f + g−1, g−1)` for `f ∣ e` (else 0),
where `f` is the residue degree and `g` the number of primes above `p` (`LocalFactor.lean` consumes
this as the hypothesis `hcount`).  The ideal-theoretic content reduces to a bijection

  `{I : Ideal (𝓞 K) // absNorm I = pᵉ} ≃ {s : Multiset (primes above p) // s.card = e/f}`

(an ideal of norm `pᵉ` is `∏ 𝔭ᵢ^{aᵢ}` over the primes above `p`, with `∑ aᵢ = e/f` since each
`absNorm 𝔭ᵢ = p^f`), after which `Sym.card_sym_eq_choose` gives the count `C(e/f + g−1, e/f)`.

This file builds the **foundational lemmas** for that bijection (axiom-clean):
* `absNorm_eq_prod_normalizedFactors` — `absNorm I = ∏ absNorm` over the prime factorization;
* `exists_pow_of_dvd_absNorm_pow` — every prime factor of an ideal of norm `pᵉ` has norm a power of
  `p` (so the factorization is supported on primes above `p`).

The full bijection — assembling the `Multiset`/`Sym` count and folding in the cyclotomic splitting
data (`ncard_primesOver_of_prime_pow`, `inertiaDegIn_eq_of_prime_pow`, all `f` equal) — is consumed
where needed as the `hcount` hypothesis of `LocalFactor.lean`.
-/

open NumberField UniqueFactorizationMonoid

namespace CyclotomicNT

variable {K : Type*} [Field K] [NumberField K]

/-- `absNorm I = ∏_{Q ∈ normalizedFactors I} absNorm Q`: the ideal norm is the product of the norms
of the prime factors (`absNorm` is a multiplicative-with-zero hom, `prod_normalizedFactors` for the
factorization, `associated_iff_eq` since ideals have unique units). -/
theorem absNorm_eq_prod_normalizedFactors (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    Ideal.absNorm I = ((normalizedFactors I).map Ideal.absNorm).prod := by
  conv_lhs => rw [← associated_iff_eq.mp (prod_normalizedFactors hI)]
  rw [map_multiset_prod]

/-- A maximal ideal `Q` dividing an ideal of norm `pᵉ` (with `p` prime) has norm a power of `p` —
hence lies above `p`.  (`absNorm Q ∣ absNorm I = pᵉ`, and `absNorm Q = qⁿ` is a prime power, forcing
`q = p`.) -/
theorem exists_pow_of_dvd_absNorm_pow {p e : ℕ} (hp : p.Prime) {I : Ideal (𝓞 K)}
    (hI : Ideal.absNorm I = p ^ e) (Q : Ideal (𝓞 K)) [Q.IsMaximal] (hQ : Q ∣ I) :
    ∃ n, Ideal.absNorm Q = p ^ n := by
  obtain ⟨q, n, hn, _, hq, hQn⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q
  have hdvd : Ideal.absNorm Q ∣ Ideal.absNorm I := by
    obtain ⟨J, rfl⟩ := hQ
    rw [map_mul]; exact Dvd.intro _ rfl
  rw [hI, hQn] at hdvd
  have hqp : q = p :=
    (Nat.prime_dvd_prime_iff_eq hq hp).mp
      (hq.dvd_of_dvd_pow (dvd_trans (dvd_pow_self q hn.ne') hdvd))
  exact ⟨n, by rw [hQn, hqp]⟩

/-- A maximal ideal `Q` dividing an ideal of norm `pᵉ` **lies over** the rational prime `(p)`:
`p ∈ Q` (since `absNorm Q = pⁿ ∈ Q`), and a prime of `ℤ` containing the maximal ideal `span{p}` is
`span{p}` itself.  This lets `normalizedFactors I` be read as a multiset of primes above `p`. -/
theorem liesOver_span_of_dvd_absNorm_pow {p e : ℕ} (hp : p.Prime) {I : Ideal (𝓞 K)}
    (hI : Ideal.absNorm I = p ^ e) (Q : Ideal (𝓞 K)) [hQmax : Q.IsMaximal] (hQ : Q ∣ I) :
    Q.LiesOver (Ideal.span {(p : ℤ)}) := by
  obtain ⟨n, hn⟩ := exists_pow_of_dvd_absNorm_pow hp hI Q hQ
  -- `p ∈ Q` from `pⁿ = absNorm Q ∈ Q` and primality
  have hpmem : (p : 𝓞 K) ∈ Q := by
    have hmem : ((Ideal.absNorm Q : ℕ) : 𝓞 K) ∈ Q := Ideal.absNorm_mem Q
    rw [hn] at hmem
    push_cast at hmem
    exact hQmax.isPrime.mem_of_pow_mem n hmem
  -- `under = span{p}` since `span{p}` is maximal and contained in the prime `Q.under ℤ`
  have hle : Ideal.span {(p : ℤ)} ≤ Q.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hpmem
  have hMmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (Nat.prime_iff_prime_int.mp hp).irreducible
  exact ⟨hMmax.eq_of_le (Ideal.IsPrime.under ℤ Q).ne_top hle⟩

/-- If every prime factor of `I ≠ 0` has norm `p^f`, then `absNorm I = p^(f · #factors)`.  (The norm
is the product over `normalizedFactors I`, a multiset of `p^f`'s of length `#factors`.) -/
theorem absNorm_eq_pow_card_normalizedFactors {p f : ℕ} {I : Ideal (𝓞 K)} (hI : I ≠ 0)
    (huniform : ∀ Q ∈ normalizedFactors I, Ideal.absNorm Q = p ^ f) :
    Ideal.absNorm I = p ^ (f * Multiset.card (normalizedFactors I)) := by
  rw [absNorm_eq_prod_normalizedFactors I hI]
  rw [show (normalizedFactors I).map Ideal.absNorm
        = Multiset.replicate (Multiset.card (normalizedFactors I)) (p ^ f) from ?_]
  · rw [Multiset.prod_replicate, ← pow_mul]
  · rw [Multiset.eq_replicate]
    refine ⟨Multiset.card_map _ _, fun b hb => ?_⟩
    obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.1 hb
    exact huniform Q hQ

/-- Each prime factor `Q` of an ideal of norm `pᵉ` has `absNorm Q = p^f`, where `f` is the residue
degree `inertiaDeg` of `Q` over `(p)` (given as a hypothesis — constant across the primes above `p`
in the Galois/cyclotomic case).  Combines `liesOver_span_of_dvd_absNorm_pow` with
`absNorm_eq_pow_inertiaDeg'`. -/
theorem absNorm_factor_eq_pow {p e f : ℕ} (hp : p.Prime) {I : Ideal (𝓞 K)}
    (hI : Ideal.absNorm I = p ^ e) {Q : Ideal (𝓞 K)} (hQ : Q ∈ normalizedFactors I)
    (hdeg : (Ideal.span {(p : ℤ)}).inertiaDeg Q = f) :
    Ideal.absNorm Q = p ^ f := by
  have hIne : I ≠ 0 := by
    rintro rfl; rw [map_zero] at hI; exact (pow_ne_zero e hp.ne_zero) hI.symm
  have hQprime : Prime Q := prime_of_normalized_factor Q hQ
  have hQdvd : Q ∣ I := dvd_of_mem_normalizedFactors hQ
  haveI hQP : Q.IsPrime := Ideal.isPrime_of_prime hQprime
  haveI hQmax : Q.IsMaximal := hQP.isMaximal hQprime.ne_zero
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
    liesOver_span_of_dvd_absNorm_pow hp hI Q hQdvd
  rw [Ideal.absNorm_eq_pow_inertiaDeg' Q hp, hdeg]

/-- For an ideal of norm `pᵉ` whose primes above `p` all have residue degree `f`, the number of
prime factors (with multiplicity) is exactly `e/f`: `f · #factors = e`.  In
particular `f ∣ e`. (Combines
the uniform factor norm `p^f` with `absNorm I = p^(f·#factors) = p^e`, cancelling the base `p`.) -/
theorem card_normalizedFactors_mul_eq {p e f : ℕ} (hp : p.Prime) {I : Ideal (𝓞 K)}
    (hI : Ideal.absNorm I = p ^ e)
    (hdeg : ∀ Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K),
        (Ideal.span {(p : ℤ)}).inertiaDeg Q = f) :
    f * Multiset.card (normalizedFactors I) = e := by
  have hIne : I ≠ 0 := by
    rintro rfl; rw [map_zero] at hI; exact (pow_ne_zero e hp.ne_zero) hI.symm
  have huniform : ∀ Q ∈ normalizedFactors I, Ideal.absNorm Q = p ^ f := by
    intro Q hQ
    have hQprime : Prime Q := prime_of_normalized_factor Q hQ
    haveI hQP : Q.IsPrime := Ideal.isPrime_of_prime hQprime
    haveI hQmax : Q.IsMaximal := hQP.isMaximal hQprime.ne_zero
    haveI hlo : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
      liesOver_span_of_dvd_absNorm_pow hp hI Q (dvd_of_mem_normalizedFactors hQ)
    exact absNorm_factor_eq_pow hp hI hQ (hdeg Q ⟨hQP, hlo⟩)
  have hnorm := absNorm_eq_pow_card_normalizedFactors hIne huniform
  have heq : p ^ e = p ^ (f * Multiset.card (normalizedFactors I)) := by rw [← hI, hnorm]
  exact (Nat.pow_right_injective hp.two_le heq).symm

/-- **Backward direction norm:** the product of a multiset of ideals each of norm `p^f` has norm
`p^(f · #s)`.  (The image multiset `s.map absNorm` is `replicate (#s) (p^f)`.) -/
theorem absNorm_multiset_prod_eq_pow {p f : ℕ} {s : Multiset (Ideal (𝓞 K))}
    (huniform : ∀ Q ∈ s, Ideal.absNorm Q = p ^ f) :
    Ideal.absNorm s.prod = p ^ (f * Multiset.card s) := by
  rw [map_multiset_prod]
  rw [show s.map Ideal.absNorm = Multiset.replicate (Multiset.card s) (p ^ f) from ?_]
  · rw [Multiset.prod_replicate, ← pow_mul]
  · rw [Multiset.eq_replicate]
    exact ⟨Multiset.card_map _ _, fun b hb => by
      obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.1 hb; exact huniform Q hQ⟩

open scoped Classical in
/-- **The counting bijection (Sym-native form).**  When the primes above `p` all have residue degree
`f` (and `f ∣ e`), ideals of norm `pᵉ` correspond to multisets of size `e/f` of primes above `p`:
`{I // absNorm I = pᵉ} ≃ Sym (primesOver (p)) (e/f)`.  Forward: `I ↦ normalizedFactors I` (each
factor is a prime above `p`, total `e/f`); backward: `s ↦ ∏ s`.  The count is then the multichoose
`(g + e/f − 1).choose (e/f)` (`Sym.card_sym_eq_choose`, `g = #primes above p`). -/
theorem card_setOf_absNorm_eq_prime_pow_sym {p e f g : ℕ} (hp : p.Prime) (hf : 0 < f) (hfe : f ∣ e)
    (hdeg : ∀ Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K),
        (Ideal.span {(p : ℤ)}).inertiaDeg Q = f)
    (hg : Nat.card (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) = g) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ e} = (g + e / f - 1).choose (e / f) := by
  set S := Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K) with hS
  haveI hMmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  haveI hSfin : Fintype ↥S := by rw [hS]; infer_instance
  -- each prime above `p` has norm `p^f`
  have hSnorm : ∀ Q ∈ S, Ideal.absNorm Q = p ^ f := by
    rintro Q ⟨hQP, hlo⟩
    haveI := hlo
    rw [Ideal.absNorm_eq_pow_inertiaDeg' Q hp, hdeg Q ⟨hQP, hlo⟩]
  -- every prime factor of a norm-`pᵉ` ideal lies in `S`
  have hmem : ∀ {I : Ideal (𝓞 K)}, Ideal.absNorm I = p ^ e →
      ∀ Q ∈ normalizedFactors I, Q ∈ S := by
    intro I hI Q hQ
    have hQprime := prime_of_normalized_factor Q hQ
    haveI hQP := Ideal.isPrime_of_prime hQprime
    haveI hQmax := hQP.isMaximal hQprime.ne_zero
    exact ⟨hQP, liesOver_span_of_dvd_absNorm_pow hp hI Q (dvd_of_mem_normalizedFactors hQ)⟩
  have hIne : ∀ {I : Ideal (𝓞 K)}, Ideal.absNorm I = p ^ e → I ≠ 0 := by
    intro I hI h; rw [h, map_zero] at hI; exact (pow_ne_zero e hp.ne_zero) hI.symm
  -- elements of `S` are irreducible (prime, nonzero since norm `p^f ≠ 0`)
  have hSirr : ∀ q : S, Irreducible q.1 := by
    intro q
    have hne : q.1 ≠ 0 := fun h => by
      have hz := hSnorm q.1 q.2
      rw [h, map_zero] at hz
      exact (pow_ne_zero f hp.ne_zero) hz.symm
    exact ((Ideal.prime_iff_isPrime hne).mpr q.2.1).irreducible
  -- the bijection
  have e_equiv : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ e} ≃ Sym S (e / f) := by
    refine
      { toFun := fun I =>
          ⟨(normalizedFactors I.1).attach.map (fun x => ⟨x.1, hmem I.2 x.1 x.2⟩), ?_⟩
        invFun := fun s => ⟨(s.1.map Subtype.val).prod, ?_⟩
        left_inv := ?_, right_inv := ?_ }
    · -- card of forward = e/f
      rw [Multiset.card_map, Multiset.card_attach]
      have hcard := card_normalizedFactors_mul_eq hp I.2 hdeg
      exact (Nat.div_eq_of_eq_mul_left hf (by rw [mul_comm]; exact hcard.symm)).symm
    · -- norm of backward = p^e
      have huniform : ∀ Q ∈ s.1.map Subtype.val, Ideal.absNorm Q = p ^ f := by
        intro Q hQ
        obtain ⟨q, _, rfl⟩ := Multiset.mem_map.1 hQ
        exact hSnorm q.1 q.2
      rw [absNorm_multiset_prod_eq_pow huniform, Multiset.card_map, s.2,
        Nat.mul_div_cancel' hfe]
    · -- left inverse
      rintro ⟨I, hI⟩
      apply Subtype.ext
      simp only [Multiset.map_map, Function.comp_def, Multiset.attach_map_val]
      exact associated_iff_eq.mp (prod_normalizedFactors (hIne hI))
    · -- right inverse
      rintro ⟨m, hm⟩
      apply Subtype.ext
      have hirr : ∀ Q ∈ m.map Subtype.val, Irreducible Q := by
        intro Q hQ
        obtain ⟨q, _, rfl⟩ := Multiset.mem_map.1 hQ
        exact hSirr q
      have hnf : normalizedFactors ((m.map Subtype.val).prod) = m.map Subtype.val := by
        rw [normalizedFactors_prod_eq _ hirr]
        refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id _)
        intro Q _; exact associated_iff_eq.mp (normalize_associated Q)
      apply Multiset.map_injective Subtype.val_injective
      simp only [Multiset.map_map, Function.comp_def, Multiset.attach_map_val, hnf]
  have hScard : Fintype.card ↥S = g := by rw [← Nat.card_eq_fintype_card]; exact hg
  rw [Nat.card_congr e_equiv, Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, hScard]

/-- When `f ∤ e` there are **no** ideals of norm `pᵉ` (every such ideal has norm `p^(f·#factors)`,
forcing `f ∣ e`), so the count is `0`. -/
theorem card_setOf_absNorm_eq_prime_pow_of_not_dvd {p e f : ℕ} (hp : p.Prime)
    (hdeg : ∀ Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K),
        (Ideal.span {(p : ℤ)}).inertiaDeg Q = f)
    (hfe : ¬ f ∣ e) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ e} = 0 := by
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun I => hfe ⟨_, (card_normalizedFactors_mul_eq hp I.2 hdeg).symm⟩⟩

/-- **The local ideal count** in `hcount` form: with the primes above `p` all of residue degree `f`
and `g` of them, `idealCount K (pᵉ) = if f ∣ e then C(e/f + g−1, g−1) else 0`.  This is exactly the
hypothesis consumed by `LocalFactor.tsum_dedekindSummand_prime_pow` to give the Euler factor
`(1 − p^{-sf})^{-g}` of `ζ_K` — closing the ideal-counting input to `ζ_K = ∏_χ L`. -/
theorem idealCount_prime_pow {p e f g : ℕ} (hp : p.Prime) (hf : 0 < f) (hg0 : 0 < g)
    (hdeg : ∀ Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K),
        (Ideal.span {(p : ℤ)}).inertiaDeg Q = f)
    (hg : Nat.card (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) = g) :
    idealCount K (p ^ e) = if f ∣ e then (e / f + (g - 1)).choose (g - 1) else 0 := by
  rw [idealCount_apply_of_ne_zero K (pow_ne_zero e hp.ne_zero)]
  have hn : g + e / f - 1 = e / f + (g - 1) := by
    rw [Nat.add_comm g (e / f), Nat.add_sub_assoc hg0]
  by_cases hfe : f ∣ e
  · rw [if_pos hfe, card_setOf_absNorm_eq_prime_pow_sym hp hf hfe hdeg hg, hn,
      Nat.choose_symm_add]
  · rw [if_neg hfe, card_setOf_absNorm_eq_prime_pow_of_not_dvd hp hdeg hfe]

end CyclotomicNT
