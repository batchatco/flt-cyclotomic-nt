import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.Int.Basic

/-!
# A coprimality transfer lemma for class-group maps

The "regular ⇒ Vandiver" step rests on a purely group-theoretic fact about the
pair of maps between `Cl(O_{K⁺})` and `Cl(O_K)`:

* `extend : Cl(O_{K⁺}) → Cl(O_K)` (extension of ideals), and
* `relNorm : Cl(O_K) → Cl(O_{K⁺})` (the relative ideal norm),

whose composite `relNorm ∘ extend` is squaring (because `N_{K/K⁺}(I · O_K) = I^{[K:K⁺]} = I²`).
This forces `ker extend` to be killed by `2`, hence to have `2`-power order, so any odd prime
not dividing `|Cl(O_K)|` cannot divide `|Cl(O_{K⁺})|` either.

This file proves that group-theoretic core in full generality.
-/

namespace CyclotomicNT

variable {A B : Type*} [CommGroup A] [CommGroup B] [Finite A]

omit [Finite A] in
/-- If `f : A →* B` admits a `g : B →* A` with `g ∘ f` equal to squaring, then every element
of `ker f` squares to the identity. -/
theorem sq_eq_one_of_mem_ker {f : A →* B} {g : B →* A} (hgf : ∀ a, g (f a) = a ^ 2)
    {a : A} (ha : a ∈ f.ker) : a ^ 2 = 1 := by
  have h := hgf a
  rw [(MonoidHom.mem_ker).mp ha, map_one] at h
  exact h.symm

/-- An odd prime that does not divide `|B|` does not divide `|ker f|`, given the squaring
factorization `g ∘ f = (· ^ 2)`: indeed `ker f` is killed by `2`, so its order is a power of
`2`. -/
theorem prime_not_dvd_card_ker {f : A →* B} {g : B →* A} (hgf : ∀ a, g (f a) = a ^ 2)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : ¬ p ∣ Nat.card f.ker := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) p hdvd
  have hx2 : (x : A) ^ 2 = 1 := sq_eq_one_of_mem_ker hgf x.2
  have hxsub : x ^ 2 = 1 := by
    apply Subtype.ext
    push_cast
    exact hx2
  have hp2 : p ∣ 2 := hx ▸ orderOf_dvd_of_pow_eq_one hxsub
  exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2)

/-- **Coprimality transfer.** If `f : A →* B` and `g : B →* A` satisfy `g (f a) = a ^ 2` for all
`a`, then any odd prime coprime to `|B|` is coprime to `|A|`.

Applied with `A = Cl(O_{K⁺})`, `B = Cl(O_K)`, this is exactly "`p ∤ h ⇒ p ∤ h⁺`" for odd `p`. -/
theorem coprime_card_of_sq {f : A →* B} {g : B →* A} (hgf : ∀ a, g (f a) = a ^ 2)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hB : p.Coprime (Nat.card B)) : p.Coprime (Nat.card A) := by
  have hdvd : Nat.card (A ⧸ f.ker) ∣ Nat.card B := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Subgroup.card_subgroup_dvd_card f.range
  rw [hp.coprime_iff_not_dvd, Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, hp.dvd_mul]
  rintro (h | h)
  · exact (hp.coprime_iff_not_dvd.mp hB) (h.trans hdvd)
  · exact prime_not_dvd_card_ker hgf hp hodd h

/-- **Coprime-power descent.** In a commutative group, if `u ^ m = w ^ n` with `m` and `n`
coprime, then `u` is an `n`-th power. (Bézout: with `m·a + n·b = 1`, one has
`u = (u ^ m) ^ a · (u ^ n) ^ b = (w ^ a · u ^ b) ^ n`.)

This is the descent that turns "`ι(u)` is a `p`-th power in `O_K`" plus
"`N(ι u) = u^{[K:K⁺]} = u²`" into "`u` is a `p`-th power in `O_{K⁺}`", using `[K:K⁺] = 2`
coprime to the odd prime `p`. -/
theorem exists_pow_eq_of_pow_eq_pow {G : Type*} [CommGroup G] {m n : ℕ} (hmn : Nat.Coprime m n)
    {u w : G} (h : u ^ m = w ^ n) : ∃ v : G, u = v ^ n := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, (m : ℤ) * a + (n : ℤ) * b = 1 := by
    have hco : IsCoprime (m : ℤ) (n : ℤ) := by
      rw [Int.isCoprime_iff_nat_coprime]; simpa using hmn
    obtain ⟨a, b, hba⟩ := hco
    exact ⟨a, b, by rw [mul_comm (m : ℤ) a, mul_comm (n : ℤ) b]; exact hba⟩
  have hz : u ^ (m : ℤ) = w ^ (n : ℤ) := by rw [zpow_natCast, zpow_natCast]; exact h
  refine ⟨w ^ a * u ^ b, ?_⟩
  calc u = u ^ ((m : ℤ) * a + (n : ℤ) * b) := by rw [hab, zpow_one]
    _ = (u ^ (m : ℤ)) ^ a * (u ^ (n : ℤ)) ^ b := by rw [zpow_add, zpow_mul, zpow_mul]
    _ = (w ^ (n : ℤ)) ^ a * (u ^ (n : ℤ)) ^ b := by rw [hz]
    _ = (w ^ a * u ^ b) ^ (n : ℤ) := by
        rw [mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul,
          mul_comm (n : ℤ) a, mul_comm (n : ℤ) b]
    _ = (w ^ a * u ^ b) ^ n := by rw [zpow_natCast]

/-- **Plus-part triviality (Case II principality core).** Let `f : A →* B`, `g : B →* A` be
homomorphisms of commutative groups such that `A` has no nontrivial `p`-torsion
(`∀ a, a ^ p = 1 → a = 1` — the form `IsVandiverPrime` provides for `A = Cl(O_{K⁺})`). If
`b : B` is `p`-torsion and satisfies `f (g b) = b ^ 2`, then `b = 1`.

Applied with `A = Cl(O_{K⁺})`, `B = Cl(O_K)`, `f` = extension, `g` = relative norm: a
`p`-torsion class `b = [I]` that is *fixed by complex conjugation* satisfies
`f (g b) = ι(N b) = b^{1+j} = b²`. Then `g b = N b` is `p`-torsion in `Cl(O_{K⁺})`, hence `1`
by Vandiver, so `b² = 1`; together with `b^p = 1` and `gcd(2, p) = 1` this forces `b = 1`.
This is the Galois-symmetry argument that lets `p ∤ h⁺` discharge the Case II principality
step (Varma §7 "Step 1") — in contrast to Case I, whose ideal classes lie in the *minus*
part and require Stickelberger's theorem. -/
theorem eq_one_of_pow_eq_one_of_image_sq {A B : Type*} [CommGroup A] [CommGroup B]
    (f : A →* B) (g : B →* A) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hA : ∀ a : A, a ^ p = 1 → a = 1)
    {b : B} (hbp : b ^ p = 1) (hsq : f (g b) = b ^ 2) : b = 1 := by
  have hgb : g b = 1 := hA _ (by rw [← map_pow, hbp, map_one])
  have hb2 : b ^ 2 = 1 := by rw [← hsq, hgb, map_one]
  have hco : Nat.gcd 2 p = 1 := Nat.coprime_two_left.mpr (hp.odd_of_ne_two hodd)
  have hdvd : orderOf b ∣ 1 :=
    hco ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hb2) (orderOf_dvd_of_pow_eq_one hbp)
  rwa [Nat.dvd_one, orderOf_eq_one_iff] at hdvd

end CyclotomicNT
