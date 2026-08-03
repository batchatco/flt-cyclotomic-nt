import CyclotomicNT.Stickelberger

/-!
# Herbrand, step 1: eigenclasses and the Stickelberger exponent-kill

For a class `cl` of order `p` in `Cl(ℚ(ζ_p))` on which the Galois group acts through the
`k`-th power of the cyclotomic character (`σ_a · cl = cl^{a^k}`), the Stickelberger relation
`∏_a (σ_a⁻¹ cl)^{⌊c·a/p⌋} = 1` collapses to a single scalar relation

  `p ∣ ∑_a (a^{−k} mod p)·⌊c·a/p⌋`   for every `c : ℕ`.

This is the eigenspace projection of Stickelberger; identifying the right-hand sum with
`(c^{p−k} − 1)·B_{p−k}` modulo `p` (the Bernoulli step, `HerbrandBernoulli`) yields Herbrand's
theorem.
-/

open NumberField IsCyclotomicExtension.Rat

namespace CyclotomicNT

variable {p : ℕ} [hpri : Fact p.Prime] {k₀ : Type*} [Field k₀] [NumberField k₀]
  [IsCyclotomicExtension {p} ℚ k₀]

/-- `cl` is an eigenclass of weight `k`: each `σ_a ∈ Gal(k₀/ℚ)` (corresponding to
`a ∈ (ℤ/p)ˣ` under `galEquivZMod`) acts on `cl` by the scalar `a^k`. -/
def IsEigenClass (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} ℚ k₀] (k : ℕ)
    (cl : ClassGroup (𝓞 k₀)) : Prop :=
  ∀ a : (ZMod p)ˣ,
    classGroupGalAct ((galEquivZMod p k₀).symm a) cl = cl ^ ((a ^ k : (ZMod p)ˣ) : ZMod p).val

/-- **The Stickelberger relation on a weight-`k` eigenclass collapses to a scalar**: the class
is killed by the integer `∑_a (a^{−k} mod p)·⌊c·a/p⌋`. -/
theorem eigenClass_pow_sum_eq_one {k : ℕ} {cl : ClassGroup (𝓞 k₀)}
    (heig : IsEigenClass p k cl) (c : ℕ) :
    cl ^ (∑ a : (ZMod p)ˣ,
      ((a⁻¹ ^ k : (ZMod p)ˣ) : ZMod p).val * (c * (a : ZMod p).val / p)) = 1 := by
  have hst := stickelberger_annihilates (p := p) c cl
  calc cl ^ (∑ a : (ZMod p)ˣ,
      ((a⁻¹ ^ k : (ZMod p)ˣ) : ZMod p).val * (c * (a : ZMod p).val / p))
      = ∏ a : (ZMod p)ˣ,
          cl ^ (((a⁻¹ ^ k : (ZMod p)ˣ) : ZMod p).val * (c * (a : ZMod p).val / p)) :=
        (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ = ∏ a : (ZMod p)ˣ,
          (classGroupGalAct (((galEquivZMod p k₀).symm a)⁻¹) cl)
            ^ (c * (a : ZMod p).val / p) := by
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [← map_inv ((galEquivZMod p k₀).symm) a, heig a⁻¹, ← pow_mul]
    _ = 1 := hst

/-- **The eigenspace projection of Stickelberger**: a nontrivial weight-`k` eigenclass of
order dividing `p` forces `p ∣ ∑_a (a^{−k} mod p)·⌊c·a/p⌋` for every `c`. -/
theorem eigenClass_dvd_sum {k : ℕ} {cl : ClassGroup (𝓞 k₀)} (hcl1 : cl ≠ 1)
    (hclp : cl ^ p = 1) (heig : IsEigenClass p k cl) (c : ℕ) :
    p ∣ ∑ a : (ZMod p)ˣ,
      ((a⁻¹ ^ k : (ZMod p)ˣ) : ZMod p).val * (c * (a : ZMod p).val / p) := by
  have hord : orderOf cl = p := by
    rcases (Nat.dvd_prime hpri.out).mp (orderOf_dvd_of_pow_eq_one hclp) with h1 | hp
    · exact absurd (orderOf_eq_one_iff.mp h1) hcl1
    · exact hp
  have hdvd := orderOf_dvd_of_pow_eq_one (eigenClass_pow_sum_eq_one heig c)
  rwa [hord] at hdvd

end CyclotomicNT
