import CyclotomicNT.CyclotomicUnitIndex
import CyclotomicNT.UnitModP
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.Noetherian.Orzech

/-!
# Washington Thm 8.14 from Thm 8.2 (single-operator eigenspace bridge)

This file builds the algebraic bridge `p ∣ h⁺ ⟺ some Eᵢ is a p-th power in E` on top of the index
theorem `cyclotomic_unit_index` (Thm 8.2, `[E:C]=h⁺`).  We **bypass `F_p[Δ]`,
Maschke and idempotents**: model `V = E/E^p` as a `ZMod p`-vector space via Mathlib's `ModN`, use
    the
*single* Galois operator `T = σ_g` (a primitive root `g`), observe that the explicit exponent of
    `Eᵢ`
makes it an eigenvector with eigenvalue `g^i`, and finish by linear independence of distinct
eigenvalues against a `p`-rank bound.

Done so far:
* the architecture-independent **engine** lemma (`p ∣ |G| ⟺` nontrivial `p`-torsion);
* the `ZMod p`-vector space `unitModP = E/E^p` with its **finiteness** (`E` is f.g. by Dirichlet but
  not free, so this is derived by hand, not from `ModN.instFinite`).

The Galois operator, `Eᵢ`-eigenvector computation, index reduction, and assembly
live in the subsequent `Thm814*`/`QiVandiverBridge` files. -/

namespace CyclotomicNT

open scoped NumberField
open NumberField.IsCMField Module

open scoped Classical in
/-- **Engine of Thm 8.14.**  A finite group has order divisible by a prime `p` iff it contains a
nontrivial element killed by `p`.  Applied to the finite group `E/(C·E^p)` (resp. an
    eigencomponent),
this turns `p ∣ [E:C]` into the existence of a unit that is "missing a `p`-th root", i.e. a `p`-th
power obstruction — the form the Thm 8.14 proof feeds through the `Δ`-eigenspace decomposition. -/
theorem prime_dvd_card_iff_exists_pow_eq_one {G : Type*} [Group G] [Finite G] (p : ℕ)
    [Fact p.Prime] : p ∣ Nat.card G ↔ ∃ x : G, x ≠ 1 ∧ x ^ p = 1 := by
  constructor
  · intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    refine ⟨x, ?_, ?_⟩
    · rintro rfl; simp only [orderOf_one] at hx; exact (Fact.out (p := p.Prime)).ne_one hx.symm
    · rw [← hx]; exact pow_orderOf_eq_one x
  · rintro ⟨x, hx1, hxp⟩
    have hord : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
    rcases (Nat.dvd_prime (Fact.out (p := p.Prime))).mp hord with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · rw [← h]; exact orderOf_dvd_natCard x

/-- **Index reduction engine.**  For a finite commutative group `Q`, `p ∣ |Q|` iff the `p`-th-power
map is *not* surjective.  Applied to `Q = E/C`: `C·E^p = E` says exactly that every class is a
    `p`-th
power, i.e. `x ↦ x^p` is surjective on `E/C`; so `p ∣ [E:C] ⟺ C·E^p ≠ E`. -/
theorem prime_dvd_card_iff_not_surjective_pow {Q : Type*} [CommGroup Q] [Finite Q] (p : ℕ)
    [Fact p.Prime] : p ∣ Nat.card Q ↔ ¬ Function.Surjective (fun q : Q => q ^ p) := by
  have hker : (fun q : Q => q ^ p) = ⇑(powMonoidHom p : Q →* Q) := by
    ext q; simp [powMonoidHom]
  rw [prime_dvd_card_iff_exists_pow_eq_one, hker, ← Finite.injective_iff_surjective,
    ← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall, not_forall]
  constructor
  · rintro ⟨x, hx1, hxp⟩
    exact ⟨x, fun h => hx1 (h (by simp [MonoidHom.mem_ker, powMonoidHom, hxp]))⟩
  · rintro ⟨x, hx⟩
    rw [Classical.not_imp] at hx
    exact ⟨x, hx.2, by simpa [MonoidHom.mem_ker, powMonoidHom] using hx.1⟩

section Module

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

/-- **`V = E/E^p`** — the real unit group `E = realUnits K` modulo `p`-th powers, as a `ZMod
    p`-vector
space (Mathlib's `ModN`, which supplies the `Module (ZMod p)` structure and quotient map for free).
The torsion `{±1}` of `E` dies automatically since `p` is odd (`−1 = (−1)^p`). -/
noncomputable abbrev unitModP : Type _ := ModN (Additive (realUnits K)) p

/-- `V = E/E^p` is finite-dimensional over `ZMod p`.  `E` is finitely generated (Dirichlet's unit
theorem: `Module.Finite ℤ (Additive (𝓞 K)ˣ)`) but **not free** (the torsion `{±1}`), so `ModN`'s
free-module finiteness instance does not apply; we derive it via Noetherianity of the ambient unit
group and base change `ℤ → ZMod p`. -/
instance unitModP.instModuleFinite : Module.Finite (ZMod p) (unitModP (K := K) (p := p)) := by
  haveI hinj : Function.Injective ((realUnits K).toAddSubgroup.subtype.toIntLinearMap) :=
    Subtype.val_injective
  haveI hN : IsNoetherian ℤ (Additive ↥(realUnits K)) := isNoetherian_of_injective _ hinj
  haveI : Module.Finite ℤ (unitModP (K := K) (p := p)) :=
    Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  exact Module.Finite.of_restrictScalars_finite ℤ (ZMod p) _

instance unitModP.instFinite : Finite (unitModP (K := K) (p := p)) :=
  Module.finite_of_finite (ZMod p)

/-- **`p`-rank bound** (Dirichlet's unit theorem consequence) — **now a THEOREM**
(`CyclotomicNT/UnitModP.lean`, axiom-free).  The real unit group `E = realUnits K` has free `ℤ`-rank
`(p−3)/2` and torsion `{±1}`; since `p` is odd `−1 = (−1)ᵖ` kills the `2`-torsion in `E/Eᵖ`, so
`dim_{F_p} E/Eᵖ = rank ≤ (p−3)/2`.  This is what lets the `(p−3)/2` eigenvectors `Eᵢ` (when none is
    a
`p`-th power) *span* `V`, rather than the deep "eigenspaces are 1-dimensional" fact. -/
theorem unitModP_finrank_le {K : Type*} {p : ℕ} [Fact p.Prime] [Field K] [CharZero K] [NumberField
    K]
    [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] (hp : p ≠ 2) :
    finrank (ZMod p) (unitModP (K := K) (p := p)) ≤ (p - 3) / 2 :=
  unitModP_finrank_le_proof hp

end Module

end CyclotomicNT
