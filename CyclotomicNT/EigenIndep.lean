import CyclotomicNT.EigenReindex

/-!
# Thm 8.14, step (4) — linear independence of the eigenvectors (foundation)

The cyclotomic units `Eᵢ` (even `i ∈ [2,p-3]`) are eigenvectors of `T = σ_g` with eigenvalues
`g^i` (`galV_eigen`).  Taking `g` a primitive root mod `p`, these eigenvalues are *distinct*, so if
no `Eᵢ` is a `p`-th power (all images nonzero) the `Eᵢ` are linearly independent in `V = E/E^p`;
    with
the `p`-rank bound they then span.  This file starts with the primitive-root distinctness. -/

namespace CyclotomicNT

open scoped NumberField
open Finset

variable {p : ℕ} [hpri : Fact p.Prime]

/-- There is a primitive root `g` mod `p` whose powers `g^i` (for `i < p-1`) are distinct in `ZMod
    p`
— the source of the distinct eigenvalues. -/
theorem exists_primRoot_pow_inj :
    ∃ g : (ZMod p)ˣ, ∀ i j : ℕ, i < p - 1 → j < p - 1 →
      (g : ZMod p) ^ i = (g : ZMod p) ^ j → i = j := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units p]
  refine ⟨g, fun i j hi hj h => ?_⟩
  have hgu : g ^ i = g ^ j := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]; exact h
  rw [pow_eq_pow_iff_modEq, hord] at hgu
  have h2 : i % (p - 1) = j % (p - 1) := hgu
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h2

open NumberField NumberField.IsCMField Module in
section
variable {K : Type*} [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}

/-- The eigenvector family `k ↦ Ē_{2(k+1)}` (`k : Fin ((p-3)/2)`), indexing the even `i ∈
    [2,p-3]`. -/
noncomputable def eigenFamily (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (k : Fin ((p - 3) / 2)) :
    ModN (Additive (realUnits K)) p :=
  vOf ⟨eigenCyclotomicUnit hζ (2 * (k.1 + 1)), eigenCyclotomicUnit_mem_realUnits hζ hp _⟩

theorem eigenFamily_linindep (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (g : (ZMod p)ˣ)
    (hg : ∀ i j : ℕ, i < p - 1 → j < p - 1 → (g : ZMod p) ^ i = (g : ZMod p) ^ j → i = j)
    (hne : ∀ k : Fin ((p - 3) / 2), eigenFamily hζ hp k ≠ 0) :
    LinearIndependent (ZMod p) (eigenFamily hζ hp) := by
  have hp1 : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two hp)
  have h2le : 2 ≤ p := hpri.out.two_le
  refine Module.End.eigenvectors_linearIndependent' (galV hζ g)
    (fun k => (g : ZMod p) ^ (2 * (k.1 + 1))) ?_ (eigenFamily hζ hp) ?_
  · intro k1 k2 h
    have := hg (2 * (k1.1 + 1)) (2 * (k2.1 + 1)) (by omega) (by omega) h
    exact Fin.ext (by omega)
  · intro k
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hne k⟩
    exact galV_eigen hζ hp g (2 * (k.1 + 1)) ⟨k.1 + 1, by ring⟩ (by omega) (by omega)

theorem eigenFamily_span (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (g : (ZMod p)ˣ)
    (hg : ∀ i j : ℕ, i < p - 1 → j < p - 1 → (g : ZMod p) ^ i = (g : ZMod p) ^ j → i = j)
    (hne : ∀ k : Fin ((p - 3) / 2), eigenFamily hζ hp k ≠ 0) :
    Submodule.span (ZMod p) (Set.range (eigenFamily hζ hp)) = ⊤ := by
  have hli := eigenFamily_linindep hζ hp g hg hne
  have hcard : Fintype.card (Fin ((p - 3) / 2))
      = finrank (ZMod p) (ModN (Additive (realUnits K)) p) := by
    have hle : finrank (ZMod p) (ModN (Additive (realUnits K)) p) ≤ (p - 3) / 2 :=
      unitModP_finrank_le hp
    have hge : Fintype.card (Fin ((p - 3) / 2))
        ≤ finrank (ZMod p) (ModN (Additive (realUnits K)) p) := hli.fintype_card_le_finrank
    rw [Fintype.card_fin] at hge ⊢
    omega
  exact hli.span_eq_top_of_card_eq_finrank' hcard

end

end CyclotomicNT
