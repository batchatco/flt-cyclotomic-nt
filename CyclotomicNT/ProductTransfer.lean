import CyclotomicNT.CyclotomicRegulator
import CyclotomicNT.EigenvalueLValue

/-!
# `[E:C]·Reg(K⁺) = (√p/2)^{m−1} · ∏_{χ even ≠ 1} ‖L(1,χ)‖`

Combines the geometric half (`relIndex_cyclotomicUnitGroup_mul_regulator`:
`[E:C]·Reg(K⁺) = ∏_{k≠0}‖λ_k‖`) with the eigenvalue identification
(`lam_eq_neg_half_gaussSum_mul_LFunction`: `λ_{k(χ)} = −½τ(χ⁻¹)L(1,χ)`), the character
bijection (`evenCharEquiv`) and the Gauss sum absolute value (`norm_gaussSum_inv`: `‖τ‖ = √p`).

What remains for `cyclotomic_unit_index` is the identification
`∏_{χ even ≠1} L(1,χ) = Res_{s=1} ζ_{K⁺} = 2^{m−1}·h⁺·Reg(K⁺)/√(p^{m−2}·p)` — the Euler
factorization of `ζ_{K⁺}` and `|disc K⁺| = p^{(p−3)/2}`.
-/

open NumberField NumberField.Units NumberField.IsCMField Finset

namespace CyclotomicNT

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ p) {g : (ZMod p)ˣ}

open scoped Classical in
/-- **The cyclotomic-unit index against the even `L`-values**:
`[E:C]·Reg(K⁺) = (√p/2)^{m−1} · ∏_{χ even ≠1} ‖L(1,χ)‖`. -/
theorem relIndex_mul_regulator_eq_prod_norm_LFunction [NeZero ((p - 1) / 2)]
    (hgen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hp : p ≠ 2) :
    (((cyclotomicUnitGroup hζ).relIndex (realUnits K) : ℝ))
        * regulator (maximalRealSubfield K)
      = (Real.sqrt p / 2) ^ ((p - 1) / 2 - 1)
        * ∏ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ p)).filter
            (fun χ : DirichletCharacter ℂ p => χ.Even), ‖DirichletCharacter.LFunction χ 1‖ := by
  classical
  rw [relIndex_cyclotomicUnitGroup_mul_regulator hζ hgen hp]
  -- the index set of even nontrivial characters
  set S : Finset (DirichletCharacter ℂ p) :=
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)).filter
      (fun χ : DirichletCharacter ℂ p => χ.Even) with hS
  have hmemS : ∀ χ : DirichletCharacter ℂ p, χ ∈ S ↔ χ.Even ∧ χ ≠ 1 := by
    intro χ
    rw [hS, Finset.mem_filter, Finset.mem_erase]
    simp only [Finset.mem_univ, and_true]
    tauto
  -- the equivalence `{χ // χ ∈ S} ≃ {k // k ≠ 0}`
  let e1 : {χ : DirichletCharacter ℂ p // χ ∈ S} ≃
      {c : {χ : DirichletCharacter ℂ p // χ.Even} // c.1 ≠ 1} :=
    { toFun := fun c => ⟨⟨c.1, ((hmemS c.1).mp c.2).1⟩, ((hmemS c.1).mp c.2).2⟩
      invFun := fun d => ⟨d.1.1, (hmemS d.1.1).mpr ⟨d.1.2, d.2⟩⟩
      left_inv := fun c => rfl
      right_inv := fun d => rfl }
  let e2 : {c : {χ : DirichletCharacter ℂ p // χ.Even} // c.1 ≠ 1} ≃
      {k : ZMod ((p - 1) / 2) // k ≠ 0} :=
    (evenCharEquiv hgen hp).subtypeEquiv fun c =>
      not_congr (evenCharIdx_eq_zero_iff hgen hp c).symm
  -- transfer the product
  rw [← Equiv.prod_comp (e1.trans e2)
    (fun k : {k : ZMod ((p - 1) / 2) // k ≠ 0} =>
      ‖∑ x : ZMod ((p - 1) / 2), ((vIdx g x : ℝ) : ℂ)
        * (AddChar.mulShift ZMod.stdAddChar k.1) (-x)‖)]
  -- evaluate each factor through the eigenvalue identity
  have hterm : ∀ c : {χ : DirichletCharacter ℂ p // χ ∈ S},
      ‖∑ x : ZMod ((p - 1) / 2), ((vIdx g x : ℝ) : ℂ)
          * (AddChar.mulShift ZMod.stdAddChar (((e1.trans e2) c) : ZMod ((p - 1) / 2))) (-x)‖
        = Real.sqrt p / 2 * ‖DirichletCharacter.LFunction c.1 1‖ := by
    intro c
    have hk : (((e1.trans e2) c) : ZMod ((p - 1) / 2))
        = evenCharIdx hgen hp ⟨c.1, ((hmemS c.1).mp c.2).1⟩ := rfl
    have hhalf : ‖(-(1 / 2) : ℂ)‖ = 1 / 2 := by
      rw [norm_neg, show ((1 : ℂ) / 2) = ((2 : ℂ))⁻¹ by norm_num, norm_inv,
        Complex.norm_ofNat]
      norm_num
    rw [hk, lam_eq_neg_half_gaussSum_mul_LFunction hgen hp _ ((hmemS c.1).mp c.2).2,
      norm_mul, norm_mul, hhalf, norm_gaussSum_inv _ ((hmemS c.1).mp c.2).2]
    ring
  rw [Finset.prod_congr rfl fun c _ => hterm c, Finset.prod_mul_distrib, Finset.prod_const]
  -- the cardinality of the index set
  have hcard : Finset.univ.card (α := {χ : DirichletCharacter ℂ p // χ ∈ S})
      = (p - 1) / 2 - 1 := by
    rw [Finset.card_univ, Fintype.card_congr (e1.trans e2)]
    have h2 := Fintype.card_subtype_compl (fun k : ZMod ((p - 1) / 2) => k = 0)
    rw [Fintype.card_subtype_eq] at h2
    have h3 : Fintype.card {k : ZMod ((p - 1) / 2) // k ≠ 0}
        = Fintype.card (ZMod ((p - 1) / 2)) - 1 := h2
    rw [h3, ZMod.card]
  rw [hcard]
  congr 1
  -- finally, identify the subtype product with the `Finset` product
  exact Finset.prod_coe_sort S (fun χ => ‖DirichletCharacter.LFunction χ 1‖)

end CyclotomicNT
