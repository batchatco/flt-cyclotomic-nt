import CyclotomicNT.CyclotomicEulerMatch
import CyclotomicNT.OddLOneValue

/-!
# The analytic class number formula for cyclotomic fields

Taking the residue at `s = 1` of the factorization `ζ_{ℚ(ζ_p)}(s) = ζ(s)·∏_{χ≠1}L(s,χ)`
(`dedekindZeta_eq_riemannZeta_mul_prod`): the `ζ(s)` simple pole (residue `1`,
`riemannZeta_residue_one`) meets the holomorphic values `L(1,χ)` (`χ ≠ 1` nontrivial, so
`DirichletCharacter.LFunction χ` is entire), giving

  `Res_{s=1} ζ_{ℚ(ζ_p)}(s) = ∏_{χ ≠ 1} L(1,χ)`.

Combined with Mathlib's Dirichlet class number formula
(`tendsto_sub_one_mul_dedekindZeta_nhdsGT`, `Res = dedekindZeta_residue K`), this yields

  `∏_{χ ≠ 1} L(1,χ) = (2^{r₁}(2π)^{r₂}·Reg·h)/(w·√|d|)`   (as a complex number),

the analytic class number formula factored through Dirichlet `L`-values — a step toward Washington
Thm 8.2 (`[E:C] = h⁺`).  The limit is taken along **real** `s → 1⁺` (matching Mathlib's residue
    lemma),
where the `LSeries`/`LFunction` factorization is valid (`Re s = s > 1`). -/

open NumberField Filter Topology

namespace CyclotomicNT

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K]

open scoped LSeries.notation Classical in
/-- **Residue of `ζ_{ℚ(ζ_p)}` as a product of Dirichlet `L`-values.**  `(dedekindZeta_residue K : ℂ)
= ∏_{χ ≠ 1} L(1,χ)`.  Both sides arise as the `s → 1⁺` limit of `(s−1)·ζ_K(s)`: the left from
Mathlib's class number formula, the right from `ζ_K = ζ·∏L` + the `ζ` residue `1` + continuity of
    the
nontrivial `LFunction χ` at `1`.  Uniqueness of limits closes it. -/
theorem dedekindZeta_residue_eq_prod_LFunction_one :
    (dedekindZeta_residue K : ℂ)
      = ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p),
          DirichletCharacter.LFunction χ 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- the real cast `s ↦ (s:ℂ)` sends `𝓝[>]1` into the punctured `𝓝[≠](1:ℂ)`
  have hcast_ne : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : (1 : ℝ) < s := hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have hs2 : s = 1 := by exact_mod_cast h
    linarith
  have hcast_nhds : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) :=
    hcast_ne.mono_right nhdsWithin_le_nhds
  -- `(s−1)·ζ(s) → 1` along the real filter
  have hzeta : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ)) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp hcast_ne
  -- each nontrivial `L`-function is continuous at `1`
  have hLχ : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p),
      Tendsto (fun s : ℝ => DirichletCharacter.LFunction χ (s : ℂ)) (𝓝[>] 1)
        (𝓝 (DirichletCharacter.LFunction χ 1)) := fun χ hχ =>
    ((DirichletCharacter.differentiable_LFunction (Finset.ne_of_mem_erase hχ)).continuous.tendsto
      1).comp hcast_nhds
  have hprod : Tendsto
      (fun s : ℝ => ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p),
        DirichletCharacter.LFunction χ (s : ℂ)) (𝓝[>] 1)
      (𝓝 (∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p),
        DirichletCharacter.LFunction χ 1)) :=
    tendsto_finsetProd _ hLχ
  -- the right-hand side limit of `(s−1)·ζ_K(s)`
  have hRHS : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * dedekindZeta K (s : ℂ)) (𝓝[>] 1)
      (𝓝 (∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p),
        DirichletCharacter.LFunction χ 1)) := by
    have hmul := hzeta.mul hprod
    rw [one_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsre : 1 < (s : ℂ).re := by rw [Complex.ofReal_re]; exact hs
    rw [dedekindZeta_eq_riemannZeta_mul_prod (p := p) (K := K) (s : ℂ) hsre,
      Finset.prod_congr rfl
        (fun χ _ => (DirichletCharacter.LFunction_eq_LSeries χ hsre).symm)]
    ring
  exact tendsto_nhds_unique (tendsto_sub_one_mul_dedekindZeta_nhdsGT K) hRHS

omit [Fact p.Prime] in
/-- The principal character mod `p` is **even**: `1(-1) = 1`. -/
theorem one_even : (1 : DirichletCharacter ℂ p).Even :=
  MulChar.one_apply (isUnit_one.neg)

open scoped Classical in
/-- **Even/odd split of `∏_{χ≠1} L(1,χ)`.**  Every character mod `p` is even or odd; the principal
character `1` is even, so the odd characters are automatically `≠ 1`.  Hence
`∏_{χ≠1} L(1,χ) = (∏_{χ≠1, even} L(1,χ)) · (∏_{χ odd} L(1,χ))`.  The two factors are the analytic
`h⁺·Reg⁺` (even, real subfield) and `h⁻` (odd, relative) halves of the class number formula. -/
theorem prod_LFunction_one_even_mul_odd :
    (∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p), DirichletCharacter.LFunction χ 1)
      = (∏ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ p)).filter (fun χ : DirichletCharacter
          ℂ p => χ.Even),
            DirichletCharacter.LFunction χ 1)
        * (∏ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Odd),
            DirichletCharacter.LFunction χ 1) := by
  rw [← Finset.prod_filter_mul_prod_filter_not
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)) (fun χ : DirichletCharacter ℂ p => χ.Even)]
  refine congrArg _ (Finset.prod_congr (Finset.ext fun χ => ?_) (fun _ _ => rfl))
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
  constructor
  · rintro ⟨_, hnotEven⟩
    exact χ.even_or_odd.resolve_left hnotEven
  · intro hodd
    refine ⟨?_, hodd.not_even⟩
    rintro rfl
    exact (1 : DirichletCharacter ℂ p).not_even_and_odd ⟨one_even, hodd⟩

open scoped Classical in
/-- **Class number formula, even/odd factored:** `(dedekindZeta_residue K : ℂ) =
(∏_{χ≠1, even} L(1,χ))·(∏_{χ odd} L(1,χ))`.  Combines `dedekindZeta_residue_eq_prod_LFunction_one`
with the parity split — isolating the `h⁺`/regulator (even) and `h⁻` (odd) analytic factors. -/
theorem dedekindZeta_residue_eq_even_mul_odd :
    (dedekindZeta_residue K : ℂ)
      = (∏ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ p)).filter (fun χ : DirichletCharacter
          ℂ p => χ.Even),
            DirichletCharacter.LFunction χ 1)
        * (∏ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Odd),
            DirichletCharacter.LFunction χ 1) := by
  rw [dedekindZeta_residue_eq_prod_LFunction_one (p := p) (K := K),
    prod_LFunction_one_even_mul_odd]

end CyclotomicNT
