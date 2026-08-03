import CyclotomicNT.GroupDeterminant

/-!
# The reduced group determinant (Washington Lemma 5.26)

The cyclotomic-unit regulator matrix is the **reduced** group matrix
`A_{σ,τ} = v(σ+τ) − v(τ)` (`σ,τ ≠ 0`) — the full group matrix with the trivial row/column
projected away (regulator entries `log w_b(ξ_a) = log‖1−ζ^{ab}‖ − log‖1−ζ^b‖`).  This file
proves the reduced analogue of the Dedekind determinant (`det_circulant_eq_prod_of_injective`):

  `‖det A‖ = ∏_{ψ ≠ trivial} ‖∑_g v(g)·ψ(−g)‖`

over `ℝ`/`ℂ` (Washington, *Cyclotomic Fields*, Lemma 5.26 — with absolute values, which is all
the regulator needs).

Proof: border the reduced matrix back up to a full `G×G` matrix `R` (row `0` replaced by all
ones).  Then `R·Q` (with `Q_{τ,k} = ψ_k(−τ)` the inverse-character matrix) is explicitly
computable: row `0` becomes `(|G|, 0, …, 0)` by orthogonality, and the rows `σ ≠ 0` become
`ψ_k(σ)·λ_k` by the circulant eigenvalue computation.  Pivoting both `det(R·Q)` and `det Q` on
their `0`-row (block-triangular) and cancelling, `det R = ±∏_{k≠0} λ_k`; finally column
operations identify `det R` with `det A`.
-/

open Matrix Finset

namespace CyclotomicNT

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

section Pivot

variable {R : Type*} [CommRing R]

/-- **Pivot lemma:** if row `0` of `M` is supported at column `0`, the determinant factors as
`M 0 0` times the minor at `(0,0)` (block-triangular decomposition along `{0} ⊕ {≠0}`). -/
theorem det_eq_mul_det_submatrix_of_row_support (M : Matrix G G R)
    (h0 : ∀ k : G, k ≠ 0 → M 0 k = 0) :
    M.det = M 0 0 * (M.submatrix (fun σ : {x : G // x ≠ 0} => (σ : G))
      (fun τ : {x : G // x ≠ 0} => (τ : G))).det := by
  classical
  haveI : Unique {x : G // x = 0} := ⟨⟨⟨0, rfl⟩⟩, fun a => Subtype.ext a.2⟩
  let e : ({x : G // x = 0} ⊕ {x : G // ¬x = 0}) ≃ G := Equiv.sumCompl (· = 0)
  have hblock : (M.submatrix ⇑e ⇑e).toBlocks₁₂ = 0 := by
    ext i j
    show M (e (Sum.inl i)) (e (Sum.inr j)) = 0
    rw [Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, i.2]
    exact h0 j.1 j.2
  calc M.det = (M.submatrix ⇑e ⇑e).det := (Matrix.det_submatrix_equiv_self e M).symm
    _ = (Matrix.fromBlocks (M.submatrix ⇑e ⇑e).toBlocks₁₁ 0
          (M.submatrix ⇑e ⇑e).toBlocks₂₁ (M.submatrix ⇑e ⇑e).toBlocks₂₂).det := by
        rw [← hblock, Matrix.fromBlocks_toBlocks]
    _ = (M.submatrix ⇑e ⇑e).toBlocks₁₁.det * (M.submatrix ⇑e ⇑e).toBlocks₂₂.det :=
        Matrix.det_fromBlocks_zero₁₂ _ _ _
    _ = M 0 0 * (M.submatrix (fun σ : {x : G // x ≠ 0} => (σ : G))
          (fun τ : {x : G // x ≠ 0} => (τ : G))).det := by
        congr 1
        rw [Matrix.det_unique]
        show M (e (Sum.inl default)) (e (Sum.inl default)) = M 0 0
        rw [Equiv.sumCompl_apply_inl, (default : {x : G // x = 0}).2]

end Pivot

section Reduced

variable {𝕂 : Type*} [RCLike 𝕂]

/-- The eigenvalue `λ_ψ = ∑_g v(g)·ψ(−g)` of the group matrix at the character `ψ`. -/
private abbrev lam (v : G → 𝕂) (ψ : AddChar G 𝕂) : 𝕂 := ∑ g : G, v g * ψ (-g)

/-- **The bordered matrix forms:** `R` = group matrix with row `0` replaced by all-ones. -/
private abbrev borderedMatrix (v : G → 𝕂) : Matrix G G 𝕂 :=
  Matrix.of fun σ τ : G => if σ = 0 then 1 else v (σ + τ)

/-- The inverse-character matrix `Q_{τ,k} = ψ_k(−τ)`. -/
private abbrev invCharMatrix (ψ : G → AddChar G 𝕂) : Matrix G G 𝕂 :=
  Matrix.of fun (τ k : G) => (ψ k) (-τ)

/-- The product `R·Q` computed entrywise: row `0` is `(|G|,0,…,0)` (character orthogonality),
row `σ ≠ 0` is `(ψ_k(σ)·λ_k)_k` (the circulant eigenvalue computation). -/
private theorem bordered_mul_invChar (v : G → 𝕂) (ψ : G → AddChar G 𝕂)
    (hinj : Function.Injective ψ) (hψ0 : ψ 0 = 0) :
    borderedMatrix v * invCharMatrix ψ
      = Matrix.of fun σ k : G =>
          if σ = 0 then (if k = 0 then (Fintype.card G : 𝕂) else 0)
          else (ψ k) σ * lam v (ψ k) := by
  ext σ k
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rcases eq_or_ne σ 0 with rfl | hσ
  · have hsum : ∑ τ : G, (if (0 : G) = 0 then (1 : 𝕂) else v (0 + τ)) * (ψ k) (-τ)
        = ∑ τ : G, (ψ k) τ := by
      rw [← Equiv.sum_comp (Equiv.neg G) (fun τ => (ψ k) τ)]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [if_pos rfl, one_mul]
      rfl
    rw [hsum, if_pos rfl]
    rcases eq_or_ne k 0 with rfl | hk
    · rw [if_pos rfl, hψ0]
      simp [AddChar.zero_apply]
    · rw [if_neg hk]
      exact AddChar.sum_eq_zero_iff_ne_zero.mpr fun h => hk (hinj (h.trans hψ0.symm))
  · rw [if_neg hσ]
    have hstep : ∀ τ : G, (if σ = 0 then (1 : 𝕂) else v (σ + τ)) * (ψ k) (-τ)
        = v (σ + τ) * (ψ k) (-τ) := fun τ => by rw [if_neg hσ]
    rw [Finset.sum_congr rfl fun τ _ => hstep τ,
      ← Equiv.sum_comp (Equiv.subRight σ) (fun τ => v (σ + τ) * (ψ k) (-τ)), lam,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Equiv.subRight_apply]
    rw [show σ + (g - σ) = g by abel, show -(g - σ) = σ + -g by abel,
      AddChar.map_add_eq_mul]
    ring

/-- Character orthogonality in inverse form: `∑_τ ψ_k(−τ) = |G|·[k = 0]`. -/
private theorem sum_invChar_eq (ψ : G → AddChar G 𝕂) (hinj : Function.Injective ψ)
    (hψ0 : ψ 0 = 0) (k : G) :
    ∑ τ : G, (ψ k) (-τ) = if k = 0 then (Fintype.card G : 𝕂) else 0 := by
  have h := Equiv.sum_comp (Equiv.neg G) (fun τ => (ψ k) τ)
  simp only [Equiv.neg_apply] at h
  rw [h]
  rcases eq_or_ne k 0 with rfl | hk
  · rw [if_pos rfl, hψ0]
    simp [AddChar.zero_apply]
  · rw [if_neg hk]
    exact AddChar.sum_eq_zero_iff_ne_zero.mpr fun h0 => hk (hinj (h0.trans hψ0.symm))

/-- `det Q ≠ 0`: the inverse-character matrix is a character matrix for the (injective)
inverse family. -/
private theorem det_invCharMatrix_ne_zero (ψ : G → AddChar G 𝕂)
    (hinj : Function.Injective ψ) :
    (invCharMatrix ψ).det ≠ 0 := by
  have h : invCharMatrix ψ = Matrix.of fun (τ k : G) => ((ψ k)⁻¹) τ := by
    ext τ k
    show (ψ k) (-τ) = ((ψ k)⁻¹) τ
    rw [AddChar.inv_apply]
  rw [h]
  exact det_charMatrix_ne_zero (fun k => (ψ k)⁻¹) (fun a b hab => hinj (inv_injective hab))

/-- `det(R·Q) = |G| · (∏_{k≠0} λ_k) · det P₁` with `P₁ = (ψ_k(σ))_{σ,k≠0}` — pivot on the
`(|G|,0,…,0)` row, then pull the `λ_k` out of the columns. -/
private theorem det_bordered_mul_invChar (v : G → 𝕂) (ψ : G → AddChar G 𝕂)
    (hinj : Function.Injective ψ) (hψ0 : ψ 0 = 0) :
    (borderedMatrix v * invCharMatrix ψ).det
      = (Fintype.card G : 𝕂) * ((∏ k : {x : G // x ≠ 0}, lam v (ψ k.1))
          * (Matrix.of fun σ k : {x : G // x ≠ 0} => (ψ k.1) σ.1).det) := by
  rw [bordered_mul_invChar v ψ hinj hψ0,
    det_eq_mul_det_submatrix_of_row_support _ (fun k hk => by simp [hk])]
  congr 1
  · simp
  · have hminor : ((Matrix.of fun σ k : G =>
        if σ = 0 then (if k = 0 then (Fintype.card G : 𝕂) else 0)
        else (ψ k) σ * lam v (ψ k)).submatrix
          (fun σ : {x : G // x ≠ 0} => (σ : G)) (fun τ : {x : G // x ≠ 0} => (τ : G)))
        = Matrix.of fun σ k : {x : G // x ≠ 0} =>
            lam v (ψ k.1) * (Matrix.of fun σ k : {x : G // x ≠ 0} => (ψ k.1) σ.1) σ k := by
      ext σ k
      show (if σ.1 = 0 then _ else (ψ k.1) σ.1 * lam v (ψ k.1)) = _
      rw [if_neg σ.2]
      exact mul_comm _ _
    rw [hminor, Matrix.det_mul_row]

/-- `det Q = |G| · det Q₂` with `Q₂ = (ψ_k(−σ))_{σ,k≠0}` — add all rows to row `0`
(orthogonality), then pivot. -/
private theorem det_invCharMatrix_eq (ψ : G → AddChar G 𝕂)
    (hinj : Function.Injective ψ) (hψ0 : ψ 0 = 0) :
    (invCharMatrix ψ).det
      = (Fintype.card G : 𝕂)
          * (Matrix.of fun σ k : {x : G // x ≠ 0} => (ψ k.1) (-σ.1)).det := by
  set Q := invCharMatrix ψ with hQ
  have hupd : (Q.updateRow 0 (∑ τ : G, Q τ)).det = Q.det := by
    have h := Matrix.det_updateRow_sum Q (0 : G) (fun _ => 1)
    simpa using h
  have hrow : ∀ k : G, (∑ τ : G, Q τ) k = if k = 0 then (Fintype.card G : 𝕂) else 0 := by
    intro k
    rw [Finset.sum_apply]
    exact sum_invChar_eq ψ hinj hψ0 k
  rw [← hupd, det_eq_mul_det_submatrix_of_row_support _
    (fun k hk => by rw [Matrix.updateRow_self, hrow k, if_neg hk])]
  congr 1
  · rw [Matrix.updateRow_self, hrow 0, if_pos rfl]
  · congr 1
    ext σ k
    show (Q.updateRow 0 (∑ τ : G, Q τ)) σ.1 k.1 = (ψ k.1) (-σ.1)
    rw [Matrix.updateRow_ne σ.2]
    rfl

/-- The negation permutation on `{x : G // x ≠ 0}`. -/
private def negPerm : Equiv.Perm {x : G // x ≠ 0} :=
  (Equiv.neg G).subtypeEquiv fun x => by simp

/-- `‖det Q₂‖ = ‖det P₁‖` — `Q₂` is `P₁` with rows permuted by negation. -/
private theorem norm_det_Q₂_eq_norm_det_P₁ (ψ : G → AddChar G 𝕂) :
    ‖(Matrix.of fun σ k : {x : G // x ≠ 0} => (ψ k.1) (-σ.1)).det‖
      = ‖(Matrix.of fun σ k : {x : G // x ≠ 0} => (ψ k.1) σ.1).det‖ := by
  have h : (Matrix.of fun σ k : {x : G // x ≠ 0} => (ψ k.1) (-σ.1))
      = (Matrix.of fun σ k : {x : G // x ≠ 0} => (ψ k.1) σ.1).submatrix negPerm id := by
    ext σ k
    rfl
  rw [h, Matrix.det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (negPerm (G := G))) with hs | hs <;>
    rw [hs] <;> simp

/-- The elementary column-operations matrix `E` (column `τ ≠ 0` ← column `τ` − column `0`):
unipotent, `det E = 1`. -/
private abbrev elemMatrix : Matrix G G 𝕂 :=
  Matrix.of fun τ τ' : G => if τ = τ' then 1 else if τ = 0 ∧ τ' ≠ 0 then -1 else 0

private theorem det_elemMatrix : (elemMatrix (G := G) (𝕂 := 𝕂)).det = 1 := by
  rw [← Matrix.det_transpose,
    det_eq_mul_det_submatrix_of_row_support _ (fun k hk => by
      show (if (k : G) = 0 then (1 : 𝕂) else if k = 0 ∧ (0 : G) ≠ 0 then -1 else 0) = 0
      rw [if_neg hk, if_neg (fun h => hk h.1)])]
  have hminor : ((elemMatrix (G := G) (𝕂 := 𝕂)).transpose.submatrix
      (fun σ : {x : G // x ≠ 0} => (σ : G)) (fun τ : {x : G // x ≠ 0} => (τ : G)))
      = (1 : Matrix {x : G // x ≠ 0} {x : G // x ≠ 0} 𝕂) := by
    ext σ τ
    show (if (τ : G) = (σ : G) then (1 : 𝕂) else if (τ : G) = 0 ∧ (σ : G) ≠ 0 then -1 else 0)
      = (1 : Matrix {x : G // x ≠ 0} {x : G // x ≠ 0} 𝕂) σ τ
    rcases eq_or_ne ((τ : G)) ((σ : G)) with h | h
    · rw [if_pos h, show σ = τ from Subtype.ext h.symm, Matrix.one_apply_eq]
    · rw [if_neg h, if_neg (fun hc => τ.2 hc.1),
        Matrix.one_apply_ne (fun hc => h (congrArg _ hc.symm))]
  rw [hminor, Matrix.det_one]
  show (if (0 : G) = 0 then (1 : 𝕂) else _) * 1 = 1
  rw [if_pos rfl, one_mul]

/-- `R·E` computed entrywise: row `0` becomes `e_0`, rows `σ ≠ 0` become
`(v(σ), (v(σ+τ)−v(σ))_τ)`. -/
private theorem bordered_mul_elem (v : G → 𝕂) :
    borderedMatrix v * elemMatrix
      = Matrix.of fun σ τ : G =>
          if σ = 0 then (if τ = 0 then 1 else 0)
          else (if τ = 0 then v σ else v (σ + τ) - v σ) := by
  ext σ τ'
  rw [Matrix.mul_apply]
  have hsplit : ∀ τ : G, (borderedMatrix v) σ τ * (elemMatrix (𝕂 := 𝕂)) τ τ'
      = (if τ = τ' then (borderedMatrix v) σ τ' else 0)
        + (if τ = 0 ∧ τ' ≠ 0 ∧ (0 : G) ≠ τ' then -(borderedMatrix v) σ 0 else 0) := by
    intro τ
    show (borderedMatrix v) σ τ * (if τ = τ' then (1 : 𝕂) else if τ = 0 ∧ τ' ≠ 0 then -1 else 0) = _
    rcases eq_or_ne τ τ' with rfl | hττ'
    · rw [if_pos rfl, if_pos rfl, mul_one, if_neg (fun h => h.2.2 h.1.symm), add_zero]
    · rw [if_neg hττ', if_neg hττ']
      rcases eq_or_ne τ 0 with rfl | hτ0
      · rcases eq_or_ne τ' 0 with rfl | hτ'0
        · exact absurd rfl hττ'
        · rw [if_pos ⟨rfl, hτ'0⟩, if_pos ⟨rfl, hτ'0, fun h => hττ' h⟩, mul_neg_one, zero_add]
      · rw [if_neg (fun h => hτ0 h.1), if_neg (fun h => hτ0 h.1), mul_zero, add_zero]
  have hcollapse : ∀ τ : G, (if τ = 0 ∧ τ' ≠ 0 ∧ (0 : G) ≠ τ' then -(borderedMatrix v) σ 0 else 0)
      = (if τ = 0 then (if τ' ≠ 0 ∧ (0 : G) ≠ τ' then -(borderedMatrix v) σ 0 else 0) else 0) := by
    intro τ
    rcases eq_or_ne τ 0 with rfl | hτ
    · rcases eq_or_ne τ' 0 with rfl | hτ'
      · rw [if_neg (fun h => h.2.1 rfl), if_pos rfl, if_neg (fun h => h.1 rfl)]
      · rw [if_pos ⟨rfl, hτ', fun h => hτ' h.symm⟩, if_pos rfl,
          if_pos ⟨hτ', fun h => hτ' h.symm⟩]
    · rw [if_neg (fun h => hτ h.1), if_neg hτ]
  rw [Finset.sum_congr rfl fun τ _ => by rw [hsplit τ, hcollapse τ], Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ τ' _, Finset.sum_ite_eq' Finset.univ (0 : G) _]
  simp only [Finset.mem_univ, if_true, Matrix.of_apply]
  by_cases hσ : σ = 0 <;> by_cases hτ' : τ' = 0 <;>
    simp [hσ, hτ', ne_comm, sub_eq_add_neg]

/-- **The reduced group determinant** (Washington, *Cyclotomic Fields*, Lemma 5.26 —
absolute-value form over `ℝ`/`ℂ`).  For an injective complete family of additive characters
`ψ` (`ψ 0` trivial) and any `v : G → 𝕂`,

  `‖det (v(σ+τ) − v(τ))_{σ,τ≠0}‖ = ∏_{k≠0} ‖∑_g v(g)·ψ_k(−g)‖` —

the regulator-shaped reduced determinant equals the product of the nontrivial character
eigenvalues. -/
theorem norm_det_reduced_groupMatrix (v : G → 𝕂) (ψ : G → AddChar G 𝕂)
    (hinj : Function.Injective ψ) (hψ0 : ψ 0 = 0) :
    ‖(Matrix.of fun σ τ : {x : G // x ≠ 0} => v (σ.1 + τ.1) - v τ.1).det‖
      = ∏ k : {x : G // x ≠ 0}, ‖∑ g : G, v g * (ψ k.1) (-g)‖ := by
  have hcard : (Fintype.card G : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- Step 1: `det A = det R` via the column operations `E` and the row-0 pivot.
  have hRE := congrArg Matrix.det (bordered_mul_elem v)
  rw [Matrix.det_mul, det_elemMatrix, mul_one] at hRE
  have hpivot : (Matrix.of fun σ τ : G => if σ = 0 then (if τ = 0 then (1 : 𝕂) else 0)
      else (if τ = 0 then v σ else v (σ + τ) - v σ)).det
      = (Matrix.of fun σ τ : {x : G // x ≠ 0} => v (σ.1 + τ.1) - v σ.1).det := by
    rw [det_eq_mul_det_submatrix_of_row_support _ (fun k hk => by simp [hk])]
    have hminor : ((Matrix.of fun σ τ : G => if σ = 0 then (if τ = 0 then (1 : 𝕂) else 0)
        else (if τ = 0 then v σ else v (σ + τ) - v σ)).submatrix
          (fun σ : {x : G // x ≠ 0} => (σ : G)) (fun τ : {x : G // x ≠ 0} => (τ : G)))
        = Matrix.of fun σ τ : {x : G // x ≠ 0} => v (σ.1 + τ.1) - v σ.1 := by
      ext σ τ
      show (if σ.1 = 0 then _ else (if τ.1 = 0 then v σ.1 else v (σ.1 + τ.1) - v σ.1)) = _
      rw [if_neg σ.2, if_neg τ.2]
      rfl
    rw [hminor]
    show (if (0 : G) = 0 then (if (0 : G) = 0 then (1 : 𝕂) else 0) else _) * _ = _
    rw [if_pos rfl, if_pos rfl, one_mul]
  have hAdet : (Matrix.of fun σ τ : {x : G // x ≠ 0} => v (σ.1 + τ.1) - v τ.1).det
      = (borderedMatrix v).det := by
    have hAB : (Matrix.of fun σ τ : {x : G // x ≠ 0} => v (σ.1 + τ.1) - v τ.1)
        = (Matrix.of fun σ τ : {x : G // x ≠ 0} => v (σ.1 + τ.1) - v σ.1).transpose := by
      ext σ τ
      show v (σ.1 + τ.1) - v τ.1 = v (τ.1 + σ.1) - v τ.1
      rw [add_comm]
    rw [hAB, Matrix.det_transpose, ← hpivot, ← hRE]
  -- Step 2: `‖det R‖ = ∏‖λ‖` via `R·Q` and cancellation.
  have hRQ : (borderedMatrix v).det * (invCharMatrix ψ).det
      = (Fintype.card G : 𝕂) * ((∏ k : {x : G // x ≠ 0}, lam v (ψ k.1))
          * (Matrix.of fun σ k : {x : G // x ≠ 0} => (ψ k.1) σ.1).det) := by
    rw [← Matrix.det_mul]
    exact det_bordered_mul_invChar v ψ hinj hψ0
  have hQdet := det_invCharMatrix_eq ψ hinj hψ0
  have hQne := det_invCharMatrix_ne_zero ψ hinj
  have hQ₂ne : (Matrix.of fun σ k : {x : G // x ≠ 0} => (ψ k.1) (-σ.1)).det ≠ 0 := by
    intro h
    rw [hQdet, h, mul_zero] at hQne
    exact hQne rfl
  have hkey : (borderedMatrix v).det
        * (Matrix.of fun σ k : {x : G // x ≠ 0} => (ψ k.1) (-σ.1)).det
      = (∏ k : {x : G // x ≠ 0}, lam v (ψ k.1))
        * (Matrix.of fun σ k : {x : G // x ≠ 0} => (ψ k.1) σ.1).det := by
    refine mul_left_cancel₀ hcard ?_
    rw [hQdet] at hRQ
    linear_combination hRQ
  -- take norms and cancel `‖det Q₂‖ = ‖det P₁‖ ≠ 0`
  have hnorm := congrArg norm hkey
  rw [norm_mul, norm_mul, norm_prod, norm_det_Q₂_eq_norm_det_P₁ ψ] at hnorm
  rw [hAdet]
  refine mul_right_cancel₀ (b := ‖(Matrix.of fun σ k : {x : G // x ≠ 0} =>
    (ψ k.1) σ.1).det‖) ?_ hnorm
  rw [← norm_det_Q₂_eq_norm_det_P₁ ψ]
  exact norm_ne_zero_iff.mpr hQ₂ne

end Reduced

end CyclotomicNT
