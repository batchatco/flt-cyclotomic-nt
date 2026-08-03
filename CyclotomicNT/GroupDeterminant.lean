import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

/-!
# Toward the Dedekind group determinant

The cyclotomic-unit regulator (the linear-algebra content of `cyclotomic_unit_index`, Washington
Thm 8.2) is `det` of the **group matrix** `M_{a,b} = log‖1−ζ^{a b⁻¹}‖`, and Dedekind's theorem
factors it as `∏_χ (∑_g χ(g)·v(g))` over the characters — exactly the `∏_{χ even} L(1,χ)` shape
(`EvenLOneValue.gaussSum_mul_LFunction_one_even`).  Diagonalizing by the
character (DFT) matrix is the
route; Mathlib has `Matrix.circulant` but not its eigenvalue/determinant theory.

This file builds the **eigenvalue relation** — the heart of the diagonalization: each additive
character `ψ` is an eigenvector of `circulant v`, with eigenvalue `∑_k v(k)·ψ(−k)`.
-/

open scoped BigOperators

namespace CyclotomicNT

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  {R : Type*} [CommRing R]

omit [DecidableEq G] in
/-- **Additive characters are eigenvectors of a circulant matrix.**  `circulant v *ᵥ ψ = λ_ψ • ψ`,
where `ψ = (ψ g)_g` is the character vector and the eigenvalue is `λ_ψ = ∑_k
v(k)·ψ(−k)`. (Substitute
`k = i − j`; the additive character splits `ψ(i − k) = ψ(i)·ψ(−k)`.) -/
theorem circulant_mulVec_addChar (v : G → R) (ψ : AddChar G R) :
    Matrix.mulVec (Matrix.circulant v) (fun i => ψ i)
      = (∑ k : G, v k * ψ (-k)) • (fun i => ψ i) := by
  ext i
  simp only [Matrix.mulVec, Matrix.circulant_apply, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  -- reindex `j ↦ i - j`, then `ψ(i - (i-j)) = ψ j` and `ψ(i - j) = ψ i ·
  -- ψ(-(i-j))`... handled directly:
  rw [← Equiv.sum_comp (Equiv.subLeft i) (fun j => v (i - j) * ψ j)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Equiv.subLeft_apply]
  rw [sub_sub_cancel, show ψ (i - k) = ψ i * ψ (-k) by
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]]
  ring

omit [DecidableEq G] in
/-- **Matrix diagonalization equation:** `circulant v · P = P · D`, where
`P` is the character matrix
(`P i k = ψ k i`) and `D = diagonal (λ_ψ)` the eigenvalue diagonal.  Column-wise this is
`circulant_mulVec_addChar`.  With `P` invertible (a complete character system) this gives
`det(circulant v) = ∏_k λ_{ψ k}` — Dedekind's group determinant. -/
theorem circulant_mul_charMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (v : G → R)
    (ψ : ι → AddChar G R) :
    Matrix.circulant v * Matrix.of (fun (i : G) (k : ι) => (ψ k) i)
      = Matrix.of (fun (i : G) (k : ι) => (ψ k) i)
        * Matrix.diagonal (fun k => ∑ g : G, v g * (ψ k) (-g)) := by
  ext i k
  have hev := congrFun (circulant_mulVec_addChar v (ψ k)) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hev
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.of_apply, Matrix.diagonal_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k), hev, mul_comm]

/-- **The character matrix is invertible** for an injective family of additive characters into
`ℝ`/`ℂ`: its columns are distinct characters, linearly independent by Artin's theorem
(`AddChar.linearIndependent`). -/
theorem det_charMatrix_ne_zero {K : Type*} [RCLike K] (ψ : G → AddChar G K)
    (hψ : Function.Injective ψ) :
    Matrix.det (Matrix.of (fun (i k : G) => (ψ k) i)) ≠ 0 := by
  have hli : LinearIndependent K (Matrix.of (fun (i k : G) => (ψ k) i)).col :=
    (AddChar.linearIndependent G K).comp ψ hψ
  rw [Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det] at hli
  exact hli.ne_zero

end CyclotomicNT
