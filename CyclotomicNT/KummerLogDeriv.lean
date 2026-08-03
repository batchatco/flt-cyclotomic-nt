import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import CyclotomicNT.MirimanoffSum

/-!
# Kummer's logarithmic derivatives `ℓ_n` on the group algebra `F_p[ℤ/p]`

The log-free construction of Kummer's logarithmic derivatives (Granville §2): on
`P := F_p[ℤ/p]` (where `X^p = 1` holds natively), the grading operator `θ(Xᵏ) = k·Xᵏ` is a
derivation, the augmentation `ε : P → F_p` sums coefficients (evaluation at `X = 1`), and for
a unit `γ`

  `ℓ_n(γ) := ε(θ^{n−1}(θγ·γ⁻¹))`.

The log-derivative `θγ·γ⁻¹` linearizes products, so `ℓ_n` is additive on `Pˣ`; the
`σ_a`-equivariance `ℓ_n(σ_a γ) = aⁿ·ℓ_n(γ)` follows from `θ∘σ_a = a·σ_a∘θ`; and for the
geometric unit `1 − tX` the explicit inverse `(1−t)⁻¹·∑_j tʲXʲ` evaluates `ℓ_n` to the
Mirimanoff sum `−(1−t)⁻¹·∑_{j<p} j^{n−1}tʲ`. -/

open Finset AddMonoidAlgebra

namespace CyclotomicNT

namespace KummerLog

variable {p : ℕ} [hpri : Fact p.Prime]

/-- The carrier: the group algebra `F_p[ℤ/p]`. -/
abbrev P (p : ℕ) := AddMonoidAlgebra (ZMod p) (ZMod p)

/-! ### The grading derivation `θ` -/

/-- The grading derivation `θ(Xᵏ) = k·Xᵏ`, defined coefficientwise: `(θf)(k) = k·f(k)`. -/
noncomputable def theta (f : P p) : P p :=
  Finsupp.onFinset f.support (fun k => k * f k)
    (fun k h => Finsupp.mem_support_iff.mpr fun h0 => h (by simp [h0]))

@[simp] theorem theta_apply (f : P p) (k : ZMod p) : theta f k = k * f k := rfl

theorem theta_support_subset (f : P p) : (theta f).support ⊆ f.support :=
  Finsupp.support_onFinset_subset

theorem theta_add (f g : P p) : theta (f + g) = theta f + theta g := by
  ext k
  exact mul_add k (f k) (g k)

theorem theta_smul (c : ZMod p) (f : P p) : theta (c • f) = c • theta f := by
  ext k
  change k * (c * f k) = c * (k * f k)
  ring

@[simp] theorem theta_zero : theta (0 : P p) = 0 := by
  ext k
  exact mul_zero k

@[simp] theorem theta_single (k c : ZMod p) :
    theta (single k c) = single k (k * c) := by
  classical
  ext l
  rw [theta_apply, AddMonoidAlgebra.single_apply, AddMonoidAlgebra.single_apply]
  split_ifs with h
  · rw [h]
  · ring

@[simp] theorem theta_one : theta (1 : P p) = 0 := by
  rw [AddMonoidAlgebra.one_def, theta_single, zero_mul, single_zero]

/-- `θ` is a derivation: `θ(fg) = θf·g + f·θg`. -/
theorem theta_mul (f g : P p) : theta (f * g) = theta f * g + f * theta g := by
  classical
  ext m
  change m * (f * g) m = (theta f * g) m + (f * theta g) m
  rw [AddMonoidAlgebra.mul_apply, AddMonoidAlgebra.mul_apply, AddMonoidAlgebra.mul_apply]
  change m * ∑ k ∈ f.support, ∑ l ∈ g.support, ite (k + l = m) (f k * g l) 0
      = (∑ k ∈ (theta f).support, ∑ l ∈ g.support, ite (k + l = m) ((theta f) k * g l) 0)
      + ∑ k ∈ f.support, ∑ l ∈ (theta g).support, ite (k + l = m) (f k * (theta g) l) 0
  have h1 : (∑ k ∈ (theta f).support, ∑ l ∈ g.support, ite (k + l = m) ((theta f) k * g l) 0)
      = ∑ k ∈ f.support, ∑ l ∈ g.support, ite (k + l = m) (k * f k * g l) 0 := by
    rw [Finset.sum_subset (theta_support_subset f) (fun k _ hk => by
      simp [Finsupp.notMem_support_iff.mp hk])]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
      rw [theta_apply]
  have h2 : (∑ k ∈ f.support, ∑ l ∈ (theta g).support, ite (k + l = m) (f k * (theta g) l) 0)
      = ∑ k ∈ f.support, ∑ l ∈ g.support, ite (k + l = m) (f k * (l * g l)) 0 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_subset (theta_support_subset g) (fun l _ hl => by
      simp [Finsupp.notMem_support_iff.mp hl])]
    exact Finset.sum_congr rfl fun l _ => by rw [theta_apply]
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs with h
  · rw [← h]
    ring
  · ring

theorem theta_iterate_add (m : ℕ) (f g : P p) :
    theta^[m] (f + g) = theta^[m] f + theta^[m] g := by
  induction m generalizing f g with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, theta_add, ih]

theorem theta_iterate_smul (m : ℕ) (c : ZMod p) (f : P p) :
    theta^[m] (c • f) = c • theta^[m] f := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, theta_smul, ih]

@[simp] theorem theta_iterate_single (m : ℕ) (k c : ZMod p) :
    theta^[m] (single k c) = single k (k ^ m * c) := by
  induction m generalizing c with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ m ih =>
      rw [Function.iterate_succ_apply, theta_single, ih]
      congr 1
      ring

/-! ### The augmentation `ε` (sum of coefficients) -/

/-- The augmentation `ε : P → F_p`, `∑ c_k Xᵏ ↦ ∑ c_k` (evaluation at `X = 1`),
as an additive map. -/
noncomputable def eps : P p →+ ZMod p :=
  Finsupp.liftAddHom fun _ => AddMonoidHom.id (ZMod p)

@[simp] theorem eps_single (k c : ZMod p) : eps (single k c) = c := by
  rw [eps]
  change (Finsupp.liftAddHom fun _ => AddMonoidHom.id (ZMod p)) (Finsupp.single k c) = c
  rw [Finsupp.liftAddHom_apply_single]
  rfl

/-! ### The Galois action `σ_a` -/

/-- The Galois action `σ_a : Xᵏ ↦ X^{ak}` as an algebra automorphism. -/
noncomputable def sigma (a : (ZMod p)ˣ) : P p ≃ₐ[ZMod p] P p :=
  AddMonoidAlgebra.domCongr (ZMod p) (ZMod p) (DistribMulAction.toAddEquiv (ZMod p) a)

@[simp] theorem sigma_single (a : (ZMod p)ˣ) (k c : ZMod p) :
    sigma a (single k c) = single ((a : ZMod p) * k) c := by
  rw [sigma, AddMonoidAlgebra.domCongr_single]
  rfl

@[simp] theorem sigma_apply (a : (ZMod p)ˣ) (f : P p) (m : ZMod p) :
    (sigma a f) m = f ((a⁻¹ : (ZMod p)ˣ) • m) := by
  rw [sigma, AddMonoidAlgebra.domCongr_apply]
  rfl

/-- The key twist: `θ ∘ σ_a = a · σ_a ∘ θ`. -/
theorem theta_sigma (a : (ZMod p)ˣ) (f : P p) :
    theta (sigma a f) = (a : ZMod p) • sigma a (theta f) := by
  ext m
  change m * (sigma a f) m = (a : ZMod p) * (sigma a (theta f)) m
  rw [sigma_apply, sigma_apply, theta_apply]
  have hcancel : (a : ZMod p) * (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * m) = m := by
    rw [← mul_assoc, Units.mul_inv, one_mul]
  calc m * f ((a⁻¹ : (ZMod p)ˣ) • m)
      = ((a : ZMod p) * (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * m)) * f ((a⁻¹ : (ZMod p)ˣ) • m) := by
        rw [hcancel]
    _ = (a : ZMod p) * (((a⁻¹ : (ZMod p)ˣ) • m) * f ((a⁻¹ : (ZMod p)ˣ) • m)) := by
        rw [Units.smul_def, smul_eq_mul]
        ring

theorem eps_apply (g : P p) : eps g = ∑ m ∈ g.support, g m := by
  rw [eps]
  rfl

theorem eps_sigma (a : (ZMod p)ˣ) (f : P p) : eps (sigma a f) = eps f := by
  rw [eps_apply, eps_apply]
  rw [show (sigma a f).support
      = f.support.map ((DistribMulAction.toAddEquiv (ZMod p) a :
          ZMod p ≃ ZMod p)).toEmbedding from by
    rw [sigma, AddMonoidAlgebra.domCongr_support]]
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sigma_apply]
  congr 1
  change (a⁻¹ : (ZMod p)ˣ) • ((a : (ZMod p)ˣ) • k) = k
  rw [smul_smul, inv_mul_cancel, one_smul]

theorem theta_iterate_sigma (m : ℕ) (a : (ZMod p)ˣ) (f : P p) :
    theta^[m] (sigma a f) = ((a : ZMod p)) ^ m • sigma a (theta^[m] f) := by
  induction m generalizing f with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply, pow_zero, one_smul]
  | succ m ih =>
      rw [Function.iterate_succ_apply, theta_sigma, theta_iterate_smul, ih, smul_smul,
        Function.iterate_succ_apply]
      congr 1
      ring

theorem theta_iterate_zero (m : ℕ) : theta^[m] (0 : P p) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, theta_zero, ih]

theorem eps_smul (c : ZMod p) (f : P p) : eps (c • f) = c * eps f := by
  rw [eps_apply, eps_apply, Finset.mul_sum,
    show (∑ m ∈ (c • f).support, (c • f) m) = ∑ m ∈ f.support, (c • f) m from
      Finset.sum_subset Finsupp.support_smul
        (fun m _ hm => Finsupp.notMem_support_iff.mp hm)]
  exact Finset.sum_congr rfl fun m _ => rfl

/-! ### The logarithmic derivatives `ℓ_n` -/

/-- The log-derivative `dlog γ := θγ·γ⁻¹` of a unit of the group algebra. -/
noncomputable def dlog (γ : (P p)ˣ) : P p := theta (γ : P p) * ((γ⁻¹ : (P p)ˣ) : P p)

@[simp] theorem dlog_one : dlog (1 : (P p)ˣ) = 0 := by
  rw [dlog, Units.val_one, theta_one, zero_mul]

/-- `dlog` linearizes products. -/
theorem dlog_mul (γ δ : (P p)ˣ) : dlog (γ * δ) = dlog γ + dlog δ := by
  have hγ : (γ : P p) * ((γ⁻¹ : (P p)ˣ) : P p) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hδ : (δ : P p) * ((δ⁻¹ : (P p)ˣ) : P p) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinv : (((γ * δ)⁻¹ : (P p)ˣ) : P p)
      = ((δ⁻¹ : (P p)ˣ) : P p) * ((γ⁻¹ : (P p)ˣ) : P p) := by
    rw [mul_inv_rev, Units.val_mul]
  rw [dlog, dlog, dlog, Units.val_mul, theta_mul, hinv]
  linear_combination (theta (γ : P p) * ((γ⁻¹ : (P p)ˣ) : P p)) * hδ
    + (theta (δ : P p) * ((δ⁻¹ : (P p)ˣ) : P p)) * hγ

/-- **Kummer's `n`-th logarithmic derivative** `ℓ_n(γ) := ε(θ^{n−1}(θγ·γ⁻¹))`. -/
noncomputable def ell (n : ℕ) (γ : (P p)ˣ) : ZMod p := eps (theta^[n - 1] (dlog γ))

@[simp] theorem ell_one (n : ℕ) : ell n (1 : (P p)ˣ) = 0 := by
  rw [ell, dlog_one, theta_iterate_zero, map_zero]

theorem ell_mul (n : ℕ) (γ δ : (P p)ˣ) : ell n (γ * δ) = ell n γ + ell n δ := by
  rw [ell, ell, ell, dlog_mul, theta_iterate_add, map_add]

theorem ell_prod {ι : Type*} (n : ℕ) (s : Finset ι) (γ : ι → (P p)ˣ) :
    ell n (∏ i ∈ s, γ i) = ∑ i ∈ s, ell n (γ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ell_mul, ih]

theorem ell_pow (n m : ℕ) (γ : (P p)ˣ) : ell n (γ ^ m) = (m : ZMod p) * ell n γ := by
  induction m with
  | zero => rw [pow_zero, ell_one, Nat.cast_zero, zero_mul]
  | succ m ih =>
      rw [pow_succ, ell_mul, ih]
      push_cast
      ring

/-- `ℓ_n` kills `p`-th powers. -/
theorem ell_pow_p (n : ℕ) (γ : (P p)ˣ) : ell n (γ ^ p) = 0 := by
  rw [ell_pow, ZMod.natCast_self, zero_mul]

/-! ### Equivariance -/

/-- `σ_a` on units. -/
noncomputable def sigmaU (a : (ZMod p)ˣ) : (P p)ˣ →* (P p)ˣ :=
  Units.map ((sigma a : P p ≃ₐ[ZMod p] P p) : P p →* P p)

@[simp] theorem sigmaU_val (a : (ZMod p)ˣ) (γ : (P p)ˣ) :
    ((sigmaU a γ : (P p)ˣ) : P p) = sigma a (γ : P p) := rfl

@[simp] theorem sigmaU_inv_val (a : (ZMod p)ˣ) (γ : (P p)ˣ) :
    (((sigmaU a γ)⁻¹ : (P p)ˣ) : P p) = sigma a ((γ⁻¹ : (P p)ˣ) : P p) := by
  rw [← map_inv (sigmaU a) γ]
  rfl

theorem dlog_sigmaU (a : (ZMod p)ˣ) (γ : (P p)ˣ) :
    dlog (sigmaU a γ) = (a : ZMod p) • sigma a (dlog γ) := by
  rw [dlog, sigmaU_val, sigmaU_inv_val, theta_sigma, smul_mul_assoc, ← map_mul, dlog]

/-- **Equivariance**: `ℓ_n(σ_a γ) = aⁿ·ℓ_n(γ)` (for `n ≥ 1`). -/
theorem ell_sigmaU (n : ℕ) (hn : 1 ≤ n) (a : (ZMod p)ˣ) (γ : (P p)ˣ) :
    ell n (sigmaU a γ) = ((a : ZMod p)) ^ n * ell n γ := by
  rw [ell, dlog_sigmaU, theta_iterate_smul, theta_iterate_sigma, eps_smul, eps_smul,
    eps_sigma]
  calc (a : ZMod p) * (((a : ZMod p)) ^ (n - 1) * eps (theta^[n - 1] (dlog γ)))
      = ((a : ZMod p)) ^ (n - 1 + 1) * eps (theta^[n - 1] (dlog γ)) := by
        rw [pow_succ]
        ring
    _ = ((a : ZMod p)) ^ n * ell n γ := by rw [show n - 1 + 1 = n by omega, ell]

/-- **The η-collapse (diagonal case)**: applying `ℓ_n` to `γ^{η_n} = ∏_a (σ_a γ)^{a^{−n}}`
gives `−ℓ_n(γ)`. -/
theorem ell_etaProd (n : ℕ) (hn : 1 ≤ n) (γ : (P p)ˣ) :
    ell n (∏ a : (ZMod p)ˣ, (sigmaU a γ) ^ (((a⁻¹ ^ n : (ZMod p)ˣ) : ZMod p)).val)
      = - ell n γ := by
  rw [ell_prod]
  have hterm : ∀ a : (ZMod p)ˣ,
      ell n ((sigmaU a γ) ^ (((a⁻¹ ^ n : (ZMod p)ˣ) : ZMod p)).val) = ell n γ := by
    intro a
    rw [ell_pow, ell_sigmaU n hn, ZMod.natCast_val, ZMod.cast_id]
    have : (((a⁻¹ ^ n : (ZMod p)ˣ) : ZMod p)) * ((a : ZMod p)) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
    rw [← mul_assoc, this, one_mul]
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_const, Finset.card_univ,
    ZMod.card_units_eq_totient, Nat.totient_prime hpri.out, nsmul_eq_mul]
  have : ((p - 1 : ℕ) : ZMod p) = -1 := by
    have h1 := hpri.out.one_lt
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    rw [ZMod.natCast_self]
    ring
  rw [this]
  ring

/-! ### The geometric unit `1 − tX` and the Mirimanoff evaluation -/

theorem theta_sub (f g : P p) : theta (f - g) = theta f - theta g := by
  ext k
  change k * (f k - g k) = k * f k - k * g k
  ring

theorem theta_iterate_sum {ι : Type*} (m : ℕ) (s : Finset ι) (f : ι → P p) :
    theta^[m] (∑ i ∈ s, f i) = ∑ i ∈ s, theta^[m] (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using theta_iterate_zero m
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, theta_iterate_add, ih]

/-- The truncated geometric series `∑_{j<p} tʲXʲ`. -/
noncomputable def geom (t : ZMod p) : P p :=
  ∑ j ∈ Finset.range p, single ((j : ZMod p)) (t ^ j)

/-- The geometric identity `(1 − tX)·∑_j tʲXʲ = (1−t)·1` (using `Xᵖ = 1` and `tᵖ = t`). -/
theorem one_sub_mul_geom (t : ZMod p) :
    (1 - single 1 t) * geom t = single 0 (1 - t) := by
  rw [sub_mul, one_mul, geom, Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.range p,
      single (1 : ZMod p) t * single ((j : ZMod p)) (t ^ j)
        = single (((j + 1 : ℕ) : ZMod p)) (t ^ (j + 1)) := by
    intro j _
    rw [single_mul_single]
    congr 1
    · push_cast
      ring
    · ring
  rw [Finset.sum_congr rfl hterm]
  -- reindex the shifted sum
  have hshift : (∑ j ∈ Finset.range p, single (((j + 1 : ℕ) : ZMod p)) (t ^ (j + 1)))
      = (∑ j ∈ Finset.range p, single ((j : ℕ) : ZMod p) (t ^ j))
        - single ((0 : ℕ) : ZMod p) (t ^ 0) + single ((p : ℕ) : ZMod p) (t ^ p) := by
    have h1 := Finset.sum_range_succ' (fun j => single (((j : ℕ) : ZMod p)) (t ^ j)) p
    have h2 := Finset.sum_range_succ (fun j => single (((j : ℕ) : ZMod p)) (t ^ j)) p
    rw [h2] at h1
    linear_combination -h1
  rw [hshift, show ((p : ℕ) : ZMod p) = 0 from ZMod.natCast_self p, ZMod.pow_card,
    Nat.cast_zero, pow_zero]
  have hs : single (0 : ZMod p) ((1 : ZMod p) - t) = single 0 1 - single 0 t :=
    AddMonoidHom.map_sub (Finsupp.singleAddHom (0 : ZMod p)) 1 t
  rw [hs]
  abel

theorem single_one_mul_geom (t : ZMod p) :
    single (1 : ZMod p) t * geom t
      = ∑ j ∈ Finset.range p, single (((j + 1 : ℕ) : ZMod p)) (t ^ (j + 1)) := by
  rw [geom, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [single_mul_single]
  congr 1
  · push_cast
    ring
  · ring

/-- The geometric unit `1 − tX` (for `t ≠ 1`), with explicit inverse `(1−t)⁻¹·∑_j tʲXʲ`. -/
noncomputable def geomUnit (t : ZMod p) (ht : t ≠ 1) : (P p)ˣ where
  val := 1 - single 1 t
  inv := (1 - t)⁻¹ • geom t
  val_inv := by
    rw [mul_smul_comm, one_sub_mul_geom, smul_single, smul_eq_mul,
      inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm ht))]
    exact AddMonoidAlgebra.one_def.symm
  inv_val := by
    rw [smul_mul_assoc, mul_comm (geom t) _, one_sub_mul_geom, smul_single, smul_eq_mul,
      inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm ht))]
    exact AddMonoidAlgebra.one_def.symm

theorem dlog_geomUnit (t : ZMod p) (ht : t ≠ 1) :
    dlog (geomUnit t ht)
      = (-(1 - t)⁻¹) • ∑ j ∈ Finset.range p, single (((j + 1 : ℕ) : ZMod p)) (t ^ (j + 1)) := by
  rw [dlog]
  change theta (1 - single 1 t) * ((1 - t)⁻¹ • geom t) = _
  rw [theta_sub, theta_one, theta_single, one_mul, zero_sub, neg_mul, mul_smul_comm,
    single_one_mul_geom, ← neg_smul]

/-- **The Mirimanoff evaluation**: `ℓ_n(1−tX) = −(1−t)⁻¹·∑_{j<p} jⁿ⁻¹tʲ` for `n ≥ 2`. -/
theorem ell_geomUnit (n : ℕ) (hn : 2 ≤ n) (t : ZMod p) (ht : t ≠ 1) :
    ell n (geomUnit t ht)
      = -(1 - t)⁻¹ * ∑ j ∈ Finset.range p, ((j : ZMod p)) ^ (n - 1) * t ^ j := by
  rw [ell, dlog_geomUnit, theta_iterate_smul, eps_smul, theta_iterate_sum,
    Finset.sum_congr rfl fun j _ => theta_iterate_single (n - 1) _ _, map_sum,
    Finset.sum_congr rfl fun j _ => eps_single _ _]
  congr 1
  -- reindex `∑_j f(j+1) = ∑_j f(j)` using `f(0) = f(p) = 0`
  have h1 := Finset.sum_range_succ' (fun j => (((j : ℕ) : ZMod p)) ^ (n - 1) * t ^ j) p
  have h2 := Finset.sum_range_succ (fun j => (((j : ℕ) : ZMod p)) ^ (n - 1) * t ^ j) p
  rw [h2] at h1
  have hf0 : (((0 : ℕ) : ZMod p)) ^ (n - 1) * t ^ 0 = 0 := by
    rw [Nat.cast_zero, zero_pow (by omega : n - 1 ≠ 0), zero_mul]
  have hfp : (((p : ℕ) : ZMod p)) ^ (n - 1) * t ^ p = 0 := by
    rw [ZMod.natCast_self, zero_pow (by omega : n - 1 ≠ 0), zero_mul]
  rw [hf0, hfp] at h1
  rw [show (∑ j ∈ Finset.range p, (((j + 1 : ℕ) : ZMod p)) ^ (n - 1) * t ^ (j + 1))
      = ∑ j ∈ Finset.range p, (((j : ℕ) : ZMod p)) ^ (n - 1) * t ^ j from by
    linear_combination -h1]

/-- **Nonvanishing at `n = 3`**: `ℓ₃(1−tX) ≠ 0` for `t ∉ {0, 1, −1}`. -/
theorem ell_three_geomUnit_ne_zero {t : ZMod p} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm1 : t ≠ -1) :
    ell 3 (geomUnit t h1) ≠ 0 := by
  rw [ell_geomUnit 3 (by omega)]
  intro h
  rcases mul_eq_zero.mp h with h | h
  · rw [neg_eq_zero, inv_eq_zero, sub_eq_zero] at h
    exact h1 h.symm
  · exact sum_sq_mul_pow_ne_zero h0 h1 hm1 h

/-! ### The norm element `N = ∑_j Xʲ`, Frobenius, and `N`-insensitivity of `ℓ_n` -/

theorem sum_apply_pt {ι : Type*} (s : Finset ι) (g : ι → P p) (m : ZMod p) :
    (∑ i ∈ s, g i) m = ∑ i ∈ s, (g i) m :=
  map_sum (Finsupp.applyAddHom m) g s

/-- The norm element `N := ∑_{j ∈ ℤ/p} Xʲ` (the reduction of `Φ_p`). -/
noncomputable def nelt : P p := ∑ j : ZMod p, single j 1

@[simp] theorem nelt_apply (m : ZMod p) : (nelt : P p) m = 1 := by
  classical
  rw [nelt, sum_apply_pt]
  rw [Finset.sum_eq_single m (fun j _ hj => by
      rw [AddMonoidAlgebra.single_apply, if_neg hj])
    (fun h => absurd (Finset.mem_univ m) h)]
  rw [AddMonoidAlgebra.single_apply, if_pos rfl]

@[simp] theorem theta_nelt_apply (m : ZMod p) : (theta (nelt : P p)) m = m := by
  rw [theta_apply, nelt_apply, mul_one]

/-- `ε` is multiplicative. -/
theorem eps_mul (f g : P p) : eps (f * g) = eps f * eps g := by
  classical
  rw [eps_apply, eps_apply, eps_apply]
  -- extend the support sum of `f*g` to all of `ZMod p`
  rw [show (∑ m ∈ (f * g).support, (f * g) m) = ∑ m : ZMod p, (f * g) m from
    Finset.sum_subset (Finset.subset_univ _)
      (fun m _ hm => Finsupp.notMem_support_iff.mp hm)]
  have hconv : ∀ m : ZMod p, (f * g) m
      = ∑ k ∈ f.support, ∑ l ∈ g.support, ite (k + l = m) (f k * g l) 0 := fun m => by
    rw [AddMonoidAlgebra.mul_apply]
    rfl
  rw [Finset.sum_congr rfl fun m _ => hconv m, Finset.sum_comm]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single (k + l) (fun m _ hm => by rw [if_neg (fun h => hm h.symm)])
    (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]

theorem eps_unit_ne_zero (γ : (P p)ˣ) : eps ((γ : P p)) ≠ 0 := by
  intro h
  have := eps_mul (γ : P p) ((γ⁻¹ : (P p)ˣ) : P p)
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, h, zero_mul] at this
  have h1 : eps (1 : P p) = 1 := by
    rw [AddMonoidAlgebra.one_def, eps_single]
  rw [h1] at this
  exact one_ne_zero this

theorem nelt_support : ((nelt : P p)).support = Finset.univ := by
  classical
  ext l
  simp [Finsupp.mem_support_iff]

/-- `f·N = ε(f)·N`: the norm element absorbs multiplication. -/
theorem mul_nelt (f : P p) : f * nelt = eps f • nelt := by
  classical
  ext m
  change (f * (nelt : P p)) m = eps f * (nelt : P p) m
  rw [nelt_apply, mul_one, AddMonoidAlgebra.mul_apply, eps_apply]
  change (∑ k ∈ f.support, ∑ l ∈ ((nelt : P p)).support, ite (k + l = m) (f k * (nelt : P p) l) 0)
      = ∑ k ∈ f.support, f k
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nelt_support]
  rw [Finset.sum_eq_single (m - k)
    (fun l _ hl => if_neg fun h => hl (eq_sub_of_add_eq (by rw [add_comm] at h; exact h)))
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [if_pos (show k + (m - k) = m by ring), nelt_apply, mul_one]

/-- `f·θN = ε(f)·θN − ε(θf)·N`. -/
theorem mul_theta_nelt (f : P p) :
    f * theta nelt = eps f • theta nelt - eps (theta f) • nelt := by
  classical
  ext m
  change (f * theta (nelt : P p)) m
      = eps f * (theta (nelt : P p)) m - eps (theta f) * (nelt : P p) m
  rw [theta_nelt_apply, nelt_apply, mul_one, AddMonoidAlgebra.mul_apply]
  change (∑ k ∈ f.support, ∑ l ∈ (theta (nelt : P p)).support,
      ite (k + l = m) (f k * (theta (nelt : P p)) l) 0) = eps f * m - eps (theta f)
  have hstep1 : ∀ k ∈ f.support, (∑ l ∈ (theta (nelt : P p)).support,
      ite (k + l = m) (f k * (theta (nelt : P p)) l) 0)
      = f k * (m - k) := by
    intro k _
    rw [Finset.sum_subset (Finset.subset_univ _) (fun l _ hl => by
      rw [show (theta (nelt : P p)) l = 0 from Finsupp.notMem_support_iff.mp hl, mul_zero,
        ite_self])]
    rw [Finset.sum_congr rfl fun l _ => by rw [theta_nelt_apply]]
    rw [Finset.sum_eq_single (m - k)
      (fun l _ hl => if_neg fun h => hl (eq_sub_of_add_eq (by rw [add_comm] at h; exact h)))
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [if_pos (show k + (m - k) = m by ring)]
  rw [Finset.sum_congr rfl hstep1]
  have heps1 : eps f = ∑ k ∈ f.support, f k := eps_apply f
  have heps2 : eps (theta f) = ∑ k ∈ f.support, k * f k := by
    rw [eps_apply]
    rw [Finset.sum_subset (theta_support_subset f) (fun k _ hk =>
      Finsupp.notMem_support_iff.mp hk)]
    exact Finset.sum_congr rfl fun k _ => theta_apply f k
  rw [heps1, heps2, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

@[simp] theorem eps_nelt : eps (nelt : P p) = 0 := by
  rw [eps_apply, nelt_support]
  rw [Finset.sum_congr rfl fun m _ => nelt_apply m, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, mul_one, ZMod.natCast_self]

theorem eps_theta_iterate_nelt (m : ℕ) :
    eps (theta^[m] (nelt : P p)) = ∑ j : ZMod p, j ^ m := by
  rw [nelt, theta_iterate_sum, Finset.sum_congr rfl fun j _ => theta_iterate_single m j 1,
    map_sum, Finset.sum_congr rfl fun j _ => eps_single j (j ^ m * 1)]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_one]

/-- Power sums over `ZMod p` vanish in degrees not divisible by `p − 1`. -/
theorem sum_pow_zmod_eq_zero {m : ℕ} (hm : 1 ≤ m) (hmd : ¬ (p - 1) ∣ m) :
    (∑ j : ZMod p, j ^ m) = 0 := by
  classical
  rw [← sum_units_eq_sum_zmod (p := p) (fun x => x ^ m)
    (by simp [zero_pow (show m ≠ 0 by omega)])]
  have := FiniteField.sum_pow_units (ZMod p) m
  rw [ZMod.card] at this
  rw [this, if_neg hmd]

/-- Every element is the sum of its monomials. -/
theorem support_decomp (f : P p) : f = ∑ k ∈ f.support, single k (f k) := by
  classical
  ext m
  rw [sum_apply_pt]
  by_cases hm : m ∈ f.support
  · rw [Finset.sum_eq_single m
      (fun k _ hk => by rw [AddMonoidAlgebra.single_apply, if_neg hk])
      (fun h => absurd hm h), AddMonoidAlgebra.single_apply, if_pos rfl]
  · rw [Finsupp.notMem_support_iff.mp hm]
    exact (Finset.sum_eq_zero fun k hk => by
      rw [AddMonoidAlgebra.single_apply, if_neg (fun h => hm (by rw [← h]; exact hk))]).symm

/-- Frobenius collapses `P` onto constants: `f^p = ε(f)^p·1`. -/
theorem pow_card_eq (f : P p) : f ^ p = single 0 ((eps f) ^ p) := by
  classical
  have hf : f = ∑ k ∈ f.support, single k (f k) := support_decomp f
  haveI : CharP (P p) p := charP_of_injective_algebraMap (R := ZMod p) (A := P p)
    (fun a b hab => by
      have ha : ∀ c : ZMod p, ((algebraMap (ZMod p) (P p)) c) 0 = c := fun c => by
        rw [show (algebraMap (ZMod p) (P p)) c = single 0 c from rfl,
          AddMonoidAlgebra.single_apply, if_pos rfl]
      have h2 := congrArg (fun x : P p => x 0) hab
      simpa only [ha] using h2) p
  conv_lhs => rw [hf]
  rw [sum_pow_char p _ _, Finset.sum_congr rfl fun k _ => AddMonoidAlgebra.single_pow k (f k) p]
  have hps : ∀ k : ZMod p, p • k = 0 := fun k => by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [Finset.sum_congr rfl fun k _ => by rw [hps k]]
  rw [show (∑ k ∈ f.support, single (0 : ZMod p) (f k ^ p) : P p)
      = single 0 (∑ k ∈ f.support, f k ^ p) from
    (map_sum (Finsupp.singleAddHom (0 : ZMod p)) _ _).symm]
  congr 1
  rw [← sum_pow_char p _ _, eps_apply]

/-- An element with nonzero augmentation is a unit (`ker ε` is nil). -/
theorem isUnit_of_eps_ne_zero {f : P p} (hf : eps f ≠ 0) : IsUnit f := by
  have hker : IsNilpotent (f - single 0 (eps f)) := by
    refine ⟨p, ?_⟩
    rw [pow_card_eq]
    have : eps (f - single 0 (eps f)) = 0 := by
      rw [map_sub, eps_single, sub_self]
    rw [this, zero_pow hpri.out.ne_zero, single_zero]
  have hu : IsUnit (single (0 : ZMod p) (eps f) : P p) := by
    refine IsUnit.of_mul_eq_one (single 0 (eps f)⁻¹) ?_
    rw [single_mul_single, add_zero, mul_inv_cancel₀ hf]
    exact AddMonoidAlgebra.one_def.symm
  have := hker.isUnit_add_left_of_commute hu (Commute.all _ _)
  rwa [add_sub_cancel] at this

theorem smul_eq_single_zero_mul (c : ZMod p) (f : P p) : c • f = single 0 c * f := by
  ext m
  change c * f m = ((single (0 : ZMod p) c : P p) * f) m
  rw [AddMonoidAlgebra.mul_apply]
  change c * f m = ∑ k ∈ (single (0 : ZMod p) c : P p).support,
    ∑ l ∈ f.support, ite (k + l = m) ((single (0 : ZMod p) c : P p) k * f l) 0
  by_cases hc : c = 0
  · simp [hc]
  · have hsupp : (single (0 : ZMod p) c : P p).support = {0} := Finsupp.support_single _ hc
    rw [hsupp, Finset.sum_singleton]
    by_cases hm : m ∈ f.support
    · rw [Finset.sum_eq_single m (fun l _ hl => by
        rw [if_neg (fun h => hl (by rw [← h, zero_add]))]) (fun h => absurd hm h),
        if_pos (zero_add m), AddMonoidAlgebra.single_apply, if_pos rfl]
    · rw [Finsupp.notMem_support_iff.mp hm, mul_zero]
      exact (Finset.sum_eq_zero fun l hl => by
        rw [if_neg (fun h => hm (by rw [← h, zero_add]; exact hl))]).symm

@[simp] theorem nelt_mul_nelt : (nelt : P p) * nelt = 0 := by
  rw [mul_nelt, eps_nelt, zero_smul]

theorem eps_one' : eps (1 : P p) = 1 := by
  rw [AddMonoidAlgebra.one_def, eps_single]

theorem eps_inv (δ : (P p)ˣ) :
    eps (((δ⁻¹ : (P p)ˣ) : P p)) = (eps ((δ : P p)))⁻¹ := by
  have h := eps_mul ((δ : P p)) (((δ⁻¹ : (P p)ˣ) : P p))
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, eps_one'] at h
  exact eq_inv_of_mul_eq_one_left (by linear_combination -h)

/-- The corrected inverse of an `N`-shifted unit. -/
theorem inv_add_smul_N (δ δ' : (P p)ˣ) (c : ZMod p)
    (hval : (δ' : P p) = (δ : P p) + c • nelt) :
    ((δ'⁻¹ : (P p)ˣ) : P p)
      = ((δ⁻¹ : (P p)ˣ) : P p) - (c * ((eps ((δ : P p)))⁻¹) ^ 2) • nelt := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [hval]
  have h1 : (δ : P p) * ((δ⁻¹ : (P p)ˣ) : P p) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hδN : (δ : P p) * nelt = eps ((δ : P p)) • nelt := mul_nelt _
  have hNB : (nelt : P p) * ((δ⁻¹ : (P p)ˣ) : P p) = (eps ((δ : P p)))⁻¹ • nelt := by
    rw [mul_comm, mul_nelt, eps_inv]
  have hε : eps ((δ : P p)) ≠ 0 := eps_unit_ne_zero δ
  -- normalize all smuls to multiplications and finish by `linear_combination`
  simp only [smul_eq_single_zero_mul (p := p)] at hδN hNB ⊢
  have hcancel : (single (0 : ZMod p) (eps ((δ : P p))) : P p)
        * single 0 (c * ((eps ((δ : P p)))⁻¹) ^ 2)
      = single 0 (c * (eps ((δ : P p)))⁻¹) := by
    rw [single_mul_single, add_zero]
    congr 1
    field_simp
  have hsm : (single (0 : ZMod p) c : P p) * single 0 ((eps ((δ : P p)))⁻¹)
      = single 0 (c * (eps ((δ : P p)))⁻¹) := by
    rw [single_mul_single, add_zero]
  linear_combination (nelt : P p) * hsm + h1 - (single (0 : ZMod p) (c * ((eps ((δ : P p)))⁻¹) ^ 2)
      : P p) * hδN
    + (single (0 : ZMod p) c : P p) * hNB
    - (single (0 : ZMod p) c : P p) * (single (0 : ZMod p) (c * ((eps ((δ : P p)))⁻¹) ^ 2) : P p)
      * (nelt_mul_nelt (p := p)) - (nelt : P p) * hcancel

theorem single_zero_mul_single_zero (a b : ZMod p) :
    (single (0 : ZMod p) a : P p) * single 0 b = single 0 (a * b) := by
  rw [single_mul_single, add_zero]

/-- **`ℓ_n` is insensitive to `N`-shifts** (when `(p−1) ∤ n−1` and `(p−1) ∤ n`). -/
theorem ell_eq_of_val_eq_add_smul_N {n : ℕ} (hn : 2 ≤ n)
    (h1d : ¬ (p - 1) ∣ (n - 1)) (h2d : ¬ (p - 1) ∣ n)
    (δ δ' : (P p)ˣ) (c : ZMod p) (hval : (δ' : P p) = (δ : P p) + c • nelt) :
    ell n δ' = ell n δ := by
  have hinv := inv_add_smul_N δ δ' c hval
  have hp2 : ¬ (p - 1) ∣ 1 := fun h => h1d (h.trans (one_dvd _))
  have hεθN : eps (theta (nelt : P p)) = 0 := by
    have h := eps_theta_iterate_nelt (p := p) 1
    rw [Function.iterate_one] at h
    rw [h]
    exact sum_pow_zmod_eq_zero le_rfl hp2
  have hθNN : theta (nelt : P p) * nelt = 0 := by
    rw [mul_comm, mul_theta_nelt, eps_nelt, hεθN, zero_smul, zero_smul, sub_zero]
  have hθNB : theta (nelt : P p) * ((δ⁻¹ : (P p)ˣ) : P p)
      = eps (((δ⁻¹ : (P p)ˣ) : P p)) • theta nelt
        - eps (theta (((δ⁻¹ : (P p)ˣ) : P p))) • nelt := by
    rw [mul_comm, mul_theta_nelt]
  have hθδN : theta ((δ : P p)) * nelt = eps (theta ((δ : P p))) • nelt := mul_nelt _
  -- the dlog expansion
  set e := c * ((eps ((δ : P p)))⁻¹) ^ 2 with he
  have hdlog : dlog δ' = dlog δ
      + (c * eps (((δ⁻¹ : (P p)ˣ) : P p))) • theta nelt
      + (-(e * eps (theta ((δ : P p)))) - c * eps (theta (((δ⁻¹ : (P p)ˣ) : P p)))) • nelt := by
    rw [dlog, dlog, hval, hinv, theta_add, theta_smul]
    simp only [smul_eq_single_zero_mul (p := p)] at hθNN hθNB hθδN ⊢
    have h1 := single_zero_mul_single_zero (p := p) c (eps (((δ⁻¹ : (P p)ˣ) : P p)))
    have h2 := single_zero_mul_single_zero (p := p) e (eps (theta ((δ : P p))))
    have h3 := single_zero_mul_single_zero (p := p) c (eps (theta (((δ⁻¹ : (P p)ˣ) : P p))))
    have hneg : ∀ a : ZMod p, (single (0 : ZMod p) (-a) : P p) = -single 0 a := fun a => by
      classical
      ext m
      change (single (0 : ZMod p) (-a) : P p) m = -((single (0 : ZMod p) a : P p) m)
      rw [AddMonoidAlgebra.single_apply, AddMonoidAlgebra.single_apply]
      split_ifs <;> ring
    rw [show (-(e * eps (theta ((δ : P p)))) - c * eps (theta (((δ⁻¹ : (P p)ˣ) : P p))))
        = -(e * eps (theta ((δ : P p))) + c * eps (theta (((δ⁻¹ : (P p)ˣ) : P p)))) by ring,
      hneg]
    rw [show (e * eps (theta ((δ : P p))) + c * eps (theta (((δ⁻¹ : (P p)ˣ) : P p))))
        = e * eps (theta ((δ : P p))) + c * eps (theta (((δ⁻¹ : (P p)ˣ) : P p))) from rfl]
    have hadd : (single (0 : ZMod p)
        (e * eps (theta ((δ : P p))) + c * eps (theta (((δ⁻¹ : (P p)ˣ) : P p)))) : P p)
        = single 0 (e * eps (theta ((δ : P p))))
          + single 0 (c * eps (theta (((δ⁻¹ : (P p)ˣ) : P p)))) := by
      classical
      ext m
      change _ = (single (0 : ZMod p) (e * eps (theta ((δ : P p)))) : P p) m
          + (single (0 : ZMod p) (c * eps (theta (((δ⁻¹ : (P p)ˣ) : P p)))) : P p) m
      rw [AddMonoidAlgebra.single_apply, AddMonoidAlgebra.single_apply,
        AddMonoidAlgebra.single_apply]
      split_ifs <;> ring
    rw [hadd]
    linear_combination (single (0 : ZMod p) c : P p) * hθNB
      - (single (0 : ZMod p) e : P p) * hθδN
      - (single (0 : ZMod p) c : P p) * (single (0 : ZMod p) e : P p) * hθNN
      + theta (nelt : P p) * h1 - nelt * h2 - nelt * h3
  -- apply `ε ∘ θ^[n−1]` and kill both correction terms by power-sum vanishing
  rw [ell, ell, hdlog, theta_iterate_add, theta_iterate_add, map_add, map_add,
    theta_iterate_smul, theta_iterate_smul, eps_smul, eps_smul]
  have hit : theta^[n - 1] (theta (nelt : P p)) = theta^[n] (nelt : P p) := by
    rw [← Function.iterate_succ_apply, show (n - 1).succ = n by omega]
  rw [hit, eps_theta_iterate_nelt, eps_theta_iterate_nelt,
    sum_pow_zmod_eq_zero (by omega : 1 ≤ n - 1) h1d,
    sum_pow_zmod_eq_zero (by omega : 1 ≤ n) h2d]
  ring

/-- The monomial unit `c·Xᵏ` (`c ≠ 0`). -/
noncomputable def singleUnit (k c : ZMod p) (hc : c ≠ 0) : (P p)ˣ where
  val := single k c
  inv := single (-k) c⁻¹
  val_inv := by
    rw [single_mul_single, add_neg_cancel, mul_inv_cancel₀ hc]
    exact AddMonoidAlgebra.one_def.symm
  inv_val := by
    rw [single_mul_single, neg_add_cancel, inv_mul_cancel₀ hc]
    exact AddMonoidAlgebra.one_def.symm

/-- Monomial units (constants and `±Xᵏ`) are `ℓ_n`-invisible for `n ≥ 2`. -/
theorem ell_singleUnit (n : ℕ) (hn : 2 ≤ n) (k c : ZMod p) (hc : c ≠ 0) :
    ell n (singleUnit k c hc) = 0 := by
  rw [ell, dlog]
  change eps (theta^[n - 1] (theta (single k c) * single (-k) c⁻¹)) = 0
  rw [theta_single, single_mul_single, add_neg_cancel,
    show k * c * c⁻¹ = k from by field_simp]
  have : theta^[n - 1] (single (0 : ZMod p) k) = 0 := by
    rw [theta_iterate_single, zero_pow (by omega : n - 1 ≠ 0), zero_mul, single_zero]
  rw [this, map_zero]

end KummerLog

end CyclotomicNT
