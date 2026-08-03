import CyclotomicNT.IrrListCertFast

/-!
Faithfulness — COMPLETE, sorry-free.

The kernel-`decide`-able pure-`Nat` Bernoulli check `bModN` is proven to be
the *real* irregularity check: `not_irregular_of_bModN` shows a nonzero pure-`Nat`
value certifies `¬ IsIrregularIndex p k`, with NO `native_decide`. Axioms:
`[propext, Classical.choice, Quot.sound]` only — a complete `native_decide`-free
regularity/irregularity check for small primes.

Method: define a pure-`Nat` recurrence `bModN` matching the engine's `bernZList`
(ℚ/ZMod inverse → Fermat inverse `minvN`), prove `bModN` is the `Nat.cast` of
`bernZList` by induction (`bModN_map_cast`), and inherit the engine's already-proven
`bernZList_map` / `bernZ_eq_zero_iff` to reach the semantics.

Check from this package root with:
    lake env lean CyclotomicNT/Faithfulness.lean
-/

open CyclotomicNT CyclotomicNT.QiCert

namespace FaithSpike
variable {p : ℕ} [Fact p.Prime]

/-- Fermat inverse in pure `Nat`. -/
def minvN (p a : ℕ) : ℕ := a ^ (p - 2) % p

/-- pure-`Nat` Bernoulli mod p, matching `CyclotomicNT.QiCert.bernZList`'s recurrence
    (ℚ/ZMod inverse replaced by the Fermat inverse `minvN`). -/
def bModN (p : ℕ) : ℕ → List ℕ
  | 0 => [1 % p]
  | (n + 1) =>
    let L := bModN p n
    L ++ [(1 + p - (∑ k ∈ Finset.range (n + 1),
      Nat.choose (n + 1) k % p * minvN p (n + 1 - k + 1) % p * L.getD k 0 % p) % p) % p]

/-- `(minvN p a : ZMod p) = (a : ZMod p)⁻¹` when `p ∤ a`. -/
lemma cast_minvN {a : ℕ} (ha : ((a : ZMod p)) ≠ 0) :
    ((minvN p a : ℕ) : ZMod p) = ((a : ZMod p))⁻¹ := by
  unfold minvN
  rw [ZMod.natCast_mod, Nat.cast_pow]
  have hp : Fact (Nat.Prime p) := inferInstance
  field_simp
  rw [← pow_succ]
  have : p - 2 + 1 = p - 1 := by have := hp.out.two_le; omega
  rw [this]; exact ZMod.pow_card_sub_one_eq_one ha

/-- cast commutes with `getD` through `map`. -/
lemma getD_map_cast' (L : List ℕ) (k : ℕ) :
    ((L.map (Nat.cast : ℕ → ZMod p)).getD k 0) = ((L.getD k 0 : ℕ) : ZMod p) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases L[k]? <;> simp

/-- **The bridge**: the pure-`Nat` recurrence is the `Nat.cast` of the engine's
    `bernZList`, for `n ≤ p-3`. Proven by induction; the inductive step is the
    coercion bookkeeping (cast over `Finset.sum`/products/`minvN`; `1+p-s` over ℕ
    matches `1-s̄` over `ZMod p`; per-term `minvN` unit since `n+2-k ∈ [2,p-1]`). -/
theorem bModN_map_cast (hp5 : 5 ≤ p) :
    ∀ {n : ℕ}, n ≤ p - 3 → (bModN p n).map (Nat.cast : ℕ → ZMod p) = bernZList p n := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [bModN, bernZList]
  | succ n ih =>
    intro hn
    have hp : Fact (Nat.Prime p) := inferInstance
    have hppos : 0 < p := hp.out.pos
    have hn' : n ≤ p - 3 := by omega
    rw [bModN, bernZList, List.map_append, ih hn', List.map_cons, List.map_nil]
    congr 1
    congr 1
    rw [ZMod.natCast_mod]
    have hle : (∑ k ∈ Finset.range (n + 1),
        Nat.choose (n + 1) k % p * minvN p (n + 1 - k + 1) % p
          * (bModN p n).getD k 0 % p) % p ≤ 1 + p :=
      le_trans (Nat.le_of_lt (Nat.mod_lt _ hppos)) (by omega)
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, add_zero,
      ZMod.natCast_mod, Nat.cast_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod]
    have hcop : ((↑(n + 1 - k + 1) : ZMod p)) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
      intro hdvd
      have : p ≤ n + 1 - k + 1 := Nat.le_of_dvd (by omega) hdvd
      omega
    have hden : ((↑(n + 1 - k + 1) : ZMod p)) = (↑n + 1 - ↑k + 1) := by
      have hkn : k ≤ n + 1 := by omega
      push_cast [Nat.cast_sub hkn]
      ring
    rw [cast_minvN hcop, hden]
    rw [← ih hn', getD_map_cast']

/-- **Regularity corollary**: a nonzero pure-`Nat` value certifies the engine's
    `bernZ ≠ 0` (`0 < v < p ⇒ (v : ZMod p) ≠ 0`, plus the bridge). -/
theorem bernZ_ne_zero_of_bModN (hp5 : 5 ≤ p) {k : ℕ} (hk : k ≤ p - 3)
    (hpos : 0 < (bModN p k).getD k 0) (hlt : (bModN p k).getD k 0 < p) :
    bernZ p k ≠ 0 := by
  rw [bernZ, ← bModN_map_cast hp5 hk, getD_map_cast']
  intro hc
  have hdvd : p ∣ (bModN p k).getD k 0 := (CharP.cast_eq_zero_iff (ZMod p) p _).mp hc
  exact absurd (Nat.le_of_dvd hpos hdvd) (Nat.not_le.mpr hlt)

/-- **End-to-end, no `native_decide`**: a nonzero kernel-`decide`-able pure-`Nat`
    value at index `k` certifies `¬ IsIrregularIndex p k` — the engine's
    `not_irregular_of_cert` fact with the boolean discharged by `decide` (kernel)
    rather than `native_decide` (compiler). -/
theorem not_irregular_of_bModN (hp5 : 5 ≤ p) {k : ℕ} (hk : k ≤ p - 3)
    (hpos : 0 < (bModN p k).getD k 0) (hlt : (bModN p k).getD k 0 < p) :
    ¬ IsIrregularIndex p k := by
  have hbz := bernZ_ne_zero_of_bModN hp5 hk hpos hlt
  rintro ⟨_, hk2, _, hdvd⟩
  apply hbz
  rw [bernZ_eq_zero_iff hp5 hk]
  have hbk : bern k = bernoulli k :=
    (bern_eq k).trans (bernoulli_eq_bernoulli'_of_ne_one (by omega : k ≠ 1)).symm
  rw [hbk]; exact hdvd

end FaithSpike

-- Axioms: [propext, Classical.choice, Quot.sound] — no native_decide.
-- #print axioms FaithSpike.not_irregular_of_bModN
