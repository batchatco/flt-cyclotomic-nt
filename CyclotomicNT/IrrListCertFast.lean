import CyclotomicNT.HerbrandBernoulli
import CyclotomicNT.BernoulliMod

/-!
# Fast mod-`p` Bernoulli recurrence for `irrListCert`

`bern n = bernoulli' n` is recomputed in exact ℚ (bignum numerators) — the
dominant cost of every per-prime certificate.  For `n ≤ p − 3` every denominator
in the recurrence is `p`-coprime, so the recurrence reduces faithfully to
`ZMod p`.  `bernZList` runs it there; `bernZList_map` proves it is the mod-`p`
image of `bernList`, hence `irrCheck p i` becomes a `ZMod p` zero-test.
-/

open Finset

namespace CyclotomicNT.QiCert

variable {p : ℕ} [hpri : Fact p.Prime]

/-- `(m : ZMod p) ≠ 0` for a `p`-coprime `m`. -/
theorem natZ_ne {m : ℕ} (h : ¬ (p : ℕ) ∣ m) : ((m : ℕ) : ZMod p) ≠ 0 :=
  fun hc => h ((CharP.cast_eq_zero_iff (ZMod p) p m).mp hc)

/-- `(x.den : ZMod p) ≠ 0` for a `p`-coprime denominator. -/
theorem den_cast_ne_zero {x : ℚ} (h : ¬ (p : ℕ) ∣ x.den) : ((x.den : ℕ) : ZMod p) ≠ 0 :=
  natZ_ne h

/-- `bern k` is `p`-integral for `k ≤ p − 3` (von Staudt–Clausen). -/
theorem pInt_bern (hp5 : 5 ≤ p) {k : ℕ} (hk : k ≤ p - 3) : ¬ (p : ℕ) ∣ (bern k).den := by
  have hp2 : p ≠ 2 := by omega
  rw [bern_eq]
  rcases eq_or_ne k 1 with rfl | hk1
  · rw [bernoulli'_one, show ((1 : ℚ) / 2).den = 2 from by norm_num]
    exact fun hd => absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
  · rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [bernoulli'_zero]; simp [Nat.dvd_one]; omega
    · rw [← bernoulli_eq_bernoulli'_of_ne_one hk1]
      refine CyclotomicNT.not_dvd_den_bernoulli hp2 ?_
      exact fun hd => absurd (Nat.le_of_dvd hkpos hd) (by omega)

/-- Cast of a sum of `p`-integral rationals distributes (every partial sum is
`p`-integral, so each `cast_add` step has a nonzero denominator). -/
theorem cast_sum_pInt {s : Finset ℕ} {f : ℕ → ℚ} (hf : ∀ i ∈ s, ¬ (p : ℕ) ∣ (f i).den) :
    (((∑ i ∈ s, f i : ℚ)) : ZMod p) = ∑ i ∈ s, ((f i : ℚ) : ZMod p) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      Rat.cast_add_of_ne_zero (den_cast_ne_zero (hf a (Finset.mem_insert_self a s)))
        (den_cast_ne_zero (CyclotomicNT.PInt.sum s f
          (fun i hi => hf i (Finset.mem_insert_of_mem hi)))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- The mod-`p` Bernoulli list: the recurrence of `bernList` run in `ZMod p`. -/
def bernZList (p : ℕ) [Fact p.Prime] : ℕ → List (ZMod p)
  | 0 => [1]
  | (n + 1) =>
    let L := bernZList p n
    L ++ [1 - ∑ k ∈ Finset.range (n + 1),
      ((n + 1).choose k : ZMod p) * (((n : ZMod p) + 1 - (k : ZMod p) + 1))⁻¹ * L.getD k 0]

def bernZ (p n : ℕ) [Fact p.Prime] : ZMod p := (bernZList p n).getD n 0

theorem bernZList_succ (n : ℕ) : bernZList p (n + 1) = bernZList p n ++
    [1 - ∑ k ∈ Finset.range (n + 1), ((n + 1).choose k : ZMod p)
      * (((n : ZMod p) + 1 - (k : ZMod p) + 1))⁻¹ * (bernZList p n).getD k 0] := rfl

/-- `getD` commutes with `map` when the default is fixed by the map. -/
theorem getD_map_cast (L : List ℚ) (k : ℕ) :
    (L.map (fun q : ℚ => (q : ZMod p))).getD k 0 = ((L.getD k 0 : ℚ) : ZMod p) := by
  induction L generalizing k with
  | nil => simp
  | cons a t ih => cases k with
    | zero => simp
    | succ k => simpa using ih k

/-- `(bernList n).getD k 0 = bern k` for `k ≤ n`. -/
theorem bernList_getD {n k : ℕ} (hk : k ≤ n) : (bernList n).getD k 0 = bern k := by
  rw [bern_eq, bernList_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show k < n + 1 by omega), Option.map_some, Option.getD_some]

/-- **Faithful reduction**: for `n ≤ p − 3`, the mod-`p` list is the cast of `bernList`. -/
theorem bernZList_map (hp5 : 5 ≤ p) : ∀ {n : ℕ}, n ≤ p - 3 →
    bernZList p n = (bernList n).map (fun q : ℚ => (q : ZMod p)) := by
  intro n
  induction n with
  | zero => intro _; simp [bernZList, bernList]
  | succ n ih =>
    intro hn
    have hn' : n ≤ p - 3 := by omega
    have hden : ∀ k ∈ Finset.range (n + 1),
        ¬ (p : ℕ) ∣ (((n + 1).choose k : ℚ) / ((n : ℚ) + 1 - (k : ℚ) + 1)
          * (bernList n).getD k 0).den := by
      intro k hk
      simp only [Finset.mem_range] at hk
      have hd : ((n : ℚ) + 1 - (k : ℚ) + 1) = ((n + 2 - k : ℕ) : ℚ) := by
        rw [Nat.cast_sub (show k ≤ n + 2 by omega)]; push_cast; ring
      have hdvd : ¬ (p : ℕ) ∣ (n + 2 - k) :=
        fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
      rw [hd, bernList_getD (show k ≤ n by omega)]
      exact CyclotomicNT.PInt.mul
        (CyclotomicNT.PInt.div_nat (CyclotomicNT.PInt.natCast _) hdvd)
        (pInt_bern hp5 (show k ≤ p - 3 by omega))
    rw [bernZList_succ, bernList_succ, List.map_append, List.map_cons, List.map_nil, ih hn']
    congr 1
    rw [List.cons.injEq]
    refine ⟨?_, rfl⟩
    rw [Rat.cast_sub_of_ne_zero (by norm_num)
        (den_cast_ne_zero (CyclotomicNT.PInt.sum _ _ hden)), Rat.cast_one, cast_sum_pInt hden]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    have hd : ((n : ℚ) + 1 - (k : ℚ) + 1) = ((n + 2 - k : ℕ) : ℚ) := by
      rw [Nat.cast_sub (show k ≤ n + 2 by omega)]; push_cast; ring
    have hdvd : ¬ (p : ℕ) ∣ (n + 2 - k) :=
      fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    have hbk : ¬ (p : ℕ) ∣ ((bernList n).getD k 0).den := by
      rw [bernList_getD (show k ≤ n by omega)]; exact pInt_bern hp5 (show k ≤ p - 3 by omega)
    have hX : ¬ (p : ℕ) ∣ (((n + 1).choose k : ℚ) / ((n + 2 - k : ℕ) : ℚ)).den :=
      CyclotomicNT.PInt.div_nat (CyclotomicNT.PInt.natCast _) hdvd
    have hc1 : ((((n + 1).choose k : ℚ).den : ℕ) : ZMod p) ≠ 0 := by
      rw [Rat.den_natCast, Nat.cast_one]; exact one_ne_zero
    have hc2 : ((((n + 2 - k : ℕ) : ℚ).num : ℤ) : ZMod p) ≠ 0 := by
      rw [Rat.num_natCast]; exact_mod_cast natZ_ne hdvd
    rw [getD_map_cast, hd,
      Rat.cast_mul_of_ne_zero (den_cast_ne_zero hX) (den_cast_ne_zero hbk),
      Rat.cast_div_of_ne_zero hc1 hc2,
      Rat.cast_natCast, Rat.cast_natCast, Nat.cast_sub (show k ≤ n + 2 by omega)]
    push_cast; ring

theorem bernZ_eq (hp5 : 5 ≤ p) {n : ℕ} (hn : n ≤ p - 3) : bernZ p n = ((bern n : ℚ) : ZMod p) := by
  rw [bernZ, bernZList_map hp5 hn, getD_map_cast, bern]

/-- **The irregularity test**: `bernZ p i = 0` iff `p ∣ num Bᵢ` (the condition
`irrCheck` checks), for `i ≤ p − 3`. -/
theorem bernZ_eq_zero_iff (hp5 : 5 ≤ p) {i : ℕ} (hi : i ≤ p - 3) :
    bernZ p i = 0 ↔ (p : ℤ) ∣ (bern i).num := by
  have hden : ((bern i).den : ZMod p) ≠ 0 := den_cast_ne_zero (pInt_bern hp5 hi)
  rw [bernZ_eq hp5 hi, Rat.cast_def, div_eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [hden, or_false]

theorem bernZList_length (m : ℕ) : (bernZList p m).length = m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [bernZList_succ, List.length_append, ih]; rfl

/-- `bernZList p m` agrees with `bernZ p i` at every index `i ≤ m` (the list is
extended, never rewritten). -/
theorem bernZList_getD_stable : ∀ {i m : ℕ}, i ≤ m → (bernZList p m).getD i 0 = bernZ p i := by
  intro i m
  induction m with
  | zero => intro h; obtain rfl : i = 0 := Nat.le_zero.mp h; rfl
  | succ m ih =>
    intro h
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · rfl
    · rw [bernZList_succ, List.getD_append _ _ _ _ (by rw [bernZList_length]; omega)]
      exact ih (by omega)

/-- The irregular-index check using a precomputed mod-`p` Bernoulli list `B`. -/
def irrCheckFastB (p : ℕ) (B : List (ZMod p)) (i : ℕ) : Bool :=
  decide (Even i) && decide (2 ≤ i) && decide (i ≤ p - 3) && decide (B.getD i 0 = 0)

theorem irrCheckFastB_eq (hp5 : 5 ≤ p) (i : ℕ) :
    irrCheckFastB p (bernZList p (p - 3)) i = irrCheck p i := by
  unfold irrCheckFastB irrCheck
  by_cases hi : i ≤ p - 3
  · rw [bernZList_getD_stable hi,
      show decide (bernZ p i = 0) = decide ((p : ℤ) ∣ (bern i).num) by
        rw [decide_eq_decide]; exact bernZ_eq_zero_iff hp5 hi]
  · simp [decide_eq_false (show ¬ i ≤ p - 3 by omega)]

/-- **Fast `irrListCert`**: the mod-`p` recurrence, the whole array computed ONCE. -/
def irrListCertFast (p : ℕ) [Fact p.Prime] (L : List ℕ) : Bool :=
  let B := bernZList p (p - 3)
  ((List.range (p - 2)).all fun i => irrCheckFastB p B i == decide (i ∈ L))
    && (L.all fun x => decide (x < p - 2))

/-- **The bridge**: the fast cert equals the trusted `irrListCert` (for `5 ≤ p`). -/
theorem irrListCertFast_eq (hp5 : 5 ≤ p) (L : List ℕ) :
    irrListCertFast p L = irrListCert p L := by
  unfold irrListCertFast irrListCert
  simp only [irrCheckFastB_eq hp5]

theorem irrListCert_of_fast (hp5 : 5 ≤ p) {L : List ℕ}
    (h : irrListCertFast p L = true) : irrListCert p L = true :=
  (irrListCertFast_eq hp5 L) ▸ h

end CyclotomicNT.QiCert
