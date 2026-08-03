import CyclotomicNT.Faithfulness

/-!
Irregularity certificate for FLT-37, `native_decide`-free.

Goal: `QiCert.irrListCert 37 [32] = true` — i.e. 32 is the ONLY irregular index of 37.

The engine's `irrListCert` zero-tests `(bern i).num` over ℚ (not kernel-decidable);
`irrListCertFast` swaps that for a `bernZList` (ZMod p) test (kernel STALLS). We mirror the
fast cert on the pure-`Nat` `FaithSpike.bModN` (proven faithful: `bModN_map_cast`), which DOES
kernel-`decide`, and bridge `irrListCertN (bModN) = irrListCertFast` so `irrListCert_of_fast`
delivers the engine cert.
-/

open FaithSpike CyclotomicNT CyclotomicNT.QiCert

namespace IrrCertNat

/-- Every entry of `bModN p n` is `< p` (entries are `_ % p`). -/
theorem bModN_mem_lt {p : ℕ} (hp : 0 < p) : ∀ {n : ℕ} {x : ℕ}, x ∈ bModN p n → x < p := by
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [bModN, List.mem_singleton] at hx
    subst hx; exact Nat.mod_lt _ hp
  | succ n ih =>
    intro x hx
    rw [bModN, List.mem_append] at hx
    rcases hx with h | h
    · exact ih h
    · rw [List.mem_singleton] at h; subst h; exact Nat.mod_lt _ hp

/-- Hence `getD` (default `0`) is `< p`. -/
theorem bModN_getD_lt {p : ℕ} (hp : 0 < p) (n i : ℕ) : (bModN p n).getD i 0 < p := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : (bModN p n)[i]? with _ | v
  · simpa using hp
  · simp only [Option.getD_some]
    exact bModN_mem_lt hp (List.mem_of_getElem? h)

/-- Pure-`Nat` mirror of `irrCheckFastB` reading from `bModN`. -/
def irrCheckN (p : ℕ) (Bn : List ℕ) (i : ℕ) : Bool :=
  decide (Even i) && decide (2 ≤ i) && decide (i ≤ p - 3) && decide (Bn.getD i 0 = 0)

/-- Pure-`Nat` mirror of `irrListCertFast`. -/
def irrListCertN (p : ℕ) (Bn : List ℕ) (L : List ℕ) : Bool :=
  ((List.range (p - 2)).all fun i => irrCheckN p Bn i == decide (i ∈ L))
    && (L.all fun x => decide (x < p - 2))

variable {p : ℕ} [Fact p.Prime]

/-- The `ZMod p` zero-test on `bernZList` equals the `Nat` zero-test on `bModN` (any `i`). -/
theorem zerotest_equiv (hp5 : 5 ≤ p) (i : ℕ) :
    decide ((bernZList p (p - 3)).getD i 0 = 0) = decide ((bModN p (p - 3)).getD i 0 = 0) := by
  have hppos : 0 < p := by omega
  rw [decide_eq_decide, ← bModN_map_cast hp5 (le_refl _), getD_map_cast']
  constructor
  · intro h
    have hdvd : p ∣ (bModN p (p - 3)).getD i 0 := (CharP.cast_eq_zero_iff (ZMod p) p _).mp h
    exact Nat.eq_zero_of_dvd_of_lt hdvd (bModN_getD_lt hppos _ _)
  · intro h; rw [h]; simp

/-- Per-index bridge: the fast check equals the `Nat` check. -/
theorem irrCheck_bridge (hp5 : 5 ≤ p) (i : ℕ) :
    irrCheckFastB p (bernZList p (p - 3)) i = irrCheckN p (bModN p (p - 3)) i := by
  unfold irrCheckFastB irrCheckN
  rw [zerotest_equiv hp5]

/-- The `Nat` list cert equals the engine's fast list cert. -/
theorem irrListCertN_eq (hp5 : 5 ≤ p) (L : List ℕ) :
    irrListCertN p (bModN p (p - 3)) L = irrListCertFast p L := by
  unfold irrListCertN irrListCertFast
  simp only [irrCheck_bridge hp5]

/-- **Bridge to the trusted engine cert.** -/
theorem irrListCert_of_certN (hp5 : 5 ≤ p) {L : List ℕ}
    (h : irrListCertN p (bModN p (p - 3)) L = true) : irrListCert p L = true :=
  irrListCert_of_fast hp5 ((irrListCertN_eq hp5 L).symm ▸ h)

end IrrCertNat
