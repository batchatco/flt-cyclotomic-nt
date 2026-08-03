import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic.NormNum

/-!
# An efficiently-computable Bernoulli number, and the irregular index of `37`

Mathlib's `bernoulli'` is defined by the unmemoized recurrence `B'_n = 1 - ∑_{k<n} …·B'_k`, so
evaluating `bernoulli' 32` is exponential (both `#eval` and `native_decide` time out).  Here we
build a **memoized** version `bern` (`O(n²)`), prove `bern n = bernoulli' n`, and use it to decide
the irregular index of `37` by `native_decide` — discharging the `irregularIndices_37` fact that
the `Q_i` Vandiver bridge needs.
-/

namespace CyclotomicNT.QiCert

open Finset

/-- `bernList n = [bernoulli' 0, …, bernoulli' n]`, computed in `O(n²)` (the `let` shares the
recursive call, so each level is `O(n)`). -/
def bernList : ℕ → List ℚ
  | 0 => [1]
  | (n + 1) =>
    let L := bernList n
    L ++ [1 - ∑ k ∈ range (n + 1),
      ((n + 1).choose k : ℚ) / ((n + 1 : ℚ) - (k : ℚ) + 1) * L.getD k 0]

theorem bernList_succ (n : ℕ) : bernList (n + 1) = bernList n ++
    [1 - ∑ k ∈ range (n + 1), ((n + 1).choose k : ℚ) / ((n + 1 : ℚ) - (k : ℚ) + 1)
      * (bernList n).getD k 0] := rfl

/-- The efficiently-computable Bernoulli number `bern n = bernoulli' n`. -/
def bern (n : ℕ) : ℚ := (bernList n).getD n 0

theorem bernList_eq (n : ℕ) : bernList n = (List.range (n + 1)).map bernoulli' := by
  induction n with
  | zero => simp [bernList, bernoulli'_zero, List.range_succ]
  | succ n ih =>
    have hmap : ∀ k, k < n + 1 → ((List.range (n + 1)).map bernoulli').getD k 0 = bernoulli' k := by
      intro k hk
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
      rfl
    rw [bernList_succ, ih]
    conv_rhs => rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    congr 1
    congr 1
    rw [bernoulli'_def (n + 1)]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [hmap k (mem_range.mp hk)]
    push_cast
    ring

theorem bern_eq (n : ℕ) : bern n = bernoulli' n := by
  rw [bern, bernList_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (Nat.lt_succ_self n)]
  rfl

/-- The even indices `i ∈ [2, p-3]` at which `p` is irregular (`p ∣ num Bᵢ`). -/
def IsIrregularIndex (p i : ℕ) : Prop :=
  Even i ∧ 2 ≤ i ∧ i ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli i).num

/-- Computable form of `IsIrregularIndex 37` using the memoized `bern` (`= bernoulli'`). -/
def irrCheck37 (i : ℕ) : Bool :=
  decide (Even i) && decide (2 ≤ i) && decide (i ≤ 34) && decide ((37 : ℤ) ∣ (bern i).num)

theorem isIrregularIndex_37_iff_check (i : ℕ) : IsIrregularIndex 37 i ↔ irrCheck37 i = true := by
  unfold IsIrregularIndex irrCheck37
  simp only [Bool.and_eq_true, decide_eq_true_eq, show (37 : ℕ) - 3 = 34 from rfl]
  refine ⟨fun ⟨he, h2, h34, hd⟩ => ⟨⟨⟨he, h2⟩, h34⟩, ?_⟩,
    fun ⟨⟨⟨he, h2⟩, h34⟩, hd⟩ => ⟨he, h2, h34, ?_⟩⟩
  · rwa [bernoulli_eq_bernoulli'_of_ne_one (by omega : i ≠ 1), ← bern_eq] at hd
  · rwa [bernoulli_eq_bernoulli'_of_ne_one (by omega : i ≠ 1), ← bern_eq]

/-- Computable form of `IsIrregularIndex p` on the memoized `bern` (`= bernoulli'`). -/
def irrCheck (p i : ℕ) : Bool :=
  decide (Even i) && decide (2 ≤ i) && decide (i ≤ p - 3)
    && decide ((p : ℤ) ∣ (bern i).num)

/-- The single Bool certifying that `L` is **exactly** the list of irregular indices
of `p`: the check agrees with membership on the whole range, and `L` is bounded. -/
def irrListCert (p : ℕ) (L : List ℕ) : Bool :=
  ((List.range (p - 2)).all fun i => irrCheck p i == decide (i ∈ L))
    && (L.all fun x => decide (x < p - 2))

theorem isIrregularIndex_iff_check (p i : ℕ) :
    IsIrregularIndex p i ↔ irrCheck p i = true := by
  unfold IsIrregularIndex irrCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fun ⟨he, h2, h3, hd⟩ => ⟨⟨⟨he, h2⟩, h3⟩, ?_⟩,
    fun ⟨⟨⟨he, h2⟩, h3⟩, hd⟩ => ⟨he, h2, h3, ?_⟩⟩
  · rwa [bernoulli_eq_bernoulli'_of_ne_one (by omega : i ≠ 1), ← bern_eq] at hd
  · rwa [bernoulli_eq_bernoulli'_of_ne_one (by omega : i ≠ 1), ← bern_eq]

/-- The certificate decodes to the characterization the `Q_i` bridge wants. -/
theorem irregularIndices_of_cert {p : ℕ} {L : List ℕ} (h : irrListCert p L = true) :
    ∀ i, i ∈ L ↔ IsIrregularIndex p i := by
  rw [irrListCert, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨hall, hbound⟩ := h
  intro i
  rcases Nat.lt_or_ge i (p - 2) with hi | hi
  · have h1 := hall i (List.mem_range.mpr hi)
    rw [beq_iff_eq] at h1
    rw [isIrregularIndex_iff_check, h1, decide_eq_true_eq]
  · constructor
    · intro hin
      have := hbound i hin
      rw [decide_eq_true_eq] at this
      omega
    · intro hirr
      obtain ⟨-, h2, h3, -⟩ := hirr
      omega

/-- `p − 3 ∉ L` (a `decide`) plus the certificate give Kummer's Case I hypothesis. -/
theorem not_irregular_of_cert {p : ℕ} {L : List ℕ} (h : irrListCert p L = true)
    (hfree : (p - 3) ∉ L) : ¬ IsIrregularIndex p (p - 3) :=
  fun hirr => hfree ((irregularIndices_of_cert h _).mpr hirr)

end CyclotomicNT.QiCert
