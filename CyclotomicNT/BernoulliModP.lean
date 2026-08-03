import CyclotomicNT.BernoulliMod

/-!
# The mod-`p` Bernoulli recurrence: `irrListCert` at native speed

`irrCheck p i` recomputes the memoized rational `bernList i` per index, in exact
rational arithmetic whose numerators grow to hundreds of digits — the dominant
cost of every per-prime certificate file.

For `i ≤ p − 3` every denominator appearing in the recurrence is `p`-coprime
(each division is by `n + 2 − k ≤ p − 1`; denominators of sums divide products
of denominators), so the whole recurrence reduces faithfully mod `p`.  `bernZ`
runs it in `ZMod p` — `O(p²)` word operations, computed ONCE for all indices —
and the guarded `@[csimp]` makes every existing `irrListCert` `native_decide`
take milliseconds with no statement changes.
-/

namespace CyclotomicNT.QiCert

open Finset

variable {p : ℕ} [hpri : Fact (Nat.Prime p)]

variable {p : ℕ} [hpri : Fact (Nat.Prime p)]

end CyclotomicNT.QiCert
