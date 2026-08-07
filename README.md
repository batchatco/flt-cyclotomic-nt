# flt-cyclotomic-nt

The `CyclotomicNT` Lean library: the analytic *and* algebraic number-theory core shared by the
`flt-vandiver` (Vandiver-certificate) and `flt-regular-extended` (regular-prime) routes
(sorry-free; builds on Mathlib, `flt-stickelberger`, and `flt-regular`). It supplies the
cyclotomic analytic class-number formula — proving `cyclotomic_unit_index` (Washington Thm 8.2)
and the class-number split — together with the Stickelberger / Herbrand / Kummer-Case-I /
class-group machinery and the pure-`Nat` irregularity certificates that the sibling repos consume.

Dependency graph: Mathlib + `flt-stickelberger` + `flt-regular` → **`flt-cyclotomic-nt`** →
`flt-vandiver` / `flt-regular-extended` / `flt-vandiver-primes`.

## Analytic class-number formula

- **Dedekind zeta Euler product** — `DedekindEulerProduct` (the Euler product
  `ζ_K = ∏_𝔭 (1 − N𝔭^{-s})⁻¹`, missing from Mathlib), `DedekindCounting`,
  `DedekindFactorization` (`ζ_{ℚ(ζ_p)} = ∏_χ L(·,χ)`), with the residue/class-number
  assembly in `CyclotomicClassNumber` and `KPlusSplitting`.
- **Dirichlet L-values** — `GeneralizedBernoulli`, `AbelianLFactorization`,
  `DirichletAbel`, `SawtoothFourier`, `HurwitzOddZero`, `EvenLOneValue`,
  `OddLOneValue`, `OddLValue`.
- **Group / circulant determinant** — `GroupDeterminant`,
  `ReducedGroupDeterminant` (Dedekind group determinant, Washington Lemma 5.26).
- **Cyclotomic unit index** — `CyclotomicUnitIndex` / `CyclotomicUnitIndexProof`
  (`cyclotomic_unit_index`, Washington Thm 8.2, `[E:C] = h⁺`).

## Class-group / Galois machinery

- **Stickelberger annihilation** — `Stickelberger` (`stickelberger_annihilates`: the
  Stickelberger element kills the class group), `StkBridge`
  (`stickelberger_annihilates_ideal`, `stickelberger_annihilates_prime_of_coprime`) and
  `StkAnnihilation` — the all-ideals reduction built on the clean-room `flt-stickelberger`
  single-prime core.
- **Herbrand's theorem** — `Herbrand` (`herbrand`, `herbrand_eigenProj`, Washington Thm 6.17),
  with `HerbrandEigen`, `HerbrandBernoulli`.
- **Kummer's Case-I criterion** — `CaseIKummer` (`caseI_of_not_irregular`,
  `p ∤ B_{p−3} ⟹ Case I`), with `KummerReduction`, `KummerLogDeriv`, `CaseII`, `MirimanoffSum`.
- **Class-group functoriality** — `ClassGroupMap` (`idealExtend`, `classGroupExtend`,
  `classGroupDescend`, `classGroupNorm_classGroupExtend` — extension/norm/Galois action, absent
  from Mathlib), plus the `Eigen*`, `CyclotomicUnit*`, `KPlus*` eigenspace/real-subfield families.
- **Regularity bridge** — `RegularPrimes` (`IsVandiverPrime` consequences feeding the
  Vandiver and regular routes).

## Computable / certificate base (pure `Nat`, shared with both routes)

- **Computable Bernoulli** — `BernoulliMod` (memoized `bernoulli'`), `BernoulliModP`.
- **Irregularity certificates** — `Faithfulness` (`bModN` recurrence proven equal to
  `bernZList`, the kernel Bernoulli check), `IrrCertNat` (`irrListCert_of_certN`), and
  `IrrListCertFast` (`irrListCertFast`/`irrListCertFast_eq`).

Pinned to mathlib release tag `v4.31.0` (`fabf563a7c…`, lean `v4.31.0`).

## Part of the flt-vandiver family

Six sibling libraries (clone them as siblings — Lake uses relative paths), release tag
**`afm-v1`**, GitHub topic
[`flt-vandiver`](https://github.com/batchatco?tab=repositories&q=topic:flt-vandiver).

| Repo | Role |
|------|------|
| `flt-vandiver` | Engine: Case I/II descent, crown theorems, certificate bridges (Washington 9.5) |
| `flt-vandiver-primes` | `native_decide` instances: every prime 17 ≤ p < 1000, plus 16843 and 2124679 |
| `flt-vandiver-primes-kernel` | Kernel `decide` (zero compiler trust): the 8 irregular primes < 200 |
| `flt-regular-extended` | Kernel Bernoulli ⟹ regular FLT, 17 ≤ q < 350 (47 primes) |
| `flt-cyclotomic-nt` | Herbrand, cyclotomic unit index, class-group Stickelberger, certificate base |
| `flt-stickelberger` | Clean-room Gauss-sum / Stickelberger core (Mathlib-only) |

Each ships an `AxiomAudit.lean` reprinting its headline theorems' axiom base. `sorry`-free on
Lean / Mathlib `v4.31.0`.

## Blueprint & metadata

A dependency-graph blueprint of this library is under [`blueprint/`](blueprint/) (rendered web + PDF published to GitHub Pages once the family is public). Family-level metadata lives in [`formalization.yaml`](https://github.com/batchatco/flt-vandiver/blob/afm-v1/formalization.yaml) in the flt-vandiver repo.

---

Apache License 2.0 — see [LICENSE](LICENSE).
© Bradley Taylor. Code written largely by Claude (Anthropic) under the author's direction.
