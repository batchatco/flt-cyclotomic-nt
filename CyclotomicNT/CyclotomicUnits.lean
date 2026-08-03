import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.Algebra.Ring.GeomSum

/-!
# Packaged cyclotomic units

Mathlib (`RingTheory.RootsOfUnity.CyclotomicUnits`) proves that `∑_{i<j} ζ^i = (ζ^j-1)/(ζ-1)` is a
**unit** (`IsPrimitiveRoot.geom_sum_isUnit`) and that the `ζ^j-1` are pairwise associated, but it
leaves the cyclotomic unit as an unnamed `IsUnit`.  Here we package it as a `Units` object
`cyclotomicUnit` with its defining-relation API.

This is the foundational object of the cyclotomic-unit theory:
* Washington Thm 8.14/8.16/Prop 8.18 (the `Q_i` Vandiver bridge `qiVandiverBridge`), and
* Washington Thm 8.22/8.23 (the classical scaffold of `realUnitKummer`)
both rest on cyclotomic units, as do the unit-index theorem 8.14 and the Gauss-sum criterion 8.18
(the cyclotomic unit *group*, eigenspace components `Eᵢ`, and the index `[E:C]=h⁺`).
-/

namespace CyclotomicNT

open Finset

variable {A : Type*} [CommRing A] [IsDomain A] {ζ : A} {n j : ℕ}

/-- The **cyclotomic unit** `(ζ^j - 1)/(ζ - 1) = ∑_{i<j} ζ^i ∈ Aˣ`, for `ζ` a primitive `n`-th root
of unity (`2 ≤ n`) and `j` coprime to `n`.  Packages `IsPrimitiveRoot.geom_sum_isUnit`. -/
noncomputable def cyclotomicUnit (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (hj : j.Coprime n) : Aˣ :=
  (hζ.geom_sum_isUnit hn hj).unit

@[simp]
theorem coe_cyclotomicUnit (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (hj : j.Coprime n) :
    (cyclotomicUnit hζ hn hj : A) = ∑ i ∈ range j, ζ ^ i :=
  (hζ.geom_sum_isUnit hn hj).unit_spec

/-- **Defining relation:** the cyclotomic unit times `ζ - 1` is `ζ^j - 1`. -/
theorem cyclotomicUnit_mul_sub_one (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (hj : j.Coprime n) :
    (cyclotomicUnit hζ hn hj : A) * (ζ - 1) = ζ ^ j - 1 := by
  rw [coe_cyclotomicUnit, geom_sum_mul]

/-- `ζ^j - 1` and `ζ - 1` are associated, with the cyclotomic unit as the witness. -/
theorem associated_sub_one_pow_sub_one (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (hj : j.Coprime n) :
    Associated (ζ - 1) (ζ ^ j - 1) :=
  ⟨cyclotomicUnit hζ hn hj, by rw [mul_comm, cyclotomicUnit_mul_sub_one]⟩

end CyclotomicNT
