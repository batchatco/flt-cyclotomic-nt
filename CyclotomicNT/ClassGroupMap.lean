import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Functoriality of the class group via the `mk0` presentation

Mathlib has no `ClassGroup.map` for a ring extension. This file builds the tool to make one:
since `ClassGroup.mk0 : (Ideal R)⁰ →* ClassGroup R` is a *surjective* monoid hom, any monoid
hom `Φ : (Ideal R)⁰ →* G` (`G` a group) that is constant on `mk0`-fibres descends to a group
hom `ClassGroup R →* G`.

With `Φ = mk0_S ∘ (ideal extension)` and `Φ = mk0_R ∘ relNorm` this yields the extension and
relative-norm maps on class groups, whose composite is squaring (`relNorm_algebraMap`).
-/

namespace CyclotomicNT

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {G : Type*} [Group G]

/-- Descend a monoid hom `Φ : (Ideal R)⁰ →* G` that is constant on `ClassGroup.mk0`-fibres to a
group hom `ClassGroup R →* G`. -/
noncomputable def classGroupDescend (Φ : (Ideal R)⁰ →* G)
    (hwd : ∀ I J : (Ideal R)⁰, ClassGroup.mk0 I = ClassGroup.mk0 J → Φ I = Φ J) :
    ClassGroup R →* G where
  toFun c := Φ (Classical.choose (ClassGroup.mk0_surjective c))
  map_one' := by
    have h := Classical.choose_spec (ClassGroup.mk0_surjective (1 : ClassGroup R))
    rw [hwd _ 1 (by rw [h, map_one]), map_one]
  map_mul' c d := by
    have hc := Classical.choose_spec (ClassGroup.mk0_surjective c)
    have hd := Classical.choose_spec (ClassGroup.mk0_surjective d)
    have hcd := Classical.choose_spec (ClassGroup.mk0_surjective (c * d))
    rw [hwd _ (Classical.choose (ClassGroup.mk0_surjective c) *
          Classical.choose (ClassGroup.mk0_surjective d)) (by rw [hcd, map_mul, hc, hd]), map_mul]

@[simp]
theorem classGroupDescend_mk0 (Φ : (Ideal R)⁰ →* G)
    (hwd : ∀ I J : (Ideal R)⁰, ClassGroup.mk0 I = ClassGroup.mk0 J → Φ I = Φ J)
    (I : (Ideal R)⁰) : classGroupDescend Φ hwd (ClassGroup.mk0 I) = Φ I :=
  hwd _ I (Classical.choose_spec (ClassGroup.mk0_surjective (ClassGroup.mk0 I)))

section Extension

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra R S]

/-- Extension of a nonzero ideal `I ↦ I·S`, as a monoid hom on nonzero ideals
(when `R → S` is injective, so the extension stays nonzero). -/
def idealExtend (hinj : Function.Injective (algebraMap R S)) : (Ideal R)⁰ →* (Ideal S)⁰ where
  toFun I := ⟨(I : Ideal R).map (algebraMap R S), mem_nonZeroDivisors_iff_ne_zero.mpr <|
    fun h => mem_nonZeroDivisors_iff_ne_zero.mp I.2
      ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)⟩
  map_one' := Subtype.ext <| by simp [Ideal.one_eq_top, Ideal.map_top]
  map_mul' I J := Subtype.ext <| by simp [Ideal.map_mul]

@[simp] theorem idealExtend_coe (hinj : Function.Injective (algebraMap R S)) (I : (Ideal R)⁰) :
    (idealExtend hinj I : Ideal S) = (I : Ideal R).map (algebraMap R S) := rfl

/-- The ideal-extension map descended to class groups: `Cl(R) →* Cl(S)`. -/
noncomputable def classGroupExtend (hinj : Function.Injective (algebraMap R S)) :
    ClassGroup R →* ClassGroup S :=
  classGroupDescend (ClassGroup.mk0.comp (idealExtend hinj)) <| by
    intro I J h
    rw [ClassGroup.mk0_eq_mk0_iff] at h
    obtain ⟨x, y, hx, hy, hxy⟩ := h
    simp only [MonoidHom.comp_apply, ClassGroup.mk0_eq_mk0_iff, idealExtend_coe]
    have hsp : ∀ z : R, Ideal.span {algebraMap R S z} = (Ideal.span {z}).map (algebraMap R S) :=
      fun z => by rw [Ideal.map_span, Set.image_singleton]
    refine ⟨algebraMap R S x, algebraMap R S y,
      fun h0 => hx ((map_eq_zero_iff _ hinj).mp h0), fun h0 => hy ((map_eq_zero_iff _ hinj).mp h0),
      ?_⟩
    rw [hsp, hsp, ← Ideal.map_mul, ← Ideal.map_mul, hxy]

@[simp] theorem classGroupExtend_mk0 (hinj : Function.Injective (algebraMap R S))
    (I : (Ideal R)⁰) :
    classGroupExtend hinj (ClassGroup.mk0 I) = ClassGroup.mk0 (idealExtend hinj I) := by
  rw [classGroupExtend, classGroupDescend_mk0, MonoidHom.comp_apply]

end Extension

section Norm

variable {S : Type*} [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Relative norm of a nonzero ideal, as a monoid hom on nonzero ideals. -/
noncomputable def idealNorm : (Ideal S)⁰ →* (Ideal R)⁰ where
  toFun I := ⟨Ideal.relNorm R (I : Ideal S), mem_nonZeroDivisors_iff_ne_zero.mpr <|
    fun h => mem_nonZeroDivisors_iff_ne_zero.mp I.2 (Ideal.relNorm_eq_bot_iff.mp h)⟩
  map_one' := Subtype.ext <| by simp
  map_mul' I J := Subtype.ext <| by simp

@[simp] theorem idealNorm_coe (I : (Ideal S)⁰) :
    (idealNorm (R := R) I : Ideal R) = Ideal.relNorm R (I : Ideal S) := rfl

/-- The relative-norm map descended to class groups: `Cl(S) →* Cl(R)`. -/
noncomputable def classGroupNorm : ClassGroup S →* ClassGroup R :=
  classGroupDescend (ClassGroup.mk0.comp (idealNorm (R := R))) <| by
    intro I J h
    rw [ClassGroup.mk0_eq_mk0_iff] at h
    obtain ⟨x, y, hx, hy, hxy⟩ := h
    simp only [MonoidHom.comp_apply, ClassGroup.mk0_eq_mk0_iff, idealNorm_coe]
    refine ⟨Algebra.intNorm R S x, Algebra.intNorm R S y,
      fun h0 => hx (by rwa [Algebra.intNorm_eq_zero] at h0),
      fun h0 => hy (by rwa [Algebra.intNorm_eq_zero] at h0), ?_⟩
    have hsp : ∀ z : S, Ideal.span {Algebra.intNorm R S z} = Ideal.relNorm R (Ideal.span {z}) :=
      fun z => (Ideal.spanNorm_singleton R).symm
    rw [hsp, hsp, ← map_mul, ← map_mul, hxy]

@[simp] theorem classGroupNorm_mk0 (I : (Ideal S)⁰) :
    classGroupNorm (R := R) (ClassGroup.mk0 I) = ClassGroup.mk0 (idealNorm (R := R) I) := by
  rw [classGroupNorm, classGroupDescend_mk0, MonoidHom.comp_apply]

/-- **The norm of an extension is the `finrank`-power**, on class groups:
`N (ι a) = a ^ [Frac S : Frac R]`. For a quadratic extension this is squaring. -/
theorem classGroupNorm_classGroupExtend (hinj : Function.Injective (algebraMap R S))
    (a : ClassGroup R) :
    classGroupNorm (R := R) (classGroupExtend hinj a) =
      a ^ Module.finrank (FractionRing R) (FractionRing S) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective a
  rw [classGroupExtend_mk0, classGroupNorm_mk0, ← map_pow]
  congr 1
  apply Subtype.ext
  rw [idealNorm_coe, idealExtend_coe, SubmonoidClass.coe_pow, Ideal.relNorm_algebraMap]

end Norm

section GalAut

/-- A ring automorphism `e : R ≃+* R` acting on nonzero ideals by `I ↦ e(I)`, as a monoid hom. -/
def idealMapEquiv (e : R ≃+* R) : (Ideal R)⁰ →* (Ideal R)⁰ where
  toFun I := ⟨(I : Ideal R).map e.toRingHom, mem_nonZeroDivisors_iff_ne_zero.mpr <|
    fun h => mem_nonZeroDivisors_iff_ne_zero.mp I.2
      ((Ideal.map_eq_bot_iff_of_injective e.injective).mp h)⟩
  map_one' := Subtype.ext <| by simp [Ideal.one_eq_top, Ideal.map_top]
  map_mul' I J := Subtype.ext <| by simp [Ideal.map_mul]

@[simp] theorem idealMapEquiv_coe (e : R ≃+* R) (I : (Ideal R)⁰) :
    (idealMapEquiv e I : Ideal R) = (I : Ideal R).map e.toRingHom := rfl

/-- The action of a ring automorphism `e : R ≃+* R` on the class group, `[I] ↦ [e(I)]`.

This is the Galois action on `ClassGroup R` used in the literature (`σ · [I] = [σ(I)]`) —
absent from Mathlib — here for a single automorphism. Applied with `e` the (ring-of-integers)
complex conjugation `j`, it expresses the `j`-fixedness of an ideal class needed for the
plus-part principality step of Case II. -/
noncomputable def classGroupMapEquiv (e : R ≃+* R) : ClassGroup R →* ClassGroup R :=
  classGroupDescend (ClassGroup.mk0.comp (idealMapEquiv e)) <| by
    intro I J h
    rw [ClassGroup.mk0_eq_mk0_iff] at h
    obtain ⟨x, y, hx, hy, hxy⟩ := h
    simp only [MonoidHom.comp_apply, ClassGroup.mk0_eq_mk0_iff, idealMapEquiv_coe]
    have hsp : ∀ z : R, Ideal.span {e z} = (Ideal.span {z}).map e.toRingHom :=
      fun z => by rw [Ideal.map_span, Set.image_singleton]; rfl
    refine ⟨e x, e y, fun h0 => hx (e.injective (by simpa using h0)),
      fun h0 => hy (e.injective (by simpa using h0)), ?_⟩
    rw [hsp, hsp, ← Ideal.map_mul, ← Ideal.map_mul, hxy]

@[simp] theorem classGroupMapEquiv_mk0 (e : R ≃+* R) (I : (Ideal R)⁰) :
    classGroupMapEquiv e (ClassGroup.mk0 I) = ClassGroup.mk0 (idealMapEquiv e I) := by
  rw [classGroupMapEquiv, classGroupDescend_mk0, MonoidHom.comp_apply]

end GalAut

end CyclotomicNT
