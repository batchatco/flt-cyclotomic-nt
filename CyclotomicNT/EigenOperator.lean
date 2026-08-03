import CyclotomicNT.GaloisRealUnits
import CyclotomicNT.CyclotomicUnitEigenspace

/-!
# Thm 8.14, piece 3b — the operator `T = σ_g` on `V = E/E^p` and the unit-class map

Having shown `σ_g` preserves `E = realUnits K` (`galUnit_mem_realUnits`), we descend it to a
`ZMod p`-linear endomorphism `galV = T` of `V = ModN (Additive (realUnits K)) p`, and package the
class map `vOf : E → V` (`u ↦ mkQ u`).  These satisfy `T(vOf u) = vOf (σ_g u)`, `vOf (u·v) = vOf u +
vOf v`, `vOf u⁻¹ = −vOf u` — the bridge between the multiplicative unit identities (3a) and the
additive `ZMod p`-vector space `V` where the eigenvector argument (δ) lives.
-/

namespace CyclotomicNT

open scoped NumberField
open NumberField NumberField.IsCMField

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}

/-- `σ_g` restricted to the real units, as a monoid hom of the subgroup `E`. -/
noncomputable def galUnitReal (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) :
    realUnits K →* realUnits K where
  toFun u := ⟨galUnit hζ g u, galUnit_mem_realUnits hζ g u u.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp only [Subgroup.coe_mul, map_mul]

/-- The additive version of `galUnitReal`, on `Additive E`. -/
noncomputable def aGalUnit (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) :
    Additive (realUnits K) →+ Additive (realUnits K) :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (galUnitReal hζ g (Additive.toMul a)))
    (fun a b => by simp [map_mul])

/-- **The Galois operator `T = σ_g` on `V = E/E^p`**, a `ZMod p`-linear endomorphism (the descent of
`aGalUnit` through the `ModN` quotient; well-defined since `σ_g` preserves `p`-th powers). -/
noncomputable def galV (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) :
    ModN (Additive (realUnits K)) p →ₗ[ZMod p] ModN (Additive (realUnits K)) p :=
  (ModN.liftEquiv' (G := Additive (realUnits K)) (n := p)
      (H := ModN (Additive (realUnits K)) p)).symm ⟨(ModN.mkQ p).comp (aGalUnit hζ g), fun a => by
    rw [AddMonoidHom.comp_apply, ← map_nsmul, ModN.mkQ]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩⟩

@[simp] theorem galV_mkQ (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) (a : Additive (realUnits K)) :
    galV hζ g (ModN.mkQ p a) = ModN.mkQ p (aGalUnit hζ g a) := rfl

/-- The class of a real unit in `V = E/E^p`. -/
noncomputable def vOf (u : realUnits K) : ModN (Additive (realUnits K)) p :=
  ModN.mkQ p (Additive.ofMul u)

theorem galV_vOf (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) (u : realUnits K) :
    galV hζ g (vOf u) = vOf (galUnitReal hζ g u) := by
  rw [vOf, galV_mkQ]; rfl

omit hpri [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
@[simp] theorem vOf_mul (u v : realUnits K) :
    (vOf (u * v) : ModN (Additive (realUnits K)) p) = vOf u + vOf v := by
  rw [vOf, vOf, vOf, ← map_add]; rfl

omit hpri [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
@[simp] theorem vOf_inv (u : realUnits K) :
    (vOf u⁻¹ : ModN (Additive (realUnits K)) p) = - vOf u := by
  rw [vOf, vOf, ← map_neg]; rfl

end CyclotomicNT
