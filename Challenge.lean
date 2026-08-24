import Mathlib

/-!
# Explicit general-coefficient reduction surjectivity

This is the small, Mathlib-only statement surface for the submitted result.
It gives the ordered coefficient data, the fixed generalized Markoff surface,
the complete coefficient-dependent part of the cutoff, and the advertised
surjectivity theorem without importing the proof development.
-/

open CategoryTheory

namespace GenMarkoff

universe u

/-- An ordered triple of coefficients for a generalized Markoff surface. -/
@[ext]
structure Coefficients (R : Type u) where
  a1 : R
  a2 : R
  a3 : R
deriving DecidableEq, Repr, Fintype

/-- The coefficient `3 + a₁ + a₂ + a₃` of the cubic term in the generalized
Markoff equation. -/
def Coefficients.multiplier {R : Type u} [OfNat R 3] [Add R]
    (a : Coefficients R) : R :=
  3 + a.a1 + a.a2 + a.a3

/-- An integral coefficient triple is nondegenerate when its cubic multiplier
is nonzero and none of its three quadratic discriminant factors vanishes. -/
def IntegrallyNondegenerate (a : Coefficients ℤ) : Prop :=
  a.multiplier ≠ 0 ∧
    a.a1 ^ 2 ≠ 4 ∧
    a.a2 ^ 2 ≠ 4 ∧
    a.a3 ^ 2 ≠ 4

namespace General.Assembly

/-- The functor of solutions to the generalized Markoff equation with the
fixed ordered integral coefficient triple `a`. A ring homomorphism acts by
applying it to each coordinate. -/
def fixedIntegralCoefficientSurfaceFunctor
    (a : Coefficients ℤ) : CommRingCat ⥤ Type where
  obj R := {⟨x₁, x₂, x₃⟩ : R × R × R |
    x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2
      + (a.a1 : R) * x₂ * x₃
      + (a.a2 : R) * x₃ * x₁
      + (a.a3 : R) * x₁ * x₂
      - (3 + (a.a1 : R) + (a.a2 : R) + (a.a3 : R)) *
          x₁ * x₂ * x₃ = 0}
  map f := ↾fun ⟨⟨x₁, x₂, x₃⟩, hx⟩ ↦
    ⟨⟨f.hom x₁, f.hom x₂, f.hom x₃⟩, by
      simpa only [Set.mem_setOf_eq, map_add, map_sub, map_mul, map_pow,
        map_zero, map_ofNat, map_intCast] using congrArg f.hom hx⟩

/-- The bad-reduction and first-coordinate-survival cutoff for one chosen
cyclic orientation of an ordered integral coefficient triple. -/
def orientedArithmeticCutoff (b : Coefficients ℤ) : ℕ :=
  max
    (max 5
      (max b.multiplier.natAbs
        (max (b.a1 ^ 2 - 4).natAbs
          (max (b.a2 ^ 2 - 4).natAbs
            (b.a3 ^ 2 - 4).natAbs)) + 1))
    (b.a1.natAbs + 1)

/-- For every fixed nondegenerate integral coefficient triple and every prime
above the displayed explicit cutoff, coordinatewise reduction from integral
solutions is surjective onto the full generalized Markoff surface modulo
`p`. The three arithmetic terms are the three simultaneous cyclic
orientations of the ordered coefficient triple. -/
theorem IntegrallyNondegenerate.reduction_surjective_of_concreteExplicitCutoff
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (p : ℕ) (hp : p.Prime)
    (hpCutoff :
      max ((32 * 193 ^ 6) ^ 5 * 2 ^ 1828 + 1)
        (max (orientedArithmeticCutoff a)
          (max (orientedArithmeticCutoff ⟨a.a2, a.a3, a.a1⟩)
            (orientedArithmeticCutoff ⟨a.a3, a.a1, a.a2⟩))) ≤ p) :
    Function.Surjective
      ((fixedIntegralCoefficientSurfaceFunctor a).map
        (CommRingCat.ofHom (Int.castRingHom (ZMod p)))) := by
  sorry

end General.Assembly

end GenMarkoff
