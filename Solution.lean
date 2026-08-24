import GenMarkoff.General.Assembly.ExplicitStrongApproximation

/-!
# Generalized Markoff reduction solution

This file repeats the elementary statement from `Challenge.lean` and proves
it by supplying the explicit cutoff established by the production library.
-/

namespace Challenge

/-- The integral coefficients are nondegenerate when the cubic coefficient
and the three quadratic discriminant factors are nonzero. -/
def IntegrallyNondegenerate (a₁ a₂ a₃ : ℤ) : Prop :=
  3 + a₁ + a₂ + a₃ ≠ 0 ∧
    a₁ ^ 2 ≠ 4 ∧
    a₂ ^ 2 ≠ 4 ∧
    a₃ ^ 2 ≠ 4

/-- Integral solutions of the generalized Markoff equation with coefficients
`a₁`, `a₂`, and `a₃`. -/
abbrev IntegralSolutions (a₁ a₂ a₃ : ℤ) :=
  {⟨x₁, x₂, x₃⟩ : ℤ × ℤ × ℤ |
    x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2
      + a₁ * x₂ * x₃
      + a₂ * x₃ * x₁
      + a₃ * x₁ * x₂
      - (3 + a₁ + a₂ + a₃) * x₁ * x₂ * x₃ = 0}

/-- Solutions of the same equation modulo `p`. -/
abbrev ModPSolutions (a₁ a₂ a₃ : ℤ) (p : ℕ) :=
  {⟨x₁, x₂, x₃⟩ : ZMod p × ZMod p × ZMod p |
    x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2
      + (a₁ : ZMod p) * x₂ * x₃
      + (a₂ : ZMod p) * x₃ * x₁
      + (a₃ : ZMod p) * x₁ * x₂
      - (3 + (a₁ : ZMod p) + (a₂ : ZMod p) + (a₃ : ZMod p)) *
          x₁ * x₂ * x₃ = 0}

/-- Coordinatewise reduction of an integral solution modulo `p`. -/
abbrev integralSolutionToModP (a₁ a₂ a₃ : ℤ) (p : ℕ) :
    IntegralSolutions a₁ a₂ a₃ → ModPSolutions a₁ a₂ a₃ p :=
  fun ⟨⟨x₁, x₂, x₃⟩, hx⟩ ↦
    ⟨⟨x₁, x₂, x₃⟩, by
      simpa using congrArg (fun n : ℤ ↦ (n : ZMod p)) hx⟩

/-- The coefficient-dependent cutoff for one chosen cyclic ordering. -/
def explicitOrientedArithmeticCutoff (a₁ a₂ a₃ : ℤ) : ℕ :=
  max
    (max 5
      (max (3 + a₁ + a₂ + a₃).natAbs
        (max (a₁ ^ 2 - 4).natAbs
          (max (a₂ ^ 2 - 4).natAbs
            (a₃ ^ 2 - 4).natAbs)) + 1))
    (a₁.natAbs + 1)

/-- The explicit cutoff supplied by this solution. Its definition is complete
in this file: the first term is the uniform analytic bound, and the other
three terms are the arithmetic bounds for the three cyclic coefficient
orderings. This is the definition to update when the quantitative bounds are
improved. -/
def explicitCutoff (a₁ a₂ a₃ : ℤ) : ℕ :=
  max ((32 * 193 ^ 6) ^ 5 * 2 ^ 1828 + 1)
    (max (explicitOrientedArithmeticCutoff a₁ a₂ a₃)
      (max (explicitOrientedArithmeticCutoff a₂ a₃ a₁)
        (explicitOrientedArithmeticCutoff a₃ a₁ a₂)))

/-- For every nondegenerate integral coefficient triple, coordinatewise
reduction is surjective for every sufficiently large prime. -/
theorem generalizedMarkoff_reduction_surjective_of_large_prime
    {a₁ a₂ a₃ : ℤ} (ha : IntegrallyNondegenerate a₁ a₂ a₃) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p →
      Function.Surjective (integralSolutionToModP a₁ a₂ a₃ p) := by
  let a : GenMarkoff.Coefficients ℤ := ⟨a₁, a₂, a₃⟩
  refine ⟨explicitCutoff a₁ a₂ a₃, ?_⟩
  intro p hpPrime hpCutoff
  have ha' : GenMarkoff.IntegrallyNondegenerate a := by
    simpa [a, IntegrallyNondegenerate, GenMarkoff.IntegrallyNondegenerate,
      GenMarkoff.Coefficients.multiplier] using ha
  have hsurjective :=
    GenMarkoff.General.Assembly.IntegrallyNondegenerate.reduction_surjective_of_concreteExplicitCutoff
      ha' p hpPrime hpCutoff
  intro y
  obtain ⟨x, hx⟩ := hsurjective y
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact congrArg Subtype.val hx

end Challenge
