import Mathlib

/-!
# Generalized Markoff reduction challenge

For fixed integral coefficients, the challenge asks for a bound beyond which
every solution of the generalized Markoff equation modulo a prime lifts to an
integral solution. The statement uses only explicit triples and coordinatewise
reduction; the value of the bound is deliberately left to the solution.
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

/-- For every nondegenerate integral coefficient triple, coordinatewise
reduction is surjective for every sufficiently large prime. -/
theorem generalizedMarkoff_reduction_surjective_of_large_prime
    {a₁ a₂ a₃ : ℤ} (ha : IntegrallyNondegenerate a₁ a₂ a₃) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p →
      Function.Surjective (integralSolutionToModP a₁ a₂ a₃ p) := by
  sorry

end Challenge
