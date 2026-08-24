import GenMarkoff.Symmetric.MiddleGame.ActualDiagonalization
import GenMarkoff.Symmetric.MiddleGame.ActualMoveWiring

/-!
# Transitivity on a regular split-maximal symmetric fiber

A full-order split eigenvalue alone does not guarantee transitivity on an
actual symmetric fiber: the affine conic may be degenerate.  This module
therefore packages full split order together with the existing ordered
candidate-regularity condition.  Under that condition, every point of the
fixed first-coordinate fiber has a nonzero torus parameter, and `oneStep1`
acts transitively on the fiber.

No claim about intersections between different maximal fibers, or about
global cage connectivity, is made here.
-/

namespace GenMarkoff.Symmetric.Cage

open BGS.Markoff

noncomputable section

/-- A split-maximal trace whose actual symmetric affine fiber is
candidate-regular.  The explicit eigenvalue is retained because maximal
half-step order by itself does not record the split branch. -/
def IsRegularSplitMaximalTrace
    (p : ℕ) [Fact p.Prime] (c t : ZMod p) : Prop :=
  OrderedTraceCandidateRegular c c c t ∧
    ∃ q : (ZMod p)ˣ,
      t = splitTorusTrace q ∧
        orderOf q = Nat.card (ZMod p)ˣ

/-- The first one-step generator is transitive on a fixed
regular split-maximal first-coordinate fiber. -/
theorem exists_iterate_oneStep1_eq_of_same_regularSplitMaximalFiber
    (p : ℕ) [Fact p.Prime]
    (c u t : ZMod p)
    (htrace : t = trace c u)
    (hmaximal : IsRegularSplitMaximalTrace p c t)
    (x y : Point (ZMod p))
    (hx : IsSolution (coefficients c) x) (hx1 : x.x1 = u)
    (hy : IsSolution (coefficients c) y) (hy1 : y.x1 = u) :
    ∃ n : ℕ, ((oneStep1 c)^[n]) x = y := by
  rcases hmaximal with ⟨hregular, q, heigen, horder⟩
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have hproduct : centeredFiberProduct c u t ≠ 0 :=
    MiddleGame.centeredFiberProduct_ne_zero_of_candidateRegular
      c u t htrace hregular
  obtain ⟨sx, hsx⟩ :=
    MiddleGame.exists_unit_fiberPoint_eq
      c u t q x hx1 hx htrace heigen hD hproduct
  obtain ⟨sy, hsy⟩ :=
    MiddleGame.exists_unit_fiberPoint_eq
      c u t q y hy1 hy htrace heigen hD hproduct
  have ht : t ≠ 2 := ne_two_of_discriminant_ne_zero hD
  have heigen' :
      t = (q : ZMod p) + ((q⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    simpa only [splitTorusTrace] using heigen
  have htop : Subgroup.zpowers q = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers q)).mp
    rw [Nat.card_zpowers, horder]
  let h : Subgroup.zpowers q :=
    ⟨sx⁻¹ * sy, by
      rw [htop]
      exact Subgroup.mem_top _⟩
  obtain ⟨n, hn⟩ :=
    MiddleGame.exists_iterate_fiberPoint_eq_mul_zpowers
      c u t q sx heigen' htrace ht h
  refine ⟨n, ?_⟩
  calc
    ((oneStep1 c)^[n]) x =
        ((oneStep1 c)^[n])
          (fiberPoint c u t (q : ZMod p) (sx : ZMod p)) := by
            rw [hsx]
    _ = fiberPoint c u t (q : ZMod p)
          ((sx * (h : (ZMod p)ˣ) : (ZMod p)ˣ) : ZMod p) := hn
    _ = fiberPoint c u t (q : ZMod p) (sy : ZMod p) := by
          congr 1
          simp [h]
    _ = y := hsy

end

end GenMarkoff.Symmetric.Cage
