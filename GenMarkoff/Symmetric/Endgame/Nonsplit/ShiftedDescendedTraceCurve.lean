import GenMarkoff.Symmetric.Endgame.Nonsplit.ShiftedSeededCover
import BGS.Markoff.Endgame.Nonsplit.DescendedTraceCurve

/-!
# The shifted descended seeded nonsplit trace curve

The Cayley coordinate

`w = (z - theta ^ p) / (z - theta)`

turns the shifted seeded nonsplit equation into a polynomial over `ZMod p`.
If `N` is the ordinary seeded numerator and `Q` is the Cayley norm
polynomial, then the shift changes the numerator to `N + gamma * Q ^ d`.
Thus the descended polynomial is

`(N + gamma * Q ^ d) * u ^ e - Q ^ d * (u ^ (2 * e) + 1)`.
-/

namespace GenMarkoff.Symmetric.Endgame.Nonsplit

open Polynomial
open BGS.Markoff

noncomputable section

variable (p : ℕ) [Fact p.Prime]

private abbrev F := ZMod p
private abbrev E := quadraticFiniteField p

/-- The numerator of the shifted seeded trace after clearing the Cayley
denominator.  The extra term is exactly `gamma * Q ^ d`. -/
def shiftedSeededCayleyTraceNumeratorPolynomial
    (s : (E p)ˣ) (gamma : F p) (d : ℕ) : Polynomial (F p) :=
  seededCayleyTraceNumeratorPolynomial p s d +
    Polynomial.C gamma * quadraticCayleyNormPolynomial p ^ d

/-- Scalar extension displays the two Frobenius-conjugate seed terms and the
shift term `gamma * Q ^ d`. -/
theorem shiftedSeededCayleyTraceNumeratorPolynomial_map
    (s : (E p)ˣ) (gamma : F p) (d : ℕ) :
    (shiftedSeededCayleyTraceNumeratorPolynomial p s gamma d).map
        (algebraMap (F p) (E p)) =
      Polynomial.C (s : E p) *
          (Polynomial.X - Polynomial.C (quadraticNonbaseElement p ^ p)) ^ (2 * d) +
        Polynomial.C ((s : E p) ^ p) *
          (Polynomial.X - Polynomial.C (quadraticNonbaseElement p)) ^ (2 * d) +
        Polynomial.C (algebraMap (F p) (E p) gamma) *
          ((Polynomial.X - Polynomial.C (quadraticNonbaseElement p ^ p)) *
            (Polynomial.X - Polynomial.C (quadraticNonbaseElement p))) ^ d := by
  rw [shiftedSeededCayleyTraceNumeratorPolynomial, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    seededCayleyTraceNumeratorPolynomial_map,
    quadraticCayleyNormPolynomial_map]

theorem algebraMap_eval_shiftedSeededCayleyTraceNumeratorPolynomial
    (s : (E p)ˣ) (gamma : F p) (d : ℕ) (z : F p) :
    algebraMap (F p) (E p)
        ((shiftedSeededCayleyTraceNumeratorPolynomial p s gamma d).eval z) =
      (s : E p) *
          (algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) ^ (2 * d) +
        (s : E p) ^ p *
          (algebraMap (F p) (E p) z - quadraticNonbaseElement p) ^ (2 * d) +
        algebraMap (F p) (E p) gamma *
          ((algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) *
            (algebraMap (F p) (E p) z - quadraticNonbaseElement p)) ^ d := by
  calc
    algebraMap (F p) (E p)
        ((shiftedSeededCayleyTraceNumeratorPolynomial p s gamma d).eval z) =
        ((shiftedSeededCayleyTraceNumeratorPolynomial p s gamma d).map
          (algebraMap (F p) (E p))).eval
            (algebraMap (F p) (E p) z) := by
      rw [← Polynomial.eval₂_eq_eval_map]
      exact
        (Polynomial.eval₂_at_apply
          (algebraMap (F p) (E p)) z).symm
    _ = _ := by
      rw [shiftedSeededCayleyTraceNumeratorPolynomial_map]
      simp

theorem shiftedSeededCayleyTraceNumeratorPolynomial_natDegree_le
    (s : (E p)ˣ) (gamma : F p) (d : ℕ) :
    (shiftedSeededCayleyTraceNumeratorPolynomial p s gamma d).natDegree ≤
      2 * d := by
  rw [shiftedSeededCayleyTraceNumeratorPolynomial]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le
    (seededCayleyTraceNumeratorPolynomial_natDegree_le p s d) ?_)
  calc
    (Polynomial.C gamma * quadraticCayleyNormPolynomial p ^ d).natDegree ≤
        (Polynomial.C gamma).natDegree +
          (quadraticCayleyNormPolynomial p ^ d).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + d * (quadraticCayleyNormPolynomial p).natDegree := by
      gcongr
      · simp
      · exact Polynomial.natDegree_pow_le
    _ ≤ 0 + d * 2 := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_left d
          (quadraticCayleyNormPolynomial_natDegree_le p)) 0
    _ = 2 * d := by omega

/-- The explicit shifted descended polynomial over `ZMod p`. Coordinate `0`
is the Cayley affine coordinate and coordinate `1` is the split base-field
unit. -/
def shiftedSeededNonsplitDescendedPolynomial
    (s : (E p)ˣ) (gamma : F p) (d e : ℕ) :
    MvPolynomial (Fin 2) (F p) :=
  univariateInFirstCoordinate
      (shiftedSeededCayleyTraceNumeratorPolynomial p s gamma d) *
      MvPolynomial.X 1 ^ e -
    univariateInFirstCoordinate (quadraticCayleyNormPolynomial p) ^ d *
      (MvPolynomial.X 1 ^ (2 * e) + 1)

theorem eval_shiftedSeededNonsplitDescendedPolynomial
    (s : (E p)ˣ) (gamma : F p) (d e : ℕ) (z u : F p) :
    MvPolynomial.eval ![z, u]
        (shiftedSeededNonsplitDescendedPolynomial p s gamma d e) =
      (shiftedSeededCayleyTraceNumeratorPolynomial p s gamma d).eval z *
          u ^ e -
        (quadraticCayleyNormPolynomial p).eval z ^ d *
          (u ^ (2 * e) + 1) := by
  simp [shiftedSeededNonsplitDescendedPolynomial]

private theorem degreeOf_first_X_one_pow_le
    {K : Type*} [CommSemiring K] [Nontrivial K] (n : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (MvPolynomial.X 1 ^ n : MvPolynomial (Fin 2) K) ≤ 0 := by
  calc
    _ ≤ n * MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1) :=
      MvPolynomial.degreeOf_pow_le _ _ _
    _ = 0 := by rw [MvPolynomial.degreeOf_X]; norm_num

private theorem degreeOf_second_X_one_pow_le
    {K : Type*} [CommSemiring K] [Nontrivial K] (n : ℕ) :
    MvPolynomial.degreeOf (1 : Fin 2)
      (MvPolynomial.X 1 ^ n : MvPolynomial (Fin 2) K) ≤ n := by
  calc
    _ ≤ n * MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 1) :=
      MvPolynomial.degreeOf_pow_le _ _ _
    _ = n := by rw [MvPolynomial.degreeOf_X]; norm_num

theorem shiftedSeededNonsplitDescendedPolynomial_degreeOf_first_le
    (s : (E p)ˣ) (gamma : F p) (d e : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 2)
        (shiftedSeededNonsplitDescendedPolynomial p s gamma d e) ≤ 2 * d := by
  rw [shiftedSeededNonsplitDescendedPolynomial]
  refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    have hnum :=
      (univariateInFirstCoordinate_degreeOf_first_le
        (shiftedSeededCayleyTraceNumeratorPolynomial p s gamma d)).trans
          (shiftedSeededCayleyTraceNumeratorPolynomial_natDegree_le
            p s gamma d)
    have hu := degreeOf_first_X_one_pow_le (K := F p) e
    omega
  · refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    have hnormBase :=
      (univariateInFirstCoordinate_degreeOf_first_le
        (quadraticCayleyNormPolynomial p)).trans
          (quadraticCayleyNormPolynomial_natDegree_le p)
    have hnormPow :=
      (MvPolynomial.degreeOf_pow_le (0 : Fin 2)
        (univariateInFirstCoordinate (quadraticCayleyNormPolynomial p)) d).trans
          (Nat.mul_le_mul_left d hnormBase)
    have hsum :=
      (MvPolynomial.degreeOf_add_le (0 : Fin 2)
        (MvPolynomial.X 1 ^ (2 * e) : MvPolynomial (Fin 2) (F p)) 1).trans
          (max_le (degreeOf_first_X_one_pow_le (K := F p) (2 * e)) (by simp))
    omega

theorem shiftedSeededNonsplitDescendedPolynomial_degreeOf_second_le
    (s : (E p)ˣ) (gamma : F p) (d e : ℕ) :
    MvPolynomial.degreeOf (1 : Fin 2)
        (shiftedSeededNonsplitDescendedPolynomial p s gamma d e) ≤ 2 * e := by
  rw [shiftedSeededNonsplitDescendedPolynomial]
  refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    have hnum :=
      univariateInFirstCoordinate_degreeOf_second_le
        (shiftedSeededCayleyTraceNumeratorPolynomial p s gamma d)
    have hu := degreeOf_second_X_one_pow_le (K := F p) e
    omega
  · refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    have hnormBase :=
      univariateInFirstCoordinate_degreeOf_second_le
        (quadraticCayleyNormPolynomial p)
    have hnormPow :=
      (MvPolynomial.degreeOf_pow_le (1 : Fin 2)
        (univariateInFirstCoordinate (quadraticCayleyNormPolynomial p)) d).trans
          (Nat.mul_le_mul_left d hnormBase)
    have hsum :=
      (MvPolynomial.degreeOf_add_le (1 : Fin 2)
        (MvPolynomial.X 1 ^ (2 * e) : MvPolynomial (Fin 2) (F p)) 1).trans
          (max_le
            (degreeOf_second_X_one_pow_le (K := F p) (2 * e)) (by simp))
    omega

theorem shiftedSeededNonsplitDescendedPolynomial_hasBidegreeAtMost
    (s : (E p)ˣ) (gamma : F p) (d e : ℕ) :
    BGS.External.HasBidegreeAtMost
      (shiftedSeededNonsplitDescendedPolynomial p s gamma d e)
      (2 * d) (2 * e) := by
  intro monomial hmonomial
  exact ⟨
    (MvPolynomial.degreeOf_le_iff.mp
      (shiftedSeededNonsplitDescendedPolynomial_degreeOf_first_le
        p s gamma d e)) monomial hmonomial,
    (MvPolynomial.degreeOf_le_iff.mp
      (shiftedSeededNonsplitDescendedPolynomial_degreeOf_second_le
        p s gamma d e)) monomial hmonomial⟩

private theorem clearedShiftedSeededFractionEquation_iff
    {K : Type*} [Field K]
    (seed conjugateSeed gamma X Y V : K)
    (hX : X ≠ 0) (hY : Y ≠ 0) (hV : V ≠ 0) :
    (seed * X ^ 2 + conjugateSeed * Y ^ 2 + gamma * X * Y) * V -
          X * Y * (V ^ 2 + 1) = 0 ↔
      seed * (X / Y) + conjugateSeed * (X / Y)⁻¹ + gamma =
        V + V⁻¹ := by
  field_simp [hX, hY, hV]
  constructor <;> intro h <;> linear_combination h

private theorem clearedShiftedSeededCayleyEquation_iff
    {K : Type*} [Field K]
    (seed conjugateSeed gamma A B u : K) (d e : ℕ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hu : u ≠ 0) :
    (seed * A ^ (2 * d) + conjugateSeed * B ^ (2 * d) +
          gamma * (A * B) ^ d) * u ^ e -
          (A * B) ^ d * (u ^ (2 * e) + 1) = 0 ↔
      seed * (A / B) ^ d +
          conjugateSeed * ((A / B) ^ d)⁻¹ + gamma =
        u ^ e + (u ^ e)⁻¹ := by
  rw [Nat.mul_comm 2 d, pow_mul, pow_mul, Nat.mul_comm 2 e,
    pow_mul, div_pow, mul_pow]
  simpa only [mul_assoc] using
    clearedShiftedSeededFractionEquation_iff
      seed conjugateSeed gamma (A ^ d) (B ^ d) (u ^ e)
      (pow_ne_zero d hA) (pow_ne_zero d hB) (pow_ne_zero e hu)

/-- Vanishing of the shifted descended polynomial is exactly the shifted
seeded nonsplit trace equation at the Cayley point. -/
theorem eval_shiftedSeededNonsplitDescendedPolynomial_eq_zero_iff
    (k : (F p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : F p) (d e : ℕ) (z : F p) (u : (F p)ˣ) :
    MvPolynomial.eval ![z, (u : F p)]
        (shiftedSeededNonsplitDescendedPolynomial p s.1 gamma d e) = 0 ↔
      ShiftedSeededNonsplitTraceCoverEquation
        p k s gamma d e (quadraticCayleyPoint p z) u := by
  rw [eval_shiftedSeededNonsplitDescendedPolynomial]
  rw [shiftedSeededNonsplitTraceCoverEquation_iff_weightedShiftedTraceCover]
  have hmapZero :
      (shiftedSeededCayleyTraceNumeratorPolynomial p s.1 gamma d).eval z *
            (u : F p) ^ e -
          (quadraticCayleyNormPolynomial p).eval z ^ d *
            ((u : F p) ^ (2 * e) + 1) = 0 ↔
        algebraMap (F p) (E p)
          ((shiftedSeededCayleyTraceNumeratorPolynomial p s.1 gamma d).eval z *
              (u : F p) ^ e -
            (quadraticCayleyNormPolynomial p).eval z ^ d *
              ((u : F p) ^ (2 * e) + 1)) = 0 := by
    constructor
    · intro h
      rw [h, map_zero]
    · intro h
      exact
        (algebraMap (F p) (E p)).injective
          (by simpa using h)
  rw [hmapZero]
  simp only [map_sub, map_mul, map_pow, map_add, map_one]
  rw [algebraMap_eval_shiftedSeededCayleyTraceNumeratorPolynomial,
    algebraMap_eval_quadraticCayleyNormPolynomial]
  change
    (((s.1 : E p) *
          (algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) ^
            (2 * d) +
        (s.1 : E p) ^ p *
          (algebraMap (F p) (E p) z - quadraticNonbaseElement p) ^
            (2 * d) +
        algebraMap (F p) (E p) gamma *
          ((algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) *
            (algebraMap (F p) (E p) z -
              quadraticNonbaseElement p)) ^ d) *
        algebraMap (F p) (E p) (u : F p) ^ e -
      ((algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) *
        (algebraMap (F p) (E p) z - quadraticNonbaseElement p)) ^ d *
        (algebraMap (F p) (E p) (u : F p) ^ (2 * e) + 1) = 0) ↔ _
  have hA :
      algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h =>
      quadraticNonbaseElement_frobenius_not_mem_range p ⟨z, h⟩
  have hB :
      algebraMap (F p) (E p) z - quadraticNonbaseElement p ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => quadraticNonbaseElement_not_mem_range p ⟨z, h⟩
  have hu : algebraMap (F p) (E p) (u : F p) ≠ 0 :=
    (map_ne_zero (algebraMap (F p) (E p))).mpr (Units.ne_zero u)
  rw [clearedShiftedSeededCayleyEquation_iff _ _ _ _ _ _ d e hA hB hu]
  simpa [weightedShiftedSplitTorusTrace, weightedSplitTorusTrace,
    splitTorusTrace, seededBaseUnitInQuadraticField, quadraticCayleyPoint,
    quadraticCayleyUnit, quadraticCayleyValue] using
    (eval_weightedShiftedTraceCoverPolynomial_eq_zero_iff_traceEquation
      (E p)
      (s.1 : E p)
      ((s.1 : E p) ^ p)
      (algebraMap (F p) (E p) gamma)
      e d
      (seededBaseUnitInQuadraticField p u)
      ((quadraticCayleyPoint p z : quadraticNormOneTorus p) :
        (E p)ˣ)).symm

end

end GenMarkoff.Symmetric.Endgame.Nonsplit
