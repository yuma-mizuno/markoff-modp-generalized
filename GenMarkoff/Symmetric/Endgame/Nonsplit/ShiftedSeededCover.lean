import GenMarkoff.TraceCurve.WeightedShiftedCoverCounting
import BGS.Markoff.Endgame.Nonsplit.SeededCover

/-!
# Shifted seeded nonsplit covers

The nonsplit parameter of an actual symmetric fiber lies in a quadratic
norm torsor.  After scalar extension, its trace has two weights `s` and
`s ^ p`; the generalized surface contributes the additional base-field
constant `gamma`.

This file identifies the resulting equation with the arbitrary-weight
shifted cover already used in the split endgame.  It is the scalar-extension
input for the later Cayley descent to `ZMod p`.
-/

namespace GenMarkoff.Symmetric.Endgame.Nonsplit

open BGS.Markoff

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The seeded nonsplit trace equation with the affine shift contributed by
the generalized symmetric surface. -/
def ShiftedSeededNonsplitTraceCoverEquation
    (k : (ZMod p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : ZMod p) (d e : ℕ)
    (w : quadraticNormOneTorus p) (u : (ZMod p)ˣ) : Prop :=
  Algebra.trace (ZMod p) (quadraticFiniteField p)
      ((s.1 : quadraticFiniteField p) *
        (((w ^ d : quadraticNormOneTorus p) :
          (quadraticFiniteField p)ˣ) : quadraticFiniteField p)) +
      gamma =
    splitTorusTrace (u ^ e)

/-- After scalar extension, the shifted seeded trace is the arbitrary-weight
shifted trace with weights `s` and `s ^ p`. -/
theorem algebraMap_shiftedSeededQuadraticTrace_eq_weightedShiftedTrace
    (k : (ZMod p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : ZMod p) (d : ℕ) (w : quadraticNormOneTorus p) :
    algebraMap (ZMod p) (quadraticFiniteField p)
        (Algebra.trace (ZMod p) (quadraticFiniteField p)
          ((s.1 : quadraticFiniteField p) *
            (((w ^ d : quadraticNormOneTorus p) :
              (quadraticFiniteField p)ˣ) : quadraticFiniteField p)) +
          gamma) =
      weightedSplitTorusTrace
          (s.1 : quadraticFiniteField p)
          ((s.1 : quadraticFiniteField p) ^ p)
          ((w : (quadraticFiniteField p)ˣ) ^ d) +
        algebraMap (ZMod p) (quadraticFiniteField p) gamma := by
  rw [map_add]
  rw [algebraMap_seededQuadraticTrace_eq_weightedSplitTorusTrace]

/-- The shifted seeded equation is exactly the shifted trace-cover equation
over the quadratic splitting field.  In the polynomial convention the
base-field exponent `e` is first and the norm-one exponent `d` is second. -/
theorem shiftedSeededNonsplitTraceCoverEquation_iff_weightedShiftedTraceCover
    (k : (ZMod p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : ZMod p) (d e : ℕ)
    (w : quadraticNormOneTorus p) (u : (ZMod p)ˣ) :
    ShiftedSeededNonsplitTraceCoverEquation p k s gamma d e w u ↔
      MvPolynomial.eval
          ![((seededBaseUnitInQuadraticField p u) :
              quadraticFiniteField p),
            (((w : (quadraticFiniteField p)ˣ)) :
              quadraticFiniteField p)]
          (shiftedTraceCoverPolynomial
            (s.1 : quadraticFiniteField p)
            ((s.1 : quadraticFiniteField p) ^ p)
            (algebraMap (ZMod p) (quadraticFiniteField p) gamma)
            e d) = 0 := by
  rw [eval_weightedShiftedTraceCoverPolynomial_eq_zero_iff_traceEquation]
  have hleft :=
    algebraMap_shiftedSeededQuadraticTrace_eq_weightedShiftedTrace
      p k s gamma d w
  constructor
  · intro h
    have hmapped :=
      congrArg (algebraMap (ZMod p) (quadraticFiniteField p)) h
    rw [hleft] at hmapped
    simpa [weightedShiftedSplitTorusTrace, seededBaseUnitInQuadraticField,
      splitTorusTrace] using hmapped
  · intro h
    apply (algebraMap (ZMod p) (quadraticFiniteField p)).injective
    rw [hleft]
    simpa [weightedShiftedSplitTorusTrace, seededBaseUnitInQuadraticField,
      splitTorusTrace] using h

/-- The shifted cover attached to a nontrivial norm seed is absolutely
irreducible whenever the product/shift pair avoids the common-even
obstruction. -/
theorem shiftedSeededNonsplit_weightedCover_absolutelyIrreducible
    (hpTwo : p ≠ 2)
    (k : (ZMod p)ˣ) (hk : k ≠ 1)
    (s : ↥(quadraticNormFiber p k)) (gamma : ZMod p)
    (hD2 : shiftedTraceEvenObstruction (k : ZMod p) gamma ≠ 0)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hdChar : (d : quadraticFiniteField p) ≠ 0) :
    Irreducible
      (MvPolynomial.map
        (algebraMap (quadraticFiniteField p)
          (AlgebraicClosure (quadraticFiniteField p)))
        (shiftedTraceCoverPolynomial
          (s.1 : quadraticFiniteField p)
          ((s.1 : quadraticFiniteField p) ^ p)
          (algebraMap (ZMod p) (quadraticFiniteField p) gamma)
          e d)) := by
  obtain ⟨halpha, hbeta, hproductOne⟩ :=
    seededNonsplitWeights_nondegenerate p k hk s
  have htwo : (2 : quadraticFiniteField p) ≠ 0 := by
    intro hzero
    have hbase : (2 : ZMod p) = 0 := by
      apply (algebraMap (ZMod p) (quadraticFiniteField p)).injective
      simpa only [map_ofNat, map_zero] using hzero
    have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hbase
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
    exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)
  have hD2Mapped :
      shiftedTraceEvenObstruction
          ((s.1 : quadraticFiniteField p) *
            (s.1 : quadraticFiniteField p) ^ p)
          (algebraMap (ZMod p) (quadraticFiniteField p) gamma) ≠ 0 := by
    rw [seededNonsplitWeights_mul p k s]
    let f := algebraMap (ZMod p) (quadraticFiniteField p)
    have hmap :
        f (shiftedTraceEvenObstruction (k : ZMod p) gamma) =
          shiftedTraceEvenObstruction (f (k : ZMod p)) (f gamma) := by
      simp [f, shiftedTraceEvenObstruction, map_sub, map_add, map_mul,
        map_pow, map_ofNat]
    rw [← hmap]
    exact (map_ne_zero_iff f f.injective).mpr hD2
  exact
    weightedShiftedTraceCoverPolynomial_absolutelyIrreducible_of_positiveExponents
      (s.1 : quadraticFiniteField p)
      ((s.1 : quadraticFiniteField p) ^ p)
      (algebraMap (ZMod p) (quadraticFiniteField p) gamma)
      htwo halpha hbeta hproductOne hD2Mapped d e hd hdChar he

end

end GenMarkoff.Symmetric.Endgame.Nonsplit
