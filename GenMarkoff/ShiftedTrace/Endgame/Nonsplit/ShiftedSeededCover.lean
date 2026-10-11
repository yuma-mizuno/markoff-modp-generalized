module

public import GenMarkoff.TraceCurve.WeightedShiftedCover.Counting
public import BGS.Markoff.Endgame.Nonsplit.SeededCover

@[expose] public section

/-!
# Shifted seeded nonsplit covers

On a nonsplit rotation fiber the torus parameter lies in the norm-one torus of
the quadratic extension of `ZMod p`, and the moving trace is
`Tr(s * w) + gamma` for a seed `s` of norm `k` and a base-field shift `gamma`.
After scalar extension to the quadratic field this is the arbitrary-weight
shifted trace with weights `s` and `s ^ p`.

This file defines the shifted seeded nonsplit equation, identifies it with the
zero set of `shiftedTraceCoverPolynomial` over the quadratic field, and proves
that cover absolutely irreducible for `k ≠ 1` and nonzero even obstruction.
The descent of this cover to `ZMod p` through the Cayley parametrization,
`shiftedSeededNonsplitDescendedPolynomial`, is treated in the
`ShiftedDescended` files.
-/

namespace GenMarkoff.ShiftedTrace.Endgame.Nonsplit

open BGS.Markoff

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The seeded nonsplit trace equation `Tr(s * w ^ d) + gamma = u ^ e + (u ^ e)⁻¹`,
for `w` in the norm-one torus and `u` a base-field unit. -/
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

/-- For odd `p`, a seed of norm `k ≠ 1`, and `shiftedTraceEvenObstruction k gamma ≠ 0`,
the shifted cover with weights `s`, `s ^ p` and positive exponents is absolutely
irreducible when `d` is nonzero in the quadratic field. -/
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

end GenMarkoff.ShiftedTrace.Endgame.Nonsplit
