import GenMarkoff.Core.Statements
import GenMarkoff.TraceCurve.ExceptionalRouting
import GenMarkoff.ShiftedTrace.MiddleGame.ShiftedTraceEquation
import GenMarkoff.TraceCurve.WeightedShiftedCover.Counting

/-!
# Trace fibers of weighted shifted primitive pairs

The weighted shifted primitive count `weightedShiftedSplitPrimitiveTraceSolutions`
produces pairs whose common trace is primitive on the split torus.  To discard
the pairs whose common trace is a root of an exceptional polynomial, the
endgame needs a bound on each trace fiber: above a fixed trace there are at
most two weighted left lifts and at most two right lifts, hence at most four
pairs.  `GenMarkoff.General.Endgame.RegularPrimitiveCount` combines this with
the root bound for `orderedTraceSafePolynomial`.
-/

namespace GenMarkoff.ShiftedTrace.Endgame

open BGS.Markoff Polynomial

noncomputable section

/-- A fixed common trace has at most four lifts among the weighted shifted
primitive pairs: at most two on each torus factor. -/
theorem weightedShiftedSplitPrimitiveTraceSolutions_traceFiber_card_le_four
    (p : ℕ) [Fact p.Prime]
    (alpha beta gamma : ZMod p) (orbitExponent : ℕ)
    (halpha : alpha ≠ 0) (target : ZMod p) :
    ((weightedShiftedSplitPrimitiveTraceSolutions
        p alpha beta gamma orbitExponent).filter fun z ↦
          splitTorusTrace z.2 = target).card ≤ 4 := by
  classical
  -- Both coordinates of a pair in the fiber are roots of a monic quadratic:
  -- the left one of the twisted-trace polynomial for the shifted equation,
  -- the right one of the ordinary trace polynomial.  Embed the fiber into the
  -- product of the two root sets and count roots.
  let S :=
    (weightedShiftedSplitPrimitiveTraceSolutions
      p alpha beta gamma orbitExponent).filter fun z ↦
        splitTorusTrace z.2 = target
  let leftPolynomial :=
    twistedTracePolynomial (beta / alpha) ((target - gamma) / alpha)
  let rightPolynomial := twistedTracePolynomial (1 : ZMod p) target
  have hleftPolynomial : leftPolynomial ≠ 0 :=
    (twistedTracePolynomial_monic (beta / alpha)
      ((target - gamma) / alpha)).ne_zero
  have hrightPolynomial : rightPolynomial ≠ 0 :=
    (twistedTracePolynomial_monic (1 : ZMod p) target).ne_zero
  let rootEmbedding :
      ↥S ↪
        ↥leftPolynomial.roots.toFinset ×
          ↥rightPolynomial.roots.toFinset :=
    { toFun := fun z ↦
        (⟨((z.1.1.1 : (ZMod p)ˣ) : ZMod p), by
            rw [Multiset.mem_toFinset,
              Polynomial.mem_roots hleftPolynomial]
            apply (eval_twistedTracePolynomial_eq_zero_iff
              (beta / alpha) ((target - gamma) / alpha)
              (z.1.1.1 : (ZMod p)ˣ)).2
            apply
              (MiddleGame.shiftedWeightedSplitTorusTrace_eq_iff_twistedUnitTrace_eq
                alpha beta gamma target
                (z.1.1.1 : (ZMod p)ˣ) halpha).mp
            have hzMem :
                z.1 ∈ weightedShiftedSplitPrimitiveTraceSolutions
                  p alpha beta gamma orbitExponent :=
              (Finset.mem_filter.mp z.2).1
            have hzTrace :=
              (mem_traceExactOrderSolutions_iff
                (weightedShiftedSplitTorusTrace
                  (ZMod p) alpha beta gamma)
                (splitTorusTrace : (ZMod p)ˣ → ZMod p)
                orbitExponent (Nat.card (ZMod p)ˣ) z.1).mp hzMem
            exact hzTrace.1.trans (Finset.mem_filter.mp z.2).2⟩,
          ⟨((z.1.2 : (ZMod p)ˣ) : ZMod p), by
            rw [Multiset.mem_toFinset,
              Polynomial.mem_roots hrightPolynomial]
            apply (eval_twistedTracePolynomial_eq_zero_iff
              (1 : ZMod p) target z.1.2).2
            have hzTarget : splitTorusTrace z.1.2 = target :=
              (Finset.mem_filter.mp z.2).2
            simpa only [twistedUnitTrace, splitTorusTrace, one_mul] using
              hzTarget⟩)
      inj' := by
        intro x y hxy
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          apply Units.ext
          exact congrArg (fun q ↦ (q.1 : ZMod p)) hxy
        · apply Units.ext
          exact congrArg (fun q ↦ (q.2 : ZMod p)) hxy }
  have hcard :
      S.card ≤
        leftPolynomial.roots.toFinset.card *
          rightPolynomial.roots.toFinset.card := by
    simpa only [Fintype.card_coe, Fintype.card_prod] using
      Fintype.card_le_of_injective rootEmbedding rootEmbedding.injective
  have hleftRoots : leftPolynomial.roots.toFinset.card ≤ 2 := by
    calc
      leftPolynomial.roots.toFinset.card ≤ leftPolynomial.roots.card :=
        Multiset.toFinset_card_le _
      _ ≤ leftPolynomial.natDegree := Polynomial.card_roots' _
      _ = 2 := twistedTracePolynomial_natDegree
        (beta / alpha) ((target - gamma) / alpha)
  have hrightRoots : rightPolynomial.roots.toFinset.card ≤ 2 := by
    calc
      rightPolynomial.roots.toFinset.card ≤ rightPolynomial.roots.card :=
        Multiset.toFinset_card_le _
      _ ≤ rightPolynomial.natDegree := Polynomial.card_roots' _
      _ = 2 := twistedTracePolynomial_natDegree (1 : ZMod p) target
  -- Fold the goal into the local abbreviation `S` so that `hcard` applies.
  change S.card ≤ 4
  calc
    S.card ≤
        leftPolynomial.roots.toFinset.card *
          rightPolynomial.roots.toFinset.card := hcard
    _ ≤ 2 * 2 := Nat.mul_le_mul hleftRoots hrightRoots
    _ = 4 := by norm_num

end

end GenMarkoff.ShiftedTrace.Endgame
