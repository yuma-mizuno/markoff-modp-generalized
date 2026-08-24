import GenMarkoff.Symmetric.Endgame.Nonsplit.ActualSeed
import GenMarkoff.Symmetric.Endgame.Nonsplit.ShiftedPrimitiveCount

/-!
# Primitive candidate-regular traces on an actual nonsplit orbit

This module connects the shifted nonsplit primitive count to the actual
one-step dynamics of a symmetric generalized Markoff surface.  The seed
constructed from the chosen base-field point is retained, so the counted
norm-one parameter lies in the complementary power image of the actual
nonsplit eigenvalue and is therefore reached by a forward iterate.
-/

namespace GenMarkoff.Symmetric.Endgame.Nonsplit

open BGS.Markoff

noncomputable section

/-- Under the explicit primitive-count margin, a candidate-regular point on
an actual nonsplit fiber has a forward one-step iterate whose adjacent trace
is both primitive in the split torus and candidate-regular. -/
theorem exists_iterate_actualNonsplitPoint_with_primitiveCandidateRegularAdjacentTrace
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (c u t : ZMod p) (x : Point (ZMod p))
    (hx : IsSolution (coefficients c) x) (hx1 : x.x1 = u)
    (htrace : t = trace c u) (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (w : quadraticNormOneTorus p)
    (htraceW : quadraticNormOneTrace p w = t)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) + 28 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p
            (Nat.card (quadraticNormOneTorus p) / orderOf w)) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      trace c (((oneStep1 c)^[n]) x).x2 = splitTorusTrace v ∧
        orderOf v = Nat.card (ZMod p)ˣ ∧
          OrderedTraceCandidateRegular c c c (splitTorusTrace v) := by
  have hsigma :
      actualSigma c u t ≠ 0 :=
    MiddleGame.actualSigma_ne_zero_of_candidateRegular
      c u t htrace hregular
  let k : (ZMod p)ˣ := actualSigmaUnit c u t hsigma
  have hk : k ≠ 1 := by
    intro hunit
    apply MiddleGame.actualSigma_ne_one_of_candidateRegular
      c u t htrace hregular
    have hval :=
      congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) hunit
    simpa [k] using hval
  have hD2 :
      shiftedTraceEvenObstruction (k : ZMod p)
          (actualGamma c u t) ≠ 0 := by
    simpa [k] using
      MiddleGame.actualEvenObstruction_ne_zero_of_candidateRegular
        c u t htrace hc hregular
  obtain ⟨h, S, hpoint, hS⟩ :=
    exists_actualShiftedNonsplitSeed
      p c u t x hx hx1 htrace hregular w htraceW
  let orbitExponent :=
    Nat.card (quadraticNormOneTorus p) / orderOf w
  obtain ⟨z, hzTrace, hzOrder, hzRegular⟩ :=
    exists_shiftedSeededNonsplitPrimitiveTracePair_candidateRegular_of_error_add_twentyEight_lt_main
      p coefficient hWeil hpTwo c hc k hk S (actualGamma c u t)
        hD2 orbitExponent
        (BGS.Markoff.complementaryExponent_pos w)
        (BGS.Markoff.nonsplitComplementaryExponent_cast_ne_zero p w)
        (BGS.Markoff.complementaryExponent_dvd_natCard w)
        (by simpa [orbitExponent] using hmargin)
  obtain ⟨n, hn⟩ :=
    exists_iterate_actualNonsplitSeedTrace
      p c u t x htrace hregular w htraceW h S hpoint hS z.1
  refine ⟨n, z.2, ?_, hzOrder, hzRegular⟩
  calc
    trace c (((oneStep1 c)^[n]) x).x2 =
        Algebra.trace (ZMod p) (quadraticFiniteField p)
            ((S.1 : quadraticFiniteField p) *
              ((z.1.1 : (quadraticFiniteField p)ˣ) :
                quadraticFiniteField p)) +
          actualGamma c u t := hn
    _ = shiftedSeededNonsplitTorusTrace
          p k S (actualGamma c u t) z.1 := rfl
    _ = splitTorusTrace z.2 := hzTrace

end

end GenMarkoff.Symmetric.Endgame.Nonsplit
