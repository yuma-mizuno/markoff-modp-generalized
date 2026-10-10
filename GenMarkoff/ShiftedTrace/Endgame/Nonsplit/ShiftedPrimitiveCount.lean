import GenMarkoff.ShiftedTrace.Endgame.Nonsplit.ShiftedHasseFromGeneral
import GenMarkoff.ShiftedTrace.Endgame.RegularPrimitiveCount
import BGS.Markoff.Endgame.PrimitiveTraceCount

/-!
# Primitive traces on shifted nonsplit covers

This file counts the solutions of the shifted seeded nonsplit equation whose
norm-one coordinate lies in a fixed power image and whose base-field
coordinate is a generator of `(ZMod p)ˣ`.  The Hasse--Weil estimate of
`ShiftedHasseFromGeneral` is divided by the exact power-map multiplicity and
fed into Möbius inclusion--exclusion over the divisors of `p - 1`
(`shiftedSeededNonsplitPrimitiveTraceSolutions_card_error_le`).  It also
bounds each trace fiber of these primitive pairs by four, which the general
endgame uses to discard pairs whose common trace is exceptional.
-/

namespace GenMarkoff.ShiftedTrace.Endgame.Nonsplit

open BGS.Markoff Polynomial

noncomputable section

/-- The shifted trace of a seeded norm-one parameter. -/
def shiftedSeededNonsplitTorusTrace
    (p : ℕ) [Fact p.Prime]
    (k : (ZMod p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : ZMod p) (w : quadraticNormOneTorus p) : ZMod p :=
  Algebra.trace (ZMod p) (quadraticFiniteField p)
      ((s.1 : quadraticFiniteField p) *
        (((w : quadraticNormOneTorus p) :
          (quadraticFiniteField p)ˣ) : quadraticFiniteField p)) +
    gamma

/-- The shifted seeded equation is the power-trace equation for
`shiftedSeededNonsplitTorusTrace` and the split torus trace. -/
theorem shiftedSeededNonsplitTraceCoverEquation_iff_powerTraceEquation
    (p : ℕ) [Fact p.Prime]
    (k : (ZMod p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : ZMod p) (d e : ℕ)
    (w : quadraticNormOneTorus p) (u : (ZMod p)ˣ) :
    ShiftedSeededNonsplitTraceCoverEquation
        p k s gamma d e w u ↔
      shiftedSeededNonsplitTorusTrace p k s gamma (w ^ d) =
        splitTorusTrace (u ^ e) := by
  rfl

/-- Solutions of the shifted seeded equation on the `d`-th power image of the
norm-one torus and the `e`-th power image of `(ZMod p)ˣ`. -/
abbrev shiftedSeededNonsplitPowerRangeSolutions
    (p : ℕ) [Fact p.Prime]
    (k : (ZMod p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : ZMod p) (d e : ℕ) :=
  powerTraceRangeSolutions
    (shiftedSeededNonsplitTorusTrace p k s gamma)
    (splitTorusTrace : (ZMod p)ˣ → ZMod p) d e

/-- The shifted seeded solution finset is the generic power-trace cover
solution type. -/
def shiftedSeededNonsplitTraceCurveSolutionsEquivPowerTraceCoverSolutions
    (p : ℕ) [Fact p.Prime]
    (k : (ZMod p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : ZMod p) (d e : ℕ) :
    ↥(shiftedSeededNonsplitTraceCurveSolutions
      p k s gamma d e) ≃
      powerTraceCoverSolutions
        (shiftedSeededNonsplitTorusTrace p k s gamma)
        (splitTorusTrace : (ZMod p)ˣ → ZMod p) d e where
  toFun z := ⟨z.1, by
    exact
      (shiftedSeededNonsplitTraceCoverEquation_iff_powerTraceEquation
        p k s gamma d e z.1.1 z.1.2).mp
        ((mem_shiftedSeededNonsplitTraceCurveSolutions_iff
          p k s gamma d e z.1).mp z.2)⟩
  invFun z := ⟨z.1,
    (mem_shiftedSeededNonsplitTraceCurveSolutions_iff
      p k s gamma d e z.1).mpr
      ((shiftedSeededNonsplitTraceCoverEquation_iff_powerTraceEquation
        p k s gamma d e z.1.1 z.1.2).mpr z.2)⟩
  left_inv z := by rfl
  right_inv z := by rfl

/-- Exact power-map multiplicity: for `d` and `e` dividing the two torus
orders, the cover count is `d * e` times the power-range count. -/
theorem shiftedSeededNonsplitTraceCurveSolutions_card_eq_mul_natCard_powerRange
    (p : ℕ) [Fact p.Prime]
    (k : (ZMod p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : ZMod p) (d e : ℕ)
    (hdvd : d ∣ Nat.card (quadraticNormOneTorus p))
    (hedvd : e ∣ Nat.card (ZMod p)ˣ) :
    (shiftedSeededNonsplitTraceCurveSolutions
      p k s gamma d e).card =
      d * e * Nat.card
        (shiftedSeededNonsplitPowerRangeSolutions
          p k s gamma d e) := by
  calc
    (shiftedSeededNonsplitTraceCurveSolutions
      p k s gamma d e).card =
        Nat.card ↥(shiftedSeededNonsplitTraceCurveSolutions
          p k s gamma d e) := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_coe _).symm
    _ = Nat.card
        (powerTraceCoverSolutions
          (shiftedSeededNonsplitTorusTrace p k s gamma)
          (splitTorusTrace : (ZMod p)ˣ → ZMod p) d e) :=
      Nat.card_congr
        (shiftedSeededNonsplitTraceCurveSolutionsEquivPowerTraceCoverSolutions
          p k s gamma d e)
    _ = d * e * Nat.card
        (shiftedSeededNonsplitPowerRangeSolutions
          p k s gamma d e) :=
      natCard_powerTraceCoverSolutions_of_dvd
        (shiftedSeededNonsplitTorusTrace p k s gamma)
        (splitTorusTrace : (ZMod p)ˣ → ZMod p)
        d e hdvd hedvd

/-- The power-range count differs from `p / (d * e)` by at most
`coefficient * √p`. -/
theorem shiftedSeededNonsplitPowerRangeSolutions_count_error_le
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (k : (ZMod p)ˣ) (hk : k ≠ 1)
    (s : ↥(quadraticNormFiber p k)) (gamma : ZMod p)
    (hD2 : shiftedTraceEvenObstruction (k : ZMod p) gamma ≠ 0)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hdChar : (d : quadraticFiniteField p) ≠ 0)
    (hdvd : d ∣ Nat.card (quadraticNormOneTorus p))
    (hedvd : e ∣ Nat.card (ZMod p)ˣ) :
    |(Nat.card
        (shiftedSeededNonsplitPowerRangeSolutions
          p k s gamma d e) : ℝ) -
        (p : ℝ) / ((d : ℝ) * (e : ℝ))| ≤
      (coefficient : ℝ) * Real.sqrt (p : ℝ) := by
  apply rangeCount_error_le_of_coverCount_error_and_exactMultiplicity
    (shiftedSeededNonsplitTraceCurveSolutions
      p k s gamma d e).card
    (Nat.card
      (shiftedSeededNonsplitPowerRangeSolutions
        p k s gamma d e))
    p coefficient d e hd he
    (shiftedSeededNonsplitTraceCurveSolutions_card_eq_mul_natCard_powerRange
      p k s gamma d e hdvd hedvd)
  exact
    shiftedSeededNonsplitTraceCurveSolutions_count_error_le_of_weilBoundAssumption_and_positiveExponents
      coefficient hWeil p hpTwo k hk s gamma hD2 d e hd he hdChar

/-- Shifted nonsplit coincidences whose base-field coordinate is primitive. -/
abbrev shiftedSeededNonsplitPrimitiveTraceSolutions
    (p : ℕ) [Fact p.Prime]
    (k : (ZMod p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : ZMod p) (orbitExponent : ℕ) :=
  traceExactOrderSolutions
    (shiftedSeededNonsplitTorusTrace p k s gamma)
    (splitTorusTrace : (ZMod p)ˣ → ZMod p)
    orbitExponent (Nat.card (ZMod p)ˣ)

/-- Möbius inclusion--exclusion: the number of primitive shifted nonsplit
pairs differs from its Möbius main term by at most the number of divisors of
`Nat.card (ZMod p)ˣ` times `coefficient * √p`. -/
theorem shiftedSeededNonsplitPrimitiveTraceSolutions_card_error_le
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (k : (ZMod p)ˣ) (hk : k ≠ 1)
    (s : ↥(quadraticNormFiber p k)) (gamma : ZMod p)
    (hD2 : shiftedTraceEvenObstruction (k : ZMod p) gamma ≠ 0)
    (orbitExponent : ℕ) (horbitPositive : 0 < orbitExponent)
    (horbitChar : (orbitExponent : quadraticFiniteField p) ≠ 0)
    (horbitDvd :
      orbitExponent ∣ Nat.card (quadraticNormOneTorus p)) :
    |((shiftedSeededNonsplitPrimitiveTraceSolutions
        p k s gamma orbitExponent).card : ℝ) -
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p orbitExponent| ≤
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) := by
  have hRange :
      ∀ e : ℕ, e ∣ Nat.card (ZMod p)ˣ → 0 < e →
      |(Nat.card
          (powerTraceRangeSolutions
            (shiftedSeededNonsplitTorusTrace p k s gamma)
            (splitTorusTrace : (ZMod p)ˣ → ZMod p)
            orbitExponent e) : ℝ) -
          (p : ℝ) / ((e : ℝ) * (orbitExponent : ℝ))| ≤
        (coefficient : ℝ) * Real.sqrt (p : ℝ) := by
    intro e hedvd he
    have hestimate :=
      shiftedSeededNonsplitPowerRangeSolutions_count_error_le
        p coefficient hWeil hpTwo k hk s gamma hD2
        orbitExponent e horbitPositive he horbitChar
        horbitDvd hedvd
    simpa [mul_comm] using hestimate
  simpa [shiftedSeededNonsplitPrimitiveTraceSolutions,
    primitiveTraceMoebiusMainTerm] using
    traceExactOrderSolutions_card_error_le_moebiusMain
      (shiftedSeededNonsplitTorusTrace p k s gamma)
      (splitTorusTrace : (ZMod p)ˣ → ZMod p)
      orbitExponent
      (fun e => (p : ℝ) / ((e : ℝ) * (orbitExponent : ℝ)))
      ((coefficient : ℝ) * Real.sqrt (p : ℝ)) hRange

/-- A fixed common trace has at most four lifts among primitive shifted
nonsplit pairs. -/
theorem shiftedSeededNonsplitPrimitiveTraceSolutions_traceFiber_card_le_four
    (p : ℕ) [Fact p.Prime]
    (k : (ZMod p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : ZMod p) (orbitExponent : ℕ) (target : ZMod p) :
    ((shiftedSeededNonsplitPrimitiveTraceSolutions
      p k s gamma orbitExponent).filter fun z =>
        splitTorusTrace z.2 = target).card ≤ 4 := by
  classical
  -- After scalar extension the left coordinate is a root of the twisted-trace
  -- quadratic with weights `s`, `s ^ p`; the right coordinate is a root of the
  -- ordinary trace quadratic.  Embed the fiber into the product of the two
  -- root sets and count roots.
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let primitive :=
    shiftedSeededNonsplitPrimitiveTraceSolutions
      p k s gamma orbitExponent
  let S := primitive.filter fun z => splitTorusTrace z.2 = target
  let leftPolynomial :=
    twistedTracePolynomial
      (((s.1 : E) ^ p) / (s.1 : E))
      ((f target - f gamma) / (s.1 : E))
  let rightPolynomial :=
    twistedTracePolynomial (1 : ZMod p) target
  have hleftPolynomial : leftPolynomial ≠ 0 :=
    (twistedTracePolynomial_monic
      (((s.1 : E) ^ p) / (s.1 : E))
      ((f target - f gamma) / (s.1 : E))).ne_zero
  have hrightPolynomial : rightPolynomial ≠ 0 :=
    (twistedTracePolynomial_monic (1 : ZMod p) target).ne_zero
  let rootEmbedding :
      ↥S ↪
        ↥leftPolynomial.roots.toFinset ×
          ↥rightPolynomial.roots.toFinset :=
    { toFun := fun z =>
        (⟨((((z.1.1.1 : quadraticNormOneTorus p) :
              (quadraticFiniteField p)ˣ) : quadraticFiniteField p)), by
            rw [Multiset.mem_toFinset,
              Polynomial.mem_roots hleftPolynomial]
            apply
              (eval_twistedTracePolynomial_eq_zero_iff
                (((s.1 : E) ^ p) / (s.1 : E))
                ((f target - f gamma) / (s.1 : E))
                (((z.1.1.1 : quadraticNormOneTorus p) :
                  (quadraticFiniteField p)ˣ))).2
            apply
              (MiddleGame.shiftedWeightedSplitTorusTrace_eq_iff_twistedUnitTrace_eq
                (s.1 : E) ((s.1 : E) ^ p) (f gamma) (f target)
                (((z.1.1.1 : quadraticNormOneTorus p) :
                  (quadraticFiniteField p)ˣ))
                (Units.ne_zero s.1)).mp
            have hzMem : z.1 ∈ primitive :=
              (Finset.mem_filter.mp z.2).1
            have hzTrace :=
              (mem_traceExactOrderSolutions_iff
                (shiftedSeededNonsplitTorusTrace p k s gamma)
                (splitTorusTrace : (ZMod p)ˣ → ZMod p)
                orbitExponent (Nat.card (ZMod p)ˣ) z.1).mp hzMem
            have hzTarget : splitTorusTrace z.1.2 = target :=
              (Finset.mem_filter.mp z.2).2
            have hbase :
                shiftedSeededNonsplitTorusTrace
                    p k s gamma z.1.1.1 = target :=
              hzTrace.1.trans hzTarget
            calc
              weightedShiftedSplitTorusTrace
                  E (s.1 : E) ((s.1 : E) ^ p) (f gamma)
                  (((z.1.1.1 : quadraticNormOneTorus p) :
                    (quadraticFiniteField p)ˣ)) =
                  f (shiftedSeededNonsplitTorusTrace
                    p k s gamma z.1.1.1) := by
                symm
                unfold shiftedSeededNonsplitTorusTrace
                unfold weightedShiftedSplitTorusTrace
                rw [map_add]
                congr 1
                simpa [f, E] using
                  algebraMap_seededQuadraticTrace_eq_weightedSplitTorusTrace
                    p k s 1 z.1.1.1
              _ = f target := congrArg f hbase⟩,
          ⟨((z.1.2 : (ZMod p)ˣ) : ZMod p), by
            rw [Multiset.mem_toFinset,
              Polynomial.mem_roots hrightPolynomial]
            apply
              (eval_twistedTracePolynomial_eq_zero_iff
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
          apply Subtype.ext
          apply Units.ext
          exact congrArg (fun q => (q.1 : E)) hxy
        · apply Units.ext
          exact congrArg (fun q => (q.2 : ZMod p)) hxy }
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
        (((s.1 : E) ^ p) / (s.1 : E))
        ((f target - f gamma) / (s.1 : E))
  have hrightRoots : rightPolynomial.roots.toFinset.card ≤ 2 := by
    calc
      rightPolynomial.roots.toFinset.card ≤ rightPolynomial.roots.card :=
        Multiset.toFinset_card_le _
      _ ≤ rightPolynomial.natDegree := Polynomial.card_roots' _
      _ = 2 := twistedTracePolynomial_natDegree (1 : ZMod p) target
  -- Fold the goal into the local abbreviation `S` so that `hcard` applies.
  change S.card ≤ 4
  calc
    S.card ≤ leftPolynomial.roots.toFinset.card *
        rightPolynomial.roots.toFinset.card := hcard
    _ ≤ 2 * 2 := Nat.mul_le_mul hleftRoots hrightRoots
    _ = 4 := by norm_num

end

end GenMarkoff.ShiftedTrace.Endgame.Nonsplit
