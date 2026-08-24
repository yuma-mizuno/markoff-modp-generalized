import GenMarkoff.Symmetric.Endgame.Nonsplit.ShiftedHasseFromGeneral
import GenMarkoff.Symmetric.Endgame.RegularPrimitiveCount
import BGS.Markoff.Endgame.PrimitiveTraceCount

/-!
# Primitive candidate-regular traces on shifted nonsplit covers

Möbius inclusion--exclusion is applied to the norm-one coordinate of the
shifted seeded cover.  A separate fiber argument shows that at most
twenty-eight primitive pairs have a candidate-irregular common trace.
-/

namespace GenMarkoff.Symmetric.Endgame.Nonsplit

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

abbrev shiftedSeededNonsplitPowerRangeSolutions
    (p : ℕ) [Fact p.Prime]
    (k : (ZMod p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : ZMod p) (d e : ℕ) :=
  powerTraceRangeSolutions
    (shiftedSeededNonsplitTorusTrace p k s gamma)
    (splitTorusTrace : (ZMod p)ˣ → ZMod p) d e

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
  change S.card ≤ 4
  calc
    S.card ≤ leftPolynomial.roots.toFinset.card *
        rightPolynomial.roots.toFinset.card := hcard
    _ ≤ 2 * 2 := Nat.mul_le_mul hleftRoots hrightRoots
    _ = 4 := by norm_num

noncomputable abbrev shiftedSeededNonsplitPrimitiveUnsafeTraceSolutions
    (p : ℕ) [Fact p.Prime]
    (c : ZMod p) (k : (ZMod p)ˣ)
    (s : ↥(quadraticNormFiber p k)) (gamma : ZMod p)
    (orbitExponent : ℕ) :=
  (shiftedSeededNonsplitPrimitiveTraceSolutions
    p k s gamma orbitExponent).filter fun z =>
      eval (splitTorusTrace z.2) (safePolynomial c) = 0

theorem shiftedSeededNonsplitPrimitiveUnsafeTraceSolutions_card_le_twentyEight
    (p : ℕ) [Fact p.Prime]
    (c : ZMod p) (k : (ZMod p)ˣ)
    (s : ↥(quadraticNormFiber p k)) (gamma : ZMod p)
    (orbitExponent : ℕ)
    (h2 : (2 : ZMod p) ≠ 0) (hc : c ^ 2 ≠ 4) :
    (shiftedSeededNonsplitPrimitiveUnsafeTraceSolutions
      p c k s gamma orbitExponent).card ≤ 28 := by
  classical
  let primitive :=
    shiftedSeededNonsplitPrimitiveTraceSolutions
      p k s gamma orbitExponent
  let traceValue :
      (powMonoidHom orbitExponent :
        quadraticNormOneTorus p →* quadraticNormOneTorus p).range ×
          (ZMod p)ˣ → ZMod p :=
    fun z => splitTorusTrace z.2
  let bad := primitive.filter fun z =>
    eval (traceValue z) (safePolynomial c) = 0
  have hbadFiber : ∀ t ∈ bad.image traceValue,
      (bad.filter fun z => traceValue z = t).card ≤ 4 := by
    intro t _
    calc
      (bad.filter fun z => traceValue z = t).card ≤
          (primitive.filter fun z => traceValue z = t).card := by
        apply Finset.card_le_card
        intro z hz
        simp only [bad, Finset.mem_filter] at hz ⊢
        exact ⟨hz.1.1, hz.2⟩
      _ ≤ 4 := by
        simpa [primitive, traceValue] using
          shiftedSeededNonsplitPrimitiveTraceSolutions_traceFiber_card_le_four
            p k s gamma orbitExponent t
  have hp : safePolynomial c ≠ 0 := safePolynomial_ne_zero c h2 hc
  have himage :
      bad.image traceValue ⊆ (safePolynomial c).roots.toFinset := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨z, hz, rfl⟩
    have hzero : eval (traceValue z) (safePolynomial c) = 0 :=
      (Finset.mem_filter.mp hz).2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact hzero
  have himageCard :
      (bad.image traceValue).card ≤
        (safePolynomial c).roots.toFinset.card :=
    Finset.card_le_card himage
  have hrootCard : (safePolynomial c).roots.toFinset.card ≤ 7 :=
    safePolynomial_roots_card_le c
  change bad.card ≤ 28
  calc
    bad.card ≤ 4 * (bad.image traceValue).card :=
      Finset.card_le_mul_card_image bad 4 hbadFiber
    _ ≤ 4 * (safePolynomial c).roots.toFinset.card :=
      Nat.mul_le_mul_left 4 himageCard
    _ ≤ 4 * 7 := Nat.mul_le_mul_left 4 hrootCard
    _ = 28 := by norm_num

theorem exists_shiftedSeededNonsplitPrimitiveTracePair_candidateRegular_of_error_add_twentyEight_lt_main
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (c : ZMod p) (hc : c ^ 2 ≠ 4)
    (k : (ZMod p)ˣ) (hk : k ≠ 1)
    (s : ↥(quadraticNormFiber p k)) (gamma : ZMod p)
    (hD2 : shiftedTraceEvenObstruction (k : ZMod p) gamma ≠ 0)
    (orbitExponent : ℕ)
    (horbitPositive : 0 < orbitExponent)
    (horbitChar : (orbitExponent : quadraticFiniteField p) ≠ 0)
    (horbitDvd :
      orbitExponent ∣ Nat.card (quadraticNormOneTorus p))
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) + 28 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p orbitExponent) :
    ∃ z : (powMonoidHom orbitExponent :
        quadraticNormOneTorus p →* quadraticNormOneTorus p).range ×
          (ZMod p)ˣ,
      shiftedSeededNonsplitTorusTrace p k s gamma z.1 =
          splitTorusTrace z.2 ∧
        orderOf z.2 = Nat.card (ZMod p)ˣ ∧
          OrderedTraceCandidateRegular c c c (splitTorusTrace z.2) := by
  let primitive :=
    shiftedSeededNonsplitPrimitiveTraceSolutions
      p k s gamma orbitExponent
  let mainTerm :=
    primitiveTraceMoebiusMainTerm
      (Nat.card (ZMod p)ˣ) p orbitExponent
  let error :=
    ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
      ((coefficient : ℝ) * Real.sqrt (p : ℝ))
  have henvelope :
      |(primitive.card : ℝ) - mainTerm| ≤ error := by
    simpa [primitive, mainTerm, error] using
      shiftedSeededNonsplitPrimitiveTraceSolutions_card_error_le
        p coefficient hWeil hpTwo k hk s gamma hD2
        orbitExponent horbitPositive horbitChar horbitDvd
  have hlower :
      mainTerm - (primitive.card : ℝ) ≤
        |(primitive.card : ℝ) - mainTerm| := by
    simpa only [neg_sub] using
      neg_le_abs ((primitive.card : ℝ) - mainTerm)
  have hcardReal : (28 : ℝ) < primitive.card := by
    have hmargin' : error + 28 < mainTerm := by
      simpa [error, mainTerm] using hmargin
    linarith
  have hcard : 28 < primitive.card := by
    exact_mod_cast hcardReal
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
    exact hpTwo
      (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)
  have hbad :=
    shiftedSeededNonsplitPrimitiveUnsafeTraceSolutions_card_le_twentyEight
      p c k s gamma orbitExponent h2 hc
  have hexists :
      ∃ z ∈ primitive,
        OrderedTraceCandidateRegular c c c (splitTorusTrace z.2) := by
    by_contra hnone
    push Not at hnone
    have hsubset :
        primitive ⊆
          shiftedSeededNonsplitPrimitiveUnsafeTraceSolutions
            p c k s gamma orbitExponent := by
      intro z hz
      rw [Finset.mem_filter]
      refine ⟨hz, ?_⟩
      by_contra hsafe
      exact hnone z hz
        (candidateRegular_of_eval_safePolynomial_ne_zero
          c (splitTorusTrace z.2) hc hsafe)
    have hle := Finset.card_le_card hsubset
    have : primitive.card ≤ 28 := hle.trans hbad
    exact (Nat.not_le_of_lt hcard) this
  obtain ⟨z, hz, hregular⟩ := hexists
  have hz' :=
    (mem_traceExactOrderSolutions_iff
      (shiftedSeededNonsplitTorusTrace p k s gamma)
      (splitTorusTrace : (ZMod p)ˣ → ZMod p)
      orbitExponent (Nat.card (ZMod p)ˣ) z).mp hz
  exact ⟨z, hz'.1, hz'.2, hregular⟩

end

end GenMarkoff.Symmetric.Endgame.Nonsplit
