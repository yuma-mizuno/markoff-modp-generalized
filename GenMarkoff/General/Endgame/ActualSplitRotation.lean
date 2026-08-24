import GenMarkoff.General.Endgame.RegularPrimitiveCount
import GenMarkoff.General.Arithmetic.ExplicitCutoff
import GenMarkoff.General.Arithmetic.ReasonableCutoff
import GenMarkoff.General.Assembly.RegularMiddleIteration
import GenMarkoff.General.MiddleGame.ActualDiagonalization
import GenMarkoff.General.MiddleGame.ActualMoveWiring
import GenMarkoff.General.MiddleGame.DirectedOrderGrowth
import BGS.Markoff.Endgame.PrimitiveOrbitWiring

/-!
# Fixed-coefficient alternating split actual-rotation endgame

This file treats the explicit alternating directed frames from the first
rotation axis to the second trace and back from the second rotation axis to
the first trace.  The fixed coefficient triple is never permuted.

## New considerations

* `rotation1` advances the actual fiber parameter by `q ^ 2`, not by `q`.
  Consequently the complementary power exponent is
  `Nat.card (ZMod p)ˣ / orderOf (q ^ 2)`.
* The translated parameter coset has the ordered first-coordinate weights
  `actualAlpha a.multiplier * s` and
  `actualBeta a.multiplier a.a2 a.a3 u t / s`, with shift
  `actualGammaFirst a.multiplier a.a2 a.a3 u t`.
* Candidate regularity of the primitive output is requested in the explicitly
  named target frame `(a.a2, targetB, targetC)`.  The general ordered count
  therefore pays the forty-pair exceptional margin and needs the square
  hypotheses in precisely the first two target-frame positions.
* In the reverse second-to-first direction, `fiberPoint2` orders its moving
  coordinates as `(x3, x1)`.  Thus the first-coordinate output is the second
  moving coordinate: its weights contain the eigenvalue `q`, its affine shift
  is `actualGammaSecond`, and the current regular frame is
  `(a.a2, a.a1, a.a3)`.
* Recovering a `fiberPoint2` parameter from an arbitrary point uses the ordered
  pair `(x3, x1)`.  Reverse candidate regularity must first be converted to
  nonvanishing of `centeredFiberProduct a.a3 a.a1`; the direct-order inverse
  wrapper has the opposite regular-frame order and cannot be applied blindly.
* The alternating dispatcher fixes the outgoing regular frame by direction:
  first-to-second lands in `(a.a2, a.a1, a.a3)`, while second-to-first lands
  in `(a.a1, a.a2, a.a3)`.  These are changes of directed state only, never
  permutations of the coefficient triple.
-/

namespace GenMarkoff.General.Endgame

open BGS.Markoff
open GenMarkoff.General.Assembly
open GenMarkoff.General.MiddleGame

noncomputable section

/-- A parameter in the complementary power image of `q²` is reached by a
forward `rotation1` iterate of the translated first-axis fiber point. -/
theorem
    exists_iterate_fiberPoint1_eq_of_mem_complementarySquarePowerRange
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q s : (ZMod p)ˣ)
    (hD : discriminant t ≠ 0)
    (heigen : t = splitTorusTrace q)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u)
    (h : (powMonoidHom
      (Nat.card (ZMod p)ˣ / orderOf (q ^ 2)) :
        (ZMod p)ˣ →* (ZMod p)ˣ).range) :
    ∃ n : ℕ,
      ((rotation1 a)^[n])
          (fiberPoint1 a u t (q : ZMod p) (s : ZMod p)) =
        fiberPoint1 a u t (q : ZMod p)
          ((s * h.1 : (ZMod p)ˣ) : ZMod p) := by
  obtain ⟨n, hn⟩ :=
    BGS.Markoff.exists_pow_eq_of_mem_complementaryPowerRange (q ^ 2) h
  refine ⟨n, ?_⟩
  have heigen' :
      t = (q : ZMod p) + (q : ZMod p)⁻¹ := by
    simpa only [splitTorusTrace, Units.val_inv_eq_inv_val] using heigen
  rw [iterate_rotation1_fiberPoint1_eq_pow_mul
    a u t (q : ZMod p) (s : ZMod p) hD
      (Units.ne_zero q) (Units.ne_zero s)
      heigen' hcoordinate n]
  congr 1
  have hnVal :
      ((((q ^ 2) ^ n : (ZMod p)ˣ) : ZMod p)) =
        (h.1 : ZMod p) :=
    congrArg (fun z : (ZMod p)ˣ ↦ (z : ZMod p)) hn
  simpa only [Units.val_pow_eq_pow_val, Units.val_mul, mul_comm] using
    congrArg (fun z : ZMod p ↦ (s : ZMod p) * z) hnVal

/-- The second-coordinate trace on the reached complementary `q²`-power
coset has the ordered unequal-coefficient weights and first-coordinate
shift. -/
theorem
    orderedTrace_fiberPoint1_complementarySquarePowerRange_eq_weightedShiftedTrace
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q s : (ZMod p)ˣ)
    (h : (powMonoidHom
      (Nat.card (ZMod p)ˣ / orderOf (q ^ 2)) :
        (ZMod p)ˣ →* (ZMod p)ˣ).range) :
    orderedTrace a.multiplier a.a2
        (fiberPoint1 a u t (q : ZMod p)
          ((s * h.1 : (ZMod p)ˣ) : ZMod p)).x2 =
      weightedSplitTorusTrace
          (actualAlpha a.multiplier * (s : ZMod p))
          (actualBeta a.multiplier a.a2 a.a3 u t /
            (s : ZMod p)) h.1 +
        actualGammaFirst a.multiplier a.a2 a.a3 u t := by
  exact orderedTrace_fiberPoint1_mul_eq_weightedSplitTorusTrace
    a u t q s h.1

/-- A parameter in the complementary power image of `q²` is reached by a
forward `rotation2` iterate of the translated second-axis fiber point. -/
theorem
    exists_iterate_fiberPoint2_eq_of_mem_complementarySquarePowerRange
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q s : (ZMod p)ˣ)
    (hD : discriminant t ≠ 0)
    (heigen : t = splitTorusTrace q)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u)
    (h : (powMonoidHom
      (Nat.card (ZMod p)ˣ / orderOf (q ^ 2)) :
        (ZMod p)ˣ →* (ZMod p)ˣ).range) :
    ∃ n : ℕ,
      ((rotation2 a)^[n])
          (fiberPoint2 a u t (q : ZMod p) (s : ZMod p)) =
        fiberPoint2 a u t (q : ZMod p)
          ((s * h.1 : (ZMod p)ˣ) : ZMod p) := by
  obtain ⟨n, hn⟩ :=
    BGS.Markoff.exists_pow_eq_of_mem_complementaryPowerRange (q ^ 2) h
  refine ⟨n, ?_⟩
  have heigen' :
      t = (q : ZMod p) + (q : ZMod p)⁻¹ := by
    simpa only [splitTorusTrace, Units.val_inv_eq_inv_val] using heigen
  rw [iterate_rotation2_fiberPoint2_eq_pow_mul
    a u t (q : ZMod p) (s : ZMod p) hD
      (Units.ne_zero q) (Units.ne_zero s)
      heigen' hcoordinate n]
  congr 1
  have hnVal :
      ((((q ^ 2) ^ n : (ZMod p)ˣ) : ZMod p)) =
        (h.1 : ZMod p) :=
    congrArg (fun z : (ZMod p)ˣ ↦ (z : ZMod p)) hn
  simpa only [Units.val_pow_eq_pow_val, Units.val_mul, mul_comm] using
    congrArg (fun z : ZMod p ↦ (s : ZMod p) * z) hnVal

/-- The first-coordinate trace on the reached complementary `q²`-power
coset has the reverse ordered unequal-coefficient weights and the
second-moving-coordinate shift. -/
theorem
    orderedTrace_fiberPoint2_complementarySquarePowerRange_eq_weightedShiftedTrace
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q s : (ZMod p)ˣ)
    (h : (powMonoidHom
      (Nat.card (ZMod p)ˣ / orderOf (q ^ 2)) :
        (ZMod p)ˣ →* (ZMod p)ˣ).range) :
    orderedTrace a.multiplier a.a1
        (fiberPoint2 a u t (q : ZMod p)
          ((s * h.1 : (ZMod p)ˣ) : ZMod p)).x1 =
      weightedSplitTorusTrace
          ((a.multiplier * (q : ZMod p)) * (s : ZMod p))
          ((a.multiplier * centeredFiberProduct a.a3 a.a1 u t /
              (q : ZMod p)) /
            (s : ZMod p)) h.1 +
        actualGammaSecond a.multiplier a.a3 a.a1 u t := by
  change
    a.multiplier *
          (fiberPair a.a3 a.a1 u t (q : ZMod p)
            ((s * h.1 : (ZMod p)ˣ) : ZMod p)).2 -
        a.a1 =
      weightedSplitTorusTrace
          ((a.multiplier * (q : ZMod p)) * (s : ZMod p))
          ((a.multiplier * centeredFiberProduct a.a3 a.a1 u t /
              (q : ZMod p)) /
            (s : ZMod p)) h.1 +
        actualGammaSecond a.multiplier a.a3 a.a1 u t
  exact secondTrace_fiberPair_mul_eq_weightedSplitTorusTrace
    a.multiplier a.a3 a.a1 u t q s h.1

/-- The `q²`-coset-correct primitive count is realized by an actual forward
`rotation1` iterate.  The primitive target trace is candidate regular in the
explicit ordered frame `(a.a2, targetB, targetC)`. -/
theorem
    exists_iterate_actualSplitFiberPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q s : (ZMod p)ˣ)
    (htrace : t = orderedTrace a.multiplier a.a1 u)
    (heigen : t = splitTorusTrace q)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (targetB targetC : ZMod p)
    (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) +
          40 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p
            (Nat.card (ZMod p)ˣ / orderOf (q ^ 2))) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a2
          (((rotation1 a)^[n])
            (fiberPoint1 a u t (q : ZMod p) (s : ZMod p))).x2 =
        splitTorusTrace v ∧
      orderOf v = Nat.card (ZMod p)ˣ ∧
        OrderedTraceCandidateRegular
          a.a2 targetB targetC (splitTorusTrace v) := by
  let orbitExponent :=
    Nat.card (ZMod p)ˣ / orderOf (q ^ 2)
  let alpha : ZMod p :=
    actualAlpha a.multiplier * (s : ZMod p)
  let beta : ZMod p :=
    actualBeta a.multiplier a.a2 a.a3 u t / (s : ZMod p)
  let gamma : ZMod p :=
    actualGammaFirst a.multiplier a.a2 a.a3 u t
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
    exact hpTwo
      (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)
  have hsigmaBase :
      actualSigma a.multiplier a.a2 a.a3 u t ≠ 0 :=
    actualSigma_ne_zero_of_candidateRegular
      a.multiplier a.a1 a.a2 a.a3 u t htrace hregular
  have halphaBase : actualAlpha a.multiplier ≠ 0 := by
    have hproduct :
        actualAlpha a.multiplier *
            actualBeta a.multiplier a.a2 a.a3 u t ≠ 0 := by
      simpa [actualSigma] using hsigmaBase
    exact (mul_ne_zero_iff.mp hproduct).1
  have halpha : alpha ≠ 0 := by
    exact mul_ne_zero halphaBase (Units.ne_zero s)
  have hbeta : beta ≠ 0 := by
    exact div_ne_zero
      (actualBeta_ne_zero_of_candidateRegular
        a.multiplier a.a1 a.a2 a.a3 u t htrace hregular)
      (Units.ne_zero s)
  have hweights :
      alpha * beta =
        actualSigma a.multiplier a.a2 a.a3 u t := by
    simpa [alpha, beta] using
      actual_firstDirected_coset_weights_mul
        a.multiplier a.a2 a.a3 u t s
  have hproductOne : alpha * beta ≠ 1 := by
    rw [hweights]
    exact actualSigma_ne_one_of_candidateRegular
      a.multiplier a.a1 a.a2 a.a3 u t htrace hregular
  have hD2 :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualEvenObstruction_ne_zero_of_candidateRegular
      a.multiplier a.a1 a.a2 a.a3 u t htrace hA2 hregular
  obtain ⟨z, hzTrace, hzOrder, hzRegular⟩ :=
    exists_weightedShiftedSplitPrimitiveTracePair_candidateRegular_of_error_add_forty_lt_main
      p coefficient hWeil
        a.a2 targetB targetC alpha beta gamma orbitExponent
        htwo hA2 hTargetB halpha hbeta hproductOne hD2
        (BGS.Markoff.complementaryExponent_pos (q ^ 2))
        (BGS.Markoff.splitComplementaryExponent_cast_ne_zero p (q ^ 2))
        (BGS.Markoff.complementaryExponent_dvd_natCard (q ^ 2))
        (by simpa [orbitExponent] using hmargin)
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  obtain ⟨n, hn⟩ :=
    exists_iterate_fiberPoint1_eq_of_mem_complementarySquarePowerRange
      p a u t q s hD heigen htrace z.1
  refine ⟨n, z.2, ?_, hzOrder, hzRegular⟩
  rw [hn]
  calc
    orderedTrace a.multiplier a.a2
        (fiberPoint1 a u t (q : ZMod p)
          ((s * z.1.1 : (ZMod p)ˣ) : ZMod p)).x2 =
        weightedSplitTorusTrace alpha beta z.1.1 + gamma := by
      simpa [alpha, beta, gamma] using
        orderedTrace_fiberPoint1_complementarySquarePowerRange_eq_weightedShiftedTrace
          p a u t q s z.1
    _ = weightedShiftedSplitTorusTrace
          (ZMod p) alpha beta gamma z.1 := by
      rfl
    _ = splitTorusTrace z.2 := hzTrace

/-- Reverse `q²`-coset-correct primitive endgame.  A forward `rotation2`
iterate sends a second-axis fiber to a primitive first-coordinate trace,
candidate regular in the explicitly named frame
`(a.a1, targetB, targetC)`. -/
theorem
    exists_iterate_actualSplitFiberPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q s : (ZMod p)ˣ)
    (htrace : t = orderedTrace a.multiplier a.a2 u)
    (heigen : t = splitTorusTrace q)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (targetB targetC : ZMod p)
    (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) +
          40 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p
            (Nat.card (ZMod p)ˣ / orderOf (q ^ 2))) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a1
          (((rotation2 a)^[n])
            (fiberPoint2 a u t (q : ZMod p) (s : ZMod p))).x1 =
        splitTorusTrace v ∧
      orderOf v = Nat.card (ZMod p)ˣ ∧
        OrderedTraceCandidateRegular
          a.a1 targetB targetC (splitTorusTrace v) := by
  let orbitExponent :=
    Nat.card (ZMod p)ˣ / orderOf (q ^ 2)
  let alpha : ZMod p :=
    (a.multiplier * (q : ZMod p)) * (s : ZMod p)
  let beta : ZMod p :=
    (a.multiplier * centeredFiberProduct a.a3 a.a1 u t /
      (q : ZMod p)) / (s : ZMod p)
  let gamma : ZMod p :=
    actualGammaSecond a.multiplier a.a3 a.a1 u t
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
    exact hpTwo
      (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)
  have hweights :
      alpha * beta =
        actualSigma a.multiplier a.a3 a.a1 u t := by
    simpa [alpha, beta] using
      actual_secondDirected_coset_weights_mul
        a.multiplier a.a3 a.a1 u t q s
  have hproduct : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_reverseCandidateRegular
      a.multiplier a.a2 a.a3 a.a1 u t htrace hregular
  have halpha : alpha ≠ 0 :=
    (mul_ne_zero_iff.mp hproduct).1
  have hbeta : beta ≠ 0 :=
    (mul_ne_zero_iff.mp hproduct).2
  have hproductOne : alpha * beta ≠ 1 := by
    rw [hweights,
      actualSigma_eq_orderedTraceSigma
        a.multiplier a.a2 a.a3 a.a1 u t htrace,
      orderedTraceSigma_swap a.a2 a.a3 a.a1 t]
    exact hregular.sigma_ne_one
  have hD2 :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualSecondEvenObstruction_ne_zero_of_candidateRegular
      a.multiplier a.a2 a.a3 a.a1 u t
        htrace hA1 hregular
  obtain ⟨z, hzTrace, hzOrder, hzRegular⟩ :=
    exists_weightedShiftedSplitPrimitiveTracePair_candidateRegular_of_error_add_forty_lt_main
      p coefficient hWeil
        a.a1 targetB targetC alpha beta gamma orbitExponent
        htwo hA1 hTargetB halpha hbeta hproductOne hD2
        (BGS.Markoff.complementaryExponent_pos (q ^ 2))
        (BGS.Markoff.splitComplementaryExponent_cast_ne_zero p (q ^ 2))
        (BGS.Markoff.complementaryExponent_dvd_natCard (q ^ 2))
        (by simpa [orbitExponent] using hmargin)
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  obtain ⟨n, hn⟩ :=
    exists_iterate_fiberPoint2_eq_of_mem_complementarySquarePowerRange
      p a u t q s hD heigen htrace z.1
  refine ⟨n, z.2, ?_, hzOrder, hzRegular⟩
  rw [hn]
  calc
    orderedTrace a.multiplier a.a1
        (fiberPoint2 a u t (q : ZMod p)
          ((s * z.1.1 : (ZMod p)ˣ) : ZMod p)).x1 =
        weightedSplitTorusTrace alpha beta z.1.1 + gamma := by
      simpa [alpha, beta, gamma] using
        orderedTrace_fiberPoint2_complementarySquarePowerRange_eq_weightedShiftedTrace
          p a u t q s z.1
    _ = weightedShiftedSplitTorusTrace
          (ZMod p) alpha beta gamma z.1 := by
      rfl
    _ = splitTorusTrace z.2 := hzTrace

/-- Arbitrary-point form of the fixed-coefficient first-to-second split
endgame.  Candidate regularity supplies the nonzero centered product needed
to recover the initial translated fiber parameter. -/
theorem
    exists_iterate_actualSplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q : (ZMod p)ˣ)
    (x : Point (ZMod p))
    (hx : IsSolution a x) (hx1 : x.x1 = u)
    (htrace : t = orderedTrace a.multiplier a.a1 u)
    (heigen : t = splitTorusTrace q)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (targetB targetC : ZMod p)
    (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) +
          40 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p
            (Nat.card (ZMod p)ˣ / orderOf (q ^ 2))) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a2
          (((rotation1 a)^[n]) x).x2 =
        splitTorusTrace v ∧
      orderOf v = Nat.card (ZMod p)ˣ ∧
        OrderedTraceCandidateRegular
          a.a2 targetB targetC (splitTorusTrace v) := by
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have hconic :
      fiberConic a.a2 a.a3 u t x.x2 x.x3 = 0 := by
    have hsurface := hx
    rw [IsSolution, polynomial_fixed_first, hx1, ← htrace] at hsurface
    exact hsurface
  obtain ⟨s, hsPair⟩ :=
    exists_unit_fiberPair_eq_of_candidateRegular
      a.multiplier a.a1 a.a2 a.a3 u t q (x.x2, x.x3)
        hconic htrace heigen hregular
  have hsPoint :
      fiberPoint1 a u t (q : ZMod p) (s : ZMod p) = x := by
    apply Point.ext
    · simpa using hx1.symm
    · simpa [fiberPoint1] using congrArg Prod.fst hsPair
    · simpa [fiberPoint1] using congrArg Prod.snd hsPair
  obtain ⟨n, v, hn, hvOrder, hvRegular⟩ :=
    exists_iterate_actualSplitFiberPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame
      p coefficient hWeil hpTwo a u t q s htrace heigen hA2
        targetB targetC hTargetB hregular hmargin
  refine ⟨n, v, ?_, hvOrder, hvRegular⟩
  simpa [hsPoint] using hn

/-- Reverse candidate regularity supplies the nonzero centered product needed
to invert the ordered second-axis parametrization.  The moving pair remains
`(x3, x1)`; no coefficient or coordinate permutation is performed. -/
theorem centeredFiberProduct_ne_zero_of_reverseCandidateRegular
    {K : Type*} [Field K]
    (s A B C u t : K)
    (htrace : t = orderedTrace s A u)
    (hregular : OrderedTraceCandidateRegular A C B t) :
    centeredFiberProduct B C u t ≠ 0 := by
  intro hzero
  apply actualSigma_ne_zero_of_reverseCandidateRegular
    s A B C u t htrace hregular
  simp [actualSigma, actualBeta, hzero]

/-- Arbitrary-point form of the fixed-coefficient second-to-first split
endgame.  The inverse parametrization uses the ordered moving coordinates
`(x3, x1)` and the output lies in the exact frame
`(a.a1, targetB, targetC)`. -/
theorem
    exists_iterate_actualSplitPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q : (ZMod p)ˣ)
    (x : Point (ZMod p))
    (hx : IsSolution a x) (hx2 : x.x2 = u)
    (htrace : t = orderedTrace a.multiplier a.a2 u)
    (heigen : t = splitTorusTrace q)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (targetB targetC : ZMod p)
    (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) +
          40 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p
            (Nat.card (ZMod p)ˣ / orderOf (q ^ 2))) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a1
          (((rotation2 a)^[n]) x).x1 =
        splitTorusTrace v ∧
      orderOf v = Nat.card (ZMod p)ˣ ∧
        OrderedTraceCandidateRegular
          a.a1 targetB targetC (splitTorusTrace v) := by
  have hD : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have hconic :
      fiberConic a.a3 a.a1 u t x.x3 x.x1 = 0 := by
    have hsurface := hx
    rw [IsSolution, polynomial_fixed_second, hx2, ← htrace] at hsurface
    exact hsurface
  have hproduct :
      centeredFiberProduct a.a3 a.a1 u t ≠ 0 :=
    centeredFiberProduct_ne_zero_of_reverseCandidateRegular
      a.multiplier a.a2 a.a3 a.a1 u t htrace hregular
  obtain ⟨s, hsPair⟩ :=
    exists_unit_fiberPair_eq
      a.a3 a.a1 u t q (x.x3, x.x1)
        hconic heigen hD hproduct
  have hsPoint :
      fiberPoint2 a u t (q : ZMod p) (s : ZMod p) = x := by
    apply Point.ext
    · simpa [fiberPoint2] using congrArg Prod.snd hsPair
    · simpa using hx2.symm
    · simpa [fiberPoint2] using congrArg Prod.fst hsPair
  obtain ⟨n, v, hn, hvOrder, hvRegular⟩ :=
    exists_iterate_actualSplitFiberPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame
      p coefficient hWeil hpTwo a u t q s htrace heigen hA1
        targetB targetC hTargetB hregular hmargin
  refine ⟨n, v, ?_, hvOrder, hvRegular⟩
  simpa [hsPoint] using hn

private theorem
    error_add_forty_lt_primitiveMain_of_augmented_explicitInequality
    (groupOrder fieldCard fixedExponent coefficient : ℕ)
    (hgroup : 0 < groupOrder) (hfield : 0 < fieldCard)
    (hfixed : 0 < fixedExponent)
    (hexplicit :
      (fixedExponent : ℝ) * (groupOrder.divisors.card : ℝ) ^ 2 *
          (((coefficient + 40 : ℕ) : ℝ) *
            Real.sqrt (fieldCard : ℝ)) < fieldCard) :
    (groupOrder.divisors.card : ℝ) *
          ((coefficient : ℝ) * Real.sqrt (fieldCard : ℝ)) + 40 <
      primitiveTraceMoebiusMainTerm
        groupOrder fieldCard fixedExponent := by
  have hdomination :=
    BGS.Markoff.divisorsError_lt_primitiveTraceMoebiusMainTerm_of_explicitInequality
      groupOrder fieldCard fixedExponent (coefficient + 40)
      hgroup hfixed hexplicit
  have hdivisorsOne :
      (1 : ℝ) ≤ (groupOrder.divisors.card : ℝ) := by
    exact_mod_cast
      (Nat.nonempty_divisors.mpr hgroup.ne').card_pos
  have hfieldOne : (1 : ℝ) ≤ (fieldCard : ℝ) := by
    exact_mod_cast hfield
  have hsqrtOne :
      (1 : ℝ) ≤ Real.sqrt (fieldCard : ℝ) :=
    Real.one_le_sqrt.mpr hfieldOne
  have hproductOne :
      (1 : ℝ) ≤
        (groupOrder.divisors.card : ℝ) *
          Real.sqrt (fieldCard : ℝ) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (groupOrder.divisors.card : ℝ) *
          Real.sqrt (fieldCard : ℝ) := by gcongr
  calc
    (groupOrder.divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (fieldCard : ℝ)) + 40 =
        (coefficient : ℝ) *
            ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ)) + 40 := by ring
    _ ≤ (coefficient : ℝ) *
            ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ)) +
          40 * ((groupOrder.divisors.card : ℝ) *
            Real.sqrt (fieldCard : ℝ)) := by
      have hforty :
          (40 : ℝ) ≤
            40 * ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ)) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hproductOne
            (show (0 : ℝ) ≤ 40 by norm_num))
      exact add_le_add
        (le_refl
          ((coefficient : ℝ) *
            ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ))))
        hforty
    _ = (groupOrder.divisors.card : ℝ) *
          (((coefficient + 40 : ℕ) : ℝ) *
            Real.sqrt (fieldCard : ℝ)) := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      ring
    _ < primitiveTraceMoebiusMainTerm
        groupOrder fieldCard fixedExponent := hdomination

/-- Uniform large-`orderOf(q²)` split endgame for the fixed first-to-second
frame.  The forty-point ordered exceptional loss is absorbed by applying the
numerical threshold to `coefficient + 40`. -/
theorem
    exists_threshold_actualSplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)) (u t : ZMod p)
          (q : (ZMod p)ˣ) (x : Point (ZMod p))
          (targetB targetC : ZMod p),
        IsSolution a x →
        x.x1 = u →
        t = orderedTrace a.multiplier a.a1 u →
        t = splitTorusTrace q →
        a.a2 ^ 2 ≠ 4 →
        targetB ^ 2 ≠ 4 →
        OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t →
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (q ^ 2) →
        ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
          orderedTrace a.multiplier a.a2
              (((rotation1 a)^[n]) x).x2 =
            splitTorusTrace v ∧
          orderOf v = Nat.card (ZMod p)ˣ ∧
            OrderedTraceCandidateRegular
              a.a2 targetB targetC (splitTorusTrace v) := by
  obtain ⟨inequalityThreshold, hInequality⟩ :=
    BGS.Markoff.exists_threshold_endgamePrimitiveTrace_explicitInequality_of_largeOrder
      (coefficient + 40) hdelta
  refine ⟨max inequalityThreshold 3, ?_⟩
  intro p hp _ a u t q x targetB targetC hx hx1 htrace heigen
    hA2 hTargetB hregular hlarge
  have hpInequality : inequalityThreshold ≤ p :=
    (Nat.le_max_left inequalityThreshold 3).trans hp
  have hpThree : 3 ≤ p :=
    (Nat.le_max_right inequalityThreshold 3).trans hp
  have hpTwo : p ≠ 2 := by omega
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  let orbitExponent :=
    Nat.card (ZMod p)ˣ / orderOf (q ^ 2)
  have hmul :
      orbitExponent * orderOf (q ^ 2) = p - 1 := by
    dsimp [orbitExponent]
    rw [Nat.div_mul_cancel (orderOf_dvd_natCard (q ^ 2)), hcard]
  have hexplicit :=
    hInequality p hpInequality orbitExponent (orderOf (q ^ 2))
      hmul hlarge
  have hexplicit' :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
            (((coefficient + 40 : ℕ) : ℝ) *
              Real.sqrt (p : ℝ)) < p := by
    simpa only [hcard] using hexplicit
  have hgroupPositive : 0 < Nat.card (ZMod p)ˣ := by
    rw [hcard]
    omega
  have hmargin :=
    error_add_forty_lt_primitiveMain_of_augmented_explicitInequality
      (Nat.card (ZMod p)ˣ) p orbitExponent coefficient
        hgroupPositive (by omega)
        (BGS.Markoff.complementaryExponent_pos (q ^ 2)) hexplicit'
  exact
    exists_iterate_actualSplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame
      p coefficient hWeil hpTwo a u t q x hx hx1 htrace heigen hA2
        targetB targetC hTargetB hregular
        (by simpa [orbitExponent] using hmargin)

/-- Uniform large-`orderOf(q²)` split endgame for the fixed second-to-first
frame.  The reverse ordered weights have the same invariant product, while
the forty-point numerical loss is again absorbed at `coefficient + 40`. -/
theorem
    exists_threshold_actualSplitPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)) (u t : ZMod p)
          (q : (ZMod p)ˣ) (x : Point (ZMod p))
          (targetB targetC : ZMod p),
        IsSolution a x →
        x.x2 = u →
        t = orderedTrace a.multiplier a.a2 u →
        t = splitTorusTrace q →
        a.a1 ^ 2 ≠ 4 →
        targetB ^ 2 ≠ 4 →
        OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t →
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (q ^ 2) →
        ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
          orderedTrace a.multiplier a.a1
              (((rotation2 a)^[n]) x).x1 =
            splitTorusTrace v ∧
          orderOf v = Nat.card (ZMod p)ˣ ∧
            OrderedTraceCandidateRegular
              a.a1 targetB targetC (splitTorusTrace v) := by
  obtain ⟨inequalityThreshold, hInequality⟩ :=
    BGS.Markoff.exists_threshold_endgamePrimitiveTrace_explicitInequality_of_largeOrder
      (coefficient + 40) hdelta
  refine ⟨max inequalityThreshold 3, ?_⟩
  intro p hp _ a u t q x targetB targetC hx hx2 htrace heigen
    hA1 hTargetB hregular hlarge
  have hpInequality : inequalityThreshold ≤ p :=
    (Nat.le_max_left inequalityThreshold 3).trans hp
  have hpThree : 3 ≤ p :=
    (Nat.le_max_right inequalityThreshold 3).trans hp
  have hpTwo : p ≠ 2 := by omega
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  let orbitExponent :=
    Nat.card (ZMod p)ˣ / orderOf (q ^ 2)
  have hmul :
      orbitExponent * orderOf (q ^ 2) = p - 1 := by
    dsimp [orbitExponent]
    rw [Nat.div_mul_cancel (orderOf_dvd_natCard (q ^ 2)), hcard]
  have hexplicit :=
    hInequality p hpInequality orbitExponent (orderOf (q ^ 2))
      hmul hlarge
  have hexplicit' :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
            (((coefficient + 40 : ℕ) : ℝ) *
              Real.sqrt (p : ℝ)) < p := by
    simpa only [hcard] using hexplicit
  have hgroupPositive : 0 < Nat.card (ZMod p)ˣ := by
    rw [hcard]
    omega
  have hmargin :=
    error_add_forty_lt_primitiveMain_of_augmented_explicitInequality
      (Nat.card (ZMod p)ˣ) p orbitExponent coefficient
        hgroupPositive (by omega)
        (BGS.Markoff.complementaryExponent_pos (q ^ 2)) hexplicit'
  exact
    exists_iterate_actualSplitPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame
      p coefficient hWeil hpTwo a u t q x hx hx2 htrace heigen hA1
        targetB targetC hTargetB hregular
        (by simpa [orbitExponent] using hmargin)

/-- Pointwise version of the first-to-second split endgame at the closed
analytic cutoff.  The hypotheses expose the only two numerical facts used:
`delta ≥ 1/32` and the augmented Weil coefficient is at most `1032`. -/
theorem
    actualSplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame_of_analyticCutoff
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : (1 : ℝ) / 32 ≤ delta)
    (hcoefficient : coefficient + 40 ≤ 1032)
    (p : ℕ) (hp : GenMarkoff.General.Explicit.analyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q : (ZMod p)ˣ) (x : Point (ZMod p))
    (targetB targetC : ZMod p)
    (hx : IsSolution a x) (hx1 : x.x1 = u)
    (htrace : t = orderedTrace a.multiplier a.a1 u)
    (heigen : t = splitTorusTrace q)
    (hA2 : a.a2 ^ 2 ≠ 4) (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t)
    (hlarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (q ^ 2)) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a2 (((rotation1 a)^[n]) x).x2 =
          splitTorusTrace v ∧
        orderOf v = Nat.card (ZMod p)ˣ ∧
          OrderedTraceCandidateRegular
            a.a2 targetB targetC (splitTorusTrace v) := by
  have hpThree : 3 ≤ p := by
    have := GenMarkoff.General.Explicit.five_le_analyticCutoff.trans hp
    omega
  have hpTwo : p ≠ 2 := by omega
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  let orbitExponent :=
    Nat.card (ZMod p)ˣ / orderOf (q ^ 2)
  have hmul :
      orbitExponent * orderOf (q ^ 2) = p - 1 := by
    dsimp [orbitExponent]
    rw [Nat.div_mul_cancel (orderOf_dvd_natCard (q ^ 2)), hcard]
  have hexplicit :=
    GenMarkoff.General.Explicit.primitiveTrace_explicitInequality_of_card_sub_one
      hp hmul hlarge hdelta hcoefficient
  have hexplicit' :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
            (((coefficient + 40 : ℕ) : ℝ) *
              Real.sqrt (p : ℝ)) < p := by
    simpa only [hcard] using hexplicit
  have hgroupPositive : 0 < Nat.card (ZMod p)ˣ := by
    rw [hcard]
    omega
  have hmargin :=
    error_add_forty_lt_primitiveMain_of_augmented_explicitInequality
      (Nat.card (ZMod p)ˣ) p orbitExponent coefficient
        hgroupPositive (by omega)
        (BGS.Markoff.complementaryExponent_pos (q ^ 2)) hexplicit'
  exact
    exists_iterate_actualSplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame
      p coefficient hWeil hpTwo a u t q x hx hx1 htrace heigen hA2
        targetB targetC hTargetB hregular
        (by simpa [orbitExponent] using hmargin)

/-- Pointwise reverse-frame companion to
`actualSplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame_of_analyticCutoff`. -/
theorem
    actualSplitPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame_of_analyticCutoff
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : (1 : ℝ) / 32 ≤ delta)
    (hcoefficient : coefficient + 40 ≤ 1032)
    (p : ℕ) (hp : GenMarkoff.General.Explicit.analyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q : (ZMod p)ˣ) (x : Point (ZMod p))
    (targetB targetC : ZMod p)
    (hx : IsSolution a x) (hx2 : x.x2 = u)
    (htrace : t = orderedTrace a.multiplier a.a2 u)
    (heigen : t = splitTorusTrace q)
    (hA1 : a.a1 ^ 2 ≠ 4) (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t)
    (hlarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (q ^ 2)) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a1 (((rotation2 a)^[n]) x).x1 =
          splitTorusTrace v ∧
        orderOf v = Nat.card (ZMod p)ˣ ∧
          OrderedTraceCandidateRegular
            a.a1 targetB targetC (splitTorusTrace v) := by
  have hpThree : 3 ≤ p := by
    have := GenMarkoff.General.Explicit.five_le_analyticCutoff.trans hp
    omega
  have hpTwo : p ≠ 2 := by omega
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  let orbitExponent :=
    Nat.card (ZMod p)ˣ / orderOf (q ^ 2)
  have hmul :
      orbitExponent * orderOf (q ^ 2) = p - 1 := by
    dsimp [orbitExponent]
    rw [Nat.div_mul_cancel (orderOf_dvd_natCard (q ^ 2)), hcard]
  have hexplicit :=
    GenMarkoff.General.Explicit.primitiveTrace_explicitInequality_of_card_sub_one
      hp hmul hlarge hdelta hcoefficient
  have hexplicit' :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
            (((coefficient + 40 : ℕ) : ℝ) *
              Real.sqrt (p : ℝ)) < p := by
    simpa only [hcard] using hexplicit
  have hgroupPositive : 0 < Nat.card (ZMod p)ˣ := by
    rw [hcard]
    omega
  have hmargin :=
    error_add_forty_lt_primitiveMain_of_augmented_explicitInequality
      (Nat.card (ZMod p)ˣ) p orbitExponent coefficient
        hgroupPositive (by omega)
        (BGS.Markoff.complementaryExponent_pos (q ^ 2)) hexplicit'
  exact
    exists_iterate_actualSplitPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame
      p coefficient hWeil hpTwo a u t q x hx hx2 htrace heigen hA1
        targetB targetC hTargetB hregular
        (by simpa [orbitExponent] using hmargin)

/-- Direction-indexed primitive split endgame with the exact outgoing
alternating regular frame.  The fixed coefficient triple `a` is unchanged in
both branches. -/
def alternatingPrimitiveSplitEndgameResult
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (direction : AlternatingDirectedAxis)
    (x : Point (ZMod p)) : Prop :=
  match direction with
  | .firstSecond =>
      ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
        orderedTrace a.multiplier a.a2
            (((rotation1 a)^[n]) x).x2 =
          splitTorusTrace v ∧
        orderOf v = Nat.card (ZMod p)ˣ ∧
          OrderedTraceCandidateRegular
            a.a2 a.a1 a.a3 (splitTorusTrace v)
  | .secondFirst =>
      ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
        orderedTrace a.multiplier a.a1
            (((rotation2 a)^[n]) x).x1 =
          splitTorusTrace v ∧
        orderOf v = Nat.card (ZMod p)ˣ ∧
          OrderedTraceCandidateRegular
            a.a1 a.a2 a.a3 (splitTorusTrace v)

/-- A uniform dispatcher for either alternating directed state.  Large
`orderOf(q²)` on the currently fixed split trace produces a primitive trace
in the exact outgoing alternating frame by iterating the corresponding
actual rotation. -/
theorem
    exists_threshold_alternatingRegularState_actualSplitPrimitiveEndgame
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)),
        a.a1 ^ 2 ≠ 4 →
        a.a2 ^ 2 ≠ 4 →
        ∀ (state : AlternatingRegularState a) (q : (ZMod p)ˣ),
          traceAt a state.direction.fixed state.point.1 =
              splitTorusTrace q →
          (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (q ^ 2) →
          alternatingPrimitiveSplitEndgameResult
            p a state.direction state.point.1 := by
  obtain ⟨forwardThreshold, hforward⟩ :=
    exists_threshold_actualSplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame
      coefficient hWeil hdelta
  obtain ⟨reverseThreshold, hreverse⟩ :=
    exists_threshold_actualSplitPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame
      coefficient hWeil hdelta
  refine ⟨max forwardThreshold reverseThreshold, ?_⟩
  intro p hp _ a hA1 hA2 state q heigen hlarge
  have hpForward : forwardThreshold ≤ p :=
    (Nat.le_max_left forwardThreshold reverseThreshold).trans hp
  have hpReverse : reverseThreshold ≤ p :=
    (Nat.le_max_right forwardThreshold reverseThreshold).trans hp
  rcases state with ⟨direction, point, hregular⟩
  cases direction with
  | firstSecond =>
      obtain ⟨n, v, hn, hvOrder, hvRegular⟩ :=
        hforward p hpForward
          a point.1.x1 (traceAt a .first point.1) q point.1
            a.a1 a.a3 point.2 rfl rfl
            (by
              simpa [AlternatingDirectedAxis.fixed] using heigen)
            hA2 hA1
            (by
              simpa [alternatingTraceRegular] using hregular)
            hlarge
      exact ⟨n, v, hn, hvOrder, hvRegular⟩
  | secondFirst =>
      obtain ⟨n, v, hn, hvOrder, hvRegular⟩ :=
        hreverse p hpReverse
          a point.1.x2 (traceAt a .second point.1) q point.1
            a.a2 a.a3 point.2 rfl rfl
            (by
              simpa [AlternatingDirectedAxis.fixed] using heigen)
            hA1 hA2
            (by
              simpa [alternatingTraceRegular] using hregular)
            hlarge
      exact ⟨n, v, hn, hvOrder, hvRegular⟩

/-- Explicit-cutoff dispatcher for either alternating split direction. -/
theorem alternatingRegularState_actualSplitPrimitiveEndgame_of_analyticCutoff
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : (1 : ℝ) / 32 ≤ delta)
    (hcoefficient : coefficient + 40 ≤ 1032)
    (p : ℕ) (hp : GenMarkoff.General.Explicit.analyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (state : AlternatingRegularState a) (q : (ZMod p)ˣ)
    (heigen :
      traceAt a state.direction.fixed state.point.1 = splitTorusTrace q)
    (hlarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (q ^ 2)) :
    alternatingPrimitiveSplitEndgameResult
      p a state.direction state.point.1 := by
  rcases state with ⟨direction, point, hregular⟩
  cases direction with
  | firstSecond =>
      exact
        actualSplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame_of_analyticCutoff
          coefficient hWeil hdelta hcoefficient p hp
          a point.1.x1 (traceAt a .first point.1) q point.1
          a.a1 a.a3 point.2 rfl rfl
          (by simpa [AlternatingDirectedAxis.fixed] using heigen)
          hA2 hA1
          (by simpa [alternatingTraceRegular] using hregular)
          hlarge
  | secondFirst =>
      exact
        actualSplitPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame_of_analyticCutoff
          coefficient hWeil hdelta hcoefficient p hp
          a point.1.x2 (traceAt a .second point.1) q point.1
          a.a2 a.a3 point.2 rfl rfl
          (by simpa [AlternatingDirectedAxis.fixed] using heigen)
          hA1 hA2
          (by simpa [alternatingTraceRegular] using hregular)
          hlarge

/-- Reasonable-cutoff version of the first-to-second split endgame.  The
three-quarter source scale supplies `delta ≥ 1/4`. -/
theorem
    actualSplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame_of_reasonableCutoff
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : (1 : ℝ) / 4 ≤ delta)
    (hcoefficient : coefficient + 40 ≤ 1032)
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q : (ZMod p)ˣ) (x : Point (ZMod p))
    (targetB targetC : ZMod p)
    (hx : IsSolution a x) (hx1 : x.x1 = u)
    (htrace : t = orderedTrace a.multiplier a.a1 u)
    (heigen : t = splitTorusTrace q)
    (hA2 : a.a2 ^ 2 ≠ 4) (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t)
    (hlarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (q ^ 2)) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a2 (((rotation1 a)^[n]) x).x2 =
          splitTorusTrace v ∧
        orderOf v = Nat.card (ZMod p)ˣ ∧
          OrderedTraceCandidateRegular
            a.a2 targetB targetC (splitTorusTrace v) := by
  have hpThree : 3 ≤ p := by
    have :=
      GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans hp
    omega
  have hpTwo : p ≠ 2 := by omega
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  let orbitExponent :=
    Nat.card (ZMod p)ˣ / orderOf (q ^ 2)
  have hmul :
      orbitExponent * orderOf (q ^ 2) = p - 1 := by
    dsimp [orbitExponent]
    rw [Nat.div_mul_cancel (orderOf_dvd_natCard (q ^ 2)), hcard]
  have hexplicit :=
    GenMarkoff.General.Explicit.reasonable_primitiveTrace_explicitInequality_of_card_sub_one
      hp hmul hlarge hdelta hcoefficient
  have hexplicit' :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
            (((coefficient + 40 : ℕ) : ℝ) *
              Real.sqrt (p : ℝ)) < p := by
    simpa only [hcard] using hexplicit
  have hgroupPositive : 0 < Nat.card (ZMod p)ˣ := by
    rw [hcard]
    omega
  have hmargin :=
    error_add_forty_lt_primitiveMain_of_augmented_explicitInequality
      (Nat.card (ZMod p)ˣ) p orbitExponent coefficient
        hgroupPositive (by omega)
        (BGS.Markoff.complementaryExponent_pos (q ^ 2)) hexplicit'
  exact
    exists_iterate_actualSplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame
      p coefficient hWeil hpTwo a u t q x hx hx1 htrace heigen hA2
        targetB targetC hTargetB hregular
        (by simpa [orbitExponent] using hmargin)

/-- Reverse-frame companion at the reasonable cutoff. -/
theorem
    actualSplitPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame_of_reasonableCutoff
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : (1 : ℝ) / 4 ≤ delta)
    (hcoefficient : coefficient + 40 ≤ 1032)
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q : (ZMod p)ˣ) (x : Point (ZMod p))
    (targetB targetC : ZMod p)
    (hx : IsSolution a x) (hx2 : x.x2 = u)
    (htrace : t = orderedTrace a.multiplier a.a2 u)
    (heigen : t = splitTorusTrace q)
    (hA1 : a.a1 ^ 2 ≠ 4) (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t)
    (hlarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (q ^ 2)) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a1 (((rotation2 a)^[n]) x).x1 =
          splitTorusTrace v ∧
        orderOf v = Nat.card (ZMod p)ˣ ∧
          OrderedTraceCandidateRegular
            a.a1 targetB targetC (splitTorusTrace v) := by
  have hpThree : 3 ≤ p := by
    have :=
      GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans hp
    omega
  have hpTwo : p ≠ 2 := by omega
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  let orbitExponent :=
    Nat.card (ZMod p)ˣ / orderOf (q ^ 2)
  have hmul :
      orbitExponent * orderOf (q ^ 2) = p - 1 := by
    dsimp [orbitExponent]
    rw [Nat.div_mul_cancel (orderOf_dvd_natCard (q ^ 2)), hcard]
  have hexplicit :=
    GenMarkoff.General.Explicit.reasonable_primitiveTrace_explicitInequality_of_card_sub_one
      hp hmul hlarge hdelta hcoefficient
  have hexplicit' :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
            (((coefficient + 40 : ℕ) : ℝ) *
              Real.sqrt (p : ℝ)) < p := by
    simpa only [hcard] using hexplicit
  have hgroupPositive : 0 < Nat.card (ZMod p)ˣ := by
    rw [hcard]
    omega
  have hmargin :=
    error_add_forty_lt_primitiveMain_of_augmented_explicitInequality
      (Nat.card (ZMod p)ˣ) p orbitExponent coefficient
        hgroupPositive (by omega)
        (BGS.Markoff.complementaryExponent_pos (q ^ 2)) hexplicit'
  exact
    exists_iterate_actualSplitPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame
      p coefficient hWeil hpTwo a u t q x hx hx2 htrace heigen hA1
        targetB targetC hTargetB hregular
        (by simpa [orbitExponent] using hmargin)

/-- Reasonable-cutoff dispatcher for either alternating split direction. -/
theorem alternatingRegularState_actualSplitPrimitiveEndgame_of_reasonableCutoff
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : (1 : ℝ) / 4 ≤ delta)
    (hcoefficient : coefficient + 40 ≤ 1032)
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (state : AlternatingRegularState a) (q : (ZMod p)ˣ)
    (heigen :
      traceAt a state.direction.fixed state.point.1 = splitTorusTrace q)
    (hlarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (q ^ 2)) :
    alternatingPrimitiveSplitEndgameResult
      p a state.direction state.point.1 := by
  rcases state with ⟨direction, point, hregular⟩
  cases direction with
  | firstSecond =>
      exact
        actualSplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame_of_reasonableCutoff
          coefficient hWeil hdelta hcoefficient p hp
          a point.1.x1 (traceAt a .first point.1) q point.1
          a.a1 a.a3 point.2 rfl rfl
          (by simpa [AlternatingDirectedAxis.fixed] using heigen)
          hA2 hA1
          (by simpa [alternatingTraceRegular] using hregular)
          hlarge
  | secondFirst =>
      exact
        actualSplitPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame_of_reasonableCutoff
          coefficient hWeil hdelta hcoefficient p hp
          a point.1.x2 (traceAt a .second point.1) q point.1
          a.a2 a.a3 point.2 rfl rfl
          (by simpa [AlternatingDirectedAxis.fixed] using heigen)
          hA1 hA2
          (by simpa [alternatingTraceRegular] using hregular)
          hlarge

end

end GenMarkoff.General.Endgame
