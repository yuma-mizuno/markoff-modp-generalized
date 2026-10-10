import GenMarkoff.General.Axis
import GenMarkoff.General.MiddleGame.ParityClosedOrderEscape
import GenMarkoff.General.MiddleGame.DirectedOrderGrowth
import GenMarkoff.Core.Statements
import GenMarkoff.TraceCurve.ExceptionalRouting
import GenMarkoff.ShiftedTrace.MiddleGame.ActualOrderEscape
import BGS.Dynamics.StrictMeasureEscape

/-!
# Regular middle-game iteration for a fixed coefficient triple

A directed middle-game move starts from a point whose fixed trace is
candidate regular and moves along a fiber to a point whose next trace has
strictly larger actual rotation order.  This module adds candidate
regularity of the target trace in a prescribed ordered frame: a single
square-coset parameter avoids both the parity-closed bad-order support and
the at most twenty parameters at which the ordered safe polynomial vanishes
(`exists_iterate_with_larger_actualOrder_and_regular_of_squareCosetTrace`).

The surface iteration alternates the directed choices `.firstSecond`
(along `rotation1`, from the first to the second axis) and `.secondFirst`
(along `rotation2`, back to the first axis), packaged as
`AlternatingRegularState`.  Each move returns exactly the ordered regularity
required by the reverse move.  The main result,
`exists_sameRotationComponent_alternatingRegularState_reaches_threshold`,
reaches any actual-order target for which the endgame upper bound and the
regular-escape margin hold from the starting order up to the target.  The
coefficient triple is fixed throughout; no coordinate permutation is used.
-/

namespace GenMarkoff.General.Assembly

open Filter BGS.Markoff
open GenMarkoff.General.MiddleGame
open GenMarkoff.ShiftedTrace.MiddleGame
open Polynomial

noncomputable section

/-- Current square-coset parameters whose shifted target trace is not
candidate regular in the ordered frame `(A,B,C)`. -/
def shiftedWeightedOrderedUnsafeTraceSupport
    {E : Type} [Field E] [Fintype E]
    (A B C alpha beta gamma : E) (H1 : Subgroup Eˣ) :
    Finset H1 := by
  classical
  exact Finset.univ.filter fun h ↦
    eval (weightedSplitTorusTrace alpha beta h + gamma)
      (orderedTraceSafePolynomial A B C) = 0

@[simp]
theorem mem_shiftedWeightedOrderedUnsafeTraceSupport_iff
    {E : Type} [Field E] [Fintype E]
    {A B C alpha beta gamma : E} {H1 : Subgroup Eˣ} {h : H1} :
    h ∈ shiftedWeightedOrderedUnsafeTraceSupport
        A B C alpha beta gamma H1 ↔
      eval (weightedSplitTorusTrace alpha beta h + gamma)
        (orderedTraceSafePolynomial A B C) = 0 := by
  classical
  simp [shiftedWeightedOrderedUnsafeTraceSupport]

/-- At most twenty elements of the current square coset have a shifted
target trace that is not candidate regular in the ordered frame `(A,B,C)`:
the ordered safe polynomial has at most ten roots, and each trace value is
attained by at most two parameters. -/
theorem shiftedWeightedOrderedUnsafeTraceSupport_card_le_twenty
    {E : Type} [Field E] [Fintype E]
    (A B C alpha beta gamma : E) (H1 : Subgroup Eˣ)
    (h2 : (2 : E) ≠ 0) (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4)
    (halpha : alpha ≠ 0) :
    (shiftedWeightedOrderedUnsafeTraceSupport
      A B C alpha beta gamma H1).card ≤ 20 := by
  classical
  let traceValue : H1 → E :=
    fun h ↦ weightedSplitTorusTrace alpha beta h + gamma
  have hfiber :
      ∀ target,
        ((Finset.univ : Finset H1).filter
          fun h ↦ traceValue h = target).card ≤ 2 := by
    intro target
    simpa [traceValue, shiftedWeightedTraceValueFiber] using
      shiftedWeightedTraceValueFiber_card_le_two
        alpha beta gamma H1 target halpha
  simpa [shiftedWeightedOrderedUnsafeTraceSupport, traceValue] using
    card_orderedTraceSafePolynomial_zero_le_twenty
      A B C (Finset.univ : Finset H1) traceValue h2 hA hB hfiber

/-- Avoid the parity-closed bad-order support and the ordered exceptional
trace support with one and the same square-coset parameter. -/
theorem
    exists_left_element_escaping_shiftedParityClosedOrders_and_regular
    {E : Type} [Field E] [Fintype E]
    (A B C alpha beta gamma : E) (H1 : Subgroup Eˣ)
    (orders : Finset ℕ) (rightSubgroup : ℕ → Subgroup Eˣ)
    (h2 : (2 : E) ≠ 0) (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4)
    (halpha : alpha ≠ 0)
    (hsmall :
      (shiftedWeightedBadOrderTraceSupport
          alpha beta gamma H1 orders rightSubgroup).card +
        20 < Nat.card H1) :
    ∃ h1 : H1,
      OrderedTraceCandidateRegular A B C
          (weightedSplitTorusTrace alpha beta h1 + gamma) ∧
        ∀ d ∈ orders, ∀ h2 : rightSubgroup d,
          weightedSplitTorusTrace alpha beta h1 + gamma ≠
            splitTorusTrace h2 := by
  classical
  let bad :=
    shiftedWeightedBadOrderTraceSupport
      alpha beta gamma H1 orders rightSubgroup
  let unsafeSet :=
    shiftedWeightedOrderedUnsafeTraceSupport
      A B C alpha beta gamma H1
  have hunsafe : unsafeSet.card ≤ 20 := by
    simpa [unsafeSet] using
      shiftedWeightedOrderedUnsafeTraceSupport_card_le_twenty
        A B C alpha beta gamma H1 h2 hA hB halpha
  have hunion :
      (bad ∪ unsafeSet).card < Nat.card H1 := by
    calc
      (bad ∪ unsafeSet).card ≤ bad.card + unsafeSet.card :=
        Finset.card_union_le _ _
      _ ≤ bad.card + 20 := Nat.add_le_add_left hunsafe _
      _ < Nat.card H1 := by simpa [bad] using hsmall
  have hexists : ∃ h1 : H1, h1 ∉ bad ∪ unsafeSet := by
    by_contra hall
    push Not at hall
    have hle : (Finset.univ : Finset H1).card ≤
        (bad ∪ unsafeSet).card :=
      Finset.card_le_card fun h _ ↦ hall h
    rw [Finset.card_univ, Fintype.card_eq_nat_card] at hle
    exact (Nat.not_le_of_lt hunion) hle
  obtain ⟨h1, hh1⟩ := hexists
  have hnotBad : h1 ∉ bad :=
    fun hmem ↦ hh1 (Finset.mem_union_left _ hmem)
  have hnotUnsafe : h1 ∉ unsafeSet :=
    fun hmem ↦ hh1 (Finset.mem_union_right _ hmem)
  refine ⟨h1, ?_, ?_⟩
  · apply
      (orderedTraceSafePolynomial_eval_ne_zero_iff
        A B C _).mp
    simpa [unsafeSet] using hnotUnsafe
  · intro d hd hright heq
    apply hnotBad
    exact mem_shiftedWeightedBadOrderTraceSupport_iff.mpr
      ⟨d, hd, hright, heq⟩

/-- Assume the Corvaja--Zannier bound for every parity-closed candidate
order and the margin `2 T E + 20 < Nat.card H1`, where `T` is the
simultaneous divisor count of `p - 1` and `p + 1` and `E` the current-order
envelope.  Then some square-coset parameter gives a shifted trace that is
candidate regular in `(A,B,C)` and avoids every parity-closed bad order. -/
theorem
    exists_left_element_escaping_shiftedParityClosedOrders_and_regular_of_estimate
    {E : Type} [Field E] [Fintype E]
    (p : ℕ) (A B C alpha beta gamma : E) (H1 : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ)
    (h2 : (2 : E) ≠ 0) (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4)
    (halpha : alpha ≠ 0)
    (hrightOrder :
      ∀ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
        Nat.card (rightSubgroup d) = d)
    (hCZ :
      ∀ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
        ((shiftedWeightedTraceEquationSolutions
          alpha beta gamma H1 (rightSubgroup d)).card : ℝ) ≤
            corvajaZannierTraceUpperBound p (Nat.card H1)
              (Nat.card (rightSubgroup d)))
    (hmargin :
      2 *
          (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p (Nat.card H1) +
          20 <
        (Nat.card H1 : ℝ)) :
    ∃ h1 : H1,
      OrderedTraceCandidateRegular A B C
          (weightedSplitTorusTrace alpha beta h1 + gamma) ∧
        ∀ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
          ∀ h2 : rightSubgroup d,
            weightedSplitTorusTrace alpha beta h1 + gamma ≠
              splitTorusTrace h2 := by
  classical
  -- Bound the bad-order support by the doubled divisor envelope.
  have hCZIndexed :
      ∀ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
        ((shiftedWeightedTraceEquationSolutions
          alpha beta gamma H1 (rightSubgroup d)).card : ℝ) ≤
            corvajaZannierTraceUpperBound p (Nat.card H1) d := by
    intro d hd
    have hEstimate := hCZ d hd
    rw [hrightOrder d hd] at hEstimate
    exact hEstimate
  have hbad :
      ((shiftedWeightedBadOrderTraceSupport
        alpha beta gamma H1
          (parityClosedMiddleGameCandidateOrders p (Nat.card H1))
          rightSubgroup).card : ℝ) ≤
        2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p (Nat.card H1) := by
    calc
      ((shiftedWeightedBadOrderTraceSupport
        alpha beta gamma H1
          (parityClosedMiddleGameCandidateOrders p (Nat.card H1))
          rightSubgroup).card : ℝ) ≤
          ∑ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
            corvajaZannierTraceUpperBound p (Nat.card H1) d := by
        exact
          shiftedWeightedBadOrderTraceSupport_card_cast_le_sum
            (E := E) (alpha := alpha) (beta := beta) (gamma := gamma)
            (H1 := H1)
            (orders :=
              parityClosedMiddleGameCandidateOrders p (Nat.card H1))
            (rightSubgroup := rightSubgroup)
            (bound :=
              fun d ↦ corvajaZannierTraceUpperBound
                p (Nat.card H1) d)
            hCZIndexed
      _ ≤
          2 *
            (((p - 1).divisors.card +
              (p + 1).divisors.card : ℕ) : ℝ) *
              corvajaZannierCurrentOrderEnvelope p (Nat.card H1) :=
        parityClosedCorvajaZannierSum_le_two_mul_divisorCount_mul_envelope
          p (Nat.card H1)
  -- Add the twenty unsafe parameters and apply the counting lemma.
  have hsmallReal :
      (((shiftedWeightedBadOrderTraceSupport
        alpha beta gamma H1
          (parityClosedMiddleGameCandidateOrders p (Nat.card H1))
          rightSubgroup).card + 20 : ℕ) : ℝ) <
        (Nat.card H1 : ℝ) := by
    calc
      (((shiftedWeightedBadOrderTraceSupport
        alpha beta gamma H1
          (parityClosedMiddleGameCandidateOrders p (Nat.card H1))
          rightSubgroup).card + 20 : ℕ) : ℝ) =
          ((shiftedWeightedBadOrderTraceSupport
            alpha beta gamma H1
              (parityClosedMiddleGameCandidateOrders p (Nat.card H1))
              rightSubgroup).card : ℝ) + 20 := by norm_num
      _ ≤
          2 *
              (((p - 1).divisors.card +
                (p + 1).divisors.card : ℕ) : ℝ) *
                corvajaZannierCurrentOrderEnvelope p (Nat.card H1) +
            20 := by
        linarith
      _ < (Nat.card H1 : ℝ) := hmargin
  have hsmall :
      (shiftedWeightedBadOrderTraceSupport
        alpha beta gamma H1
          (parityClosedMiddleGameCandidateOrders p (Nat.card H1))
          rightSubgroup).card + 20 <
        Nat.card H1 := by
    exact_mod_cast hsmallReal
  exact
    exists_left_element_escaping_shiftedParityClosedOrders_and_regular
      A B C alpha beta gamma H1
        (parityClosedMiddleGameCandidateOrders p (Nat.card H1))
        rightSubgroup h2 hA hB halpha hsmall

/-- Axis-independent simultaneous regularity and strict actual-order growth.

Let `t` be a nonparabolic trace with eigenvalue `q` and actual order below
`p ^ (1/2 + delta)`, satisfying the regular-escape margin.  If every element
of `zpowers (q ^ 2)` gives a shifted trace `alpha h + beta h⁻¹ + gamma` that
is attained as `targetTrace` along some iterate of `rotation`, then some
iterate has a target trace that is candidate regular in the frame `(A,B,C)`
and of strictly larger actual order than `t`.  The target frame may differ
from the current fiber frame. -/
theorem
    exists_iterate_with_larger_actualOrder_and_regular_of_squareCosetTrace
    {T : Type*}
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (t : ZMod p) (hD : discriminant t ≠ 0)
    (q : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (rotation : T → T) (x : T) (targetTrace : T → ZMod p)
    (A B C : ZMod p) (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4)
    (alpha beta gamma : quadraticFiniteField p)
    (hsigma : alpha * beta ≠ 0)
    (hEven : shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0)
    (hreachable :
      ∀ h : Subgroup.zpowers (q ^ 2),
        ∃ n : ℕ,
          weightedSplitTorusTrace alpha beta h + gamma =
            algebraMap (ZMod p) (quadraticFiniteField p)
              (targetTrace (((rotation)^[n]) x)))
    (hbelowEndgame :
      (rotationLinearOrder t : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hmargin :
      2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p
              (rotationLinearOrder t) +
          20 <
        (rotationLinearOrder t : ℝ)) :
    ∃ n : ℕ,
      let t' := targetTrace (((rotation)^[n]) x)
      OrderedTraceCandidateRegular A B C t' ∧
        rotationLinearOrder t < rotationLinearOrder t' := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let H1 : Subgroup Eˣ := Subgroup.zpowers (q ^ 2)
  let rightSubgroup : ℕ → Subgroup Eˣ :=
    fun d ↦ middleGameRightSubgroup p d
  letI : DecidableEq E := Classical.decEq E
  -- Choose a square-coset parameter `h` escaping the bad orders and the
  -- unsafe traces, using the Corvaja--Zannier count for each candidate order.
  have hleftCard :
      Nat.card H1 = rotationLinearOrder t := by
    simpa [H1, E] using
      card_zpowers_sq_eq_rotationLinearOrder_of_discriminant_ne_zero
        p t q hD heigen
  have hrightOrder :
      ∀ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
        Nat.card (rightSubgroup d) = d := by
    intro d hd
    exact
      middleGameRightSubgroup_natCard p (2 * Nat.card H1) d
        (mem_middleGameCandidateOrders_two_mul_of_mem_parityClosed hd)
  have hCZ :
      ∀ d ∈ parityClosedMiddleGameCandidateOrders p (Nat.card H1),
        ((shiftedWeightedTraceEquationSolutions
          alpha beta gamma H1 (rightSubgroup d)).card : ℝ) ≤
            corvajaZannierTraceUpperBound p (Nat.card H1)
              (Nat.card (rightSubgroup d)) := by
    intro d _hd
    exact
      weightedShiftedTraceEquationSolutions_card_cast_le_corvajaZannier
        p E alpha beta gamma H1 (rightSubgroup d)
          hpTwo hsigma hEven
  have htwo : (2 : E) ≠ 0 := by
    have hfour : (4 : E) ≠ 0 :=
      four_ne_zero_quadraticFiniteField_of_prime_ne_two p hpTwo
    intro hzero
    apply hfour
    calc
      (4 : E) = 2 * 2 := by norm_num
      _ = 0 := by rw [hzero, zero_mul]
  have hAE : (f A) ^ 2 ≠ 4 := by
    intro hzero
    apply hA
    apply f.injective
    simpa [map_ofNat] using hzero
  have hBE : (f B) ^ 2 ≠ 4 := by
    intro hzero
    apply hB
    apply f.injective
    simpa [map_ofNat] using hzero
  have halpha : alpha ≠ 0 := (mul_ne_zero_iff.mp hsigma).1
  obtain ⟨h, hregularE, hEscapes⟩ :=
    exists_left_element_escaping_shiftedParityClosedOrders_and_regular_of_estimate
      p (f A) (f B) (f C) alpha beta gamma H1 rightSubgroup
        htwo hAE hBE halpha hrightOrder hCZ
        (by rw [hleftCard]; exact hmargin)
  -- The iterate reaching `h` has a candidate-regular target trace `t'`.
  obtain ⟨n, hyTrace⟩ := hreachable h
  let t' : ZMod p := targetTrace (((rotation)^[n]) x)
  have hregularBase : OrderedTraceCandidateRegular A B C t' := by
    apply
      GenMarkoff.General.MiddleGame.orderedTraceCandidateRegular_of_map f
    rw [← hyTrace]
    exact hregularE
  refine ⟨n, hregularBase, ?_⟩
  -- The statement's `let`-bound target trace is the local `t'`; restate the
  -- goal with `t'` so that the hypotheses below mention the same term.
  change rotationLinearOrder t < rotationLinearOrder t'
  -- Growth: if `t'` had actual order at most that of `t`, its order would be
  -- a parity-closed candidate order (`t'` is not parabolic, since a
  -- parabolic trace has order `p`), contradicting the choice of `h`.
  by_contra hgrowth
  have htargetLe :
      rotationLinearOrder t' ≤ rotationLinearOrder t :=
    Nat.le_of_not_gt hgrowth
  have hnonparabolic : t' ^ 2 ≠ 4 := by
    intro hparabolic
    have htarget :
        rotationLinearOrder t' = p :=
      rotationLinearOrder_eq_prime_of_parabolicTrace
        p hpTwo t' hparabolic
    have hthreshold :=
      endgamePowerThreshold_le_prime p delta hdelta
    have htargetLeReal :
        (p : ℝ) ≤ (rotationLinearOrder t : ℝ) := by
      calc
        (p : ℝ) = (rotationLinearOrder t' : ℝ) := by
          exact_mod_cast htarget.symm
        _ ≤ (rotationLinearOrder t : ℝ) := by
          exact_mod_cast htargetLe
    exact
      (not_le_of_gt hbelowEndgame)
        (hthreshold.trans htargetLeReal)
  have hd :
      BGS.Markoff.rotationOrder t' ∈
        parityClosedMiddleGameCandidateOrders p (Nat.card H1) := by
    simpa only [hleftCard] using
      rotationOrder_mem_parityClosedCandidates_of_nonparabolic_actualOrder_le
        p (rotationLinearOrder t) hpTwo t' hnonparabolic htargetLe
  obtain ⟨h2, htrace2⟩ :=
    exists_middleGameRightSubgroup_trace_of_nonparabolic_rotationOrder
      p (BGS.Markoff.rotationOrder t') hpTwo t' hnonparabolic rfl
  apply hEscapes (BGS.Markoff.rotationOrder t') hd h2
  exact hyTrace.trans htrace2

/-- The centered product is symmetric in the two moving coefficients even
though the affine center and the directed target trace are ordered. -/
theorem centeredFiberProduct_swap
    {K : Type*} [Field K] (B C u t : K) :
    centeredFiberProduct B C u t =
      centeredFiberProduct C B u t := by
  simp only [centeredFiberProduct, centeredNorm, discriminant]
  congr 2
  ring

/-- A nonparabolic first-coordinate fiber with nonzero centered product has
an actual diagonalization over the canonical quadratic finite field. -/
theorem exists_axisOne_actualFiber_diagonalization
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hx1 : x.x1 = u)
    (htrace : t = orderedTrace a.multiplier a.a1 u)
    (hD : discriminant t ≠ 0)
    (hproduct : centeredFiberProduct a.a2 a.a3 u t ≠ 0) :
    ∃ q r : (quadraticFiniteField p)ˣ,
      algebraMap (ZMod p) (quadraticFiniteField p) t =
          splitTorusTrace q ∧
        Point.map (algebraMap (ZMod p) (quadraticFiniteField p)) x =
          fiberPoint1
            (Coefficients.map
              (algebraMap (ZMod p) (quadraticFiniteField p)) a)
            (algebraMap (ZMod p) (quadraticFiniteField p) u)
            (algebraMap (ZMod p) (quadraticFiniteField p) t)
            (q : quadraticFiniteField p)
            (r : quadraticFiniteField p) := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := Coefficients.map f a
  let uE : E := f u
  let tE : E := f t
  let xE : Point E := Point.map f x
  -- Transport the fiber conic and its nondegeneracy to the quadratic field.
  have hnonparabolic : t ^ 2 ≠ 4 := by
    exact sub_ne_zero.mp (by simpa [discriminant] using hD)
  have hDE : discriminant tE ≠ 0 := by
    simpa [tE, discriminant, map_ofNat] using
      (_root_.map_ne_zero (f := f)).mpr hD
  have hproductE :
      centeredFiberProduct aE.a2 aE.a3 uE tE ≠ 0 := by
    simpa [aE, uE, tE, centeredFiberProduct, centeredNorm,
      discriminant, map_ofNat] using
        (_root_.map_ne_zero (f := f)).mpr hproduct
  have hconic :
      fiberConic a.a2 a.a3 u t x.x2 x.x3 = 0 := by
    rw [htrace]
    rw [← polynomial_fixed_first a u x.x2 x.x3]
    rw [← hx1]
    exact hx
  have hconicE :
      fiberConic aE.a2 aE.a3 uE tE xE.x2 xE.x3 = 0 := by
    have hmap := congrArg f hconic
    simpa [aE, uE, tE, xE, Point.map, Coefficients.map, fiberConic,
      map_ofNat] using hmap
  -- The eigenvalue is a split unit or a norm-one unit; in either case
  -- `exists_unit_fiberPair_eq` gives the fiber parameter `r`.
  rcases exists_split_or_quadraticNormOneTrace p hpTwo t hnonparabolic with
    ⟨w, htraceW, _hw⟩ | ⟨w, htraceW, _hw⟩
  · let embedding : (ZMod p)ˣ →* Eˣ := Units.map f.toMonoidHom
    let q : Eˣ := embedding w
    have heigen : tE = splitTorusTrace q := by
      dsimp [tE]
      rw [← htraceW]
      -- Unfold the local `q` to `embedding w` (the image of `w` under
      -- `Units.map f`); after unfolding `splitTorusTrace` and `map_add` the
      -- two sides agree by `rfl`.
      change f (splitTorusTrace w) = splitTorusTrace (embedding w)
      rw [splitTorusTrace, splitTorusTrace, map_add]
      rfl
    obtain ⟨r, hr⟩ :=
      exists_unit_fiberPair_eq
        aE.a2 aE.a3 uE tE q (xE.x2, xE.x3)
          hconicE heigen hDE hproductE
    refine ⟨q, r, heigen, ?_⟩
    -- Fold `Point.map f x`, `Coefficients.map f a`, `f u`, `f t` into the
    -- local names `xE`, `aE`, `uE`, `tE` used by `hr` and the `simpa`s below.
    change xE = fiberPoint1 aE uE tE (q : E) (r : E)
    apply Point.ext
    · simpa [xE, uE, Point.map] using congrArg f hx1
    · simpa [fiberPoint1] using congrArg Prod.fst hr.symm
    · simpa [fiberPoint1] using congrArg Prod.snd hr.symm
  · let q : Eˣ := (w : (quadraticFiniteField p)ˣ)
    have heigen : tE = splitTorusTrace q := by
      dsimp [tE, f]
      rw [← htraceW]
      exact algebraMap_quadraticNormOneTrace p w
    obtain ⟨r, hr⟩ :=
      exists_unit_fiberPair_eq
        aE.a2 aE.a3 uE tE q (xE.x2, xE.x3)
          hconicE heigen hDE hproductE
    refine ⟨q, r, heigen, ?_⟩
    -- Fold `Point.map f x`, `Coefficients.map f a`, `f u`, `f t` into the
    -- local names `xE`, `aE`, `uE`, `tE` used by `hr` and the `simpa`s below.
    change xE = fiberPoint1 aE uE tE (q : E) (r : E)
    apply Point.ext
    · simpa [xE, uE, Point.map] using congrArg f hx1
    · simpa [fiberPoint1] using congrArg Prod.fst hr.symm
    · simpa [fiberPoint1] using congrArg Prod.snd hr.symm

/-- A nonparabolic second-coordinate fiber with nonzero centered product has
an actual diagonalization, in the fixed moving order `(x₃,x₁)`. -/
theorem exists_axisTwo_actualFiber_diagonalization
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hx2 : x.x2 = u)
    (htrace : t = orderedTrace a.multiplier a.a2 u)
    (hD : discriminant t ≠ 0)
    (hproduct : centeredFiberProduct a.a3 a.a1 u t ≠ 0) :
    ∃ q r : (quadraticFiniteField p)ˣ,
      algebraMap (ZMod p) (quadraticFiniteField p) t =
          splitTorusTrace q ∧
        Point.map (algebraMap (ZMod p) (quadraticFiniteField p)) x =
          fiberPoint2
            (Coefficients.map
              (algebraMap (ZMod p) (quadraticFiniteField p)) a)
            (algebraMap (ZMod p) (quadraticFiniteField p) u)
            (algebraMap (ZMod p) (quadraticFiniteField p) t)
            (q : quadraticFiniteField p)
            (r : quadraticFiniteField p) := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := Coefficients.map f a
  let uE : E := f u
  let tE : E := f t
  let xE : Point E := Point.map f x
  -- Transport the fiber conic and its nondegeneracy to the quadratic field.
  have hnonparabolic : t ^ 2 ≠ 4 := by
    exact sub_ne_zero.mp (by simpa [discriminant] using hD)
  have hDE : discriminant tE ≠ 0 := by
    simpa [tE, discriminant, map_ofNat] using
      (_root_.map_ne_zero (f := f)).mpr hD
  have hproductE :
      centeredFiberProduct aE.a3 aE.a1 uE tE ≠ 0 := by
    simpa [aE, uE, tE, centeredFiberProduct, centeredNorm,
      discriminant, map_ofNat] using
        (_root_.map_ne_zero (f := f)).mpr hproduct
  have hconic :
      fiberConic a.a3 a.a1 u t x.x3 x.x1 = 0 := by
    rw [htrace]
    rw [← polynomial_fixed_second a u x.x3 x.x1]
    rw [← hx2]
    exact hx
  have hconicE :
      fiberConic aE.a3 aE.a1 uE tE xE.x3 xE.x1 = 0 := by
    have hmap := congrArg f hconic
    simpa [aE, uE, tE, xE, Point.map, Coefficients.map, fiberConic,
      map_ofNat] using hmap
  -- The eigenvalue is a split unit or a norm-one unit; in either case
  -- `exists_unit_fiberPair_eq` gives the fiber parameter `r`.
  rcases exists_split_or_quadraticNormOneTrace p hpTwo t hnonparabolic with
    ⟨w, htraceW, _hw⟩ | ⟨w, htraceW, _hw⟩
  · let embedding : (ZMod p)ˣ →* Eˣ := Units.map f.toMonoidHom
    let q : Eˣ := embedding w
    have heigen : tE = splitTorusTrace q := by
      dsimp [tE]
      rw [← htraceW]
      -- Unfold the local `q` to `embedding w` (the image of `w` under
      -- `Units.map f`); after unfolding `splitTorusTrace` and `map_add` the
      -- two sides agree by `rfl`.
      change f (splitTorusTrace w) = splitTorusTrace (embedding w)
      rw [splitTorusTrace, splitTorusTrace, map_add]
      rfl
    obtain ⟨r, hr⟩ :=
      exists_unit_fiberPair_eq
        aE.a3 aE.a1 uE tE q (xE.x3, xE.x1)
          hconicE heigen hDE hproductE
    refine ⟨q, r, heigen, ?_⟩
    -- Fold `Point.map f x`, `Coefficients.map f a`, `f u`, `f t` into the
    -- local names `xE`, `aE`, `uE`, `tE` used by `hr` and the `simpa`s below.
    change xE = fiberPoint2 aE uE tE (q : E) (r : E)
    apply Point.ext
    · simpa [fiberPoint2] using congrArg Prod.snd hr.symm
    · simpa [xE, uE, Point.map] using congrArg f hx2
    · simpa [fiberPoint2] using congrArg Prod.fst hr.symm
  · let q : Eˣ := (w : (quadraticFiniteField p)ˣ)
    have heigen : tE = splitTorusTrace q := by
      dsimp [tE, f]
      rw [← htraceW]
      exact algebraMap_quadraticNormOneTrace p w
    obtain ⟨r, hr⟩ :=
      exists_unit_fiberPair_eq
        aE.a3 aE.a1 uE tE q (xE.x3, xE.x1)
          hconicE heigen hDE hproductE
    refine ⟨q, r, heigen, ?_⟩
    -- Fold `Point.map f x`, `Coefficients.map f a`, `f u`, `f t` into the
    -- local names `xE`, `aE`, `uE`, `tE` used by `hr` and the `simpa`s below.
    change xE = fiberPoint2 aE uE tE (q : E) (r : E)
    apply Point.ext
    · simpa [fiberPoint2] using congrArg Prod.snd hr.symm
    · simpa [xE, uE, Point.map] using congrArg f hx2
    · simpa [fiberPoint2] using congrArg Prod.fst hr.symm

/-- The first-to-second directed surface step on a diagonalized first-axis
fiber: some `rotation1` iterate has a second trace of strictly larger actual
order that is candidate regular in the target frame `(a₂, targetB, targetC)`. -/
theorem
    exists_rotation1_iterate_axisTwo_with_larger_actualOrder_and_regular_in_targetFrame_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (targetB targetC : ZMod p)
    (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      Point.map (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint1
          (Coefficients.map
            (algebraMap (ZMod p) (quadraticFiniteField p)) a)
          (algebraMap (ZMod p) (quadraticFiniteField p) u)
          (algebraMap (ZMod p) (quadraticFiniteField p) t)
          (q : quadraticFiniteField p) (r : quadraticFiniteField p))
    (hbelowEndgame :
      (rotationLinearOrder t : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hmargin :
      2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p
              (rotationLinearOrder t) +
          20 <
        (rotationLinearOrder t : ℝ)) :
    ∃ n : ℕ,
      let y := ((rotation1 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a2 y.x2
      OrderedTraceCandidateRegular a.a2 targetB targetC t' ∧
        rotationLinearOrder t < rotationLinearOrder t' := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := Coefficients.map f a
  let uE : E := f u
  let tE : E := f t
  let alpha : E := actualAlpha aE.multiplier * (r : E)
  let beta : E :=
    actualBeta aE.multiplier aE.a2 aE.a3 uE tE / (r : E)
  let gamma : E :=
    actualGammaFirst aE.multiplier aE.a2 aE.a3 uE tE
  -- Candidate regularity of `t` makes the weights `alpha`, `beta`, `gamma`
  -- of the shifted square-coset trace nondegenerate.
  have hDBase : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a1 uE := by
    have hmap := congrArg f hcoordinate
    simpa [tE, uE, aE, orderedTrace] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a1 aE.a2 aE.a3 tE := by
    simpa [aE, tE] using
      GenMarkoff.General.MiddleGame.orderedTraceCandidateRegular_map
        f f.injective hregular
  have hA2E : aE.a2 ^ 2 ≠ 4 := by
    intro hzero
    apply hA2
    apply f.injective
    simpa [aE, map_ofNat] using hzero
  have hweights :
      alpha * beta =
        actualSigma aE.multiplier aE.a2 aE.a3 uE tE := by
    simpa [alpha, beta] using
      actual_firstDirected_coset_weights_mul
        aE.multiplier aE.a2 aE.a3 uE tE r
  have hsigma : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_candidateRegular
      aE.multiplier aE.a1 aE.a2 aE.a3 uE tE htraceE hregularE
  have hEven :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualEvenObstruction_ne_zero_of_candidateRegular
      aE.multiplier aE.a1 aE.a2 aE.a3 uE tE
        htraceE hA2E hregularE
  -- Every shifted square-coset trace is the next trace of a rotation iterate.
  have hreachable :
      ∀ h : Subgroup.zpowers (q ^ 2),
        ∃ n : ℕ,
          weightedSplitTorusTrace alpha beta h + gamma =
            f (orderedTrace a.multiplier a.a2
              (((rotation1 a)^[n]) x).x2) := by
    intro h
    have hDE : discriminant tE ≠ 0 := by
      simpa [discriminant] using hregularE.1
    have heigen' :
        tE = (q : E) + ((q⁻¹ : Eˣ) : E) := by
      simpa [tE, E, f, splitTorusTrace] using heigen
    obtain ⟨n, hn⟩ :=
      exists_iterate_fiberPoint1_eq_mul_zpowers_sq
        aE uE tE q r hDE heigen' htraceE h
    let y : Point (ZMod p) := ((rotation1 a)^[n]) x
    have hyPoint :
        Point.map f y =
          fiberPoint1 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := by
      calc
        Point.map f y =
            ((rotation1 aE)^[n]) (Point.map f x) := by
          simpa [y, aE] using Point.map_iterate_rotation1 f a x n
        _ = ((rotation1 aE)^[n])
            (fiberPoint1 aE uE tE (q : E) (r : E)) := by
          simpa [E, f, aE, uE, tE] using congrArg
            (fun z : Point E ↦ ((rotation1 aE)^[n]) z) hdiagonalized
        _ = fiberPoint1 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := hn
    refine ⟨n, ?_⟩
    calc
      weightedSplitTorusTrace alpha beta h + gamma =
          orderedTrace aE.multiplier aE.a2
            (fiberPoint1 aE uE tE (q : E)
              ((r * (h : Eˣ) : Eˣ) : E)).x2 := by
        simpa [alpha, beta, gamma] using
          (orderedTrace_fiberPoint1_mul_eq_weightedSplitTorusTrace
            aE uE tE q r (h : Eˣ)).symm
      _ = orderedTrace aE.multiplier aE.a2 (Point.map f y).x2 := by
        rw [hyPoint]
      _ = f (orderedTrace a.multiplier a.a2 y.x2) := by
        simp [orderedTrace, aE, Point.map]
      _ = f (orderedTrace a.multiplier a.a2
          (((rotation1 a)^[n]) x).x2) := rfl
  -- Apply the axis-independent escape theorem to the rotation iterates.
  exact
    exists_iterate_with_larger_actualOrder_and_regular_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation1 a) x
        (fun y ↦ orderedTrace a.multiplier a.a2 y.x2)
        a.a2 targetB targetC hA2 hTargetB
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hmargin

/-- Reverse-frame specialization.  It returns the state needed to alternate
the fixed directed choices `.firstSecond` and `.secondFirst`. -/
theorem
    exists_rotation1_iterate_axisTwo_with_larger_actualOrder_and_reverseRegular_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      Point.map (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint1
          (Coefficients.map
            (algebraMap (ZMod p) (quadraticFiniteField p)) a)
          (algebraMap (ZMod p) (quadraticFiniteField p) u)
          (algebraMap (ZMod p) (quadraticFiniteField p) t)
          (q : quadraticFiniteField p) (r : quadraticFiniteField p))
    (hbelowEndgame :
      (rotationLinearOrder t : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hmargin :
      2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p
              (rotationLinearOrder t) +
          20 <
        (rotationLinearOrder t : ℝ)) :
    ∃ n : ℕ,
      let y := ((rotation1 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a2 y.x2
      OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t' ∧
        rotationLinearOrder t < rotationLinearOrder t' :=
  exists_rotation1_iterate_axisTwo_with_larger_actualOrder_and_regular_in_targetFrame_of_diagonalizedFiber
    p hpTwo delta hdelta a u t x hx hcoordinate hA2
      a.a1 a.a3 hA1 hregular q r heigen hdiagonalized
      hbelowEndgame hmargin

/-- Non-diagonalized first-to-second growth returning the reverse ordered
frame `(a₂,a₁,a₃)`. -/
theorem
    exists_rotation1_iterate_axisTwo_with_larger_actualOrder_and_reverseRegular
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3
        (traceAt a .first x))
    (hbelowEndgame :
      (rotationLinearOrderAt a .first x : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hmargin :
      2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p
              (rotationLinearOrderAt a .first x) +
          20 <
        (rotationLinearOrderAt a .first x : ℝ)) :
    ∃ n : ℕ,
      let y := ((rotation1 a)^[n]) x
      OrderedTraceCandidateRegular a.a2 a.a1 a.a3
          (traceAt a .second y) ∧
        rotationLinearOrderAt a .first x <
          rotationLinearOrderAt a .second y := by
  let t := traceAt a .first x
  have hD : discriminant t ≠ 0 := by
    simpa [t, discriminant] using hregular.1
  have hproduct :
      centeredFiberProduct a.a2 a.a3 x.x1 t ≠ 0 :=
    centeredFiberProduct_ne_zero_of_candidateRegular
      a.multiplier a.a1 a.a2 a.a3 x.x1 t rfl hregular
  obtain ⟨q, r, heigen, hdiagonalized⟩ :=
    exists_axisOne_actualFiber_diagonalization
      p hpTwo a x.x1 t x hx rfl rfl hD hproduct
  simpa [t, rotationLinearOrderAt, traceAt, orderedTrace,
    coefficientAt, coordinateAt] using
    exists_rotation1_iterate_axisTwo_with_larger_actualOrder_and_reverseRegular_of_diagonalizedFiber
      p hpTwo delta hdelta a x.x1 t x hx rfl hA2 hA1 hregular
        q r heigen hdiagonalized
        (by
          simpa [t, rotationLinearOrderAt, traceAt, orderedTrace, coefficientAt,
            coordinateAt] using hbelowEndgame)
        (by
          simpa [t, rotationLinearOrderAt, traceAt, orderedTrace, coefficientAt,
            coordinateAt] using hmargin)

/-- The second-to-first directed surface step with an arbitrary ordered
target frame starting at `a₁`.  This is the fixed-coefficient reverse move
needed to return from `.secondFirst` to `.firstSecond`. -/
theorem
    exists_rotation2_iterate_axisOne_with_larger_actualOrder_and_regular_in_targetFrame_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (targetB targetC : ZMod p)
    (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      Point.map (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint2
          (Coefficients.map
            (algebraMap (ZMod p) (quadraticFiniteField p)) a)
          (algebraMap (ZMod p) (quadraticFiniteField p) u)
          (algebraMap (ZMod p) (quadraticFiniteField p) t)
          (q : quadraticFiniteField p) (r : quadraticFiniteField p))
    (hbelowEndgame :
      (rotationLinearOrder t : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hmargin :
      2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p
              (rotationLinearOrder t) +
          20 <
        (rotationLinearOrder t : ℝ)) :
    ∃ n : ℕ,
      let y := ((rotation2 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a1 y.x1
      OrderedTraceCandidateRegular a.a1 targetB targetC t' ∧
        rotationLinearOrder t < rotationLinearOrder t' := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := Coefficients.map f a
  let uE : E := f u
  let tE : E := f t
  let alpha : E :=
    (aE.multiplier * (q : E)) * (r : E)
  let beta : E :=
    (aE.multiplier * centeredFiberProduct aE.a3 aE.a1 uE tE /
      (q : E)) / (r : E)
  let gamma : E :=
    actualGammaSecond aE.multiplier aE.a3 aE.a1 uE tE
  -- Candidate regularity of `t` makes the weights `alpha`, `beta`, `gamma`
  -- of the shifted square-coset trace nondegenerate.
  have hDBase : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a2 uE := by
    have hmap := congrArg f hcoordinate
    simpa [tE, uE, aE, orderedTrace] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a2 aE.a1 aE.a3 tE := by
    simpa [aE, tE] using
      GenMarkoff.General.MiddleGame.orderedTraceCandidateRegular_map
        f f.injective hregular
  have hA1E : aE.a1 ^ 2 ≠ 4 := by
    intro hzero
    apply hA1
    apply f.injective
    simpa [aE, map_ofNat] using hzero
  have hweights :
      alpha * beta =
        actualSigma aE.multiplier aE.a3 aE.a1 uE tE := by
    simpa [alpha, beta] using
      actual_secondDirected_coset_weights_mul
        aE.multiplier aE.a3 aE.a1 uE tE q r
  have hsigma : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_reverseCandidateRegular
      aE.multiplier aE.a2 aE.a3 aE.a1 uE tE htraceE hregularE
  have hEven :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualSecondEvenObstruction_ne_zero_of_candidateRegular
      aE.multiplier aE.a2 aE.a3 aE.a1 uE tE
        htraceE hA1E hregularE
  -- Every shifted square-coset trace is the next trace of a rotation iterate.
  have hreachable :
      ∀ h : Subgroup.zpowers (q ^ 2),
        ∃ n : ℕ,
          weightedSplitTorusTrace alpha beta h + gamma =
            f (orderedTrace a.multiplier a.a1
              (((rotation2 a)^[n]) x).x1) := by
    intro h
    have hDE : discriminant tE ≠ 0 := by
      simpa [discriminant] using hregularE.1
    have heigen' :
        tE = (q : E) + ((q⁻¹ : Eˣ) : E) := by
      simpa [tE, E, f, splitTorusTrace] using heigen
    obtain ⟨n, hn⟩ :=
      exists_iterate_fiberPoint2_eq_mul_zpowers_sq
        aE uE tE q r hDE heigen' htraceE h
    let y : Point (ZMod p) := ((rotation2 a)^[n]) x
    have hyPoint :
        Point.map f y =
          fiberPoint2 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := by
      calc
        Point.map f y =
            ((rotation2 aE)^[n]) (Point.map f x) := by
          simpa [y, aE] using Point.map_iterate_rotation2 f a x n
        _ = ((rotation2 aE)^[n])
            (fiberPoint2 aE uE tE (q : E) (r : E)) := by
          simpa [E, f, aE, uE, tE] using congrArg
            (fun z : Point E ↦ ((rotation2 aE)^[n]) z) hdiagonalized
        _ = fiberPoint2 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := hn
    refine ⟨n, ?_⟩
    calc
      weightedSplitTorusTrace alpha beta h + gamma =
          orderedTrace aE.multiplier aE.a1
            (fiberPoint2 aE uE tE (q : E)
              ((r * (h : Eˣ) : Eˣ) : E)).x1 := by
        -- `orderedTrace s A u` unfolds to `s * u - A` and `(fiberPoint2 ..).x1`
        -- to `(fiberPair aE.a3 aE.a1 ..).2`; restate in the form of
        -- `secondTrace_fiberPair_mul_eq_weightedSplitTorusTrace`.
        change
          weightedSplitTorusTrace alpha beta h + gamma =
            aE.multiplier *
                (fiberPair aE.a3 aE.a1 uE tE (q : E)
                  ((r * (h : Eˣ) : Eˣ) : E)).2 -
              aE.a1
        simpa [alpha, beta, gamma] using
          (secondTrace_fiberPair_mul_eq_weightedSplitTorusTrace
            aE.multiplier aE.a3 aE.a1 uE tE q r (h : Eˣ)).symm
      _ = orderedTrace aE.multiplier aE.a1 (Point.map f y).x1 := by
        rw [hyPoint]
      _ = f (orderedTrace a.multiplier a.a1 y.x1) := by
        simp [orderedTrace, aE, Point.map]
      _ = f (orderedTrace a.multiplier a.a1
          (((rotation2 a)^[n]) x).x1) := rfl
  -- Apply the axis-independent escape theorem to the rotation iterates.
  exact
    exists_iterate_with_larger_actualOrder_and_regular_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation2 a) x
        (fun y ↦ orderedTrace a.multiplier a.a1 y.x1)
        a.a1 targetB targetC hA1 hTargetB
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hmargin

/-- Second-to-first growth returning the forward frame
`(a₁,a₂,a₃)`. -/
theorem
    exists_rotation2_iterate_axisOne_with_larger_actualOrder_and_forwardRegular_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      Point.map (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint2
          (Coefficients.map
            (algebraMap (ZMod p) (quadraticFiniteField p)) a)
          (algebraMap (ZMod p) (quadraticFiniteField p) u)
          (algebraMap (ZMod p) (quadraticFiniteField p) t)
          (q : quadraticFiniteField p) (r : quadraticFiniteField p))
    (hbelowEndgame :
      (rotationLinearOrder t : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hmargin :
      2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p
              (rotationLinearOrder t) +
          20 <
        (rotationLinearOrder t : ℝ)) :
    ∃ n : ℕ,
      let y := ((rotation2 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a1 y.x1
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t' ∧
        rotationLinearOrder t < rotationLinearOrder t' :=
  exists_rotation2_iterate_axisOne_with_larger_actualOrder_and_regular_in_targetFrame_of_diagonalizedFiber
    p hpTwo delta hdelta a u t x hx hcoordinate hA1
      a.a2 a.a3 hA2 hregular q r heigen hdiagonalized
      hbelowEndgame hmargin

/-- Non-diagonalized second-to-first growth returning the forward frame. -/
theorem
    exists_rotation2_iterate_axisOne_with_larger_actualOrder_and_forwardRegular
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hregular :
      OrderedTraceCandidateRegular a.a2 a.a1 a.a3
        (traceAt a .second x))
    (hbelowEndgame :
      (rotationLinearOrderAt a .second x : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hmargin :
      2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p
              (rotationLinearOrderAt a .second x) +
          20 <
        (rotationLinearOrderAt a .second x : ℝ)) :
    ∃ n : ℕ,
      let y := ((rotation2 a)^[n]) x
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3
          (traceAt a .first y) ∧
        rotationLinearOrderAt a .second x <
          rotationLinearOrderAt a .first y := by
  let t := traceAt a .second x
  have hD : discriminant t ≠ 0 := by
    simpa [t, discriminant] using hregular.1
  have hproduct :
      centeredFiberProduct a.a3 a.a1 x.x2 t ≠ 0 := by
    have hswap :=
      centeredFiberProduct_ne_zero_of_candidateRegular
        a.multiplier a.a2 a.a1 a.a3 x.x2 t rfl hregular
    simpa [centeredFiberProduct_swap] using hswap
  obtain ⟨q, r, heigen, hdiagonalized⟩ :=
    exists_axisTwo_actualFiber_diagonalization
      p hpTwo a x.x2 t x hx rfl rfl hD hproduct
  simpa [t, rotationLinearOrderAt, traceAt, orderedTrace,
    coefficientAt, coordinateAt] using
    exists_rotation2_iterate_axisOne_with_larger_actualOrder_and_forwardRegular_of_diagonalizedFiber
      p hpTwo delta hdelta a x.x2 t x hx rfl hA1 hA2 hregular
        q r heigen hdiagonalized
        (by
          simpa [t, rotationLinearOrderAt, traceAt, orderedTrace, coefficientAt,
            coordinateAt] using hbelowEndgame)
        (by
          simpa [t, rotationLinearOrderAt, traceAt, orderedTrace, coefficientAt,
            coordinateAt] using hmargin)

/-- A point reached by iterating `rotation1` lies in the same rotation
component. -/
private theorem sameRotationComponent_of_iterate_rotation1
    {R : Type*} [CommRing R] (a : Coefficients R)
    (x y : SolutionSurface a) (n : ℕ)
    (hxy : ((rotation1 a)^[n]) x.1 = y.1) :
    SameRotationComponent x y := by
  obtain ⟨g, hg⟩ :=
    sameRotationComponent_iterate_rotationSurfacePermAt
      a .first x n
  refine ⟨g, hg.trans ?_⟩
  apply Subtype.ext
  simpa [rotationSurfacePermAt] using
    (coe_iterate_rotation1SurfacePerm a x n).trans hxy

/-- A point reached by iterating `rotation2` lies in the same rotation
component. -/
private theorem sameRotationComponent_of_iterate_rotation2
    {R : Type*} [CommRing R] (a : Coefficients R)
    (x y : SolutionSurface a) (n : ℕ)
    (hxy : ((rotation2 a)^[n]) x.1 = y.1) :
    SameRotationComponent x y := by
  obtain ⟨g, hg⟩ :=
    sameRotationComponent_iterate_rotationSurfacePermAt
      a .second x n
  refine ⟨g, hg.trans ?_⟩
  apply Subtype.ext
  simpa [rotationSurfacePermAt] using
    (coe_iterate_rotation2SurfacePerm a x n).trans hxy

/-- The two fixed directed choices used by the alternating regular iterator.
They are labels only and never act on the coefficient triple. -/
inductive AlternatingDirectedAxis
  | firstSecond
  | secondFirst
deriving DecidableEq, Repr

/-- The active fixed coordinate of an alternating directed state. -/
def AlternatingDirectedAxis.fixed : AlternatingDirectedAxis → Axis
  | .firstSecond => .first
  | .secondFirst => .second

/-- The ordered candidate-regular predicate carried by an alternating
state. -/
def alternatingTraceRegular
    {R : Type*} [Field R] (a : Coefficients R)
    (direction : AlternatingDirectedAxis) (x : Point R) : Prop :=
  match direction with
  | .firstSecond =>
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3
        (traceAt a .first x)
  | .secondFirst =>
      OrderedTraceCandidateRegular a.a2 a.a1 a.a3
        (traceAt a .second x)

/-- A surface point together with exactly the ordered regularity needed by
the next alternating directed move. -/
structure AlternatingRegularState
    {R : Type*} [Field R] (a : Coefficients R) where
  direction : AlternatingDirectedAxis
  point : SolutionSurface a
  regular : alternatingTraceRegular a direction point.1

/-- Actual order of the fixed trace carried by an alternating state. -/
noncomputable def alternatingActualOrder
    {R : Type*} [Field R] {a : Coefficients R}
    (state : AlternatingRegularState a) : ℕ :=
  rotationLinearOrderAt a state.direction.fixed state.point.1

/-- One regular alternating move strictly raises the carried actual order
and remains inside the fixed-coefficient rotation component. -/
theorem exists_nextAlternatingRegularState_with_larger_actualOrder
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (state : AlternatingRegularState a)
    (hbelowEndgame :
      (alternatingActualOrder state : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hmargin :
      2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p
              (alternatingActualOrder state) +
          20 <
        (alternatingActualOrder state : ℝ)) :
    ∃ next : AlternatingRegularState a,
      SameRotationComponent state.point next.point ∧
        alternatingActualOrder state <
          alternatingActualOrder next := by
  cases state with
  | mk direction point regular =>
      cases direction with
      | firstSecond =>
          obtain ⟨n, hnextRegular, hincrease⟩ :=
            exists_rotation1_iterate_axisTwo_with_larger_actualOrder_and_reverseRegular
              p hpTwo delta hdelta a point.1 point.2 hA2 hA1 regular
                (by
                  simpa [alternatingActualOrder,
                    AlternatingDirectedAxis.fixed] using hbelowEndgame)
                (by
                  simpa [alternatingActualOrder,
                    AlternatingDirectedAxis.fixed] using hmargin)
          let yPoint : Point (ZMod p) := ((rotation1 a)^[n]) point.1
          have hySolution : IsSolution a yPoint :=
            (isSolution_iterate_rotation1 a point.1 n).2 point.2
          let y : SolutionSurface a := ⟨yPoint, hySolution⟩
          let next : AlternatingRegularState a :=
            ⟨.secondFirst, y, by simpa [alternatingTraceRegular, y, yPoint]
              using hnextRegular⟩
          refine ⟨next, ?_, ?_⟩
          · exact sameRotationComponent_of_iterate_rotation1
              a point y n rfl
          · simpa [alternatingActualOrder,
              AlternatingDirectedAxis.fixed, next, y, yPoint] using hincrease
      | secondFirst =>
          obtain ⟨n, hnextRegular, hincrease⟩ :=
            exists_rotation2_iterate_axisOne_with_larger_actualOrder_and_forwardRegular
              p hpTwo delta hdelta a point.1 point.2 hA1 hA2 regular
                (by
                  simpa [alternatingActualOrder,
                    AlternatingDirectedAxis.fixed] using hbelowEndgame)
                (by
                  simpa [alternatingActualOrder,
                    AlternatingDirectedAxis.fixed] using hmargin)
          let yPoint : Point (ZMod p) := ((rotation2 a)^[n]) point.1
          have hySolution : IsSolution a yPoint :=
            (isSolution_iterate_rotation2 a point.1 n).2 point.2
          let y : SolutionSurface a := ⟨yPoint, hySolution⟩
          let next : AlternatingRegularState a :=
            ⟨.firstSecond, y, by
              simpa [alternatingTraceRegular, y, yPoint]
                using hnextRegular⟩
          refine ⟨next, ?_, ?_⟩
          · exact sameRotationComponent_of_iterate_rotation2
              a point y n rfl
          · simpa [alternatingActualOrder,
              AlternatingDirectedAxis.fixed, next, y, yPoint] using hincrease

/-- An alternating regular state reaches, in its rotation component, an
alternating regular state of actual order at least `target`, provided the
endgame upper bound `current < p ^ (1/2 + delta)` and the regular-escape
margin hold for every order `current` from the starting order up to
`target`. -/
theorem exists_sameRotationComponent_alternatingRegularState_reaches_threshold
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (start : AlternatingRegularState a) (target : ℕ)
    (hbelowEndgame :
      ∀ current : ℕ,
        alternatingActualOrder start ≤ current →
        current < target →
        (current : ℝ) <
          (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hmargin :
      ∀ current : ℕ,
        alternatingActualOrder start ≤ current →
        current < target →
        2 *
            (((p - 1).divisors.card +
              (p + 1).divisors.card : ℕ) : ℝ) *
              corvajaZannierCurrentOrderEnvelope p current +
            20 <
          (current : ℝ)) :
    ∃ finish : AlternatingRegularState a,
      SameRotationComponent start.point finish.point ∧
        target ≤ alternatingActualOrder finish := by
  let startOrder : ℕ := alternatingActualOrder start
  let MiddleState :=
    {state : AlternatingRegularState a //
      startOrder ≤ alternatingActualOrder state}
  let initial : MiddleState := ⟨start, le_rfl⟩
  let relation : MiddleState → MiddleState → Prop :=
    fun x y ↦ SameRotationComponent x.1.point y.1.point
  let measure : MiddleState → ℕ :=
    fun state ↦ alternatingActualOrder state.1
  have hstep :
      ∀ current : MiddleState,
        measure current < target →
          ∃ next : MiddleState,
            relation current next ∧
              measure current < measure next := by
    intro current hcurrent
    obtain ⟨next, hcomponent, hincrease⟩ :=
      exists_nextAlternatingRegularState_with_larger_actualOrder
        p hpTwo delta hdelta a hA1 hA2 current.1
          (hbelowEndgame (measure current)
            (by simpa [measure, startOrder] using current.2) hcurrent)
          (hmargin (measure current)
            (by simpa [measure, startOrder] using current.2) hcurrent)
    let nextState : MiddleState :=
      ⟨next, by
        exact current.2.trans hincrease.le⟩
    exact ⟨nextState, hcomponent, hincrease⟩
  obtain ⟨finish, hchain, htarget⟩ :=
    BGS.exists_reflTransGen_measure_ge
      relation measure target hstep initial
  have hcomponent :
      SameRotationComponent start.point finish.1.point := by
    have hchainComponent :
        ∀ {x y : MiddleState},
          Relation.ReflTransGen relation x y →
            SameRotationComponent x.1.point y.1.point := by
      intro x y hxy
      induction hxy with
      | refl =>
          exact sameRotationComponent_refl x.1.point
      | tail hprefix hlast ih =>
          exact sameRotationComponent_trans ih hlast
    simpa [initial] using hchainComponent hchain
  exact ⟨finish.1, hcomponent, by simpa [measure] using htarget⟩

end

end GenMarkoff.General.Assembly
