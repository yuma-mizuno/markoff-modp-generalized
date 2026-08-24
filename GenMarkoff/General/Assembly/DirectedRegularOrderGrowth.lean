import GenMarkoff.General.Assembly.RegularMiddleIteration

/-!
# Directed iterable regular actual-order growth

This module completes the five directed surface steps not exposed uniformly
by `RegularMiddleIteration`.  Every non-diagonalized endpoint returns
candidate regularity in `DirectedAxes.reverse` together with strict growth of
`rotationLinearOrderAt`.

The coefficient triple remains fixed.  The ordered target frames below are
parameter choices for `OrderedTraceCandidateRegular`; they are not coordinate
permutations of the surface.
-/

namespace GenMarkoff.General.Assembly

open Filter BGS.Markoff
open GenMarkoff.General.MiddleGame
open GenMarkoff.Symmetric.MiddleGame
open Polynomial

noncomputable section

/-- First-to-third growth with an arbitrary ordered target frame based at
`a₃`.  The target trace is the second moving coordinate of the first-axis
fiber, so its square-coset weights are the reverse-directed ones. -/
theorem
    exists_rotation1_iterate_axisThree_with_larger_actualOrder_and_regular_in_targetFrame_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (targetB targetC : ZMod p)
    (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a3 a.a2 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      mapPoint (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint1
          (mapCoefficients
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
      let t' := orderedTrace a.multiplier a.a3 y.x3
      OrderedTraceCandidateRegular a.a3 targetB targetC t' ∧
        rotationLinearOrder t < rotationLinearOrder t' := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := mapCoefficients f a
  let uE : E := f u
  let tE : E := f t
  let alpha : E :=
    (aE.multiplier * (q : E)) * (r : E)
  let beta : E :=
    (aE.multiplier * centeredFiberProduct aE.a2 aE.a3 uE tE /
      (q : E)) / (r : E)
  let gamma : E :=
    actualGammaSecond aE.multiplier aE.a2 aE.a3 uE tE
  have hDBase : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a1 uE := by
    have hmap := congrArg f hcoordinate
    simpa [tE, uE, aE, orderedTrace] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a1 aE.a3 aE.a2 tE := by
    simpa [aE, tE] using
      GenMarkoff.General.MiddleGame.orderedTraceCandidateRegular_map
        f f.injective hregular
  have hA3E : aE.a3 ^ 2 ≠ 4 := by
    intro hzero
    apply hA3
    apply f.injective
    simpa [aE, map_ofNat] using hzero
  have hweights :
      alpha * beta =
        actualSigma aE.multiplier aE.a2 aE.a3 uE tE := by
    simpa [alpha, beta] using
      actual_secondDirected_coset_weights_mul
        aE.multiplier aE.a2 aE.a3 uE tE q r
  have hsigma : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_reverseCandidateRegular
      aE.multiplier aE.a1 aE.a2 aE.a3 uE tE htraceE hregularE
  have hEven :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualSecondEvenObstruction_ne_zero_of_candidateRegular
      aE.multiplier aE.a1 aE.a2 aE.a3 uE tE
        htraceE hA3E hregularE
  have hreachable :
      ∀ h : Subgroup.zpowers (q ^ 2),
        ∃ n : ℕ,
          weightedSplitTorusTrace alpha beta h + gamma =
            f (orderedTrace a.multiplier a.a3
              (((rotation1 a)^[n]) x).x3) := by
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
        mapPoint f y =
          fiberPoint1 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := by
      calc
        mapPoint f y =
            ((rotation1 aE)^[n]) (mapPoint f x) := by
          simpa [y, aE] using mapPoint_iterate_rotation1 f a x n
        _ = ((rotation1 aE)^[n])
            (fiberPoint1 aE uE tE (q : E) (r : E)) := by
          simpa [E, f, aE, uE, tE] using congrArg
            (fun z : Point E ↦ ((rotation1 aE)^[n]) z) hdiagonalized
        _ = fiberPoint1 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := hn
    refine ⟨n, ?_⟩
    calc
      weightedSplitTorusTrace alpha beta h + gamma =
          orderedTrace aE.multiplier aE.a3
            (fiberPoint1 aE uE tE (q : E)
              ((r * (h : Eˣ) : Eˣ) : E)).x3 := by
        change
          weightedSplitTorusTrace alpha beta h + gamma =
            aE.multiplier *
                (fiberPair aE.a2 aE.a3 uE tE (q : E)
                  ((r * (h : Eˣ) : Eˣ) : E)).2 -
              aE.a3
        simpa [alpha, beta, gamma] using
          (secondTrace_fiberPair_mul_eq_weightedSplitTorusTrace
            aE.multiplier aE.a2 aE.a3 uE tE q r (h : Eˣ)).symm
      _ = orderedTrace aE.multiplier aE.a3 (mapPoint f y).x3 := by
        rw [hyPoint]
      _ = f (orderedTrace a.multiplier a.a3 y.x3) := by
        simp [orderedTrace, aE, mapPoint]
      _ = f (orderedTrace a.multiplier a.a3
          (((rotation1 a)^[n]) x).x3) := rfl
  exact
    exists_iterate_with_larger_actualOrder_and_regular_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation1 a) x
        (fun y ↦ orderedTrace a.multiplier a.a3 y.x3)
        a.a3 targetB targetC hA3 hTargetB
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hmargin

/-- Diagonalized first-to-third step returning the reverse frame
`(a₃, a₁, a₂)`. -/
theorem
    exists_rotation1_iterate_axisThree_with_larger_actualOrder_and_reverseRegular_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a3 a.a2 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      mapPoint (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint1
          (mapCoefficients
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
      let t' := orderedTrace a.multiplier a.a3 y.x3
      OrderedTraceCandidateRegular a.a3 a.a1 a.a2 t' ∧
        rotationLinearOrder t < rotationLinearOrder t' :=
  exists_rotation1_iterate_axisThree_with_larger_actualOrder_and_regular_in_targetFrame_of_diagonalizedFiber
    p hpTwo delta hdelta a u t x hx hcoordinate hA3
      a.a1 a.a2 hA1 hregular q r heigen hdiagonalized
      hbelowEndgame hmargin

/-- Non-diagonalized `.firstThird` step returning regularity for
`.firstThird.reverse = .thirdFirst`. -/
theorem
    exists_rotation1_iterate_axisThree_with_larger_actualOrder_and_reverseRegular
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a3 a.a2
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
      OrderedTraceCandidateRegular a.a3 a.a1 a.a2
          (traceAt a .third y) ∧
        rotationLinearOrderAt a .first x <
          rotationLinearOrderAt a .third y := by
  let t := traceAt a .first x
  have hD : discriminant t ≠ 0 := by
    simpa [t, discriminant] using hregular.1
  have hproduct :
      centeredFiberProduct a.a2 a.a3 x.x1 t ≠ 0 := by
    have hswap :=
      centeredFiberProduct_ne_zero_of_candidateRegular
        a.multiplier a.a1 a.a3 a.a2 x.x1 t rfl hregular
    simpa [centeredFiberProduct_swap] using hswap
  obtain ⟨q, r, heigen, hdiagonalized⟩ :=
    exists_axisOne_actualFiber_diagonalization
      p hpTwo a x.x1 t x hx rfl rfl hD hproduct
  simpa [t, rotationLinearOrderAt, traceAt, orderedTrace,
    coefficientAt, coordinateAt] using
    exists_rotation1_iterate_axisThree_with_larger_actualOrder_and_reverseRegular_of_diagonalizedFiber
      p hpTwo delta hdelta a x.x1 t x hx rfl hA3 hA1 hregular
        q r heigen hdiagonalized
        (by
          simpa [t, rotationLinearOrderAt, traceAt, orderedTrace, coefficientAt,
            coordinateAt] using hbelowEndgame)
        (by
          simpa [t, rotationLinearOrderAt, traceAt, orderedTrace, coefficientAt,
            coordinateAt] using hmargin)

/-- Reverse-named diagonalized alias for the existing second-to-first step.
Its returned frame `(a₁, a₂, a₃)` is
`.secondFirst.reverse = .firstSecond`. -/
theorem
    exists_rotation2_iterate_axisOne_with_larger_actualOrder_and_reverseRegular_of_diagonalizedFiber
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
      mapPoint (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint2
          (mapCoefficients
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
  exists_rotation2_iterate_axisOne_with_larger_actualOrder_and_forwardRegular_of_diagonalizedFiber
    p hpTwo delta hdelta a u t x hx hcoordinate hA1 hA2 hregular
      q r heigen hdiagonalized hbelowEndgame hmargin

/-- Non-diagonalized `.secondFirst` step, named uniformly by the returned
reverse frame. -/
theorem
    exists_rotation2_iterate_axisOne_with_larger_actualOrder_and_reverseRegular
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
          rotationLinearOrderAt a .first y :=
  exists_rotation2_iterate_axisOne_with_larger_actualOrder_and_forwardRegular
    p hpTwo delta hdelta a x hx hA1 hA2 hregular
      hbelowEndgame hmargin

/-- Second-to-third growth with an arbitrary ordered target frame based at
`a₃`. -/
theorem
    exists_rotation2_iterate_axisThree_with_larger_actualOrder_and_regular_in_targetFrame_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (targetB targetC : ZMod p)
    (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a3 a.a1 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      mapPoint (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint2
          (mapCoefficients
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
      let t' := orderedTrace a.multiplier a.a3 y.x3
      OrderedTraceCandidateRegular a.a3 targetB targetC t' ∧
        rotationLinearOrder t < rotationLinearOrder t' := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := mapCoefficients f a
  let uE : E := f u
  let tE : E := f t
  let alpha : E := actualAlpha aE.multiplier * (r : E)
  let beta : E :=
    actualBeta aE.multiplier aE.a3 aE.a1 uE tE / (r : E)
  let gamma : E :=
    actualGammaFirst aE.multiplier aE.a3 aE.a1 uE tE
  have hDBase : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a2 uE := by
    have hmap := congrArg f hcoordinate
    simpa [tE, uE, aE, orderedTrace] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a2 aE.a3 aE.a1 tE := by
    simpa [aE, tE] using
      GenMarkoff.General.MiddleGame.orderedTraceCandidateRegular_map
        f f.injective hregular
  have hA3E : aE.a3 ^ 2 ≠ 4 := by
    intro hzero
    apply hA3
    apply f.injective
    simpa [aE, map_ofNat] using hzero
  have hweights :
      alpha * beta =
        actualSigma aE.multiplier aE.a3 aE.a1 uE tE := by
    simpa [alpha, beta] using
      actual_firstDirected_coset_weights_mul
        aE.multiplier aE.a3 aE.a1 uE tE r
  have hsigma : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_candidateRegular
      aE.multiplier aE.a2 aE.a3 aE.a1 uE tE htraceE hregularE
  have hEven :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualEvenObstruction_ne_zero_of_candidateRegular
      aE.multiplier aE.a2 aE.a3 aE.a1 uE tE
        htraceE hA3E hregularE
  have hreachable :
      ∀ h : Subgroup.zpowers (q ^ 2),
        ∃ n : ℕ,
          weightedSplitTorusTrace alpha beta h + gamma =
            f (orderedTrace a.multiplier a.a3
              (((rotation2 a)^[n]) x).x3) := by
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
        mapPoint f y =
          fiberPoint2 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := by
      calc
        mapPoint f y =
            ((rotation2 aE)^[n]) (mapPoint f x) := by
          simpa [y, aE] using mapPoint_iterate_rotation2 f a x n
        _ = ((rotation2 aE)^[n])
            (fiberPoint2 aE uE tE (q : E) (r : E)) := by
          simpa [E, f, aE, uE, tE] using congrArg
            (fun z : Point E ↦ ((rotation2 aE)^[n]) z) hdiagonalized
        _ = fiberPoint2 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := hn
    refine ⟨n, ?_⟩
    calc
      weightedSplitTorusTrace alpha beta h + gamma =
          orderedTrace aE.multiplier aE.a3
            (fiberPoint2 aE uE tE (q : E)
              ((r * (h : Eˣ) : Eˣ) : E)).x3 := by
        change
          weightedSplitTorusTrace alpha beta h + gamma =
            aE.multiplier *
                (fiberPair aE.a3 aE.a1 uE tE (q : E)
                  ((r * (h : Eˣ) : Eˣ) : E)).1 -
              aE.a3
        simpa [alpha, beta, gamma] using
          (firstTrace_fiberPair_mul_eq_weightedSplitTorusTrace
            aE.multiplier aE.a3 aE.a1 uE tE q r (h : Eˣ)).symm
      _ = orderedTrace aE.multiplier aE.a3 (mapPoint f y).x3 := by
        rw [hyPoint]
      _ = f (orderedTrace a.multiplier a.a3 y.x3) := by
        simp [orderedTrace, aE, mapPoint]
      _ = f (orderedTrace a.multiplier a.a3
          (((rotation2 a)^[n]) x).x3) := rfl
  exact
    exists_iterate_with_larger_actualOrder_and_regular_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation2 a) x
        (fun y ↦ orderedTrace a.multiplier a.a3 y.x3)
        a.a3 targetB targetC hA3 hTargetB
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hmargin

/-- Diagonalized second-to-third step returning the reverse frame
`(a₃, a₂, a₁)`. -/
theorem
    exists_rotation2_iterate_axisThree_with_larger_actualOrder_and_reverseRegular_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a3 a.a1 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      mapPoint (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint2
          (mapCoefficients
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
      let t' := orderedTrace a.multiplier a.a3 y.x3
      OrderedTraceCandidateRegular a.a3 a.a2 a.a1 t' ∧
        rotationLinearOrder t < rotationLinearOrder t' :=
  exists_rotation2_iterate_axisThree_with_larger_actualOrder_and_regular_in_targetFrame_of_diagonalizedFiber
    p hpTwo delta hdelta a u t x hx hcoordinate hA3
      a.a2 a.a1 hA2 hregular q r heigen hdiagonalized
      hbelowEndgame hmargin

/-- Non-diagonalized `.secondThird` step returning regularity for
`.secondThird.reverse = .thirdSecond`. -/
theorem
    exists_rotation2_iterate_axisThree_with_larger_actualOrder_and_reverseRegular
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hregular :
      OrderedTraceCandidateRegular a.a2 a.a3 a.a1
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
      OrderedTraceCandidateRegular a.a3 a.a2 a.a1
          (traceAt a .third y) ∧
        rotationLinearOrderAt a .second x <
          rotationLinearOrderAt a .third y := by
  let t := traceAt a .second x
  have hD : discriminant t ≠ 0 := by
    simpa [t, discriminant] using hregular.1
  have hproduct :
      centeredFiberProduct a.a3 a.a1 x.x2 t ≠ 0 :=
    centeredFiberProduct_ne_zero_of_candidateRegular
      a.multiplier a.a2 a.a3 a.a1 x.x2 t rfl hregular
  obtain ⟨q, r, heigen, hdiagonalized⟩ :=
    exists_axisTwo_actualFiber_diagonalization
      p hpTwo a x.x2 t x hx rfl rfl hD hproduct
  simpa [t, rotationLinearOrderAt, traceAt, orderedTrace,
    coefficientAt, coordinateAt] using
    exists_rotation2_iterate_axisThree_with_larger_actualOrder_and_reverseRegular_of_diagonalizedFiber
      p hpTwo delta hdelta a x.x2 t x hx rfl hA3 hA2 hregular
        q r heigen hdiagonalized
        (by
          simpa [t, rotationLinearOrderAt, traceAt, orderedTrace, coefficientAt,
            coordinateAt] using hbelowEndgame)
        (by
          simpa [t, rotationLinearOrderAt, traceAt, orderedTrace, coefficientAt,
            coordinateAt] using hmargin)

/-- Third-to-first growth with an arbitrary ordered target frame based at
`a₁`. -/
theorem
    exists_rotation3_iterate_axisOne_with_larger_actualOrder_and_regular_in_targetFrame_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (targetB targetC : ZMod p)
    (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a3 a.a1 a.a2 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      mapPoint (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint3
          (mapCoefficients
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
      let y := ((rotation3 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a1 y.x1
      OrderedTraceCandidateRegular a.a1 targetB targetC t' ∧
        rotationLinearOrder t < rotationLinearOrder t' := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := mapCoefficients f a
  let uE : E := f u
  let tE : E := f t
  let alpha : E := actualAlpha aE.multiplier * (r : E)
  let beta : E :=
    actualBeta aE.multiplier aE.a1 aE.a2 uE tE / (r : E)
  let gamma : E :=
    actualGammaFirst aE.multiplier aE.a1 aE.a2 uE tE
  have hDBase : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a3 uE := by
    have hmap := congrArg f hcoordinate
    simpa [tE, uE, aE, orderedTrace] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a3 aE.a1 aE.a2 tE := by
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
        actualSigma aE.multiplier aE.a1 aE.a2 uE tE := by
    simpa [alpha, beta] using
      actual_firstDirected_coset_weights_mul
        aE.multiplier aE.a1 aE.a2 uE tE r
  have hsigma : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_candidateRegular
      aE.multiplier aE.a3 aE.a1 aE.a2 uE tE htraceE hregularE
  have hEven :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualEvenObstruction_ne_zero_of_candidateRegular
      aE.multiplier aE.a3 aE.a1 aE.a2 uE tE
        htraceE hA1E hregularE
  have hreachable :
      ∀ h : Subgroup.zpowers (q ^ 2),
        ∃ n : ℕ,
          weightedSplitTorusTrace alpha beta h + gamma =
            f (orderedTrace a.multiplier a.a1
              (((rotation3 a)^[n]) x).x1) := by
    intro h
    have hDE : discriminant tE ≠ 0 := by
      simpa [discriminant] using hregularE.1
    have heigen' :
        tE = (q : E) + ((q⁻¹ : Eˣ) : E) := by
      simpa [tE, E, f, splitTorusTrace] using heigen
    obtain ⟨n, hn⟩ :=
      exists_iterate_fiberPoint3_eq_mul_zpowers_sq
        aE uE tE q r hDE heigen' htraceE h
    let y : Point (ZMod p) := ((rotation3 a)^[n]) x
    have hyPoint :
        mapPoint f y =
          fiberPoint3 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := by
      calc
        mapPoint f y =
            ((rotation3 aE)^[n]) (mapPoint f x) := by
          simpa [y, aE] using mapPoint_iterate_rotation3 f a x n
        _ = ((rotation3 aE)^[n])
            (fiberPoint3 aE uE tE (q : E) (r : E)) := by
          simpa [E, f, aE, uE, tE] using congrArg
            (fun z : Point E ↦ ((rotation3 aE)^[n]) z) hdiagonalized
        _ = fiberPoint3 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := hn
    refine ⟨n, ?_⟩
    calc
      weightedSplitTorusTrace alpha beta h + gamma =
          orderedTrace aE.multiplier aE.a1
            (fiberPoint3 aE uE tE (q : E)
              ((r * (h : Eˣ) : Eˣ) : E)).x1 := by
        change
          weightedSplitTorusTrace alpha beta h + gamma =
            aE.multiplier *
                (fiberPair aE.a1 aE.a2 uE tE (q : E)
                  ((r * (h : Eˣ) : Eˣ) : E)).1 -
              aE.a1
        simpa [alpha, beta, gamma] using
          (firstTrace_fiberPair_mul_eq_weightedSplitTorusTrace
            aE.multiplier aE.a1 aE.a2 uE tE q r (h : Eˣ)).symm
      _ = orderedTrace aE.multiplier aE.a1 (mapPoint f y).x1 := by
        rw [hyPoint]
      _ = f (orderedTrace a.multiplier a.a1 y.x1) := by
        simp [orderedTrace, aE, mapPoint]
      _ = f (orderedTrace a.multiplier a.a1
          (((rotation3 a)^[n]) x).x1) := rfl
  exact
    exists_iterate_with_larger_actualOrder_and_regular_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation3 a) x
        (fun y ↦ orderedTrace a.multiplier a.a1 y.x1)
        a.a1 targetB targetC hA1 hTargetB
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hmargin

/-- Diagonalized third-to-first step returning the reverse frame
`(a₁, a₃, a₂)`. -/
theorem
    exists_rotation3_iterate_axisOne_with_larger_actualOrder_and_reverseRegular_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a3 a.a1 a.a2 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      mapPoint (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint3
          (mapCoefficients
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
      let y := ((rotation3 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a1 y.x1
      OrderedTraceCandidateRegular a.a1 a.a3 a.a2 t' ∧
        rotationLinearOrder t < rotationLinearOrder t' :=
  exists_rotation3_iterate_axisOne_with_larger_actualOrder_and_regular_in_targetFrame_of_diagonalizedFiber
    p hpTwo delta hdelta a u t x hx hcoordinate hA1
      a.a3 a.a2 hA3 hregular q r heigen hdiagonalized
      hbelowEndgame hmargin

/-- Non-diagonalized `.thirdFirst` step returning regularity for
`.thirdFirst.reverse = .firstThird`. -/
theorem
    exists_rotation3_iterate_axisOne_with_larger_actualOrder_and_reverseRegular
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hregular :
      OrderedTraceCandidateRegular a.a3 a.a1 a.a2
        (traceAt a .third x))
    (hbelowEndgame :
      (rotationLinearOrderAt a .third x : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hmargin :
      2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p
              (rotationLinearOrderAt a .third x) +
          20 <
        (rotationLinearOrderAt a .third x : ℝ)) :
    ∃ n : ℕ,
      let y := ((rotation3 a)^[n]) x
      OrderedTraceCandidateRegular a.a1 a.a3 a.a2
          (traceAt a .first y) ∧
        rotationLinearOrderAt a .third x <
          rotationLinearOrderAt a .first y := by
  let t := traceAt a .third x
  have hD : discriminant t ≠ 0 := by
    simpa [t, discriminant] using hregular.1
  have hproduct :
      centeredFiberProduct a.a1 a.a2 x.x3 t ≠ 0 :=
    centeredFiberProduct_ne_zero_of_candidateRegular
      a.multiplier a.a3 a.a1 a.a2 x.x3 t rfl hregular
  obtain ⟨q, r, heigen, hdiagonalized⟩ :=
    exists_axisThree_actualFiber_diagonalization
      p hpTwo a x.x3 t x hx rfl rfl hD hproduct
  simpa [t, rotationLinearOrderAt, traceAt, orderedTrace,
    coefficientAt, coordinateAt] using
    exists_rotation3_iterate_axisOne_with_larger_actualOrder_and_reverseRegular_of_diagonalizedFiber
      p hpTwo delta hdelta a x.x3 t x hx rfl hA1 hA3 hregular
        q r heigen hdiagonalized
        (by
          simpa [t, rotationLinearOrderAt, traceAt, orderedTrace, coefficientAt,
            coordinateAt] using hbelowEndgame)
        (by
          simpa [t, rotationLinearOrderAt, traceAt, orderedTrace, coefficientAt,
            coordinateAt] using hmargin)

/-- Third-to-second growth with an arbitrary ordered target frame based at
`a₂`.  The target is the second coordinate of the third-axis moving pair. -/
theorem
    exists_rotation3_iterate_axisTwo_with_larger_actualOrder_and_regular_in_targetFrame_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (targetB targetC : ZMod p)
    (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a3 a.a2 a.a1 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      mapPoint (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint3
          (mapCoefficients
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
      let y := ((rotation3 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a2 y.x2
      OrderedTraceCandidateRegular a.a2 targetB targetC t' ∧
        rotationLinearOrder t < rotationLinearOrder t' := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := mapCoefficients f a
  let uE : E := f u
  let tE : E := f t
  let alpha : E :=
    (aE.multiplier * (q : E)) * (r : E)
  let beta : E :=
    (aE.multiplier * centeredFiberProduct aE.a1 aE.a2 uE tE /
      (q : E)) / (r : E)
  let gamma : E :=
    actualGammaSecond aE.multiplier aE.a1 aE.a2 uE tE
  have hDBase : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a3 uE := by
    have hmap := congrArg f hcoordinate
    simpa [tE, uE, aE, orderedTrace] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a3 aE.a2 aE.a1 tE := by
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
        actualSigma aE.multiplier aE.a1 aE.a2 uE tE := by
    simpa [alpha, beta] using
      actual_secondDirected_coset_weights_mul
        aE.multiplier aE.a1 aE.a2 uE tE q r
  have hsigma : alpha * beta ≠ 0 := by
    rw [hweights]
    exact actualSigma_ne_zero_of_reverseCandidateRegular
      aE.multiplier aE.a3 aE.a1 aE.a2 uE tE htraceE hregularE
  have hEven :
      shiftedTraceEvenObstruction (alpha * beta) gamma ≠ 0 := by
    rw [hweights]
    exact actualSecondEvenObstruction_ne_zero_of_candidateRegular
      aE.multiplier aE.a3 aE.a1 aE.a2 uE tE
        htraceE hA2E hregularE
  have hreachable :
      ∀ h : Subgroup.zpowers (q ^ 2),
        ∃ n : ℕ,
          weightedSplitTorusTrace alpha beta h + gamma =
            f (orderedTrace a.multiplier a.a2
              (((rotation3 a)^[n]) x).x2) := by
    intro h
    have hDE : discriminant tE ≠ 0 := by
      simpa [discriminant] using hregularE.1
    have heigen' :
        tE = (q : E) + ((q⁻¹ : Eˣ) : E) := by
      simpa [tE, E, f, splitTorusTrace] using heigen
    obtain ⟨n, hn⟩ :=
      exists_iterate_fiberPoint3_eq_mul_zpowers_sq
        aE uE tE q r hDE heigen' htraceE h
    let y : Point (ZMod p) := ((rotation3 a)^[n]) x
    have hyPoint :
        mapPoint f y =
          fiberPoint3 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := by
      calc
        mapPoint f y =
            ((rotation3 aE)^[n]) (mapPoint f x) := by
          simpa [y, aE] using mapPoint_iterate_rotation3 f a x n
        _ = ((rotation3 aE)^[n])
            (fiberPoint3 aE uE tE (q : E) (r : E)) := by
          simpa [E, f, aE, uE, tE] using congrArg
            (fun z : Point E ↦ ((rotation3 aE)^[n]) z) hdiagonalized
        _ = fiberPoint3 aE uE tE (q : E)
            ((r * (h : Eˣ) : Eˣ) : E) := hn
    refine ⟨n, ?_⟩
    calc
      weightedSplitTorusTrace alpha beta h + gamma =
          orderedTrace aE.multiplier aE.a2
            (fiberPoint3 aE uE tE (q : E)
              ((r * (h : Eˣ) : Eˣ) : E)).x2 := by
        change
          weightedSplitTorusTrace alpha beta h + gamma =
            aE.multiplier *
                (fiberPair aE.a1 aE.a2 uE tE (q : E)
                  ((r * (h : Eˣ) : Eˣ) : E)).2 -
              aE.a2
        simpa [alpha, beta, gamma] using
          (secondTrace_fiberPair_mul_eq_weightedSplitTorusTrace
            aE.multiplier aE.a1 aE.a2 uE tE q r (h : Eˣ)).symm
      _ = orderedTrace aE.multiplier aE.a2 (mapPoint f y).x2 := by
        rw [hyPoint]
      _ = f (orderedTrace a.multiplier a.a2 y.x2) := by
        simp [orderedTrace, aE, mapPoint]
      _ = f (orderedTrace a.multiplier a.a2
          (((rotation3 a)^[n]) x).x2) := rfl
  exact
    exists_iterate_with_larger_actualOrder_and_regular_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation3 a) x
        (fun y ↦ orderedTrace a.multiplier a.a2 y.x2)
        a.a2 targetB targetC hA2 hTargetB
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hmargin

/-- Diagonalized third-to-second step returning the reverse frame
`(a₂, a₃, a₁)`. -/
theorem
    exists_rotation3_iterate_axisTwo_with_larger_actualOrder_and_reverseRegular_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a3 a.a2 a.a1 t)
    (q r : (quadraticFiniteField p)ˣ)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (hdiagonalized :
      mapPoint (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint3
          (mapCoefficients
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
      let y := ((rotation3 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a2 y.x2
      OrderedTraceCandidateRegular a.a2 a.a3 a.a1 t' ∧
        rotationLinearOrder t < rotationLinearOrder t' :=
  exists_rotation3_iterate_axisTwo_with_larger_actualOrder_and_regular_in_targetFrame_of_diagonalizedFiber
    p hpTwo delta hdelta a u t x hx hcoordinate hA2
      a.a3 a.a1 hA3 hregular q r heigen hdiagonalized
      hbelowEndgame hmargin

/-- Non-diagonalized `.thirdSecond` step returning regularity for
`.thirdSecond.reverse = .secondThird`. -/
theorem
    exists_rotation3_iterate_axisTwo_with_larger_actualOrder_and_reverseRegular
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hregular :
      OrderedTraceCandidateRegular a.a3 a.a2 a.a1
        (traceAt a .third x))
    (hbelowEndgame :
      (rotationLinearOrderAt a .third x : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hmargin :
      2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p
              (rotationLinearOrderAt a .third x) +
          20 <
        (rotationLinearOrderAt a .third x : ℝ)) :
    ∃ n : ℕ,
      let y := ((rotation3 a)^[n]) x
      OrderedTraceCandidateRegular a.a2 a.a3 a.a1
          (traceAt a .second y) ∧
        rotationLinearOrderAt a .third x <
          rotationLinearOrderAt a .second y := by
  let t := traceAt a .third x
  have hD : discriminant t ≠ 0 := by
    simpa [t, discriminant] using hregular.1
  have hproduct :
      centeredFiberProduct a.a1 a.a2 x.x3 t ≠ 0 := by
    have hswap :=
      centeredFiberProduct_ne_zero_of_candidateRegular
        a.multiplier a.a3 a.a2 a.a1 x.x3 t rfl hregular
    simpa [centeredFiberProduct_swap] using hswap
  obtain ⟨q, r, heigen, hdiagonalized⟩ :=
    exists_axisThree_actualFiber_diagonalization
      p hpTwo a x.x3 t x hx rfl rfl hD hproduct
  simpa [t, rotationLinearOrderAt, traceAt, orderedTrace,
    coefficientAt, coordinateAt] using
    exists_rotation3_iterate_axisTwo_with_larger_actualOrder_and_reverseRegular_of_diagonalizedFiber
      p hpTwo delta hdelta a x.x3 t x hx rfl hA2 hA3 hregular
        q r heigen hdiagonalized
        (by
          simpa [t, rotationLinearOrderAt, traceAt, orderedTrace, coefficientAt,
            coordinateAt] using hbelowEndgame)
        (by
          simpa [t, rotationLinearOrderAt, traceAt, orderedTrace, coefficientAt,
            coordinateAt] using hmargin)

/-- Every directed state admits an iterable step to its reverse state.

The selected rotation is determined by `axes.fixed`; the target trace is
`axes.target`.  The two explicit coefficient hypotheses are exactly those
needed by the current target trace and by the second coefficient of the
reverse ordered frame. -/
theorem exists_directedRotation_iterate_with_larger_actualOrder_and_reverseRegular
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (axes : DirectedAxes)
    (x : Point (ZMod p))
    (hx : IsSolution a x)
    (hTarget : coefficientAt axes.target a ^ 2 ≠ 4)
    (hFixed : coefficientAt axes.fixed a ^ 2 ≠ 4)
    (hregular :
      OrderedTraceCandidateRegular
        (directedCoefficients a axes).a1
        (directedCoefficients a axes).a2
        (directedCoefficients a axes).a3
        (traceAt a axes.fixed x))
    (hbelowEndgame :
      (rotationLinearOrderAt a axes.fixed x : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hmargin :
      2 *
          (((p - 1).divisors.card +
            (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p
              (rotationLinearOrderAt a axes.fixed x) +
          20 <
        (rotationLinearOrderAt a axes.fixed x : ℝ)) :
    ∃ n : ℕ,
      let y := ((rotationAt a axes.fixed)^[n]) x
      let nextFrame := directedCoefficients a axes.reverse
      OrderedTraceCandidateRegular
          nextFrame.a1 nextFrame.a2 nextFrame.a3
          (traceAt a axes.target y) ∧
        rotationLinearOrderAt a axes.fixed x <
          rotationLinearOrderAt a axes.target y := by
  cases axes with
  | firstSecond =>
      simpa [rotationAt, directedCoefficients, coefficientAt,
        DirectedAxes.fixed, DirectedAxes.target, DirectedAxes.remaining,
        DirectedAxes.reverse] using
        exists_rotation1_iterate_axisTwo_with_larger_actualOrder_and_reverseRegular
          p hpTwo delta hdelta a x hx hTarget hFixed hregular
            hbelowEndgame hmargin
  | firstThird =>
      simpa [rotationAt, directedCoefficients, coefficientAt,
        DirectedAxes.fixed, DirectedAxes.target, DirectedAxes.remaining,
        DirectedAxes.reverse] using
        exists_rotation1_iterate_axisThree_with_larger_actualOrder_and_reverseRegular
          p hpTwo delta hdelta a x hx hTarget hFixed hregular
            hbelowEndgame hmargin
  | secondFirst =>
      simpa [rotationAt, directedCoefficients, coefficientAt,
        DirectedAxes.fixed, DirectedAxes.target, DirectedAxes.remaining,
        DirectedAxes.reverse] using
        exists_rotation2_iterate_axisOne_with_larger_actualOrder_and_reverseRegular
          p hpTwo delta hdelta a x hx hTarget hFixed hregular
            hbelowEndgame hmargin
  | secondThird =>
      simpa [rotationAt, directedCoefficients, coefficientAt,
        DirectedAxes.fixed, DirectedAxes.target, DirectedAxes.remaining,
        DirectedAxes.reverse] using
        exists_rotation2_iterate_axisThree_with_larger_actualOrder_and_reverseRegular
          p hpTwo delta hdelta a x hx hTarget hFixed hregular
            hbelowEndgame hmargin
  | thirdFirst =>
      simpa [rotationAt, directedCoefficients, coefficientAt,
        DirectedAxes.fixed, DirectedAxes.target, DirectedAxes.remaining,
        DirectedAxes.reverse] using
        exists_rotation3_iterate_axisOne_with_larger_actualOrder_and_reverseRegular
          p hpTwo delta hdelta a x hx hTarget hFixed hregular
            hbelowEndgame hmargin
  | thirdSecond =>
      simpa [rotationAt, directedCoefficients, coefficientAt,
        DirectedAxes.fixed, DirectedAxes.target, DirectedAxes.remaining,
        DirectedAxes.reverse] using
        exists_rotation3_iterate_axisTwo_with_larger_actualOrder_and_reverseRegular
          p hpTwo delta hdelta a x hx hTarget hFixed hregular
            hbelowEndgame hmargin

end

end GenMarkoff.General.Assembly
