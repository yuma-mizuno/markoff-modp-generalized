import GenMarkoff.General.MiddleGame.ParityClosedOrderEscape
import GenMarkoff.General.MiddleGame.DirectedOrderGrowth

/-!
# Directed strict actual-order growth

This file composes the parity-closed square-coset escape theorem with the
six directed fixed-coefficient fiber parametrizations.  The coefficient
triple is never permuted: each theorem names its fixed rotation axis and
target coordinate explicitly.

The doubled Corvaja--Zannier cube and linear hypotheses are the cost of
closing the unsquared-order family under the parity quotient
`d ↦ d / gcd(d, 2)`.
-/

namespace GenMarkoff.General.MiddleGame

open BGS.Markoff
open GenMarkoff.Symmetric.MiddleGame

noncomputable section

section SurfaceSpecializations

/-- Strict actual-order growth from the first-coordinate fiber to the
second-coordinate trace, in the ordered frame `(a₁, a₂, a₃)`. -/
theorem
    exists_rotation1_iterate_axisTwo_with_larger_actualOrder_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t)
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
    (hcube :
      (2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card))) ^ 3 <
          rotationLinearOrder t)
    (hlinear :
      2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) *
          rotationLinearOrder t < p) :
    ∃ n : ℕ,
      let y := ((rotation1 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a2 y.x2
      rotationLinearOrder t < rotationLinearOrder t' := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := mapCoefficients f a
  let uE : E := f u
  let tE : E := f t
  let alpha : E := actualAlpha aE.multiplier * (r : E)
  let beta : E :=
    actualBeta aE.multiplier aE.a2 aE.a3 uE tE / (r : E)
  let gamma : E :=
    actualGammaFirst aE.multiplier aE.a2 aE.a3 uE tE
  have hDBase : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a1 uE := by
    have hmap := congrArg f hcoordinate
    simpa [tE, uE, aE, orderedTrace] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a1 aE.a2 aE.a3 tE := by
    simpa [aE, tE] using
      orderedTraceCandidateRegular_map f f.injective hregular
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
          orderedTrace aE.multiplier aE.a2
            (fiberPoint1 aE uE tE (q : E)
              ((r * (h : Eˣ) : Eˣ) : E)).x2 := by
        simpa [alpha, beta, gamma] using
          (orderedTrace_fiberPoint1_mul_eq_weightedSplitTorusTrace
            aE uE tE q r (h : Eˣ)).symm
      _ = orderedTrace aE.multiplier aE.a2 (mapPoint f y).x2 := by
        rw [hyPoint]
      _ = f (orderedTrace a.multiplier a.a2 y.x2) := by
        simp [orderedTrace, aE, mapPoint]
      _ = f (orderedTrace a.multiplier a.a2
          (((rotation1 a)^[n]) x).x2) := rfl
  exact
    exists_iterate_with_larger_actualOrder_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation1 a) x
        (fun y ↦ orderedTrace a.multiplier a.a2 y.x2)
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hcube hlinear

/-- Strict actual-order growth from the first-coordinate fiber to the
third-coordinate trace, in the reverse ordered frame `(a₁, a₃, a₂)`. -/
theorem
    exists_rotation1_iterate_axisThree_with_larger_actualOrder_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u)
    (hA3 : a.a3 ^ 2 ≠ 4)
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
    (hcube :
      (2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card))) ^ 3 <
          rotationLinearOrder t)
    (hlinear :
      2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) *
          rotationLinearOrder t < p) :
    ∃ n : ℕ,
      let y := ((rotation1 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a3 y.x3
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
      orderedTraceCandidateRegular_map f f.injective hregular
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
    exists_iterate_with_larger_actualOrder_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation1 a) x
        (fun y ↦ orderedTrace a.multiplier a.a3 y.x3)
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hcube hlinear

/-- Strict actual-order growth from the second-coordinate fiber to the
third-coordinate trace, in the ordered frame `(a₂, a₃, a₁)`. -/
theorem
    exists_rotation2_iterate_axisThree_with_larger_actualOrder_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u)
    (hA3 : a.a3 ^ 2 ≠ 4)
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
    (hcube :
      (2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card))) ^ 3 <
          rotationLinearOrder t)
    (hlinear :
      2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) *
          rotationLinearOrder t < p) :
    ∃ n : ℕ,
      let y := ((rotation2 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a3 y.x3
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
      orderedTraceCandidateRegular_map f f.injective hregular
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
    exists_iterate_with_larger_actualOrder_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation2 a) x
        (fun y ↦ orderedTrace a.multiplier a.a3 y.x3)
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hcube hlinear

/-- Strict actual-order growth from the second-coordinate fiber to the
first-coordinate trace, in the reverse ordered frame `(a₂, a₁, a₃)`. -/
theorem
    exists_rotation2_iterate_axisOne_with_larger_actualOrder_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u)
    (hA1 : a.a1 ^ 2 ≠ 4)
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
    (hcube :
      (2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card))) ^ 3 <
          rotationLinearOrder t)
    (hlinear :
      2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) *
          rotationLinearOrder t < p) :
    ∃ n : ℕ,
      let y := ((rotation2 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a1 y.x1
      rotationLinearOrder t < rotationLinearOrder t' := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := mapCoefficients f a
  let uE : E := f u
  let tE : E := f t
  let alpha : E :=
    (aE.multiplier * (q : E)) * (r : E)
  let beta : E :=
    (aE.multiplier * centeredFiberProduct aE.a3 aE.a1 uE tE /
      (q : E)) / (r : E)
  let gamma : E :=
    actualGammaSecond aE.multiplier aE.a3 aE.a1 uE tE
  have hDBase : discriminant t ≠ 0 := by
    simpa [discriminant] using hregular.1
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a2 uE := by
    have hmap := congrArg f hcoordinate
    simpa [tE, uE, aE, orderedTrace] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a2 aE.a1 aE.a3 tE := by
    simpa [aE, tE] using
      orderedTraceCandidateRegular_map f f.injective hregular
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
          orderedTrace aE.multiplier aE.a1
            (fiberPoint2 aE uE tE (q : E)
              ((r * (h : Eˣ) : Eˣ) : E)).x1 := by
        change
          weightedSplitTorusTrace alpha beta h + gamma =
            aE.multiplier *
                (fiberPair aE.a3 aE.a1 uE tE (q : E)
                  ((r * (h : Eˣ) : Eˣ) : E)).2 -
              aE.a1
        simpa [alpha, beta, gamma] using
          (secondTrace_fiberPair_mul_eq_weightedSplitTorusTrace
            aE.multiplier aE.a3 aE.a1 uE tE q r (h : Eˣ)).symm
      _ = orderedTrace aE.multiplier aE.a1 (mapPoint f y).x1 := by
        rw [hyPoint]
      _ = f (orderedTrace a.multiplier a.a1 y.x1) := by
        simp [orderedTrace, aE, mapPoint]
      _ = f (orderedTrace a.multiplier a.a1
          (((rotation2 a)^[n]) x).x1) := rfl
  exact
    exists_iterate_with_larger_actualOrder_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation2 a) x
        (fun y ↦ orderedTrace a.multiplier a.a1 y.x1)
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hcube hlinear

/-- Strict actual-order growth from the third-coordinate fiber to the
first-coordinate trace, in the ordered frame `(a₃, a₁, a₂)`. -/
theorem
    exists_rotation3_iterate_axisOne_with_larger_actualOrder_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u)
    (hA1 : a.a1 ^ 2 ≠ 4)
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
    (hcube :
      (2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card))) ^ 3 <
          rotationLinearOrder t)
    (hlinear :
      2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) *
          rotationLinearOrder t < p) :
    ∃ n : ℕ,
      let y := ((rotation3 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a1 y.x1
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
      orderedTraceCandidateRegular_map f f.injective hregular
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
    exists_iterate_with_larger_actualOrder_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation3 a) x
        (fun y ↦ orderedTrace a.multiplier a.a1 y.x1)
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hcube hlinear

/-- Strict actual-order growth from the third-coordinate fiber to the
second-coordinate trace, in the reverse ordered frame `(a₃, a₂, a₁)`. -/
theorem
    exists_rotation3_iterate_axisTwo_with_larger_actualOrder_of_diagonalizedFiber
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (_hx : IsSolution a x)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u)
    (hA2 : a.a2 ^ 2 ≠ 4)
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
    (hcube :
      (2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card))) ^ 3 <
          rotationLinearOrder t)
    (hlinear :
      2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) *
          rotationLinearOrder t < p) :
    ∃ n : ℕ,
      let y := ((rotation3 a)^[n]) x
      let t' := orderedTrace a.multiplier a.a2 y.x2
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
      orderedTraceCandidateRegular_map f f.injective hregular
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
    exists_iterate_with_larger_actualOrder_of_squareCosetTrace
      p hpTwo delta hdelta t hDBase q heigen
        (rotation3 a) x
        (fun y ↦ orderedTrace a.multiplier a.a2 y.x2)
        alpha beta gamma hsigma hEven hreachable
        hbelowEndgame hcube hlinear

end SurfaceSpecializations

end

end GenMarkoff.General.MiddleGame
