import GenMarkoff.Symmetric.Assembly.LargeRegularRouting
import GenMarkoff.Symmetric.Opening.CenteredEscape
import GenMarkoff.Symmetric.Cage.FiberConnectivity
import BGS.Markoff.MiddleGame.DivisorRange

/-!
# Entering the regular symmetric middle game

The counting argument in `LargeRegularRouting` is stated on the first
coordinate fiber.  This file transports it to the other two axes, packages
the resulting points as honest one-step iterates, and isolates the finite
affine-centered obstruction needed by the giant-orbit assembly.

There is an unavoidable square-root loss at this boundary: producing an
adjacent trace of order at least `B` requires an incoming cycle longer than
`18 + 4 * B^2`.  Consequently the eventual interface below uses an incoming
exponent `η` and an outgoing exponent `δ`, with `2 * δ < η`.
-/

namespace GenMarkoff.Symmetric.Assembly

open BGS.Markoff Filter
open GenMarkoff.Symmetric.Cage

noncomputable section

/-- The elementary number of points discarded when routing a cycle to a
candidate-regular adjacent trace of order at least `bound`. -/
def regularRoutingCost (bound : ℕ) : ℕ :=
  14 + 2 * (2 + 2 * bound ^ 2)

/-- The buffered integral cutoff associated to a real power. -/
def bufferedPowerBound (p : ℕ) (δ : ℝ) : ℕ :=
  Nat.ceil ((p : ℝ) ^ δ) + 1

/-- One honest iterate of one of the three actual symmetric one-step
generators relates `x` to `y`. -/
def IsActualOneStepIterate
    {R : Type*} [CommRing R] (c : R) (x y : Point R) : Prop :=
  (∃ n : ℕ, ((oneStep1 c)^[n]) x = y) ∨
    (∃ n : ℕ, ((oneStep2 c)^[n]) x = y) ∨
      (∃ n : ℕ, ((oneStep3 c)^[n]) x = y)

/-- A point has a candidate-regular coordinate trace whose half-step order
meets `bound`. -/
def HasRegularTraceOfOrderAtLeast
    (p : ℕ) [Fact p.Prime] (c : ZMod p) (bound : ℕ)
    (x : Point (ZMod p)) : Prop :=
  ∃ axis : Axis,
    OrderedTraceCandidateRegular c c c (traceAt c axis x) ∧
      bound ≤ halfStepOrder (traceAt c axis x)

/-- The moving-coordinate pair on the selected axis is not its affine
center. -/
def AxisNoncentered
    {R : Type*} [Field R] (c : R) (axis : Axis) (x : Point R) : Prop :=
  match axis with
  | .first =>
      centerCoordinates (fiberCenter c x.x1 (trace c x.x1))
        (movingCoordinates1 x) ≠ (0, 0)
  | .second =>
      centerCoordinates (fiberCenter c x.x2 (trace c x.x2))
        (movingCoordinates2 x) ≠ (0, 0)
  | .third =>
      centerCoordinates (fiberCenter c x.x3 (trace c x.x3))
        (movingCoordinates3 x) ≠ (0, 0)

/-! ## Cyclic forms of the large-cycle routing lemma -/

/-- A large nonparabolic, noncentered second-axis cycle contains a
candidate-regular third trace of prescribed minimum order. -/
theorem exists_regular_adjacent_order_ge_of_large_axisTwo_noncentered_cycle
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (x : Point (ZMod p)) (bound : ℕ)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (hparabolic : trace c x.x2 ^ 2 ≠ 4)
    (hnoncentered :
      centerCoordinates (fiberCenter c x.x2 (trace c x.x2))
        (movingCoordinates2 x) ≠ (0, 0))
    (hlarge :
      14 + 2 * (2 + 2 * bound ^ 2) <
        halfStepOrder (trace c x.x2)) :
    ∃ y ∈ oneStep2Cycle p c x (halfStepOrder (trace c x.x2)),
      OrderedTraceCandidateRegular c c c (trace c y.x3) ∧
        bound ≤ halfStepOrder (trace c y.x3) := by
  have hx' : IsSolution (coefficients c) (cycleLeftEquiv x) :=
    (isSolution_cycleLeftEquiv c x).2 hx
  obtain ⟨z, hz, hzRegular, hzOrder⟩ :=
    exists_regular_adjacent_order_ge_of_large_noncentered_cycle
      p hpTwo c (cycleLeftEquiv x) bound hmultiplier hc hx'
        (by simpa [cycleLeftEquiv] using hparabolic)
        (by
          simpa [cycleLeftEquiv, movingCoordinates1, movingCoordinates2]
            using hnoncentered)
        (by simpa [cycleLeftEquiv] using hlarge)
  have hzImage :
      z ∈ (oneStep2Cycle p c x
        (halfStepOrder (trace c x.x2))).image cycleLeftEquiv := by
    rw [image_cycleLeftEquiv_oneStep2Cycle]
    simpa [cycleLeftEquiv] using hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hzImage
  exact ⟨y, hy, by simpa [cycleLeftEquiv] using hzRegular,
    by simpa [cycleLeftEquiv] using hzOrder⟩

/-- A large nonparabolic, noncentered third-axis cycle contains a
candidate-regular first trace of prescribed minimum order. -/
theorem exists_regular_adjacent_order_ge_of_large_axisThree_noncentered_cycle
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (x : Point (ZMod p)) (bound : ℕ)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (hparabolic : trace c x.x3 ^ 2 ≠ 4)
    (hnoncentered :
      centerCoordinates (fiberCenter c x.x3 (trace c x.x3))
        (movingCoordinates3 x) ≠ (0, 0))
    (hlarge :
      14 + 2 * (2 + 2 * bound ^ 2) <
        halfStepOrder (trace c x.x3)) :
    ∃ y ∈ oneStep3Cycle p c x (halfStepOrder (trace c x.x3)),
      OrderedTraceCandidateRegular c c c (trace c y.x1) ∧
        bound ≤ halfStepOrder (trace c y.x1) := by
  have hx' : IsSolution (coefficients c) (cycleRightEquiv x) :=
    (isSolution_cycleRightEquiv c x).2 hx
  obtain ⟨z, hz, hzRegular, hzOrder⟩ :=
    exists_regular_adjacent_order_ge_of_large_noncentered_cycle
      p hpTwo c (cycleRightEquiv x) bound hmultiplier hc hx'
        (by simpa [cycleRightEquiv, cycleLeftEquiv] using hparabolic)
        (by
          simpa [cycleRightEquiv, cycleLeftEquiv, movingCoordinates1,
            movingCoordinates3] using hnoncentered)
        (by simpa [cycleRightEquiv, cycleLeftEquiv] using hlarge)
  have hzImage :
      z ∈ (oneStep3Cycle p c x
        (halfStepOrder (trace c x.x3))).image cycleRightEquiv := by
    rw [image_cycleRightEquiv_oneStep3Cycle]
    simpa [cycleRightEquiv, cycleLeftEquiv] using hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hzImage
  exact ⟨y, hy,
    by simpa [cycleRightEquiv, cycleLeftEquiv] using hzRegular,
    by simpa [cycleRightEquiv, cycleLeftEquiv] using hzOrder⟩

/-- Trace-`2` parabolic routing on the second axis. -/
theorem exists_regular_adjacent_order_ge_of_oneStep2_trace_eq_two
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (x : Point (ZMod p)) (bound : ℕ)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (htrace : trace c x.x2 = 2)
    (hlarge : 14 + 2 * (2 + 2 * bound ^ 2) < p) :
    ∃ y ∈ oneStep2Cycle p c x p,
      OrderedTraceCandidateRegular c c c (trace c y.x3) ∧
        bound ≤ halfStepOrder (trace c y.x3) := by
  have hx' : IsSolution (coefficients c) (cycleLeftEquiv x) :=
    (isSolution_cycleLeftEquiv c x).2 hx
  obtain ⟨z, hz, hzRegular, hzOrder⟩ :=
    exists_regular_adjacent_order_ge_of_oneStep1_trace_eq_two
      p hpTwo c (cycleLeftEquiv x) bound hmultiplier hc hx'
        (by simpa [cycleLeftEquiv] using htrace) hlarge
  have hzImage :
      z ∈ (oneStep2Cycle p c x p).image cycleLeftEquiv := by
    rw [image_cycleLeftEquiv_oneStep2Cycle]
    exact hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hzImage
  exact ⟨y, hy, by simpa [cycleLeftEquiv] using hzRegular,
    by simpa [cycleLeftEquiv] using hzOrder⟩

/-- Trace-`-2` parabolic routing on the second axis. -/
theorem exists_regular_adjacent_order_ge_of_oneStep2_trace_eq_neg_two
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (x : Point (ZMod p)) (bound : ℕ)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (htrace : trace c x.x2 = -2)
    (hlarge : 14 + 2 * (2 + 2 * bound ^ 2) < 2 * p) :
    ∃ y ∈ oneStep2Cycle p c x (2 * p),
      OrderedTraceCandidateRegular c c c (trace c y.x3) ∧
        bound ≤ halfStepOrder (trace c y.x3) := by
  have hx' : IsSolution (coefficients c) (cycleLeftEquiv x) :=
    (isSolution_cycleLeftEquiv c x).2 hx
  obtain ⟨z, hz, hzRegular, hzOrder⟩ :=
    exists_regular_adjacent_order_ge_of_oneStep1_trace_eq_neg_two
      p hpTwo c (cycleLeftEquiv x) bound hmultiplier hc hx'
        (by simpa [cycleLeftEquiv] using htrace) hlarge
  have hzImage :
      z ∈ (oneStep2Cycle p c x (2 * p)).image cycleLeftEquiv := by
    rw [image_cycleLeftEquiv_oneStep2Cycle]
    exact hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hzImage
  exact ⟨y, hy, by simpa [cycleLeftEquiv] using hzRegular,
    by simpa [cycleLeftEquiv] using hzOrder⟩

/-- Trace-`2` parabolic routing on the third axis. -/
theorem exists_regular_adjacent_order_ge_of_oneStep3_trace_eq_two
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (x : Point (ZMod p)) (bound : ℕ)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (htrace : trace c x.x3 = 2)
    (hlarge : 14 + 2 * (2 + 2 * bound ^ 2) < p) :
    ∃ y ∈ oneStep3Cycle p c x p,
      OrderedTraceCandidateRegular c c c (trace c y.x1) ∧
        bound ≤ halfStepOrder (trace c y.x1) := by
  have hx' : IsSolution (coefficients c) (cycleRightEquiv x) :=
    (isSolution_cycleRightEquiv c x).2 hx
  obtain ⟨z, hz, hzRegular, hzOrder⟩ :=
    exists_regular_adjacent_order_ge_of_oneStep1_trace_eq_two
      p hpTwo c (cycleRightEquiv x) bound hmultiplier hc hx'
        (by simpa [cycleRightEquiv, cycleLeftEquiv] using htrace) hlarge
  have hzImage :
      z ∈ (oneStep3Cycle p c x p).image cycleRightEquiv := by
    rw [image_cycleRightEquiv_oneStep3Cycle]
    exact hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hzImage
  exact ⟨y, hy,
    by simpa [cycleRightEquiv, cycleLeftEquiv] using hzRegular,
    by simpa [cycleRightEquiv, cycleLeftEquiv] using hzOrder⟩

/-- Trace-`-2` parabolic routing on the third axis. -/
theorem exists_regular_adjacent_order_ge_of_oneStep3_trace_eq_neg_two
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (x : Point (ZMod p)) (bound : ℕ)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (htrace : trace c x.x3 = -2)
    (hlarge : 14 + 2 * (2 + 2 * bound ^ 2) < 2 * p) :
    ∃ y ∈ oneStep3Cycle p c x (2 * p),
      OrderedTraceCandidateRegular c c c (trace c y.x1) ∧
        bound ≤ halfStepOrder (trace c y.x1) := by
  have hx' : IsSolution (coefficients c) (cycleRightEquiv x) :=
    (isSolution_cycleRightEquiv c x).2 hx
  obtain ⟨z, hz, hzRegular, hzOrder⟩ :=
    exists_regular_adjacent_order_ge_of_oneStep1_trace_eq_neg_two
      p hpTwo c (cycleRightEquiv x) bound hmultiplier hc hx'
        (by simpa [cycleRightEquiv, cycleLeftEquiv] using htrace) hlarge
  have hzImage :
      z ∈ (oneStep3Cycle p c x (2 * p)).image cycleRightEquiv := by
    rw [image_cycleRightEquiv_oneStep3Cycle]
    exact hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hzImage
  exact ⟨y, hy,
    by simpa [cycleRightEquiv, cycleLeftEquiv] using hzRegular,
    by simpa [cycleRightEquiv, cycleLeftEquiv] using hzOrder⟩

/-! ## Honest iterate packages -/

private theorem eq_two_or_eq_neg_two_of_sq_eq_four
    (p : ℕ) [Fact p.Prime] (t : ZMod p) (h : t ^ 2 = 4) :
    t = 2 ∨ t = -2 := by
  apply (sq_eq_sq_iff_eq_or_eq_neg).mp
  calc
    t ^ 2 = 4 := h
    _ = (2 : ZMod p) ^ 2 := by norm_num

/-- First-axis startup routing, with the semisimple and parabolic size
hypotheses kept explicit. -/
theorem exists_actual_regularTrace_of_axisOne
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (x : Point (ZMod p)) (bound : ℕ)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (hrouteable :
      trace c x.x1 ^ 2 = 4 ∨ AxisNoncentered c .first x)
    (hlargeSemisimple :
      trace c x.x1 ^ 2 ≠ 4 →
        regularRoutingCost bound < halfStepOrder (trace c x.x1))
    (hlargeParabolic : regularRoutingCost bound < p) :
    ∃ y : Point (ZMod p),
      IsSolution (coefficients c) y ∧
        IsActualOneStepIterate c x y ∧
          HasRegularTraceOfOrderAtLeast p c bound y := by
  by_cases hparabolic : trace c x.x1 ^ 2 = 4
  · rcases eq_two_or_eq_neg_two_of_sq_eq_four p _ hparabolic with
      htrace | htrace
    · obtain ⟨y, hy, hregular, horder⟩ :=
        exists_regular_adjacent_order_ge_of_oneStep1_trace_eq_two
          p hpTwo c x bound hmultiplier hc hx htrace
            (by simpa [regularRoutingCost] using hlargeParabolic)
      rw [oneStep1Cycle, Finset.mem_image] at hy
      obtain ⟨n, _hn, rfl⟩ := hy
      refine ⟨_, isSolution_iterate_oneStep1 c hx n,
        Or.inl ⟨n, rfl⟩, ?_⟩
      exact ⟨.second,
        by simpa [traceAt, coordinateAt] using hregular,
        by simpa [traceAt, coordinateAt] using horder⟩
    · obtain ⟨y, hy, hregular, horder⟩ :=
        exists_regular_adjacent_order_ge_of_oneStep1_trace_eq_neg_two
          p hpTwo c x bound hmultiplier hc hx htrace
            (by
              have hpPos := (Fact.out : p.Prime).pos
              have : regularRoutingCost bound < 2 * p := by omega
              simpa [regularRoutingCost] using this)
      rw [oneStep1Cycle, Finset.mem_image] at hy
      obtain ⟨n, _hn, rfl⟩ := hy
      refine ⟨_, isSolution_iterate_oneStep1 c hx n,
        Or.inl ⟨n, rfl⟩, ?_⟩
      exact ⟨.second,
        by simpa [traceAt, coordinateAt] using hregular,
        by simpa [traceAt, coordinateAt] using horder⟩
  · have hnoncentered := hrouteable.resolve_left hparabolic
    obtain ⟨y, hy, hregular, horder⟩ :=
      exists_regular_adjacent_order_ge_of_large_noncentered_cycle
        p hpTwo c x bound hmultiplier hc hx
          hparabolic
          (by simpa [AxisNoncentered] using hnoncentered)
          (by simpa [regularRoutingCost] using
            hlargeSemisimple hparabolic)
    rw [oneStep1Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    refine ⟨_, isSolution_iterate_oneStep1 c hx n,
      Or.inl ⟨n, rfl⟩, ?_⟩
    exact ⟨.second,
      by simpa [traceAt, coordinateAt] using hregular,
      by simpa [traceAt, coordinateAt] using horder⟩

/-- Second-axis startup routing, with the semisimple and parabolic size
hypotheses kept explicit. -/
theorem exists_actual_regularTrace_of_axisTwo
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (x : Point (ZMod p)) (bound : ℕ)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (hrouteable :
      trace c x.x2 ^ 2 = 4 ∨ AxisNoncentered c .second x)
    (hlargeSemisimple :
      trace c x.x2 ^ 2 ≠ 4 →
        regularRoutingCost bound < halfStepOrder (trace c x.x2))
    (hlargeParabolic : regularRoutingCost bound < p) :
    ∃ y : Point (ZMod p),
      IsSolution (coefficients c) y ∧
        IsActualOneStepIterate c x y ∧
          HasRegularTraceOfOrderAtLeast p c bound y := by
  by_cases hparabolic : trace c x.x2 ^ 2 = 4
  · rcases eq_two_or_eq_neg_two_of_sq_eq_four p _ hparabolic with
      htrace | htrace
    · obtain ⟨y, hy, hregular, horder⟩ :=
        exists_regular_adjacent_order_ge_of_oneStep2_trace_eq_two
          p hpTwo c x bound hmultiplier hc hx htrace
            (by simpa [regularRoutingCost] using hlargeParabolic)
      rw [oneStep2Cycle, Finset.mem_image] at hy
      obtain ⟨n, _hn, rfl⟩ := hy
      refine ⟨_, isSolution_iterate_oneStep2 c hx n,
        Or.inr (Or.inl ⟨n, rfl⟩), ?_⟩
      exact ⟨.third,
        by simpa [traceAt, coordinateAt] using hregular,
        by simpa [traceAt, coordinateAt] using horder⟩
    · obtain ⟨y, hy, hregular, horder⟩ :=
        exists_regular_adjacent_order_ge_of_oneStep2_trace_eq_neg_two
          p hpTwo c x bound hmultiplier hc hx htrace
            (by
              have hpPos := (Fact.out : p.Prime).pos
              have : regularRoutingCost bound < 2 * p := by omega
              simpa [regularRoutingCost] using this)
      rw [oneStep2Cycle, Finset.mem_image] at hy
      obtain ⟨n, _hn, rfl⟩ := hy
      refine ⟨_, isSolution_iterate_oneStep2 c hx n,
        Or.inr (Or.inl ⟨n, rfl⟩), ?_⟩
      exact ⟨.third,
        by simpa [traceAt, coordinateAt] using hregular,
        by simpa [traceAt, coordinateAt] using horder⟩
  · have hnoncentered := hrouteable.resolve_left hparabolic
    obtain ⟨y, hy, hregular, horder⟩ :=
      exists_regular_adjacent_order_ge_of_large_axisTwo_noncentered_cycle
        p hpTwo c x bound hmultiplier hc hx
          hparabolic
          (by simpa [AxisNoncentered] using hnoncentered)
          (by simpa [regularRoutingCost] using
            hlargeSemisimple hparabolic)
    rw [oneStep2Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    refine ⟨_, isSolution_iterate_oneStep2 c hx n,
      Or.inr (Or.inl ⟨n, rfl⟩), ?_⟩
    exact ⟨.third,
      by simpa [traceAt, coordinateAt] using hregular,
      by simpa [traceAt, coordinateAt] using horder⟩

/-- Third-axis startup routing, with the semisimple and parabolic size
hypotheses kept explicit. -/
theorem exists_actual_regularTrace_of_axisThree
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (x : Point (ZMod p)) (bound : ℕ)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (hrouteable :
      trace c x.x3 ^ 2 = 4 ∨ AxisNoncentered c .third x)
    (hlargeSemisimple :
      trace c x.x3 ^ 2 ≠ 4 →
        regularRoutingCost bound < halfStepOrder (trace c x.x3))
    (hlargeParabolic : regularRoutingCost bound < p) :
    ∃ y : Point (ZMod p),
      IsSolution (coefficients c) y ∧
        IsActualOneStepIterate c x y ∧
          HasRegularTraceOfOrderAtLeast p c bound y := by
  by_cases hparabolic : trace c x.x3 ^ 2 = 4
  · rcases eq_two_or_eq_neg_two_of_sq_eq_four p _ hparabolic with
      htrace | htrace
    · obtain ⟨y, hy, hregular, horder⟩ :=
        exists_regular_adjacent_order_ge_of_oneStep3_trace_eq_two
          p hpTwo c x bound hmultiplier hc hx htrace
            (by simpa [regularRoutingCost] using hlargeParabolic)
      rw [oneStep3Cycle, Finset.mem_image] at hy
      obtain ⟨n, _hn, rfl⟩ := hy
      refine ⟨_, isSolution_iterate_oneStep3 c hx n,
        Or.inr (Or.inr ⟨n, rfl⟩), ?_⟩
      exact ⟨.first,
        by simpa [traceAt, coordinateAt] using hregular,
        by simpa [traceAt, coordinateAt] using horder⟩
    · obtain ⟨y, hy, hregular, horder⟩ :=
        exists_regular_adjacent_order_ge_of_oneStep3_trace_eq_neg_two
          p hpTwo c x bound hmultiplier hc hx htrace
            (by
              have hpPos := (Fact.out : p.Prime).pos
              have : regularRoutingCost bound < 2 * p := by omega
              simpa [regularRoutingCost] using this)
      rw [oneStep3Cycle, Finset.mem_image] at hy
      obtain ⟨n, _hn, rfl⟩ := hy
      refine ⟨_, isSolution_iterate_oneStep3 c hx n,
        Or.inr (Or.inr ⟨n, rfl⟩), ?_⟩
      exact ⟨.first,
        by simpa [traceAt, coordinateAt] using hregular,
        by simpa [traceAt, coordinateAt] using horder⟩
  · have hnoncentered := hrouteable.resolve_left hparabolic
    obtain ⟨y, hy, hregular, horder⟩ :=
      exists_regular_adjacent_order_ge_of_large_axisThree_noncentered_cycle
        p hpTwo c x bound hmultiplier hc hx
          hparabolic
          (by simpa [AxisNoncentered] using hnoncentered)
          (by simpa [regularRoutingCost] using
            hlargeSemisimple hparabolic)
    rw [oneStep3Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    refine ⟨_, isSolution_iterate_oneStep3 c hx n,
      Or.inr (Or.inr ⟨n, rfl⟩), ?_⟩
    exact ⟨.first,
      by simpa [traceAt, coordinateAt] using hregular,
      by simpa [traceAt, coordinateAt] using horder⟩

/-! ## The finite centered obstruction -/

/-- The two possible punctured points centered on the first or second
nonparabolic coordinate fiber. -/
def firstTwoCenteredExceptionalSet
    {K : Type*} [Field K] (c : K) : Finset (Point K) := by
  classical
  exact {Opening.axisOneCenteredExceptionalPoint c,
    cycleRightEquiv (Opening.axisOneCenteredExceptionalPoint c)}

theorem firstTwoCenteredExceptionalSet_card_le_two
    {K : Type*} [Field K] (c : K) :
    (firstTwoCenteredExceptionalSet c).card ≤ 2 := by
  classical
  rw [firstTwoCenteredExceptionalSet]
  calc
    (insert (Opening.axisOneCenteredExceptionalPoint c)
      ({cycleRightEquiv
        (Opening.axisOneCenteredExceptionalPoint c)} :
          Finset (Point K))).card ≤
        ({cycleRightEquiv
          (Opening.axisOneCenteredExceptionalPoint c)} : Finset (Point K)).card +
          1 :=
      Finset.card_insert_le _ _
    _ = 2 := by simp

/-- Including all three possible centered axes gives at most three points. -/
def allAxesCenteredExceptionalSet
    {K : Type*} [Field K] (c : K) : Finset (Point K) := by
  classical
  exact insert (cycleLeftEquiv (Opening.axisOneCenteredExceptionalPoint c))
    (firstTwoCenteredExceptionalSet c)

theorem allAxesCenteredExceptionalSet_card_le_three
    {K : Type*} [Field K] (c : K) :
    (allAxesCenteredExceptionalSet c).card ≤ 3 := by
  classical
  rw [allAxesCenteredExceptionalSet]
  calc
    (insert (cycleLeftEquiv (Opening.axisOneCenteredExceptionalPoint c))
      (firstTwoCenteredExceptionalSet c)).card ≤
        (firstTwoCenteredExceptionalSet c).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ 2 + 1 := Nat.add_le_add_right
      (firstTwoCenteredExceptionalSet_card_le_two c) 1
    _ = 3 := rfl

/-- Classification of the first-axis centered obstruction as membership in
the two-point assembly exceptional set. -/
theorem mem_firstTwoCenteredExceptionalSet_of_axisOne_centered
    {K : Type*} [Field K]
    (c : K) (x : Point K)
    (hthree : (3 : K) ≠ 0)
    (hmultiplier : multiplier c ≠ 0)
    (hx : IsSolution (coefficients c) x)
    (hxOrigin : x ≠ origin)
    (htrace : trace c x.x1 ^ 2 ≠ 4)
    (hcenter :
      centerCoordinates (fiberCenter c x.x1 (trace c x.x1))
        (movingCoordinates1 x) = (0, 0)) :
    x ∈ firstTwoCenteredExceptionalSet c := by
  classical
  have hxExceptional :=
    Opening.eq_axisOneCenteredExceptionalPoint_of_centered
      c x hthree hmultiplier hx hxOrigin htrace hcenter
  simp [firstTwoCenteredExceptionalSet, hxExceptional]

/-- Classification of the second-axis centered obstruction as membership in
the two-point assembly exceptional set. -/
theorem mem_firstTwoCenteredExceptionalSet_of_axisTwo_centered
    {K : Type*} [Field K]
    (c : K) (x : Point K)
    (hthree : (3 : K) ≠ 0)
    (hmultiplier : multiplier c ≠ 0)
    (hx : IsSolution (coefficients c) x)
    (hxOrigin : x ≠ origin)
    (htrace : trace c x.x2 ^ 2 ≠ 4)
    (hcenter :
      centerCoordinates (fiberCenter c x.x2 (trace c x.x2))
        (movingCoordinates2 x) = (0, 0)) :
    x ∈ firstTwoCenteredExceptionalSet c := by
  classical
  have hcyclic :=
    Opening.cycleLeft_eq_axisOneCenteredExceptionalPoint_of_centered
      c x hthree hmultiplier hx hxOrigin htrace hcenter
  have hxExceptional :
      x = cycleRightEquiv (Opening.axisOneCenteredExceptionalPoint c) := by
    calc
      x = cycleRightEquiv (cycleLeftEquiv x) := by
        change x = cycleLeftEquiv.symm (cycleLeftEquiv x)
        exact (cycleLeftEquiv.symm_apply_apply x).symm
      _ = cycleRightEquiv
          (Opening.axisOneCenteredExceptionalPoint c) :=
        congrArg cycleRightEquiv hcyclic
  simp [firstTwoCenteredExceptionalSet, hxExceptional]

/-! ## Eventual power cutoffs -/

/-- A buffered integral power cutoff is eventually dominated by every
strictly larger real power. -/
theorem eventually_bufferedPowerBound_cast_le_rpow
    {δ η : ℝ} (hδ : 0 < δ) (hδη : δ < η) :
    ∀ᶠ p : ℕ in atTop,
      ((bufferedPowerBound p δ : ℕ) : ℝ) ≤ (p : ℝ) ^ η := by
  have htwoEventually :
      ∀ᶠ p : ℕ in atTop, (2 : ℝ) * (p : ℝ) ^ (0 : ℝ) <
        (p : ℝ) ^ δ :=
    eventually_const_mul_rpow_lt_rpow (C := (2 : ℝ))
      (a := (0 : ℝ)) (b := δ) hδ
  have hdoubleEventually :
      ∀ᶠ p : ℕ in atTop, (2 : ℝ) * (p : ℝ) ^ δ <
        (p : ℝ) ^ η :=
    eventually_const_mul_rpow_lt_rpow (C := (2 : ℝ))
      (a := δ) (b := η) hδη
  filter_upwards [htwoEventually, hdoubleEventually] with p htwo hdouble
  have hpPowTwo : (2 : ℝ) < (p : ℝ) ^ δ := by
    simpa using htwo
  have hceil :
      ((bufferedPowerBound p δ : ℕ) : ℝ) <
        (p : ℝ) ^ δ + 2 := by
    rw [bufferedPowerBound]
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hceilBase := Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg p) δ)
    linarith
  have haddDouble :
      (p : ℝ) ^ δ + 2 < 2 * (p : ℝ) ^ δ := by
    calc
      (p : ℝ) ^ δ + 2 <
          (p : ℝ) ^ δ + (p : ℝ) ^ δ :=
        by
          simpa [add_comm] using
            add_lt_add_left hpPowTwo ((p : ℝ) ^ δ)
      _ = 2 * (p : ℝ) ^ δ := by ring
  exact le_of_lt (hceil.trans (haddDouble.trans hdouble))

/-- With `2δ < η < 1`, the quadratic discard cost for the outgoing
`δ`-cutoff is eventually smaller than both the incoming `η`-cutoff and the
parabolic cycle length `p`. -/
theorem eventually_regularRoutingCost_lt_powerBounds
    {δ η : ℝ} (hδ : 0 < δ) (htwoDelta : 2 * δ < η)
    (hη : η < 1) :
    ∀ᶠ p : ℕ in atTop,
      regularRoutingCost (bufferedPowerBound p δ) <
          bufferedPowerBound p η ∧
        regularRoutingCost (bufferedPowerBound p δ) < p := by
  let θ : ℝ := (δ + η / 2) / 2
  have hδθ : δ < θ := by
    dsimp [θ]
    linarith
  have htwoThetaEta : 2 * θ < η := by
    dsimp [θ]
    linarith
  have htwoThetaOne : 2 * θ < 1 :=
    htwoThetaEta.trans hη
  have hθPos : 0 < θ := hδ.trans hδθ
  have hboundEventually :
      ∀ᶠ p : ℕ in atTop,
        ((bufferedPowerBound p δ : ℕ) : ℝ) ≤ (p : ℝ) ^ θ :=
    eventually_bufferedPowerBound_cast_le_rpow hδ hδθ
  have hcostEta :
      ∀ᶠ p : ℕ in atTop,
        (22 : ℝ) * (p : ℝ) ^ (2 * θ) < (p : ℝ) ^ η :=
    eventually_const_mul_rpow_lt_rpow
      (C := (22 : ℝ)) (a := 2 * θ) (b := η) htwoThetaEta
  have hcostOne :
      ∀ᶠ p : ℕ in atTop,
        (22 : ℝ) * (p : ℝ) ^ (2 * θ) < (p : ℝ) ^ (1 : ℝ) :=
    eventually_const_mul_rpow_lt_rpow
      (C := (22 : ℝ)) (a := 2 * θ) (b := 1) htwoThetaOne
  filter_upwards [hboundEventually, hcostEta, hcostOne,
    eventually_ge_atTop 1] with p hbound hEta hOne hpOne
  let B := bufferedPowerBound p δ
  have hpRealOne : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpOne
  have hpPowOne : (1 : ℝ) ≤ (p : ℝ) ^ (2 * θ) :=
    Real.one_le_rpow hpRealOne (by linarith)
  have hBSq :
      (((B ^ 2 : ℕ) : ℕ) : ℝ) ≤ (p : ℝ) ^ (2 * θ) := by
    norm_num only [Nat.cast_pow]
    calc
      ((B : ℝ) ^ 2) ≤ (((p : ℝ) ^ θ) ^ 2) := by
        gcongr
      _ = (p : ℝ) ^ (θ * (2 : ℕ)) :=
        (Real.rpow_mul_natCast (Nat.cast_nonneg p) θ 2).symm
      _ = (p : ℝ) ^ (2 * θ) := by ring_nf
  have hcost :
      ((regularRoutingCost B : ℕ) : ℝ) ≤
        22 * (p : ℝ) ^ (2 * θ) := by
    rw [regularRoutingCost]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    calc
      14 + 2 * (2 + 2 * (B : ℝ) ^ 2) =
          18 + 4 * (B : ℝ) ^ 2 := by ring
      _ ≤ 18 + 4 * (p : ℝ) ^ (2 * θ) := by
        gcongr
        simpa using hBSq
      _ ≤ 18 * (p : ℝ) ^ (2 * θ) +
          4 * (p : ℝ) ^ (2 * θ) := by
        nlinarith
      _ = 22 * (p : ℝ) ^ (2 * θ) := by ring
  have hpowEtaLtBound :
      (p : ℝ) ^ η < ((bufferedPowerBound p η : ℕ) : ℝ) := by
    rw [bufferedPowerBound]
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hceilLe :
        (p : ℝ) ^ η ≤ (Nat.ceil ((p : ℝ) ^ η) : ℝ) :=
      Nat.le_ceil ((p : ℝ) ^ η)
    linarith
  constructor
  · exact_mod_cast hcost.trans_lt (hEta.trans hpowEtaLtBound)
  · have hOne' :
        22 * (p : ℝ) ^ (2 * θ) < (p : ℝ) := by
      simpa only [Real.rpow_one] using hOne
    exact_mod_cast hcost.trans_lt hOne'

/-- Threshold form of the startup cost estimate. -/
theorem exists_threshold_regularRoutingCost_lt_powerBounds
    {δ η : ℝ} (hδ : 0 < δ) (htwoDelta : 2 * δ < η)
    (hη : η < 1) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      regularRoutingCost (bufferedPowerBound p δ) <
          bufferedPowerBound p η ∧
        regularRoutingCost (bufferedPowerBound p δ) < p :=
  eventually_atTop.mp
    (eventually_regularRoutingCost_lt_powerBounds hδ htwoDelta hη)

/-! ## Uniform startup endpoint -/

/-- For all sufficiently large primes, every incoming coordinate above the
`η` cutoff which is either parabolic or noncentered reaches, by an actual
one-step iterate, a candidate-regular trace above the `δ` cutoff. -/
theorem exists_threshold_actual_regularTrace_startup
    {δ η : ℝ} (hδ : 0 < δ) (htwoDelta : 2 * δ < η)
    (hη : η < 1) :
    ∃ threshold : ℕ,
      ∀ (p : ℕ) [Fact p.Prime], threshold ≤ p →
      ∀ (c : ZMod p) (x : Point (ZMod p)) (axis : Axis),
        multiplier c ≠ 0 →
        c ^ 2 ≠ 4 →
        IsSolution (coefficients c) x →
        (traceAt c axis x) ^ 2 = 4 ∨
          (AxisNoncentered c axis x ∧
            bufferedPowerBound p η ≤
              halfStepOrder (traceAt c axis x)) →
        ∃ y : Point (ZMod p),
          IsSolution (coefficients c) y ∧
            IsActualOneStepIterate c x y ∧
              HasRegularTraceOfOrderAtLeast p c
                (bufferedPowerBound p δ) y := by
  obtain ⟨costThreshold, hcostThreshold⟩ :=
    exists_threshold_regularRoutingCost_lt_powerBounds
      hδ htwoDelta hη
  refine ⟨costThreshold + 3, ?_⟩
  intro p _inst hp c x axis hmultiplier hc hx hrouteable
  have hpTwo : p ≠ 2 := by omega
  have hcost := hcostThreshold p (by omega)
  have hrouteable' :
      (traceAt c axis x) ^ 2 = 4 ∨ AxisNoncentered c axis x :=
    hrouteable.imp_right And.left
  have hlarge' :
      (traceAt c axis x) ^ 2 ≠ 4 →
        regularRoutingCost (bufferedPowerBound p δ) <
          halfStepOrder (traceAt c axis x) := by
    intro hnonparabolic
    rcases hrouteable with hparabolic | ⟨_hnoncentered, hlarge⟩
    · exact (hnonparabolic hparabolic).elim
    · exact hcost.1.trans_le hlarge
  cases axis with
  | first =>
      apply exists_actual_regularTrace_of_axisOne
        p hpTwo c x (bufferedPowerBound p δ) hmultiplier hc hx
      · simpa [traceAt, coordinateAt, AxisNoncentered] using hrouteable'
      · simpa [traceAt, coordinateAt] using hlarge'
      · exact hcost.2
  | second =>
      apply exists_actual_regularTrace_of_axisTwo
        p hpTwo c x (bufferedPowerBound p δ) hmultiplier hc hx
      · simpa [traceAt, coordinateAt, AxisNoncentered] using hrouteable'
      · simpa [traceAt, coordinateAt] using hlarge'
      · exact hcost.2
  | third =>
      apply exists_actual_regularTrace_of_axisThree
        p hpTwo c x (bufferedPowerBound p δ) hmultiplier hc hx
      · simpa [traceAt, coordinateAt, AxisNoncentered] using hrouteable'
      · simpa [traceAt, coordinateAt] using hlarge'
      · exact hcost.2

/-! ## Conditional giant-orbit complement interface -/

/-- An honest iterate of any one-step generator lies in the corresponding
actual one-step component. -/
theorem sameOneStepComponent_of_actualOneStepIterate
    {R : Type*} [CommRing R] (c : R)
    (x y : SolutionSurface (coefficients c))
    (hxy : IsActualOneStepIterate c x.1 y.1) :
    SameOneStepComponent c x y := by
  rcases hxy with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩
  · let g : OneStepGroup c :=
      ⟨oneStep1SurfacePerm c ^ n,
        (OneStepGroup c).pow_mem
          (oneStep1SurfacePerm_mem_OneStepGroup c) n⟩
    refine ⟨g, ?_⟩
    change (g : Equiv.Perm (SolutionSurface (coefficients c))) x = y
    dsimp [g]
    rw [Equiv.Perm.coe_pow]
    apply Subtype.ext
    rw [Opening.coe_iterate_oneStep1SurfacePerm]
    exact hn
  · let g : OneStepGroup c :=
      ⟨oneStep2SurfacePerm c ^ n,
        (OneStepGroup c).pow_mem
          (oneStep2SurfacePerm_mem_OneStepGroup c) n⟩
    refine ⟨g, ?_⟩
    change (g : Equiv.Perm (SolutionSurface (coefficients c))) x = y
    dsimp [g]
    rw [Equiv.Perm.coe_pow]
    apply Subtype.ext
    rw [Opening.coe_iterate_oneStep2SurfacePerm]
    exact hn
  · let g : OneStepGroup c :=
      ⟨oneStep3SurfacePerm c ^ n,
        (OneStepGroup c).pow_mem
          (oneStep3SurfacePerm_mem_OneStepGroup c) n⟩
    refine ⟨g, ?_⟩
    change (g : Equiv.Perm (SolutionSurface (coefficients c))) x = y
    dsimp [g]
    rw [Equiv.Perm.coe_pow]
    apply Subtype.ext
    rw [Opening.coe_iterate_oneStep3SurfacePerm]
    exact hn

private theorem three_ne_zero_zmod_of_three_lt
    (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    (3 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
  have hpLe : p ≤ 3 := Nat.le_of_dvd (by norm_num) hpDvd
  omega

/-- Conditional complement classification.  If every candidate-regular
trace above `outputBound` has already been connected to the selected
endgame/cage component, then a point outside that component either has both
first two orders below `inputBound`, or is one of the two explicitly
classified affine-centered points. -/
theorem smallFirstTwo_or_mem_centeredExceptional_of_not_regularTraceComponent
    (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (c : ZMod p) (inputBound outputBound : ℕ)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hcostInput : regularRoutingCost outputBound < inputBound)
    (hcostParabolic : regularRoutingCost outputBound < p)
    (base : SolutionSurface (coefficients c))
    (x : PuncturedSolutionSurface (coefficients c))
    (hescape :
      ∀ y : SolutionSurface (coefficients c),
        HasRegularTraceOfOrderAtLeast p c outputBound y.1 →
          SameOneStepComponent c base y)
    (hnot : ¬ SameOneStepComponent c base x.1) :
    (halfStepOrder (trace c x.1.1.x1) < inputBound ∧
        halfStepOrder (trace c x.1.1.x2) < inputBound) ∨
      x.1.1 ∈ firstTwoCenteredExceptionalSet c := by
  have hpTwo : p ≠ 2 := by omega
  have hthree : (3 : ZMod p) ≠ 0 :=
    three_ne_zero_zmod_of_three_lt p hp
  have hxOrigin : x.1.1 ≠ (origin : Point (ZMod p)) := by
    intro hzero
    apply x.2
    apply Subtype.ext
    exact hzero
  have routeAxisOne :
      inputBound ≤ halfStepOrder (trace c x.1.1.x1) →
      (trace c x.1.1.x1 ^ 2 = 4 ∨
        AxisNoncentered c .first x.1.1) → False := by
    intro horder hrouteable
    obtain ⟨y, hySolution, hxy, hyRegular⟩ :=
      exists_actual_regularTrace_of_axisOne
        p hpTwo c x.1.1 outputBound hmultiplier hc x.1.2
          hrouteable (fun _ ↦ hcostInput.trans_le horder) hcostParabolic
    let ySurface : SolutionSurface (coefficients c) := ⟨y, hySolution⟩
    have hcomponentXY :
        SameOneStepComponent c x.1 ySurface :=
      sameOneStepComponent_of_actualOneStepIterate c x.1 ySurface hxy
    have hcomponentBaseY :
        SameOneStepComponent c base ySurface :=
      hescape ySurface hyRegular
    exact hnot (sameOneStepComponent_trans hcomponentBaseY
      (sameOneStepComponent_symm hcomponentXY))
  have routeAxisTwo :
      inputBound ≤ halfStepOrder (trace c x.1.1.x2) →
      (trace c x.1.1.x2 ^ 2 = 4 ∨
        AxisNoncentered c .second x.1.1) → False := by
    intro horder hrouteable
    obtain ⟨y, hySolution, hxy, hyRegular⟩ :=
      exists_actual_regularTrace_of_axisTwo
        p hpTwo c x.1.1 outputBound hmultiplier hc x.1.2
          hrouteable (fun _ ↦ hcostInput.trans_le horder) hcostParabolic
    let ySurface : SolutionSurface (coefficients c) := ⟨y, hySolution⟩
    have hcomponentXY :
        SameOneStepComponent c x.1 ySurface :=
      sameOneStepComponent_of_actualOneStepIterate c x.1 ySurface hxy
    have hcomponentBaseY :
        SameOneStepComponent c base ySurface :=
      hescape ySurface hyRegular
    exact hnot (sameOneStepComponent_trans hcomponentBaseY
      (sameOneStepComponent_symm hcomponentXY))
  by_cases hfirst :
      halfStepOrder (trace c x.1.1.x1) < inputBound
  · by_cases hsecond :
        halfStepOrder (trace c x.1.1.x2) < inputBound
    · exact Or.inl ⟨hfirst, hsecond⟩
    · have hsecondLarge :
          inputBound ≤ halfStepOrder (trace c x.1.1.x2) :=
        Nat.le_of_not_gt hsecond
      by_cases hparabolic : trace c x.1.1.x2 ^ 2 = 4
      · exact (routeAxisTwo hsecondLarge (Or.inl hparabolic)).elim
      · by_cases hcenter :
          centerCoordinates
            (fiberCenter c x.1.1.x2 (trace c x.1.1.x2))
            (movingCoordinates2 x.1.1) = (0, 0)
        · exact Or.inr
            (mem_firstTwoCenteredExceptionalSet_of_axisTwo_centered
              c x.1.1 hthree hmultiplier x.1.2 hxOrigin
                hparabolic hcenter)
        · exact (routeAxisTwo hsecondLarge
            (Or.inr (by simpa [AxisNoncentered] using hcenter))).elim
  · have hfirstLarge :
        inputBound ≤ halfStepOrder (trace c x.1.1.x1) :=
      Nat.le_of_not_gt hfirst
    by_cases hparabolic : trace c x.1.1.x1 ^ 2 = 4
    · exact (routeAxisOne hfirstLarge (Or.inl hparabolic)).elim
    · by_cases hcenter :
        centerCoordinates
          (fiberCenter c x.1.1.x1 (trace c x.1.1.x1))
          (movingCoordinates1 x.1.1) = (0, 0)
      · exact Or.inr
          (mem_firstTwoCenteredExceptionalSet_of_axisOne_centered
            c x.1.1 hthree hmultiplier x.1.2 hxOrigin
              hparabolic hcenter)
      · exact (routeAxisOne hfirstLarge
          (Or.inr (by simpa [AxisNoncentered] using hcenter))).elim

/-- Eventual two-exponent form of the conditional complement
classification. -/
theorem exists_threshold_smallFirstTwo_or_mem_centeredExceptional
    {δ η : ℝ} (hδ : 0 < δ) (htwoDelta : 2 * δ < η)
    (hη : η < 1) :
    ∃ threshold : ℕ,
      ∀ (p : ℕ) [Fact p.Prime], threshold ≤ p →
      ∀ (c : ZMod p),
        multiplier c ≠ 0 →
        c ^ 2 ≠ 4 →
        ∀ (base : SolutionSurface (coefficients c))
          (x : PuncturedSolutionSurface (coefficients c)),
          (∀ y : SolutionSurface (coefficients c),
            HasRegularTraceOfOrderAtLeast p c
                (bufferedPowerBound p δ) y.1 →
              SameOneStepComponent c base y) →
          ¬ SameOneStepComponent c base x.1 →
          (halfStepOrder (trace c x.1.1.x1) <
                bufferedPowerBound p η ∧
              halfStepOrder (trace c x.1.1.x2) <
                bufferedPowerBound p η) ∨
            x.1.1 ∈ firstTwoCenteredExceptionalSet c := by
  obtain ⟨costThreshold, hcostThreshold⟩ :=
    exists_threshold_regularRoutingCost_lt_powerBounds
      hδ htwoDelta hη
  refine ⟨costThreshold + 4, ?_⟩
  intro p _inst hp c hmultiplier hc base x hescape hnot
  have hpThree : 3 < p := by omega
  have hcost := hcostThreshold p (by omega)
  exact
    smallFirstTwo_or_mem_centeredExceptional_of_not_regularTraceComponent
      p hpThree c (bufferedPowerBound p η)
        (bufferedPowerBound p δ) hmultiplier hc hcost.1 hcost.2
          base x hescape hnot

end

end GenMarkoff.Symmetric.Assembly
