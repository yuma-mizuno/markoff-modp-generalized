import GenMarkoff.General.Assembly.RegularSplitEndgame
import GenMarkoff.General.Endgame.CageReadyActualSplitRotation
import GenMarkoff.General.Arithmetic.ReasonableCutoff

/-!
# Cage-ready canonical first-axis split endgame

A canonical primitive first-axis endpoint is not automatically suitable for
both directed connecting postprocesses.  This module strengthens the
canonical endpoint predicate by requiring `CageReadyFirstAxisTrace`.

Starting from an old canonical endpoint, the proof makes two
fixed-coefficient moves:

1. a forward `rotation1` segment produces a primitive, candidate-regular
   second-axis trace in the ordered frame `(a₂, a₁, a₃)`;
2. a forward `rotation2` segment returns to the first axis and uses the
   cage-ready primitive filter.

No coordinate permutation is used.  The square of each primitive
split-torus parameter has order `(p - 1) / 2`, which eventually dominates
the fixed three-quarter endgame scale needed for the next move.
-/

namespace GenMarkoff.General.Assembly

open BGS.Markoff
open GenMarkoff.General.Endgame

noncomputable section

/-- Canonical primitive split target on the first axis whose trace is ready
for both directed connecting postprocesses. -/
def IsCageReadyCanonicalFirstAxisPrimitiveSplit
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (x : SolutionSurface a) : Prop :=
  ∃ v : (ZMod p)ˣ,
    traceAt a .first x.1 = splitTorusTrace v ∧
      orderOf v = Nat.card (ZMod p)ˣ ∧
        CageReadyFirstAxisTrace a (traceAt a .first x.1)

/-- A cage-ready canonical endpoint is, in particular, an old canonical
candidate-regular primitive split endpoint. -/
theorem
    IsCageReadyCanonicalFirstAxisPrimitiveSplit.isCanonical
    {p : ℕ} [Fact p.Prime]
    {a : Coefficients (ZMod p)} {x : SolutionSurface a}
    (h : IsCageReadyCanonicalFirstAxisPrimitiveSplit p a x) :
    IsCanonicalFirstAxisPrimitiveSplit p a x := by
  obtain ⟨v, htrace, horder, hready⟩ := h
  exact ⟨v, htrace, horder, hready.1⟩

private theorem coe_iterate_rotation1SurfacePerm_cageReady
    {R : Type*} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) (n : ℕ) :
    ((((rotation1SurfacePerm a)^[n]) x :
      SolutionSurface a) : Point R) =
        ((rotation1 a)^[n]) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        coe_rotation1SurfacePerm, ih]

private theorem coe_iterate_rotation2SurfacePerm_cageReady
    {R : Type*} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) (n : ℕ) :
    ((((rotation2SurfacePerm a)^[n]) x :
      SolutionSurface a) : Point R) =
        ((rotation2 a)^[n]) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        coe_rotation2SurfacePerm, ih]

/-- Every sufficiently large old canonical first-axis primitive split
endpoint reaches a cage-ready canonical endpoint in the same
fixed-coefficient rotation component.

The first move uses the ordinary candidate-regular split threshold from the
first axis to the second.  The second move uses the cage-ready threshold from
the second axis back to the first. -/
theorem
    exists_threshold_canonicalFirstAxisPrimitiveSplit_reaches_cageReady
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      [Fact p.Prime] →
      ∀ (a : Coefficients (ZMod p)),
        a.a1 ^ 2 ≠ 4 →
        a.a2 ^ 2 ≠ 4 →
        a.a3 ^ 2 ≠ 4 →
        ∀ x : SolutionSurface a,
          IsCanonicalFirstAxisPrimitiveSplit p a x →
          ∃ finish : SolutionSurface a,
            SameRotationComponent x finish ∧
              IsCageReadyCanonicalFirstAxisPrimitiveSplit
                p a finish := by
  obtain ⟨firstThreshold, hfirst⟩ :=
    exists_threshold_actualSplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame
      coefficient hWeil
        (delta := (1 : ℝ) / 4) (by norm_num)
  obtain ⟨secondThreshold, hsecond⟩ :=
    exists_threshold_actualSplitPoint_with_primitiveCageReadyAxisOneTrace
      coefficient hWeil
        (delta := (1 : ℝ) / 4) (by norm_num)
  obtain ⟨squareThreshold, hsquare⟩ :=
    exists_threshold_threeQuarter_le_half_sub_one
  refine
    ⟨max (max firstThreshold secondThreshold)
        (max squareThreshold 3), ?_⟩
  intro p hp _ a hA1 hA2 hA3 x hx
  have hpFirst : firstThreshold ≤ p :=
    (Nat.le_max_left firstThreshold secondThreshold).trans
      ((Nat.le_max_left
        (max firstThreshold secondThreshold)
        (max squareThreshold 3)).trans hp)
  have hpSecond : secondThreshold ≤ p :=
    (Nat.le_max_right firstThreshold secondThreshold).trans
      ((Nat.le_max_left
        (max firstThreshold secondThreshold)
        (max squareThreshold 3)).trans hp)
  have hpSquare : squareThreshold ≤ p :=
    (Nat.le_max_left squareThreshold 3).trans
      ((Nat.le_max_right
        (max firstThreshold secondThreshold)
        (max squareThreshold 3)).trans hp)
  have hpThree : 3 ≤ p :=
    (Nat.le_max_right squareThreshold 3).trans
      ((Nat.le_max_right
        (max firstThreshold secondThreshold)
        (max squareThreshold 3)).trans hp)
  have hpTwo : p ≠ 2 := by omega
  obtain ⟨q, htrace, hqOrder, hregular⟩ := hx
  have hqSquareOrder :
      orderOf (q ^ 2) = (p - 1) / 2 :=
    orderOf_sq_eq_half_sub_one_of_primitive
      p hpTwo q hqOrder
  have hqLarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
        orderOf (q ^ 2) := by
    rw [hqSquareOrder]
    exact hsquare p hpSquare
  have hfirstMove :=
    hfirst p hpFirst a x.1.x1 (traceAt a .first x.1) q x.1
      a.a1 a.a3 x.2 rfl rfl htrace
      hA2 hA1 hregular hqLarge
  obtain ⟨n₁, v₁, hn₁, hv₁Order, hv₁Regular⟩ :=
    hfirstMove
  let middle : SolutionSurface a :=
    ((rotation1SurfacePerm a)^[n₁]) x
  have hmiddlePoint :
      middle.1 = ((rotation1 a)^[n₁]) x.1 := by
    simpa [middle] using
      coe_iterate_rotation1SurfacePerm_cageReady a x n₁
  have hmiddleTrace :
      traceAt a .second middle.1 = splitTorusTrace v₁ := by
    change
      orderedTrace a.multiplier a.a2 middle.1.x2 =
        splitTorusTrace v₁
    rw [hmiddlePoint]
    exact hn₁
  have hmiddleRegular :
      OrderedTraceCandidateRegular a.a2 a.a1 a.a3
        (traceAt a .second middle.1) := by
    rw [hmiddleTrace]
    exact hv₁Regular
  have hmiddleComponent :
      SameRotationComponent x middle := by
    simpa [middle, rotationSurfacePermAt] using
      sameRotationComponent_iterate_rotationSurfacePermAt
        a .first x n₁
  have hv₁SquareOrder :
      orderOf (v₁ ^ 2) = (p - 1) / 2 :=
    orderOf_sq_eq_half_sub_one_of_primitive
      p hpTwo v₁ hv₁Order
  have hv₁Large :
      (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
        orderOf (v₁ ^ 2) := by
    rw [hv₁SquareOrder]
    exact hsquare p hpSquare
  have hsecondMove :=
    hsecond p hpSecond a middle.1.x2
      (traceAt a .second middle.1) v₁ middle.1
      middle.2 rfl rfl hmiddleTrace
      hA1 hA2 hA3 hmiddleRegular hv₁Large
  obtain ⟨n₂, v₂, hn₂, hv₂Order, hv₂CageReady⟩ :=
    hsecondMove
  let finish : SolutionSurface a :=
    ((rotation2SurfacePerm a)^[n₂]) middle
  have hfinishPoint :
      finish.1 = ((rotation2 a)^[n₂]) middle.1 := by
    simpa [finish] using
      coe_iterate_rotation2SurfacePerm_cageReady a middle n₂
  have hfinishTrace :
      traceAt a .first finish.1 = splitTorusTrace v₂ := by
    change
      orderedTrace a.multiplier a.a1 finish.1.x1 =
        splitTorusTrace v₂
    rw [hfinishPoint]
    exact hn₂
  have hfinishComponent :
      SameRotationComponent middle finish := by
    simpa [finish, rotationSurfacePermAt] using
      sameRotationComponent_iterate_rotationSurfacePermAt
        a .second middle n₂
  refine
    ⟨finish,
      sameRotationComponent_trans
        hmiddleComponent hfinishComponent,
      v₂, hfinishTrace, hv₂Order, ?_⟩
  rw [hfinishTrace]
  exact hv₂CageReady

/-- Closed-cutoff canonical-to-cage-ready conversion. -/
theorem canonicalFirstAxisPrimitiveSplit_reaches_cageReady_of_analyticCutoff
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (hcoefficient : coefficient + 96 ≤ 1032)
    (p : ℕ) (hp : GenMarkoff.General.Explicit.analyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (x : SolutionSurface a)
    (hx : IsCanonicalFirstAxisPrimitiveSplit p a x) :
    ∃ finish : SolutionSurface a,
      SameRotationComponent x finish ∧
        IsCageReadyCanonicalFirstAxisPrimitiveSplit p a finish := by
  have hpTwo : p ≠ 2 := by
    have hpFive :=
      GenMarkoff.General.Explicit.five_le_analyticCutoff.trans hp
    omega
  obtain ⟨q, htrace, hqOrder, hregular⟩ := hx
  have hqSquareOrder :
      orderOf (q ^ 2) = (p - 1) / 2 :=
    orderOf_sq_eq_half_sub_one_of_primitive
      p hpTwo q hqOrder
  have hqLarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
        orderOf (q ^ 2) := by
    rw [hqSquareOrder]
    exact threeQuarter_le_half_sub_one_of_analyticCutoff hp
  have hfirstMove :=
    actualSplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame_of_analyticCutoff
      coefficient hWeil (delta := (1 : ℝ) / 4) (by norm_num)
      (by omega) p hp
      a x.1.x1 (traceAt a .first x.1) q x.1
      a.a1 a.a3 x.2 rfl rfl htrace
      hA2 hA1 hregular hqLarge
  obtain ⟨n₁, v₁, hn₁, hv₁Order, hv₁Regular⟩ :=
    hfirstMove
  let middle : SolutionSurface a :=
    ((rotation1SurfacePerm a)^[n₁]) x
  have hmiddlePoint :
      middle.1 = ((rotation1 a)^[n₁]) x.1 := by
    simpa [middle] using
      coe_iterate_rotation1SurfacePerm_cageReady a x n₁
  have hmiddleTrace :
      traceAt a .second middle.1 = splitTorusTrace v₁ := by
    change
      orderedTrace a.multiplier a.a2 middle.1.x2 =
        splitTorusTrace v₁
    rw [hmiddlePoint]
    exact hn₁
  have hmiddleRegular :
      OrderedTraceCandidateRegular a.a2 a.a1 a.a3
        (traceAt a .second middle.1) := by
    rw [hmiddleTrace]
    exact hv₁Regular
  have hmiddleComponent :
      SameRotationComponent x middle := by
    simpa [middle, rotationSurfacePermAt] using
      sameRotationComponent_iterate_rotationSurfacePermAt
        a .first x n₁
  have hv₁SquareOrder :
      orderOf (v₁ ^ 2) = (p - 1) / 2 :=
    orderOf_sq_eq_half_sub_one_of_primitive
      p hpTwo v₁ hv₁Order
  have hv₁Large :
      (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
        orderOf (v₁ ^ 2) := by
    rw [hv₁SquareOrder]
    exact threeQuarter_le_half_sub_one_of_analyticCutoff hp
  have hsecondMove :=
    actualSplitPoint_with_primitiveCageReadyAxisOneTrace_of_analyticCutoff
      coefficient hWeil (delta := (1 : ℝ) / 4) (by norm_num)
      hcoefficient p hp
      a middle.1.x2 (traceAt a .second middle.1) v₁ middle.1
      middle.2 rfl rfl hmiddleTrace
      hA1 hA2 hA3 hmiddleRegular hv₁Large
  obtain ⟨n₂, v₂, hn₂, hv₂Order, hv₂CageReady⟩ :=
    hsecondMove
  let finish : SolutionSurface a :=
    ((rotation2SurfacePerm a)^[n₂]) middle
  have hfinishPoint :
      finish.1 = ((rotation2 a)^[n₂]) middle.1 := by
    simpa [finish] using
      coe_iterate_rotation2SurfacePerm_cageReady a middle n₂
  have hfinishTrace :
      traceAt a .first finish.1 = splitTorusTrace v₂ := by
    change
      orderedTrace a.multiplier a.a1 finish.1.x1 =
        splitTorusTrace v₂
    rw [hfinishPoint]
    exact hn₂
  have hfinishComponent :
      SameRotationComponent middle finish := by
    simpa [finish, rotationSurfacePermAt] using
      sameRotationComponent_iterate_rotationSurfacePermAt
        a .second middle n₂
  refine
    ⟨finish,
      sameRotationComponent_trans
        hmiddleComponent hfinishComponent,
      v₂, hfinishTrace, hv₂Order, ?_⟩
  rw [hfinishTrace]
  exact hv₂CageReady

/-- Reasonable-cutoff canonical-to-cage-ready conversion. -/
theorem canonicalFirstAxisPrimitiveSplit_reaches_cageReady_of_reasonableCutoff
    (coefficient : ℕ)
    (hWeil : WeightedShiftedTraceWeilBoundAssumption coefficient)
    (hcoefficient : coefficient + 96 ≤ 1032)
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (x : SolutionSurface a)
    (hx : IsCanonicalFirstAxisPrimitiveSplit p a x) :
    ∃ finish : SolutionSurface a,
      SameRotationComponent x finish ∧
        IsCageReadyCanonicalFirstAxisPrimitiveSplit p a finish := by
  have hpTwo : p ≠ 2 := by
    have hpFive :=
      GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans hp
    omega
  obtain ⟨q, htrace, hqOrder, hregular⟩ := hx
  have hqSquareOrder :
      orderOf (q ^ 2) = (p - 1) / 2 :=
    orderOf_sq_eq_half_sub_one_of_primitive
      p hpTwo q hqOrder
  have hqLarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
        orderOf (q ^ 2) := by
    rw [hqSquareOrder]
    exact threeQuarter_le_half_sub_one_of_reasonableCutoff hp
  have hfirstMove :=
    actualSplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame_of_reasonableCutoff
      coefficient hWeil (delta := (1 : ℝ) / 4) (by norm_num)
      (by omega) p hp
      a x.1.x1 (traceAt a .first x.1) q x.1
      a.a1 a.a3 x.2 rfl rfl htrace
      hA2 hA1 hregular hqLarge
  obtain ⟨n₁, v₁, hn₁, hv₁Order, hv₁Regular⟩ :=
    hfirstMove
  let middle : SolutionSurface a :=
    ((rotation1SurfacePerm a)^[n₁]) x
  have hmiddlePoint :
      middle.1 = ((rotation1 a)^[n₁]) x.1 := by
    simpa [middle] using
      coe_iterate_rotation1SurfacePerm_cageReady a x n₁
  have hmiddleTrace :
      traceAt a .second middle.1 = splitTorusTrace v₁ := by
    change
      orderedTrace a.multiplier a.a2 middle.1.x2 =
        splitTorusTrace v₁
    rw [hmiddlePoint]
    exact hn₁
  have hmiddleRegular :
      OrderedTraceCandidateRegular a.a2 a.a1 a.a3
        (traceAt a .second middle.1) := by
    rw [hmiddleTrace]
    exact hv₁Regular
  have hmiddleComponent :
      SameRotationComponent x middle := by
    simpa [middle, rotationSurfacePermAt] using
      sameRotationComponent_iterate_rotationSurfacePermAt
        a .first x n₁
  have hv₁SquareOrder :
      orderOf (v₁ ^ 2) = (p - 1) / 2 :=
    orderOf_sq_eq_half_sub_one_of_primitive
      p hpTwo v₁ hv₁Order
  have hv₁Large :
      (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
        orderOf (v₁ ^ 2) := by
    rw [hv₁SquareOrder]
    exact threeQuarter_le_half_sub_one_of_reasonableCutoff hp
  have hsecondMove :=
    actualSplitPoint_with_primitiveCageReadyAxisOneTrace_of_reasonableCutoff
      coefficient hWeil (delta := (1 : ℝ) / 4) (by norm_num)
      hcoefficient p hp
      a middle.1.x2 (traceAt a .second middle.1) v₁ middle.1
      middle.2 rfl rfl hmiddleTrace
      hA1 hA2 hA3 hmiddleRegular hv₁Large
  obtain ⟨n₂, v₂, hn₂, hv₂Order, hv₂CageReady⟩ :=
    hsecondMove
  let finish : SolutionSurface a :=
    ((rotation2SurfacePerm a)^[n₂]) middle
  have hfinishPoint :
      finish.1 = ((rotation2 a)^[n₂]) middle.1 := by
    simpa [finish] using
      coe_iterate_rotation2SurfacePerm_cageReady a middle n₂
  have hfinishTrace :
      traceAt a .first finish.1 = splitTorusTrace v₂ := by
    change
      orderedTrace a.multiplier a.a1 finish.1.x1 =
        splitTorusTrace v₂
    rw [hfinishPoint]
    exact hn₂
  have hfinishComponent :
      SameRotationComponent middle finish := by
    simpa [finish, rotationSurfacePermAt] using
      sameRotationComponent_iterate_rotationSurfacePermAt
        a .second middle n₂
  refine
    ⟨finish,
      sameRotationComponent_trans
        hmiddleComponent hfinishComponent,
      v₂, hfinishTrace, hv₂Order, ?_⟩
  rw [hfinishTrace]
  exact hv₂CageReady

end

end GenMarkoff.General.Assembly
