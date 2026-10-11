module

public import GenMarkoff.General.Assembly.RegularSplitEndgame
public import GenMarkoff.General.Endgame.CageReady.ActualSplitRotation
public import GenMarkoff.General.Arithmetic.ReasonableCutoff

@[expose] public section

/-!
# Cage-ready canonical first-axis split points

The predicate `IsCanonicalFirstAxisPrimitiveSplit` only asks for candidate
regularity of the first-axis trace, which is not enough for both directed
connecting-cage arguments.  This module defines the stronger predicate
`IsCageReadyCanonicalFirstAxisPrimitiveSplit`, which also requires
`CageReadyFirstAxisTrace`, and proves
`canonicalFirstAxisPrimitiveSplit_reaches_cageReady_of_reasonableCutoff`:
beyond `reasonableAnalyticCutoff`, every canonical point lies in the rotation
component of a cage-ready one.

The proof makes two fixed-coefficient moves:

1. a `rotation1` segment produces a primitive, candidate-regular
   second-axis trace in the ordered frame `(a₂, a₁, a₃)`;
2. a `rotation2` segment returns to the first axis with a primitive
   cage-ready trace.

No coordinate permutation is used.  The square of each primitive
split-torus parameter has order `(p - 1) / 2`, which dominates the
three-quarter scale `p ^ (3/4)` required by each move.
-/

namespace GenMarkoff.General.Assembly

open BGS.Markoff
open GenMarkoff.General.Endgame

noncomputable section

/-- A surface point whose first-axis trace is `v + v⁻¹` for a primitive
`v : (ZMod p)ˣ` and satisfies `CageReadyFirstAxisTrace`, the condition used by
both directed connecting-cage arguments. -/
def IsCageReadyCanonicalFirstAxisPrimitiveSplit
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (x : SolutionSurface a) : Prop :=
  ∃ v : (ZMod p)ˣ,
    traceAt a .first x.1 = splitTorusTrace v ∧
      orderOf v = Nat.card (ZMod p)ˣ ∧
        CageReadyFirstAxisTrace a (traceAt a .first x.1)

/-- Beyond `reasonableAnalyticCutoff`, for coefficients with `aᵢ ^ 2 ≠ 4`,
every canonical primitive split first-axis point is in the same rotation
component as a cage-ready one.  The affine point-count estimate enters through
`hWeil`. -/
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
  -- First move: a `rotation1` segment to a primitive, candidate-regular
  -- second-axis trace.
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
      coe_iterate_rotation1SurfacePerm a x n₁
  have hmiddleTrace :
      traceAt a .second middle.1 = splitTorusTrace v₁ := by
    -- `traceAt a .second` unfolds to `orderedTrace a.multiplier a.a2 _.x2`;
    -- restate so that after `rw [hmiddlePoint]` the goal is exactly `hn₁`.
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
  -- Second move: a `rotation2` segment back to a primitive cage-ready
  -- first-axis trace.
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
      coe_iterate_rotation2SurfacePerm a middle n₂
  have hfinishTrace :
      traceAt a .first finish.1 = splitTorusTrace v₂ := by
    -- `traceAt a .first` unfolds to `orderedTrace a.multiplier a.a1 _.x1`;
    -- restate so that after `rw [hfinishPoint]` the goal is exactly `hn₂`.
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
