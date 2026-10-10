import GenMarkoff.General.Endgame.ActualSplitRotation
import GenMarkoff.General.Arithmetic.ReasonableCutoff

/-!
# Canonical first-axis regular split endgame

This module defines `IsCanonicalFirstAxisPrimitiveSplit`: a surface point
whose first-axis trace is `v + v⁻¹` for a primitive `v : (ZMod p)ˣ` and is
candidate regular in the ordered frame `(a.a1, a.a2, a.a3)`.  It proves that
an alternating regular state with a split trace of large actual order reaches
such a point in its rotation component
(`alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit_of_reasonableCutoff`).
No coordinate or coefficient permutation is used.

A `.secondFirst` state needs one `rotation2` segment.  A `.firstSecond` state
first reaches a primitive second-axis eigenvalue `v` by a `rotation1` segment
and then needs a second move back to the first axis.  The actual rotation
generator there is `v ^ 2`, of order `(p - 1) / 2`, and
`threeQuarter_le_half_sub_one_of_reasonableCutoff` shows that this order is
at least `p ^ (3/4)`, as the second move requires.
-/

namespace GenMarkoff.General.Assembly

open BGS.Markoff
open Filter
open GenMarkoff.General.Endgame

noncomputable section

/-- A surface point whose first-axis trace is `v + v⁻¹` for a primitive
`v : (ZMod p)ˣ` and is candidate regular in the ordered frame
`(a.a1, a.a2, a.a3)`. -/
def IsCanonicalFirstAxisPrimitiveSplit
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (x : SolutionSurface a) : Prop :=
  ∃ v : (ZMod p)ˣ,
    traceAt a .first x.1 = splitTorusTrace v ∧
      orderOf v = Nat.card (ZMod p)ˣ ∧
        OrderedTraceCandidateRegular a.a1 a.a2 a.a3
          (traceAt a .first x.1)

/-- A primitive split eigenvalue has square order exactly half the size of
the prime-field unit group. -/
theorem orderOf_sq_eq_half_sub_one_of_primitive
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (v : (ZMod p)ˣ)
    (hprimitive : orderOf v = Nat.card (ZMod p)ˣ) :
    orderOf (v ^ 2) = (p - 1) / 2 := by
  rw [orderOf_pow, hprimitive, Nat.card_units, Nat.card_zmod]
  rw [Nat.gcd_eq_right
    ((Fact.out : p.Prime).even_sub_one hpTwo).two_dvd]

/-- Beyond `reasonableAnalyticCutoff`, `p ^ (3/4) ≤ (p - 1) / 2`: the square
of a primitive split eigenvalue has order at least the three-quarter endgame
scale.  The estimate follows from `4 < p ^ (1/8)`, since `1/8 + 3/4 < 1`. -/
theorem threeQuarter_le_half_sub_one_of_reasonableCutoff
    {p : ℕ} (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p) :
    (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
      (((p - 1) / 2 : ℕ) : ℝ) := by
  have hpFive : 5 ≤ p :=
    GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans hp
  have hpRealOne : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpRealPos : (0 : ℝ) < p := zero_lt_one.trans hpRealOne
  have hfour :
      (4 : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ) :=
    GenMarkoff.General.Explicit.reasonable_small_fixed_lt_rpow_one_div_eight
      hp (by norm_num)
  have habsorb :
      (4 : ℝ) * (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) <
        (p : ℝ) := by
    calc
      (4 : ℝ) * (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) <
          (p : ℝ) ^ (1 / 8 : ℝ) *
            (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) := by
        exact mul_lt_mul_of_pos_right hfour
          (Real.rpow_pos_of_pos hpRealPos _)
      _ = (p : ℝ) ^ (7 / 8 : ℝ) := by
        rw [← Real.rpow_add hpRealPos]
        congr 1
        norm_num
      _ < (p : ℝ) := by
        simpa only [Real.rpow_one] using
          Real.rpow_lt_rpow_of_exponent_lt hpRealOne
            (show (7 / 8 : ℝ) < 1 by norm_num)
  have hnat : p ≤ 4 * ((p - 1) / 2) := by omega
  have hcast :
      (p : ℝ) ≤ (4 : ℝ) * (((p - 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- An alternating regular state whose split endgame move succeeds
(`hstart`) reaches a canonical primitive split point on the first axis in
the same rotation component, provided the split endgame move also succeeds
from every state whose squared eigenvalue has order at least `p ^ (3/4)`
(`hprimitive`) and `p ^ (3/4) ≤ (p - 1) / 2` (`hsquare`).

The `.secondFirst` branch uses one `rotation2` segment.  The `.firstSecond`
branch uses a `rotation1` segment to a primitive second-axis state, then
applies `hprimitive` once more and returns to the first axis by a
`rotation2` segment. -/
theorem
    alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit
    (p : ℕ) [Fact p.Prime]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (state : AlternatingRegularState a)
    (hstart :
      alternatingPrimitiveSplitEndgameResult
        p a state.direction state.point.1)
    (hprimitive :
      ∀ (next : AlternatingRegularState a) (v : (ZMod p)ˣ),
        traceAt a next.direction.fixed next.point.1 = splitTorusTrace v →
        (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤ orderOf (v ^ 2) →
        alternatingPrimitiveSplitEndgameResult
          p a next.direction next.point.1)
    (hsquare :
      (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
        (((p - 1) / 2 : ℕ) : ℝ)) :
    ∃ finish : SolutionSurface a,
      SameRotationComponent state.point finish ∧
        IsCanonicalFirstAxisPrimitiveSplit p a finish := by
  have hfirstResult := hstart
  cases state with
  | mk direction point hregular =>
      cases direction with
      | secondFirst =>
          -- `alternatingPrimitiveSplitEndgameResult` at `.secondFirst` is its
          -- `rotation2` branch; restate it so that `obtain` can destructure it.
          change
            ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
              orderedTrace a.multiplier a.a1
                  (((rotation2 a)^[n]) point.1).x1 =
                splitTorusTrace v ∧
              orderOf v = Nat.card (ZMod p)ˣ ∧
                OrderedTraceCandidateRegular
                  a.a1 a.a2 a.a3 (splitTorusTrace v)
            at hfirstResult
          obtain ⟨n, v, hn, hvOrder, hvRegular⟩ :=
            hfirstResult
          let finish : SolutionSurface a :=
            ((rotation2SurfacePerm a)^[n]) point
          have hfinishPoint :
              finish.1 = ((rotation2 a)^[n]) point.1 := by
            simpa [finish] using
              coe_iterate_rotation2SurfacePerm a point n
          have hfinishTrace :
              traceAt a .first finish.1 = splitTorusTrace v := by
            -- `traceAt a .first` unfolds to `orderedTrace a.multiplier a.a1 _.x1`;
            -- restate so that after `rw [hfinishPoint]` the goal is `hn`.
            change
              orderedTrace a.multiplier a.a1 finish.1.x1 =
                splitTorusTrace v
            rw [hfinishPoint]
            exact hn
          have hcomponent :
              SameRotationComponent point finish := by
            simpa [finish, rotationSurfacePermAt] using
              sameRotationComponent_iterate_rotationSurfacePermAt
                a .second point n
          refine ⟨finish, hcomponent, v, hfinishTrace, hvOrder, ?_⟩
          rw [hfinishTrace]
          exact hvRegular
      | firstSecond =>
          -- `alternatingPrimitiveSplitEndgameResult` at `.firstSecond` is its
          -- `rotation1` branch; restate it so that `obtain` can destructure it.
          change
            ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
              orderedTrace a.multiplier a.a2
                  (((rotation1 a)^[n]) point.1).x2 =
                splitTorusTrace v ∧
              orderOf v = Nat.card (ZMod p)ˣ ∧
                OrderedTraceCandidateRegular
                  a.a2 a.a1 a.a3 (splitTorusTrace v)
            at hfirstResult
          -- First move: a `rotation1` segment to a primitive second-axis state.
          obtain ⟨n₁, v₁, hn₁, hv₁Order, hv₁Regular⟩ :=
            hfirstResult
          let middle : SolutionSurface a :=
            ((rotation1SurfacePerm a)^[n₁]) point
          have hmiddlePoint :
              middle.1 = ((rotation1 a)^[n₁]) point.1 := by
            simpa [middle] using
              coe_iterate_rotation1SurfacePerm a point n₁
          have hmiddleTrace :
              traceAt a .second middle.1 = splitTorusTrace v₁ := by
            -- `traceAt a .second` unfolds to `orderedTrace a.multiplier a.a2 _.x2`;
            -- restate so that after `rw [hmiddlePoint]` the goal is `hn₁`.
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
          let middleState : AlternatingRegularState a :=
            ⟨.secondFirst, middle, hmiddleRegular⟩
          have hmiddleComponent :
              SameRotationComponent point middle := by
            simpa [middle, rotationSurfacePermAt] using
              sameRotationComponent_iterate_rotationSurfacePermAt
                a .first point n₁
          -- Second move: `v₁ ^ 2` has order `(p - 1) / 2 ≥ p ^ (3/4)`, so
          -- `hprimitive` gives a `rotation2` segment back to the first axis.
          have hv₁SquareOrder :
              orderOf (v₁ ^ 2) = (p - 1) / 2 :=
            orderOf_sq_eq_half_sub_one_of_primitive
              p hpTwo v₁ hv₁Order
          have hv₁Large :
              (p : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 4) ≤
                orderOf (v₁ ^ 2) := by
            rw [hv₁SquareOrder]
            exact hsquare
          have hmiddleEigen :
              traceAt a middleState.direction.fixed middleState.point.1 =
                splitTorusTrace v₁ := by
            simpa [middleState, AlternatingDirectedAxis.fixed] using
              hmiddleTrace
          have hsecondResult :=
            hprimitive middleState v₁ hmiddleEigen hv₁Large
          -- `middleState` has direction `.secondFirst`, so the endgame result
          -- is its `rotation2` branch; restate it so that `obtain` applies.
          change
            ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
              orderedTrace a.multiplier a.a1
                  (((rotation2 a)^[n]) middle.1).x1 =
                splitTorusTrace v ∧
              orderOf v = Nat.card (ZMod p)ˣ ∧
                OrderedTraceCandidateRegular
                  a.a1 a.a2 a.a3 (splitTorusTrace v)
            at hsecondResult
          obtain ⟨n₂, v₂, hn₂, hv₂Order, hv₂Regular⟩ :=
            hsecondResult
          let finish : SolutionSurface a :=
            ((rotation2SurfacePerm a)^[n₂]) middle
          have hfinishPoint :
              finish.1 = ((rotation2 a)^[n₂]) middle.1 := by
            simpa [finish] using
              coe_iterate_rotation2SurfacePerm a middle n₂
          have hfinishTrace :
              traceAt a .first finish.1 = splitTorusTrace v₂ := by
            -- `traceAt a .first` unfolds to `orderedTrace a.multiplier a.a1 _.x1`;
            -- restate so that after `rw [hfinishPoint]` the goal is `hn₂`.
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
          exact hv₂Regular

/-- Beyond `reasonableAnalyticCutoff`, with `a₁ ^ 2 ≠ 4` and `a₂ ^ 2 ≠ 4`, an
alternating regular state whose fixed trace is `q + q⁻¹` with
`p ^ (1/2 + delta) ≤ orderOf (q ^ 2)` for some `delta ≥ 1/4` reaches a
canonical primitive split first-axis point in its rotation component.  Both
moves use `alternatingRegularState_actualSplitPrimitiveEndgame_of_reasonableCutoff`. -/
theorem alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit_of_reasonableCutoff
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
    ∃ finish : SolutionSurface a,
      SameRotationComponent state.point finish ∧
        IsCanonicalFirstAxisPrimitiveSplit p a finish := by
  have hpTwo : p ≠ 2 := by
    have hpFive :=
      GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans hp
    omega
  exact
    alternatingRegularState_reaches_canonicalFirstAxisPrimitiveSplit
      p hpTwo a state
      (alternatingRegularState_actualSplitPrimitiveEndgame_of_reasonableCutoff
        coefficient hWeil hdelta hcoefficient p hp
          a hA1 hA2 state q heigen hlarge)
      (fun next v hnext hnextLarge =>
        alternatingRegularState_actualSplitPrimitiveEndgame_of_reasonableCutoff
          coefficient hWeil (delta := (1 : ℝ) / 4) (by norm_num)
            hcoefficient p hp a hA1 hA2 next v hnext hnextLarge)
      (threeQuarter_le_half_sub_one_of_reasonableCutoff hp)

end

end GenMarkoff.General.Assembly
