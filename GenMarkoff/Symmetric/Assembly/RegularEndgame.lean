import GenMarkoff.Symmetric.Endgame.ActualRegularPrimitiveOrbit
import GenMarkoff.Symmetric.Endgame.Nonsplit.ActualPrimitiveThreshold
import GenMarkoff.Symmetric.Cage.FiberConnectivity

/-!
# The actual symmetric endgame lands in the regular split cage

The split and nonsplit primitive counts now both return an actual forward
one-step iterate and preserve candidate regularity of the new primitive split
trace.  This file packages their common consequence: a candidate-regular
coordinate of endgame size reaches the regular split-maximal cage.
-/

namespace GenMarkoff.Symmetric.Assembly

open BGS.Markoff

noncomputable section

/-- A raw first-axis forward iterate gives two solution-surface points in the
same actual one-step component. -/
theorem sameOneStepComponent_of_oneStep1_iterate
    {R : Type*} [CommRing R] (c : R)
    (x y : SolutionSurface (coefficients c)) (n : ℕ)
    (hxy : ((oneStep1 c)^[n]) x.1 = y.1) :
    Cage.SameOneStepComponent c x y := by
  let g : OneStepGroup c :=
    ⟨oneStep1SurfacePerm c ^ n,
      (OneStepGroup c).pow_mem
        (oneStep1SurfacePerm_mem_OneStepGroup c) n⟩
  refine ⟨g, ?_⟩
  change (g : Equiv.Perm (SolutionSurface (coefficients c))) x = y
  dsimp [g]
  rw [Equiv.Perm.coe_pow]
  apply Subtype.ext
  rw [Opening.coe_iterate_oneStep1SurfacePerm]
  exact hxy

/-- A raw second-axis forward iterate gives two solution-surface points in
the same actual one-step component. -/
theorem sameOneStepComponent_of_oneStep2_iterate
    {R : Type*} [CommRing R] (c : R)
    (x y : SolutionSurface (coefficients c)) (n : ℕ)
    (hxy : ((oneStep2 c)^[n]) x.1 = y.1) :
    Cage.SameOneStepComponent c x y := by
  let g : OneStepGroup c :=
    ⟨oneStep2SurfacePerm c ^ n,
      (OneStepGroup c).pow_mem
        (oneStep2SurfacePerm_mem_OneStepGroup c) n⟩
  refine ⟨g, ?_⟩
  change (g : Equiv.Perm (SolutionSurface (coefficients c))) x = y
  dsimp [g]
  rw [Equiv.Perm.coe_pow]
  apply Subtype.ext
  rw [Opening.coe_iterate_oneStep2SurfacePerm]
  exact hxy

/-- A raw third-axis forward iterate gives two solution-surface points in
the same actual one-step component. -/
theorem sameOneStepComponent_of_oneStep3_iterate
    {R : Type*} [CommRing R] (c : R)
    (x y : SolutionSurface (coefficients c)) (n : ℕ)
    (hxy : ((oneStep3 c)^[n]) x.1 = y.1) :
    Cage.SameOneStepComponent c x y := by
  let g : OneStepGroup c :=
    ⟨oneStep3SurfacePerm c ^ n,
      (OneStepGroup c).pow_mem
        (oneStep3SurfacePerm_mem_OneStepGroup c) n⟩
  refine ⟨g, ?_⟩
  change (g : Equiv.Perm (SolutionSurface (coefficients c))) x = y
  dsimp [g]
  rw [Equiv.Perm.coe_pow]
  apply Subtype.ext
  rw [Opening.coe_iterate_oneStep3SurfacePerm]
  exact hxy

/-- Uniform first-axis endgame: every candidate-regular trace of endgame
order reaches a candidate-regular primitive split trace on the adjacent
axis. -/
theorem exists_threshold_regularFirstOrder_to_regularSplitCage
    (splitCoefficient : ℕ)
    (hSplit :
      WeightedShiftedTraceWeilBoundAssumption splitCoefficient)
    (nonsplitCoefficient : ℕ)
    (hNonsplit :
      Endgame.Nonsplit.ShiftedSeededNonsplitTraceWeilBoundAssumption
        nonsplitCoefficient)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ threshold : ℕ,
      ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
        ∀ (c : ZMod p) (x : SolutionSurface (coefficients c)),
          c ^ 2 ≠ 4 →
          OrderedTraceCandidateRegular c c c (trace c x.1.x1) →
          (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
            halfStepOrder (trace c x.1.x1) →
          ∃ y : SolutionSurface (coefficients c),
            Cage.SameOneStepComponent c x y ∧
              Cage.IsInRegularSplitCage p c y := by
  obtain ⟨splitThreshold, hsplit⟩ :=
    Endgame.exists_threshold_actualSplitPoint_with_primitiveCandidateRegularAdjacentTrace
      splitCoefficient hSplit hdelta
  obtain ⟨nonsplitThreshold, hnonsplit⟩ :=
    Endgame.Nonsplit.exists_threshold_actualNonsplitPoint_with_primitiveCandidateRegularAdjacentTrace
      nonsplitCoefficient hNonsplit hdelta
  refine ⟨max (max splitThreshold nonsplitThreshold) 3, ?_⟩
  intro p hp _ c x hc hregular hlarge
  have hpSplit : splitThreshold ≤ p := by omega
  have hpNonsplit : nonsplitThreshold ≤ p := by omega
  have hpTwo : p ≠ 2 := by omega
  let t := trace c x.1.x1
  have ht : t ^ 2 ≠ 4 := by
    exact sub_ne_zero.mp (by simpa [t] using hregular.1)
  rcases exists_split_or_quadraticNormOneTrace p hpTwo t ht with
      ⟨q, htraceQ, hq⟩ | ⟨w, htraceW, hw⟩
  · have horder :
        halfStepOrder t = orderOf q := by
      rw [Opening.halfStepOrder_eq_bgsRotationOrder, ← htraceQ]
      exact rotationOrder_splitTorusTrace q hq
    have hlargeQ :
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf q := by
      simpa [t, horder] using hlarge
    obtain ⟨n, v, hnTrace, hvOrder, hvRegular⟩ :=
      hsplit p hpSplit c x.1.x1 t q x.1 x.property rfl rfl
        htraceQ.symm hc hregular hlargeQ
    let yPoint := ((oneStep1 c)^[n]) x.1
    have hySolution : IsSolution (coefficients c) yPoint :=
      isSolution_iterate_oneStep1 c x.property n
    let y : SolutionSurface (coefficients c) :=
      ⟨yPoint, hySolution⟩
    refine ⟨y, sameOneStepComponent_of_oneStep1_iterate c x y n rfl,
      Cage.Axis.second, ?_⟩
    have htraceY :
        trace c (Cage.coordinateAt Cage.Axis.second y.1) =
          splitTorusTrace v := by
      simpa [y, yPoint, Cage.coordinateAt] using hnTrace
    refine ⟨?_, v, htraceY, hvOrder⟩
    change OrderedTraceCandidateRegular c c c
      (trace c (Cage.coordinateAt Cage.Axis.second y.1))
    rw [htraceY]
    exact hvRegular
  · have horder :
        halfStepOrder t = orderOf w := by
      rw [Opening.halfStepOrder_eq_bgsRotationOrder, ← htraceW]
      exact rotationOrder_quadraticNormOneTrace p w hw
    have hlargeW :
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf w := by
      simpa [t, horder] using hlarge
    obtain ⟨n, v, hnTrace, hvOrder, hvRegular⟩ :=
      hnonsplit p hpNonsplit c x.1.x1 t x.1 w x.property rfl rfl
        hc hregular htraceW hlargeW
    let yPoint := ((oneStep1 c)^[n]) x.1
    have hySolution : IsSolution (coefficients c) yPoint :=
      isSolution_iterate_oneStep1 c x.property n
    let y : SolutionSurface (coefficients c) :=
      ⟨yPoint, hySolution⟩
    refine ⟨y, sameOneStepComponent_of_oneStep1_iterate c x y n rfl,
      Cage.Axis.second, ?_⟩
    have htraceY :
        trace c (Cage.coordinateAt Cage.Axis.second y.1) =
          splitTorusTrace v := by
      simpa [y, yPoint, Cage.coordinateAt] using hnTrace
    refine ⟨?_, v, htraceY, hvOrder⟩
    change OrderedTraceCandidateRegular c c c
      (trace c (Cage.coordinateAt Cage.Axis.second y.1))
    rw [htraceY]
    exact hvRegular

/-- Cyclic second-axis endgame: every candidate-regular trace of endgame
order reaches a candidate-regular primitive split trace on the third axis. -/
theorem exists_threshold_regularSecondOrder_to_regularSplitCage
    (splitCoefficient : ℕ)
    (hSplit :
      WeightedShiftedTraceWeilBoundAssumption splitCoefficient)
    (nonsplitCoefficient : ℕ)
    (hNonsplit :
      Endgame.Nonsplit.ShiftedSeededNonsplitTraceWeilBoundAssumption
        nonsplitCoefficient)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ threshold : ℕ,
      ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
        ∀ (c : ZMod p) (x : SolutionSurface (coefficients c)),
          c ^ 2 ≠ 4 →
          OrderedTraceCandidateRegular c c c (trace c x.1.x2) →
          (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
            halfStepOrder (trace c x.1.x2) →
          ∃ y : SolutionSurface (coefficients c),
            Cage.SameOneStepComponent c x y ∧
              Cage.IsInRegularSplitCage p c y := by
  obtain ⟨splitThreshold, hsplit⟩ :=
    Endgame.exists_threshold_actualSplitPoint_with_primitiveCandidateRegularAdjacentTrace
      splitCoefficient hSplit hdelta
  obtain ⟨nonsplitThreshold, hnonsplit⟩ :=
    Endgame.Nonsplit.exists_threshold_actualNonsplitPoint_with_primitiveCandidateRegularAdjacentTrace
      nonsplitCoefficient hNonsplit hdelta
  refine ⟨max (max splitThreshold nonsplitThreshold) 3, ?_⟩
  intro p hp _ c x hc hregular hlarge
  have hpSplit : splitThreshold ≤ p := by omega
  have hpNonsplit : nonsplitThreshold ≤ p := by omega
  have hpTwo : p ≠ 2 := by omega
  let t := trace c x.1.x2
  have ht : t ^ 2 ≠ 4 := by
    exact sub_ne_zero.mp (by simpa [t] using hregular.1)
  have hxCyclic :
      IsSolution (coefficients c) (cycleLeftEquiv x.1) :=
    (isSolution_cycleLeftEquiv c x.1).2 x.property
  rcases exists_split_or_quadraticNormOneTrace p hpTwo t ht with
      ⟨q, htraceQ, hq⟩ | ⟨w, htraceW, hw⟩
  · have horder :
        halfStepOrder t = orderOf q := by
      rw [Opening.halfStepOrder_eq_bgsRotationOrder, ← htraceQ]
      exact rotationOrder_splitTorusTrace q hq
    have hlargeQ :
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf q := by
      simpa [t, horder] using hlarge
    obtain ⟨n, v, hnTrace, hvOrder, hvRegular⟩ :=
      hsplit p hpSplit c x.1.x2 t q (cycleLeftEquiv x.1)
        hxCyclic (by simp [cycleLeftEquiv]) rfl htraceQ.symm
        hc hregular hlargeQ
    let yPoint := ((oneStep2 c)^[n]) x.1
    have hySolution : IsSolution (coefficients c) yPoint :=
      isSolution_iterate_oneStep2 c x.property n
    let y : SolutionSurface (coefficients c) :=
      ⟨yPoint, hySolution⟩
    refine ⟨y, sameOneStepComponent_of_oneStep2_iterate c x y n rfl,
      Cage.Axis.third, ?_⟩
    have htraceY :
        trace c (Cage.coordinateAt Cage.Axis.third y.1) =
          splitTorusTrace v := by
      change trace c (((oneStep2 c)^[n]) x.1).x3 =
        splitTorusTrace v
      calc
        trace c (((oneStep2 c)^[n]) x.1).x3 =
            trace c (((oneStep1 c)^[n]) (cycleLeftEquiv x.1)).x2 := by
              rw [← cycleLeftEquiv_iterate_oneStep2 n c x.1]
              rfl
        _ = splitTorusTrace v := hnTrace
    refine ⟨?_, v, htraceY, hvOrder⟩
    change OrderedTraceCandidateRegular c c c
      (trace c (Cage.coordinateAt Cage.Axis.third y.1))
    rw [htraceY]
    exact hvRegular
  · have horder :
        halfStepOrder t = orderOf w := by
      rw [Opening.halfStepOrder_eq_bgsRotationOrder, ← htraceW]
      exact rotationOrder_quadraticNormOneTrace p w hw
    have hlargeW :
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf w := by
      simpa [t, horder] using hlarge
    obtain ⟨n, v, hnTrace, hvOrder, hvRegular⟩ :=
      hnonsplit p hpNonsplit c x.1.x2 t (cycleLeftEquiv x.1) w
        hxCyclic (by simp [cycleLeftEquiv]) rfl hc hregular
        htraceW hlargeW
    let yPoint := ((oneStep2 c)^[n]) x.1
    have hySolution : IsSolution (coefficients c) yPoint :=
      isSolution_iterate_oneStep2 c x.property n
    let y : SolutionSurface (coefficients c) :=
      ⟨yPoint, hySolution⟩
    refine ⟨y, sameOneStepComponent_of_oneStep2_iterate c x y n rfl,
      Cage.Axis.third, ?_⟩
    have htraceY :
        trace c (Cage.coordinateAt Cage.Axis.third y.1) =
          splitTorusTrace v := by
      change trace c (((oneStep2 c)^[n]) x.1).x3 =
        splitTorusTrace v
      calc
        trace c (((oneStep2 c)^[n]) x.1).x3 =
            trace c (((oneStep1 c)^[n]) (cycleLeftEquiv x.1)).x2 := by
              rw [← cycleLeftEquiv_iterate_oneStep2 n c x.1]
              rfl
        _ = splitTorusTrace v := hnTrace
    refine ⟨?_, v, htraceY, hvOrder⟩
    change OrderedTraceCandidateRegular c c c
      (trace c (Cage.coordinateAt Cage.Axis.third y.1))
    rw [htraceY]
    exact hvRegular

/-- Cyclic third-axis endgame: every candidate-regular trace of endgame
order reaches a candidate-regular primitive split trace on the first axis. -/
theorem exists_threshold_regularThirdOrder_to_regularSplitCage
    (splitCoefficient : ℕ)
    (hSplit :
      WeightedShiftedTraceWeilBoundAssumption splitCoefficient)
    (nonsplitCoefficient : ℕ)
    (hNonsplit :
      Endgame.Nonsplit.ShiftedSeededNonsplitTraceWeilBoundAssumption
        nonsplitCoefficient)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ threshold : ℕ,
      ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
        ∀ (c : ZMod p) (x : SolutionSurface (coefficients c)),
          c ^ 2 ≠ 4 →
          OrderedTraceCandidateRegular c c c (trace c x.1.x3) →
          (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
            halfStepOrder (trace c x.1.x3) →
          ∃ y : SolutionSurface (coefficients c),
            Cage.SameOneStepComponent c x y ∧
              Cage.IsInRegularSplitCage p c y := by
  obtain ⟨splitThreshold, hsplit⟩ :=
    Endgame.exists_threshold_actualSplitPoint_with_primitiveCandidateRegularAdjacentTrace
      splitCoefficient hSplit hdelta
  obtain ⟨nonsplitThreshold, hnonsplit⟩ :=
    Endgame.Nonsplit.exists_threshold_actualNonsplitPoint_with_primitiveCandidateRegularAdjacentTrace
      nonsplitCoefficient hNonsplit hdelta
  refine ⟨max (max splitThreshold nonsplitThreshold) 3, ?_⟩
  intro p hp _ c x hc hregular hlarge
  have hpSplit : splitThreshold ≤ p := by omega
  have hpNonsplit : nonsplitThreshold ≤ p := by omega
  have hpTwo : p ≠ 2 := by omega
  let t := trace c x.1.x3
  have ht : t ^ 2 ≠ 4 := by
    exact sub_ne_zero.mp (by simpa [t] using hregular.1)
  have hxCyclic :
      IsSolution (coefficients c) (cycleRightEquiv x.1) :=
    (isSolution_cycleRightEquiv c x.1).2 x.property
  rcases exists_split_or_quadraticNormOneTrace p hpTwo t ht with
      ⟨q, htraceQ, hq⟩ | ⟨w, htraceW, hw⟩
  · have horder :
        halfStepOrder t = orderOf q := by
      rw [Opening.halfStepOrder_eq_bgsRotationOrder, ← htraceQ]
      exact rotationOrder_splitTorusTrace q hq
    have hlargeQ :
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf q := by
      simpa [t, horder] using hlarge
    obtain ⟨n, v, hnTrace, hvOrder, hvRegular⟩ :=
      hsplit p hpSplit c x.1.x3 t q (cycleRightEquiv x.1)
        hxCyclic
        (by simp [cycleRightEquiv, cycleLeftEquiv]) rfl htraceQ.symm
        hc hregular hlargeQ
    let yPoint := ((oneStep3 c)^[n]) x.1
    have hySolution : IsSolution (coefficients c) yPoint :=
      isSolution_iterate_oneStep3 c x.property n
    let y : SolutionSurface (coefficients c) :=
      ⟨yPoint, hySolution⟩
    refine ⟨y, sameOneStepComponent_of_oneStep3_iterate c x y n rfl,
      Cage.Axis.first, ?_⟩
    have htraceY :
        trace c (Cage.coordinateAt Cage.Axis.first y.1) =
          splitTorusTrace v := by
      change trace c (((oneStep3 c)^[n]) x.1).x1 =
        splitTorusTrace v
      calc
        trace c (((oneStep3 c)^[n]) x.1).x1 =
            trace c (((oneStep1 c)^[n]) (cycleRightEquiv x.1)).x2 := by
              rw [← cycleRightEquiv_iterate_oneStep3 n c x.1]
              rfl
        _ = splitTorusTrace v := hnTrace
    refine ⟨?_, v, htraceY, hvOrder⟩
    change OrderedTraceCandidateRegular c c c
      (trace c (Cage.coordinateAt Cage.Axis.first y.1))
    rw [htraceY]
    exact hvRegular
  · have horder :
        halfStepOrder t = orderOf w := by
      rw [Opening.halfStepOrder_eq_bgsRotationOrder, ← htraceW]
      exact rotationOrder_quadraticNormOneTrace p w hw
    have hlargeW :
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf w := by
      simpa [t, horder] using hlarge
    obtain ⟨n, v, hnTrace, hvOrder, hvRegular⟩ :=
      hnonsplit p hpNonsplit c x.1.x3 t (cycleRightEquiv x.1) w
        hxCyclic
        (by simp [cycleRightEquiv, cycleLeftEquiv]) rfl hc hregular
        htraceW hlargeW
    let yPoint := ((oneStep3 c)^[n]) x.1
    have hySolution : IsSolution (coefficients c) yPoint :=
      isSolution_iterate_oneStep3 c x.property n
    let y : SolutionSurface (coefficients c) :=
      ⟨yPoint, hySolution⟩
    refine ⟨y, sameOneStepComponent_of_oneStep3_iterate c x y n rfl,
      Cage.Axis.first, ?_⟩
    have htraceY :
        trace c (Cage.coordinateAt Cage.Axis.first y.1) =
          splitTorusTrace v := by
      change trace c (((oneStep3 c)^[n]) x.1).x1 =
        splitTorusTrace v
      calc
        trace c (((oneStep3 c)^[n]) x.1).x1 =
            trace c (((oneStep1 c)^[n]) (cycleRightEquiv x.1)).x2 := by
              rw [← cycleRightEquiv_iterate_oneStep3 n c x.1]
              rfl
        _ = splitTorusTrace v := hnTrace
    refine ⟨?_, v, htraceY, hvOrder⟩
    change OrderedTraceCandidateRegular c c c
      (trace c (Cage.coordinateAt Cage.Axis.first y.1))
    rw [htraceY]
    exact hvRegular

end

end GenMarkoff.Symmetric.Assembly
