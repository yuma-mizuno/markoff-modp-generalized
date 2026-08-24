import GenMarkoff.Symmetric.Opening.PeriodicSemisimple

/-!
# Escape from affine-centered symmetric fibers

The periodic semisimple opening argument excludes the zero centered vector.
This file classifies that obstruction on the symmetric surface.  Away from
the parabolic locus, a punctured point centered on one axis is a cyclic
permutation of one explicit point.  Two one-step moves in a transverse
direction then leave the centered locus, unless one of the resulting traces
is parabolic.
-/

namespace GenMarkoff.Symmetric.Opening

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The repeated moving coordinate of the unique punctured affine-centered
point. -/
def centeredExceptionalRadius (c : K) : K :=
  (c - 2) / (3 * c)

/-- The unique punctured point centered on its first-coordinate fiber. -/
def axisOneCenteredExceptionalPoint (c : K) : Point K :=
  ⟨-c * centeredExceptionalRadius c,
    centeredExceptionalRadius c,
    centeredExceptionalRadius c⟩

/-- The point reached from `axisOneCenteredExceptionalPoint` by two
second-axis one-step moves. -/
def axisTwoTransverseEscapePoint (c : K) : Point K :=
  ⟨(-(c + 2) / c) * centeredExceptionalRadius c,
    centeredExceptionalRadius c,
    centeredExceptionalRadius c⟩

/-- At least one coordinate trace is parabolic. -/
def HasParabolicTrace (c : K) (x : Point K) : Prop :=
  trace c x.x1 ^ 2 = 4 ∨
    trace c x.x2 ^ 2 = 4 ∨
      trace c x.x3 ^ 2 = 4

/-- None of the three moving-coordinate pairs is the corresponding affine
center. -/
def AllAxesNoncentered (c : K) (x : Point K) : Prop :=
  centerCoordinates (fiberCenter c x.x1 (trace c x.x1))
      (movingCoordinates1 x) ≠ (0, 0) ∧
    centerCoordinates (fiberCenter c x.x2 (trace c x.x2))
        (movingCoordinates2 x) ≠ (0, 0) ∧
      centerCoordinates (fiberCenter c x.x3 (trace c x.x3))
          (movingCoordinates3 x) ≠ (0, 0)

theorem hasParabolicTrace_cycleLeftEquiv_iff (c : K) (x : Point K) :
    HasParabolicTrace c (cycleLeftEquiv x) ↔
      HasParabolicTrace c x := by
  simp only [HasParabolicTrace, cycleLeftEquiv_apply]
  tauto

theorem hasParabolicTrace_cycleRightEquiv_iff (c : K) (x : Point K) :
    HasParabolicTrace c (cycleRightEquiv x) ↔
      HasParabolicTrace c x := by
  simp only [HasParabolicTrace, cycleRightEquiv_apply]
  tauto

theorem allAxesNoncentered_cycleLeftEquiv_iff (c : K) (x : Point K) :
    AllAxesNoncentered c (cycleLeftEquiv x) ↔
      AllAxesNoncentered c x := by
  simp only [AllAxesNoncentered, cycleLeftEquiv_apply,
    movingCoordinates1, movingCoordinates2, movingCoordinates3]
  tauto

theorem allAxesNoncentered_cycleRightEquiv_iff (c : K) (x : Point K) :
    AllAxesNoncentered c (cycleRightEquiv x) ↔
      AllAxesNoncentered c x := by
  simp only [AllAxesNoncentered, cycleRightEquiv_apply,
    movingCoordinates1, movingCoordinates2, movingCoordinates3]
  tauto

/-- Under a left cyclic relabeling, a third-axis one-step move becomes a
second-axis move. -/
theorem cycleLeftEquiv_oneStep3_eq_oneStep2 (c : K) (x : Point K) :
    cycleLeftEquiv (oneStep3 c x) =
      oneStep2 c (cycleLeftEquiv x) := by
  ext <;>
    simp [cycleLeftEquiv, oneStep2, oneStep3, swap13, swap12,
      vieta1, vieta3, coefficients, Coefficients.multiplier]

/-- Under a right cyclic relabeling, a first-axis one-step move becomes a
second-axis move. -/
theorem cycleRightEquiv_oneStep1_eq_oneStep2 (c : K) (x : Point K) :
    cycleRightEquiv (oneStep1 c x) =
      oneStep2 c (cycleRightEquiv x) := by
  ext <;>
    simp [cycleRightEquiv, cycleLeftEquiv, oneStep1, oneStep2,
      swap23, swap13, vieta2, vieta3, coefficients,
      Coefficients.multiplier]

theorem centeredExceptionalRadius_ne_zero
    (c : K) (hthree : (3 : K) ≠ 0) (hcZero : c ≠ 0)
    (hcTwo : c ≠ 2) :
    centeredExceptionalRadius c ≠ 0 := by
  exact div_ne_zero (sub_ne_zero.mpr hcTwo)
    (mul_ne_zero hthree hcZero)

/-- The exceptional point is fixed by the one-step generator along its
centered first-coordinate fiber. -/
theorem oneStep1_axisOneCenteredExceptionalPoint
    (c : K) (hthree : (3 : K) ≠ 0) (hcZero : c ≠ 0) :
    oneStep1 c (axisOneCenteredExceptionalPoint c) =
      axisOneCenteredExceptionalPoint c := by
  apply Point.ext <;>
    simp [oneStep1, axisOneCenteredExceptionalPoint,
      centeredExceptionalRadius, swap23, vieta2, coefficients,
      Coefficients.multiplier] <;>
    field_simp [hthree, hcZero] <;>
    ring

/-- One transverse second-axis step sends the centered point to an explicit
cyclicly placed intermediate point. -/
theorem oneStep2_axisOneCenteredExceptionalPoint
    (c : K) (hthree : (3 : K) ≠ 0) (hcZero : c ≠ 0) :
    oneStep2 c (axisOneCenteredExceptionalPoint c) =
      ⟨centeredExceptionalRadius c, centeredExceptionalRadius c,
        -c * centeredExceptionalRadius c⟩ := by
  apply Point.ext <;>
    simp [oneStep2, axisOneCenteredExceptionalPoint,
      centeredExceptionalRadius, swap13, vieta3, coefficients,
      Coefficients.multiplier] <;>
    field_simp [hthree, hcZero] <;>
    ring

/-- Two transverse second-axis steps give the explicit escape point. -/
theorem oneStep2_sq_axisOneCenteredExceptionalPoint
    (c : K) (hthree : (3 : K) ≠ 0) (hcZero : c ≠ 0) :
    oneStep2 c (oneStep2 c (axisOneCenteredExceptionalPoint c)) =
      axisTwoTransverseEscapePoint c := by
  rw [oneStep2_axisOneCenteredExceptionalPoint c hthree hcZero]
  apply Point.ext <;>
    simp [oneStep2, axisTwoTransverseEscapePoint,
      centeredExceptionalRadius, swap13, vieta3, coefficients,
      Coefficients.multiplier] <;>
    field_simp [hthree, hcZero] <;>
    ring

/-- The explicit escape point is not the original exceptional point. -/
theorem axisTwoTransverseEscapePoint_ne_axisOneCenteredExceptionalPoint
    (c : K) (hthree : (3 : K) ≠ 0) (hcZero : c ≠ 0)
    (hcOne : 1 + c ≠ 0) (hcTwo : c ≠ 2) :
    axisTwoTransverseEscapePoint c ≠
      axisOneCenteredExceptionalPoint c := by
  intro h
  have hcoord := congrArg Point.x1 h
  have hr : centeredExceptionalRadius c ≠ 0 :=
    centeredExceptionalRadius_ne_zero c hthree hcZero hcTwo
  have hratio : -(c + 2) / c = -c := by
    apply mul_right_cancel₀ hr
    simpa [axisTwoTransverseEscapePoint,
      axisOneCenteredExceptionalPoint] using hcoord
  have hfactor : (c - 2) * (1 + c) = 0 := by
    field_simp [hcZero] at hratio
    linear_combination hratio
  rcases mul_eq_zero.mp hfactor with h | h
  · exact hcTwo (sub_eq_zero.mp h)
  · exact hcOne h

/-- The left cyclic placement of the escape point is not exceptional. -/
theorem cycleLeft_axisTwoTransverseEscapePoint_ne_exceptional
    (c : K) (hthree : (3 : K) ≠ 0) (hcZero : c ≠ 0)
    (hcOne : 1 + c ≠ 0) (hcTwo : c ≠ 2) :
    cycleLeftEquiv (axisTwoTransverseEscapePoint c) ≠
      axisOneCenteredExceptionalPoint c := by
  intro h
  have hcoord := congrArg Point.x1 h
  change centeredExceptionalRadius c =
    -c * centeredExceptionalRadius c at hcoord
  have hr : centeredExceptionalRadius c ≠ 0 :=
    centeredExceptionalRadius_ne_zero c hthree hcZero hcTwo
  have hzero : (1 + c) * centeredExceptionalRadius c = 0 := by
    linear_combination hcoord
  exact (mul_ne_zero hcOne hr) hzero

/-- The right cyclic placement of the escape point is not exceptional. -/
theorem cycleRight_axisTwoTransverseEscapePoint_ne_exceptional
    (c : K) (hthree : (3 : K) ≠ 0) (hcZero : c ≠ 0)
    (hcOne : 1 + c ≠ 0) (hcTwo : c ≠ 2) :
    cycleRightEquiv (axisTwoTransverseEscapePoint c) ≠
      axisOneCenteredExceptionalPoint c := by
  intro h
  have hcoord := congrArg Point.x1 h
  change centeredExceptionalRadius c =
    -c * centeredExceptionalRadius c at hcoord
  have hr : centeredExceptionalRadius c ≠ 0 :=
    centeredExceptionalRadius_ne_zero c hthree hcZero hcTwo
  have hzero : (1 + c) * centeredExceptionalRadius c = 0 := by
    linear_combination hcoord
  exact (mul_ne_zero hcOne hr) hzero

/-- Classification of the affine-center obstruction on the first axis. -/
theorem eq_axisOneCenteredExceptionalPoint_of_centered
    (c : K) (x : Point K)
    (hthree : (3 : K) ≠ 0)
    (hmultiplier : multiplier c ≠ 0)
    (hx : IsSolution (coefficients c) x)
    (hxOrigin : x ≠ origin)
    (htrace : trace c x.x1 ^ 2 ≠ 4)
    (hcenter :
      centerCoordinates (fiberCenter c x.x1 (trace c x.x1))
        (movingCoordinates1 x) = (0, 0)) :
    x = axisOneCenteredExceptionalPoint c := by
  let t := trace c x.x1
  have htTwo : t ≠ 2 := by
    intro ht
    apply htrace
    rw [show trace c x.x1 = t by rfl, ht]
    norm_num
  have hx2 : x.x2 = fiberCenter c x.x1 t := by
    have hfirst := congrArg Prod.fst hcenter
    simpa [t, centerCoordinates, movingCoordinates1] using
      sub_eq_zero.mp hfirst
  have hx3 : x.x3 = fiberCenter c x.x1 t := by
    have hsecond := congrArg Prod.snd hcenter
    simpa [t, centerCoordinates, movingCoordinates1] using
      sub_eq_zero.mp hsecond
  have hx1 : x.x1 ≠ 0 := by
    intro hx1Zero
    apply hxOrigin
    apply Point.ext
    · simpa [origin] using hx1Zero
    · rw [hx2, fiberCenter, hx1Zero]
      simp only [mul_zero, zero_div]
      rfl
    · rw [hx3, fiberCenter, hx1Zero]
      simp only [mul_zero, zero_div]
      rfl
  have hcentered := polynomial_centered_fixed_first
    c x.x1 t 0 0 rfl htTwo
  have hpolyZero :
      polynomial (coefficients c)
        ⟨x.x1, 0 + fiberCenter c x.x1 t,
          0 + fiberCenter c x.x1 t⟩ = 0 := by
    simpa only [zero_add] using
      (show polynomial (coefficients c)
          ⟨x.x1, fiberCenter c x.x1 t,
            fiberCenter c x.x1 t⟩ = 0 by
        have hpoint :
            (⟨x.x1, fiberCenter c x.x1 t,
              fiberCenter c x.x1 t⟩ : Point K) = x := by
          apply Point.ext
          · rfl
          · exact hx2.symm
          · exact hx3.symm
        rw [hpoint]
        exact hx)
  have hconstant :
      x.x1 ^ 2 * (t + c ^ 2 - 2) / (t - 2) = 0 := by
    calc
      x.x1 ^ 2 * (t + c ^ 2 - 2) / (t - 2) =
          polynomial (coefficients c)
            ⟨x.x1, 0 + fiberCenter c x.x1 t,
              0 + fiberCenter c x.x1 t⟩ := by
            simpa using hcentered.symm
      _ = 0 := hpolyZero
  have hcenterTerm : t + c ^ 2 - 2 = 0 := by
    have hnumerator : x.x1 ^ 2 * (t + c ^ 2 - 2) = 0 :=
      (div_eq_zero_iff).mp hconstant |>.resolve_right
        (sub_ne_zero.mpr htTwo)
    exact (mul_eq_zero.mp hnumerator).resolve_left (pow_ne_zero 2 hx1)
  have hcZero : c ≠ 0 := by
    intro hc
    subst c
    apply htrace
    have ht : t = 2 := by
      linear_combination hcenterTerm
    rw [show trace (0 : K) x.x1 = t by rfl, ht]
    norm_num
  have hcOne : 1 + c ≠ 0 := by
    intro hc
    apply hmultiplier
    rw [multiplier, hc]
    simp
  have hfactor : (1 + c) * (3 * x.x1 + c - 2) = 0 := by
    have hcenterTerm' := hcenterTerm
    change trace c x.x1 + c ^ 2 - 2 = 0 at hcenterTerm'
    rw [trace, multiplier] at hcenterTerm'
    linear_combination hcenterTerm'
  have hx1Formula : x.x1 = (2 - c) / 3 := by
    have hlinear :
        3 * x.x1 + c - 2 = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left hcOne
    field_simp [hthree]
    linear_combination hlinear
  have htFormula : t = 2 - c ^ 2 := by
    linear_combination hcenterTerm
  have hmFormula :
      fiberCenter c x.x1 t = centeredExceptionalRadius c := by
    rw [fiberCenter, centeredExceptionalRadius, hx1Formula, htFormula]
    field_simp [hthree, hcZero]
    ring
  apply Point.ext
  · rw [hx1Formula, axisOneCenteredExceptionalPoint,
      centeredExceptionalRadius]
    field_simp [hthree, hcZero]
    ring
  · simpa [axisOneCenteredExceptionalPoint, hx2] using hmFormula
  · simpa [axisOneCenteredExceptionalPoint, hx3] using hmFormula

/-- Cyclic classification of a point centered on its second-coordinate
fiber. -/
theorem cycleLeft_eq_axisOneCenteredExceptionalPoint_of_centered
    (c : K) (x : Point K)
    (hthree : (3 : K) ≠ 0)
    (hmultiplier : multiplier c ≠ 0)
    (hx : IsSolution (coefficients c) x)
    (hxOrigin : x ≠ origin)
    (htrace : trace c x.x2 ^ 2 ≠ 4)
    (hcenter :
      centerCoordinates (fiberCenter c x.x2 (trace c x.x2))
        (movingCoordinates2 x) = (0, 0)) :
    cycleLeftEquiv x = axisOneCenteredExceptionalPoint c := by
  apply eq_axisOneCenteredExceptionalPoint_of_centered
    c (cycleLeftEquiv x) hthree hmultiplier
  · exact (isSolution_cycleLeftEquiv c x).2 hx
  · intro hzero
    apply hxOrigin
    apply cycleLeftEquiv.injective
    simpa [origin] using hzero
  · simpa [cycleLeftEquiv] using htrace
  · simpa [cycleLeftEquiv, movingCoordinates1, movingCoordinates2] using
      hcenter

/-- Cyclic classification of a point centered on its third-coordinate
fiber. -/
theorem cycleRight_eq_axisOneCenteredExceptionalPoint_of_centered
    (c : K) (x : Point K)
    (hthree : (3 : K) ≠ 0)
    (hmultiplier : multiplier c ≠ 0)
    (hx : IsSolution (coefficients c) x)
    (hxOrigin : x ≠ origin)
    (htrace : trace c x.x3 ^ 2 ≠ 4)
    (hcenter :
      centerCoordinates (fiberCenter c x.x3 (trace c x.x3))
        (movingCoordinates3 x) = (0, 0)) :
    cycleRightEquiv x = axisOneCenteredExceptionalPoint c := by
  apply eq_axisOneCenteredExceptionalPoint_of_centered
    c (cycleRightEquiv x) hthree hmultiplier
  · exact (isSolution_cycleRightEquiv c x).2 hx
  · intro hzero
    apply hxOrigin
    apply cycleRightEquiv.injective
    simpa [origin, cycleRightEquiv, cycleLeftEquiv] using hzero
  · simpa [cycleRightEquiv, cycleLeftEquiv] using htrace
  · simpa [cycleRightEquiv, cycleLeftEquiv, movingCoordinates1,
      movingCoordinates3] using hcenter

/-- Two one-step moves in the second-axis direction escape a first-axis
affine center.  The only alternative is that the resulting point has reached
a parabolic coordinate trace, which is handled by the parabolic opening
route. -/
theorem two_oneStep2_of_axisOne_centered_hasParabolicTrace_or_allAxesNoncentered
    (c : K) (x : Point K)
    (hthree : (3 : K) ≠ 0)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (hxOrigin : x ≠ origin)
    (htrace : trace c x.x1 ^ 2 ≠ 4)
    (hcenter :
      centerCoordinates (fiberCenter c x.x1 (trace c x.x1))
        (movingCoordinates1 x) = (0, 0)) :
    HasParabolicTrace c (oneStep2 c (oneStep2 c x)) ∨
      AllAxesNoncentered c (oneStep2 c (oneStep2 c x)) := by
  let y := oneStep2 c (oneStep2 c x)
  change HasParabolicTrace c y ∨ AllAxesNoncentered c y
  have hxExceptional :
      x = axisOneCenteredExceptionalPoint c :=
    eq_axisOneCenteredExceptionalPoint_of_centered
      c x hthree hmultiplier hx hxOrigin htrace hcenter
  have hcZero : c ≠ 0 := by
    intro hcZero
    subst c
    apply hxOrigin
    simpa [axisOneCenteredExceptionalPoint, centeredExceptionalRadius,
      origin] using hxExceptional
  have hcOne : 1 + c ≠ 0 := by
    intro hcOne
    apply hmultiplier
    rw [multiplier, hcOne]
    simp
  have hcTwo : c ≠ 2 := by
    intro hcTwo
    apply hc
    rw [hcTwo]
    norm_num
  have hr : centeredExceptionalRadius c ≠ 0 :=
    centeredExceptionalRadius_ne_zero c hthree hcZero hcTwo
  have hyEscape : y = axisTwoTransverseEscapePoint c := by
    dsimp [y]
    rw [hxExceptional,
      oneStep2_sq_axisOneCenteredExceptionalPoint c hthree hcZero]
  have hySolution : IsSolution (coefficients c) y := by
    dsimp [y]
    exact (isSolution_oneStep2 c _).2
      ((isSolution_oneStep2 c _).2 hx)
  have hyOrigin : y ≠ origin := by
    intro hzero
    have hcoord := congrArg Point.x2 (hyEscape.symm.trans hzero)
    apply hr
    simpa [axisTwoTransverseEscapePoint, origin] using hcoord
  by_cases hparabolic1 : trace c y.x1 ^ 2 = 4
  · left
    exact Or.inl hparabolic1
  by_cases hparabolic2 : trace c y.x2 ^ 2 = 4
  · left
    exact Or.inr (Or.inl hparabolic2)
  by_cases hparabolic3 : trace c y.x3 ^ 2 = 4
  · left
    exact Or.inr (Or.inr hparabolic3)
  right
  refine ⟨?_, ?_, ?_⟩
  · intro hcentered
    have hyExceptional :
        y = axisOneCenteredExceptionalPoint c :=
      eq_axisOneCenteredExceptionalPoint_of_centered
        c y hthree hmultiplier hySolution hyOrigin hparabolic1 hcentered
    exact
      (axisTwoTransverseEscapePoint_ne_axisOneCenteredExceptionalPoint
        c hthree hcZero hcOne hcTwo)
        (hyEscape.symm.trans hyExceptional)
  · intro hcentered
    have hyExceptional :
        cycleLeftEquiv y = axisOneCenteredExceptionalPoint c :=
      cycleLeft_eq_axisOneCenteredExceptionalPoint_of_centered
        c y hthree hmultiplier hySolution hyOrigin hparabolic2 hcentered
    exact
      (cycleLeft_axisTwoTransverseEscapePoint_ne_exceptional
        c hthree hcZero hcOne hcTwo)
        ((congrArg cycleLeftEquiv hyEscape).symm.trans hyExceptional)
  · intro hcentered
    have hyExceptional :
        cycleRightEquiv y = axisOneCenteredExceptionalPoint c :=
      cycleRight_eq_axisOneCenteredExceptionalPoint_of_centered
        c y hthree hmultiplier hySolution hyOrigin hparabolic3 hcentered
    exact
      (cycleRight_axisTwoTransverseEscapePoint_ne_exceptional
        c hthree hcZero hcOne hcTwo)
        ((congrArg cycleRightEquiv hyEscape).symm.trans hyExceptional)

/-- Cyclic second-axis form of the centered escape dichotomy. -/
theorem two_oneStep3_of_axisTwo_centered_hasParabolicTrace_or_allAxesNoncentered
    (c : K) (x : Point K)
    (hthree : (3 : K) ≠ 0)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (hxOrigin : x ≠ origin)
    (htrace : trace c x.x2 ^ 2 ≠ 4)
    (hcenter :
      centerCoordinates (fiberCenter c x.x2 (trace c x.x2))
        (movingCoordinates2 x) = (0, 0)) :
    HasParabolicTrace c (oneStep3 c (oneStep3 c x)) ∨
      AllAxesNoncentered c (oneStep3 c (oneStep3 c x)) := by
  have hxCyclic : IsSolution (coefficients c) (cycleLeftEquiv x) :=
    (isSolution_cycleLeftEquiv c x).2 hx
  have hxCyclicOrigin : cycleLeftEquiv x ≠ origin := by
    intro hzero
    apply hxOrigin
    apply cycleLeftEquiv.injective
    simpa [origin] using hzero
  have h :=
    two_oneStep2_of_axisOne_centered_hasParabolicTrace_or_allAxesNoncentered
      c (cycleLeftEquiv x) hthree hmultiplier hc hxCyclic
        hxCyclicOrigin (by simpa [cycleLeftEquiv] using htrace)
        (by
          simpa [cycleLeftEquiv, movingCoordinates1, movingCoordinates2] using
            hcenter)
  have hmove :
      cycleLeftEquiv (oneStep3 c (oneStep3 c x)) =
        oneStep2 c (oneStep2 c (cycleLeftEquiv x)) := by
    rw [cycleLeftEquiv_oneStep3_eq_oneStep2,
      cycleLeftEquiv_oneStep3_eq_oneStep2]
  rw [← hmove] at h
  rcases h with hparabolic | hnoncentered
  · exact Or.inl ((hasParabolicTrace_cycleLeftEquiv_iff c _).mp hparabolic)
  · exact Or.inr ((allAxesNoncentered_cycleLeftEquiv_iff c _).mp
      hnoncentered)

/-- Cyclic third-axis form of the centered escape dichotomy. -/
theorem two_oneStep1_of_axisThree_centered_hasParabolicTrace_or_allAxesNoncentered
    (c : K) (x : Point K)
    (hthree : (3 : K) ≠ 0)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (hxOrigin : x ≠ origin)
    (htrace : trace c x.x3 ^ 2 ≠ 4)
    (hcenter :
      centerCoordinates (fiberCenter c x.x3 (trace c x.x3))
        (movingCoordinates3 x) = (0, 0)) :
    HasParabolicTrace c (oneStep1 c (oneStep1 c x)) ∨
      AllAxesNoncentered c (oneStep1 c (oneStep1 c x)) := by
  have hxCyclic : IsSolution (coefficients c) (cycleRightEquiv x) :=
    (isSolution_cycleRightEquiv c x).2 hx
  have hxCyclicOrigin : cycleRightEquiv x ≠ origin := by
    intro hzero
    apply hxOrigin
    apply cycleRightEquiv.injective
    simpa [origin, cycleRightEquiv, cycleLeftEquiv] using hzero
  have h :=
    two_oneStep2_of_axisOne_centered_hasParabolicTrace_or_allAxesNoncentered
      c (cycleRightEquiv x) hthree hmultiplier hc hxCyclic
        hxCyclicOrigin
        (by simpa [cycleRightEquiv, cycleLeftEquiv] using htrace)
        (by
          simpa [cycleRightEquiv, cycleLeftEquiv, movingCoordinates1,
            movingCoordinates3] using hcenter)
  have hmove :
      cycleRightEquiv (oneStep1 c (oneStep1 c x)) =
        oneStep2 c (oneStep2 c (cycleRightEquiv x)) := by
    rw [cycleRightEquiv_oneStep1_eq_oneStep2,
      cycleRightEquiv_oneStep1_eq_oneStep2]
  rw [← hmove] at h
  rcases h with hparabolic | hnoncentered
  · exact Or.inl ((hasParabolicTrace_cycleRightEquiv_iff c _).mp hparabolic)
  · exact Or.inr ((allAxesNoncentered_cycleRightEquiv_iff c _).mp
      hnoncentered)

private theorem three_ne_zero_zmod_of_three_lt
    (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    (3 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
  have hpLe : p ≤ 3 := Nat.le_of_dvd (by norm_num) hpDvd
  omega

/-- Prime-field form of the centered escape dichotomy.  The characteristic
assumption is discharged by the large-prime hypothesis. -/
theorem two_oneStep2_of_axisOne_centered_hasParabolicTrace_or_allAxesNoncentered_zmod
    (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (c : ZMod p) (x : Point (ZMod p))
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (hxOrigin : x ≠ origin)
    (htrace : trace c x.x1 ^ 2 ≠ 4)
    (hcenter :
      centerCoordinates (fiberCenter c x.x1 (trace c x.x1))
        (movingCoordinates1 x) = (0, 0)) :
    HasParabolicTrace c (oneStep2 c (oneStep2 c x)) ∨
      AllAxesNoncentered c (oneStep2 c (oneStep2 c x)) :=
  two_oneStep2_of_axisOne_centered_hasParabolicTrace_or_allAxesNoncentered
    c x (three_ne_zero_zmod_of_three_lt p hp) hmultiplier hc hx
      hxOrigin htrace hcenter

/-- Prime-field second-axis form of the centered escape dichotomy. -/
theorem two_oneStep3_of_axisTwo_centered_hasParabolicTrace_or_allAxesNoncentered_zmod
    (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (c : ZMod p) (x : Point (ZMod p))
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (hxOrigin : x ≠ origin)
    (htrace : trace c x.x2 ^ 2 ≠ 4)
    (hcenter :
      centerCoordinates (fiberCenter c x.x2 (trace c x.x2))
        (movingCoordinates2 x) = (0, 0)) :
    HasParabolicTrace c (oneStep3 c (oneStep3 c x)) ∨
      AllAxesNoncentered c (oneStep3 c (oneStep3 c x)) :=
  two_oneStep3_of_axisTwo_centered_hasParabolicTrace_or_allAxesNoncentered
    c x (three_ne_zero_zmod_of_three_lt p hp) hmultiplier hc hx
      hxOrigin htrace hcenter

/-- Prime-field third-axis form of the centered escape dichotomy. -/
theorem two_oneStep1_of_axisThree_centered_hasParabolicTrace_or_allAxesNoncentered_zmod
    (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (c : ZMod p) (x : Point (ZMod p))
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (hxOrigin : x ≠ origin)
    (htrace : trace c x.x3 ^ 2 ≠ 4)
    (hcenter :
      centerCoordinates (fiberCenter c x.x3 (trace c x.x3))
        (movingCoordinates3 x) = (0, 0)) :
    HasParabolicTrace c (oneStep1 c (oneStep1 c x)) ∨
      AllAxesNoncentered c (oneStep1 c (oneStep1 c x)) :=
  two_oneStep1_of_axisThree_centered_hasParabolicTrace_or_allAxesNoncentered
    c x (three_ne_zero_zmod_of_three_lt p hp) hmultiplier hc hx
      hxOrigin htrace hcenter

end

end GenMarkoff.Symmetric.Opening
