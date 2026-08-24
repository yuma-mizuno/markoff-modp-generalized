import GenMarkoff.Symmetric.Cage.FiberConnectivity
import GenMarkoff.Symmetric.MiddleGame.ActualOrderGrowth
import BGS.Dynamics.StrictMeasureEscape
import BGS.Markoff.MiddleGame.DivisorRange

/-!
# Iterating candidate-regular symmetric middle-game growth

The shifted middle-game step must retain candidate regularity at every
iteration.  We therefore measure only coordinate traces satisfying the
ordered candidate-regular predicate.  The maximum of those three orders is
strictly increased by an actual one-step group move until it reaches the
endgame scale.

The fourteen additional exceptional parameters in the regular trace
selection are absorbed by a factor-two strengthening of the usual
divisor-count envelope estimate.
-/

namespace GenMarkoff.Symmetric.Assembly

open Filter BGS.Markoff

noncomputable section

/-- The half-step order of a trace when it is candidate regular, and zero
otherwise. -/
def candidateRegularHalfStepOrder
    {R : Type*} [Field R] (c t : R) : ℕ :=
  by
    classical
    exact if OrderedTraceCandidateRegular c c c t then halfStepOrder t else 0

@[simp]
theorem candidateRegularHalfStepOrder_eq_halfStepOrder
    {R : Type*} [Field R] (c t : R)
    (hregular : OrderedTraceCandidateRegular c c c t) :
    candidateRegularHalfStepOrder c t = halfStepOrder t := by
  simp [candidateRegularHalfStepOrder, hregular]

theorem candidateRegular_of_candidateRegularHalfStepOrder_pos
    {R : Type*} [Field R] (c t : R)
    (hpos : 0 < candidateRegularHalfStepOrder c t) :
    OrderedTraceCandidateRegular c c c t := by
  classical
  by_contra hregular
  simp [candidateRegularHalfStepOrder, hregular] at hpos

/-- Maximum candidate-regular half-step order among the three coordinate
traces. -/
def maximalCandidateRegularHalfStepOrder
    {R : Type*} [Field R] (c : R) (x : Point R) : ℕ :=
  max (candidateRegularHalfStepOrder c (trace c x.x1))
    (max (candidateRegularHalfStepOrder c (trace c x.x2))
      (candidateRegularHalfStepOrder c (trace c x.x3)))

theorem candidateRegularHalfStepOrder_first_le_maximal
    {R : Type*} [Field R] (c : R) (x : Point R) :
    candidateRegularHalfStepOrder c (trace c x.x1) ≤
      maximalCandidateRegularHalfStepOrder c x := by
  simp [maximalCandidateRegularHalfStepOrder]

theorem candidateRegularHalfStepOrder_second_le_maximal
    {R : Type*} [Field R] (c : R) (x : Point R) :
    candidateRegularHalfStepOrder c (trace c x.x2) ≤
      maximalCandidateRegularHalfStepOrder c x := by
  simp [maximalCandidateRegularHalfStepOrder]

theorem candidateRegularHalfStepOrder_third_le_maximal
    {R : Type*} [Field R] (c : R) (x : Point R) :
    candidateRegularHalfStepOrder c (trace c x.x3) ≤
      maximalCandidateRegularHalfStepOrder c x := by
  simp [maximalCandidateRegularHalfStepOrder]

/-- A positive maximum is attained by one of the three coordinate traces,
and that trace is candidate regular. -/
theorem exists_candidateRegular_axis_eq_maximal
    {R : Type*} [Field R] (c : R) (x : Point R)
    (hpos : 0 < maximalCandidateRegularHalfStepOrder c x) :
    ∃ axis : Cage.Axis,
      OrderedTraceCandidateRegular c c c (Cage.traceAt c axis x) ∧
        halfStepOrder (Cage.traceAt c axis x) =
          maximalCandidateRegularHalfStepOrder c x := by
  classical
  let o₁ := candidateRegularHalfStepOrder c (trace c x.x1)
  let o₂ := candidateRegularHalfStepOrder c (trace c x.x2)
  let o₃ := candidateRegularHalfStepOrder c (trace c x.x3)
  by_cases hfirst : o₂ ≤ o₁ ∧ o₃ ≤ o₁
  · have hmax : maximalCandidateRegularHalfStepOrder c x = o₁ := by
      simp only [maximalCandidateRegularHalfStepOrder, o₁]
      rw [max_eq_left (max_le hfirst.1 hfirst.2)]
    have ho₁ : 0 < o₁ := by simpa [hmax] using hpos
    have hregular :
        OrderedTraceCandidateRegular c c c (trace c x.x1) :=
      candidateRegular_of_candidateRegularHalfStepOrder_pos c
        (trace c x.x1) (by simpa [o₁] using ho₁)
    refine ⟨Cage.Axis.first, ?_, ?_⟩
    · simpa [Cage.traceAt, Cage.coordinateAt] using hregular
    · rw [Cage.traceAt, Cage.coordinateAt]
      calc
        halfStepOrder (trace c x.x1) =
            candidateRegularHalfStepOrder c (trace c x.x1) := by
              symm
              exact candidateRegularHalfStepOrder_eq_halfStepOrder
                c (trace c x.x1) hregular
        _ = o₁ := rfl
        _ = maximalCandidateRegularHalfStepOrder c x := hmax.symm
  · by_cases hsecond : o₁ ≤ o₂ ∧ o₃ ≤ o₂
    · have hmax : maximalCandidateRegularHalfStepOrder c x = o₂ := by
        simp only [maximalCandidateRegularHalfStepOrder, o₂]
        rw [max_eq_left hsecond.2, max_eq_right hsecond.1]
      have ho₂ : 0 < o₂ := by simpa [hmax] using hpos
      have hregular :
          OrderedTraceCandidateRegular c c c (trace c x.x2) :=
        candidateRegular_of_candidateRegularHalfStepOrder_pos c
          (trace c x.x2) (by simpa [o₂] using ho₂)
      refine ⟨Cage.Axis.second, ?_, ?_⟩
      · simpa [Cage.traceAt, Cage.coordinateAt] using hregular
      · rw [Cage.traceAt, Cage.coordinateAt]
        calc
          halfStepOrder (trace c x.x2) =
              candidateRegularHalfStepOrder c (trace c x.x2) := by
                symm
                exact candidateRegularHalfStepOrder_eq_halfStepOrder
                  c (trace c x.x2) hregular
          _ = o₂ := rfl
          _ = maximalCandidateRegularHalfStepOrder c x := hmax.symm
    · have hfirstThird : o₁ ≤ o₃ := by omega
      have hsecondThird : o₂ ≤ o₃ := by omega
      have hmax : maximalCandidateRegularHalfStepOrder c x = o₃ := by
        simp only [maximalCandidateRegularHalfStepOrder, o₃]
        rw [max_eq_right hsecondThird, max_eq_right hfirstThird]
      have ho₃ : 0 < o₃ := by simpa [hmax] using hpos
      have hregular :
          OrderedTraceCandidateRegular c c c (trace c x.x3) :=
        candidateRegular_of_candidateRegularHalfStepOrder_pos c
          (trace c x.x3) (by simpa [o₃] using ho₃)
      refine ⟨Cage.Axis.third, ?_, ?_⟩
      · simpa [Cage.traceAt, Cage.coordinateAt] using hregular
      · rw [Cage.traceAt, Cage.coordinateAt]
        calc
          halfStepOrder (trace c x.x3) =
              candidateRegularHalfStepOrder c (trace c x.x3) := by
                symm
                exact candidateRegularHalfStepOrder_eq_halfStepOrder
                  c (trace c x.x3) hregular
          _ = o₃ := rfl
          _ = maximalCandidateRegularHalfStepOrder c x := hmax.symm

/-- Doubling the standard coefficient in both elementary size hypotheses
forces twice the divisor-count envelope below the current order. -/
theorem two_mul_divisorCount_mul_corvajaZannierEnvelope_lt_currentOrder
    (p currentOrder : ℕ) (hcurrentOrder : 0 < currentOrder)
    (hcube :
      (2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card))) ^ 3 <
          currentOrder)
    (hlinear :
      2 * (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) *
          currentOrder < p) :
    2 * (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
        corvajaZannierCurrentOrderEnvelope p currentOrder <
      (currentOrder : ℝ) := by
  let divisorCount : ℕ :=
    (p - 1).divisors.card + (p + 1).divisors.card
  let coefficient : ℝ :=
    (2 * (corvajaZannierCorollaryTwoSafeCoefficient * divisorCount) : ℕ)
  have horderPos : (0 : ℝ) < currentOrder := by exact_mod_cast hcurrentOrder
  have horderNonneg : (0 : ℝ) ≤ currentOrder := horderPos.le
  have hcoefficientNonneg : 0 ≤ coefficient := by
    dsimp [coefficient]
    positivity
  have hcubeReal : coefficient ^ (3 : ℕ) < (currentOrder : ℝ) := by
    dsimp [coefficient, divisorCount]
    exact_mod_cast hcube
  have hcoefficientRoot :
      coefficient < (currentOrder : ℝ) ^ ((1 : ℝ) / 3) := by
    have h := (Real.lt_rpow_inv_iff_of_pos hcoefficientNonneg horderNonneg
      (by norm_num : (0 : ℝ) < 3)).2
    have h' : coefficient < (currentOrder : ℝ) ^ (3 : ℝ)⁻¹ :=
      h (by simpa [Real.rpow_natCast] using hcubeReal)
    simpa only [one_div] using h'
  have hrootPositive :
      0 < (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) := by
    positivity
  have hcubeRootIdentity :
      (currentOrder : ℝ) ^ ((1 : ℝ) / 3) *
          (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) =
        (currentOrder : ℝ) := by
    rw [Nat.cast_mul]
    rw [← Real.mul_rpow horderNonneg (mul_nonneg horderNonneg horderNonneg)]
    convert Real.pow_rpow_inv_natCast horderNonneg
      (by norm_num : (3 : ℕ) ≠ 0) using 1
    all_goals ring_nf
  have hrootTerm :
      coefficient *
          (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) <
        (currentOrder : ℝ) := by
    calc
      coefficient *
            (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) <
          (currentOrder : ℝ) ^ ((1 : ℝ) / 3) *
            (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) :=
        mul_lt_mul_of_pos_right hcoefficientRoot hrootPositive
      _ = (currentOrder : ℝ) := hcubeRootIdentity
  have hlinearReal :
      coefficient * (currentOrder : ℝ) < (p : ℝ) := by
    dsimp [coefficient, divisorCount]
    exact_mod_cast hlinear
  have hpPos : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hquotientTerm :
      coefficient * (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) <
        (currentOrder : ℝ) := by
    have hratio : coefficient * (currentOrder : ℝ) / (p : ℝ) < 1 :=
      (div_lt_one hpPos).2 hlinearReal
    calc
      coefficient *
            (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) =
          (coefficient * (currentOrder : ℝ) / (p : ℝ)) *
            (currentOrder : ℝ) := by
        rw [Nat.cast_mul]
        ring
      _ < 1 * (currentOrder : ℝ) :=
        mul_lt_mul_of_pos_right hratio horderPos
      _ = (currentOrder : ℝ) := one_mul _
  calc
    2 * (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p currentOrder =
        coefficient * max
          (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
          (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) := by
      simp only [corvajaZannierCurrentOrderEnvelope]
      dsimp [coefficient, divisorCount]
      push_cast
      ring
    _ = max
        (coefficient *
          (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3)))
        (coefficient *
          (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ))) :=
      mul_max_of_nonneg _ _ hcoefficientNonneg
    _ < (currentOrder : ℝ) := max_lt hrootTerm hquotientTerm

/-- Uniform middle-range inequalities with the extra fourteen-point
candidate-regularity margin. -/
theorem eventually_regularMiddleGame_sizeBounds
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ p : ℕ in atTop, ∀ currentOrder : ℕ,
      (p : ℝ) ^ delta < currentOrder →
      (currentOrder : ℝ) < (p : ℝ) ^ (1 - delta) →
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
          currentOrder ∧
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) *
          currentOrder < p ∧
      (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p currentOrder + 14 <
        (currentOrder : ℝ) := by
  let epsilon : ℝ := delta / 6
  let C : ℝ :=
    (2 * corvajaZannierCorollaryTwoSafeCoefficient : ℕ) *
      (2 : ℝ) ^ epsilon
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hThreeEpsilon : 3 * epsilon < delta := by
    dsimp [epsilon]
    linarith
  have hLinearExponent : 1 - delta + epsilon < 1 := by
    dsimp [epsilon]
    linarith
  have hDivisor :=
    eventually_corvajaZannierDivisorCount_le_rpow hepsilon
  have hCubeDominance :
      ∀ᶠ p : ℕ in atTop,
        (2 * C) ^ 3 * (p : ℝ) ^ (3 * epsilon) <
          (p : ℝ) ^ delta :=
    eventually_const_mul_rpow_lt_rpow hThreeEpsilon
  have hLinearDominance :
      ∀ᶠ p : ℕ in atTop,
        (2 * C) * (p : ℝ) ^ (1 - delta + epsilon) <
          (p : ℝ) ^ (1 : ℝ) :=
    eventually_const_mul_rpow_lt_rpow hLinearExponent
  have hTwentyEight :
      ∀ᶠ p : ℕ in atTop, (28 : ℝ) < (p : ℝ) ^ delta := by
    simpa using
      (eventually_const_mul_rpow_lt_rpow
        (C := (28 : ℝ)) (a := (0 : ℝ)) (b := delta) hdelta)
  filter_upwards [hDivisor, hCubeDominance, hLinearDominance,
    hTwentyEight, eventually_ge_atTop 1] with
      p hDivisor hCubeDominance hLinearDominance hTwentyEight hpOne
  intro currentOrder hLower hUpper
  have hpRealPos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpRealNonneg : (0 : ℝ) ≤ p := hpRealPos.le
  have hCPos : 0 < C := by
    dsimp [C]
    simp only [corvajaZannierCorollaryTwoSafeCoefficient]
    positivity
  have hCurrentPos : 0 < currentOrder := by
    have : (0 : ℝ) < currentOrder := (Real.rpow_pos_of_pos hpRealPos _).trans hLower
    exact_mod_cast this
  have hCurrentNonneg : (0 : ℝ) ≤ currentOrder := by positivity
  have hCoeffNonneg :
      (0 : ℝ) ≤ corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) := by
    simp only [corvajaZannierCorollaryTwoSafeCoefficient]
    positivity
  have hDoubleCubeIdentity :
      (2 * (C * (p : ℝ) ^ epsilon)) ^ 3 =
        (2 * C) ^ 3 * (p : ℝ) ^ (3 * epsilon) := by
    rw [mul_pow, mul_pow]
    rw [← Real.rpow_mul_natCast hpRealNonneg epsilon 3]
    ring
  have hDoubleCubeReal :
      ((2 * (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card)) : ℕ) : ℝ) ^ 3 <
        (currentOrder : ℝ) := by
    calc
      ((2 * (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card)) : ℕ) : ℝ) ^ 3 =
          (2 * (corvajaZannierCorollaryTwoSafeCoefficient *
            ((p - 1).divisors.card + (p + 1).divisors.card) : ℝ)) ^ 3 := by
        norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      _ ≤ (2 * (C * (p : ℝ) ^ epsilon)) ^ 3 := by
        apply pow_le_pow_left₀
        · positivity
        · exact mul_le_mul_of_nonneg_left hDivisor (by norm_num)
      _ = (2 * C) ^ 3 * (p : ℝ) ^ (3 * epsilon) :=
        hDoubleCubeIdentity
      _ < (p : ℝ) ^ delta := hCubeDominance
      _ < (currentOrder : ℝ) := hLower
  have hDoubleLinearIdentity :
      2 * (C * (p : ℝ) ^ epsilon) * (p : ℝ) ^ (1 - delta) =
        (2 * C) * (p : ℝ) ^ (1 - delta + epsilon) := by
    calc
      2 * (C * (p : ℝ) ^ epsilon) * (p : ℝ) ^ (1 - delta) =
          (2 * C) *
            ((p : ℝ) ^ epsilon * (p : ℝ) ^ (1 - delta)) := by ring
      _ = (2 * C) * (p : ℝ) ^ (epsilon + (1 - delta)) := by
        rw [← Real.rpow_add hpRealPos]
      _ = (2 * C) * (p : ℝ) ^ (1 - delta + epsilon) := by
        congr 2
        ring
  have hDoubleLinearReal :
      ((2 * (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card)) *
          currentOrder : ℕ) : ℝ) < (p : ℝ) := by
    calc
      ((2 * (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card)) *
          currentOrder : ℕ) : ℝ) =
          2 * (corvajaZannierCorollaryTwoSafeCoefficient *
            ((p - 1).divisors.card + (p + 1).divisors.card) : ℝ) *
              (currentOrder : ℝ) := by
        norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      _ ≤ 2 * (C * (p : ℝ) ^ epsilon) * (currentOrder : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hDivisor (by norm_num))
          hCurrentNonneg
      _ < 2 * (C * (p : ℝ) ^ epsilon) *
          (p : ℝ) ^ (1 - delta) := by
        exact mul_lt_mul_of_pos_left hUpper
          (mul_pos (by norm_num) (mul_pos hCPos
            (Real.rpow_pos_of_pos hpRealPos _)))
      _ = (2 * C) * (p : ℝ) ^ (1 - delta + epsilon) :=
        hDoubleLinearIdentity
      _ < (p : ℝ) ^ (1 : ℝ) := hLinearDominance
      _ = (p : ℝ) := by simp
  have hDoubleEnvelope :=
    two_mul_divisorCount_mul_corvajaZannierEnvelope_lt_currentOrder
      p currentOrder hCurrentPos
        (by exact_mod_cast hDoubleCubeReal)
        (by exact_mod_cast hDoubleLinearReal)
  have hMargin :
      (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p currentOrder + 14 <
        (currentOrder : ℝ) := by
    have horderTwentyEight : (28 : ℝ) < currentOrder :=
      hTwentyEight.trans hLower
    linarith
  refine ⟨?_, ?_, hMargin⟩
  · have hcubeNat :
        (2 * (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card))) ^ 3 <
            currentOrder := by
      exact_mod_cast hDoubleCubeReal
    have hle :
        (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 ≤
          (2 * (corvajaZannierCorollaryTwoSafeCoefficient *
            ((p - 1).divisors.card + (p + 1).divisors.card))) ^ 3 := by
      apply Nat.pow_le_pow_left
      omega
    exact hle.trans_lt hcubeNat
  · have hlinearNat :
        2 * (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card)) *
            currentOrder < p := by
      exact_mod_cast hDoubleLinearReal
    have hle :
        (corvajaZannierCorollaryTwoSafeCoefficient *
          ((p - 1).divisors.card + (p + 1).divisors.card)) *
            currentOrder ≤
          (2 * (corvajaZannierCorollaryTwoSafeCoefficient *
            ((p - 1).divisors.card + (p + 1).divisors.card))) *
              currentOrder := by
      apply Nat.mul_le_mul_right
      omega
    exact hle.trans_lt hlinearNat

theorem sameOneStepComponent_of_iterate_oneStep1
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

theorem sameOneStepComponent_of_iterate_oneStep2
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

theorem sameOneStepComponent_of_iterate_oneStep3
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

/-- One actual one-step component move strictly raises the largest
candidate-regular coordinate order throughout the middle range. -/
theorem
    exists_sameOneStepComponent_maximalCandidateRegularOrder_increase_of_middleRange
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (c : ZMod p) (hc : c ^ 2 ≠ 4)
    (x : SolutionSurface (coefficients c))
    (hpositive : 0 < maximalCandidateRegularHalfStepOrder c x.1)
    (hbelowEndgame :
      (maximalCandidateRegularHalfStepOrder c x.1 : ℝ) <
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
          maximalCandidateRegularHalfStepOrder c x.1)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) *
          maximalCandidateRegularHalfStepOrder c x.1 < p)
    (hregularMargin :
      (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p
            (maximalCandidateRegularHalfStepOrder c x.1) + 14 <
        (maximalCandidateRegularHalfStepOrder c x.1 : ℝ)) :
    ∃ y : SolutionSurface (coefficients c),
      Cage.SameOneStepComponent c x y ∧
        maximalCandidateRegularHalfStepOrder c x.1 <
          maximalCandidateRegularHalfStepOrder c y.1 := by
  obtain ⟨axis, hregular, horder⟩ :=
    exists_candidateRegular_axis_eq_maximal c x.1 hpositive
  cases axis with
  | first =>
      simp only [Cage.traceAt, Cage.coordinateAt] at hregular horder
      obtain ⟨n, hnewRegular, hincrease⟩ :=
        MiddleGame.exists_oneStep1_iterate_with_larger_regular_adjacent_halfStepOrder
          p hpTwo delta hdelta c x.1.x1 (trace c x.1.x1) x.1
            x.property rfl rfl hc hregular
            (by simpa only [horder] using hbelowEndgame)
            (by simpa only [horder] using hcube)
            (by simpa only [horder] using hlinear)
            (by simpa only [horder] using hregularMargin)
      let yPoint : Point (ZMod p) := ((oneStep1 c)^[n]) x.1
      have hySolution : IsSolution (coefficients c) yPoint := by
        exact isSolution_iterate_oneStep1 c x.property n
      let y : SolutionSurface (coefficients c) := ⟨yPoint, hySolution⟩
      refine ⟨y, ?_, ?_⟩
      · apply sameOneStepComponent_of_iterate_oneStep1 c x y n
        rfl
      · calc
          maximalCandidateRegularHalfStepOrder c x.1 =
              halfStepOrder (trace c x.1.x1) := horder.symm
          _ < halfStepOrder (trace c y.1.x2) := by
            simpa [y, yPoint] using hincrease
          _ = candidateRegularHalfStepOrder c (trace c y.1.x2) := by
            symm
            apply candidateRegularHalfStepOrder_eq_halfStepOrder
            simpa [y, yPoint] using hnewRegular
          _ ≤ maximalCandidateRegularHalfStepOrder c y.1 :=
            candidateRegularHalfStepOrder_second_le_maximal c y.1
  | second =>
      simp only [Cage.traceAt, Cage.coordinateAt] at hregular horder
      have hxCyclic :
          IsSolution (coefficients c) (cycleLeftEquiv x.1) :=
        (isSolution_cycleLeftEquiv c x.1).2 x.property
      obtain ⟨n, hnewRegular, hincrease⟩ :=
        MiddleGame.exists_oneStep1_iterate_with_larger_regular_adjacent_halfStepOrder
          p hpTwo delta hdelta c x.1.x2 (trace c x.1.x2)
            (cycleLeftEquiv x.1) hxCyclic rfl rfl hc hregular
            (by simpa only [horder] using hbelowEndgame)
            (by simpa only [horder] using hcube)
            (by simpa only [horder] using hlinear)
            (by simpa only [horder] using hregularMargin)
      let yPoint : Point (ZMod p) := ((oneStep2 c)^[n]) x.1
      have hcoordinate :
          (((oneStep1 c)^[n]) (cycleLeftEquiv x.1)).x2 =
            yPoint.x3 := by
        rw [← cycleLeftEquiv_iterate_oneStep2]
        rfl
      rw [hcoordinate] at hnewRegular hincrease
      have hySolution : IsSolution (coefficients c) yPoint := by
        exact isSolution_iterate_oneStep2 c x.property n
      let y : SolutionSurface (coefficients c) := ⟨yPoint, hySolution⟩
      refine ⟨y, ?_, ?_⟩
      · apply sameOneStepComponent_of_iterate_oneStep2 c x y n
        rfl
      · calc
          maximalCandidateRegularHalfStepOrder c x.1 =
              halfStepOrder (trace c x.1.x2) := horder.symm
          _ < halfStepOrder (trace c y.1.x3) := by
            simpa [y] using hincrease
          _ = candidateRegularHalfStepOrder c (trace c y.1.x3) := by
            symm
            apply candidateRegularHalfStepOrder_eq_halfStepOrder
            simpa [y] using hnewRegular
          _ ≤ maximalCandidateRegularHalfStepOrder c y.1 :=
            candidateRegularHalfStepOrder_third_le_maximal c y.1
  | third =>
      simp only [Cage.traceAt, Cage.coordinateAt] at hregular horder
      have hxCyclic :
          IsSolution (coefficients c) (cycleRightEquiv x.1) :=
        (isSolution_cycleRightEquiv c x.1).2 x.property
      obtain ⟨n, hnewRegular, hincrease⟩ :=
        MiddleGame.exists_oneStep1_iterate_with_larger_regular_adjacent_halfStepOrder
          p hpTwo delta hdelta c x.1.x3 (trace c x.1.x3)
            (cycleRightEquiv x.1) hxCyclic rfl rfl hc hregular
            (by simpa only [horder] using hbelowEndgame)
            (by simpa only [horder] using hcube)
            (by simpa only [horder] using hlinear)
            (by simpa only [horder] using hregularMargin)
      let yPoint : Point (ZMod p) := ((oneStep3 c)^[n]) x.1
      have hcoordinate :
          (((oneStep1 c)^[n]) (cycleRightEquiv x.1)).x2 =
            yPoint.x1 := by
        rw [← cycleRightEquiv_iterate_oneStep3]
        rfl
      rw [hcoordinate] at hnewRegular hincrease
      have hySolution : IsSolution (coefficients c) yPoint := by
        exact isSolution_iterate_oneStep3 c x.property n
      let y : SolutionSurface (coefficients c) := ⟨yPoint, hySolution⟩
      refine ⟨y, ?_, ?_⟩
      · apply sameOneStepComponent_of_iterate_oneStep3 c x y n
        rfl
      · calc
          maximalCandidateRegularHalfStepOrder c x.1 =
              halfStepOrder (trace c x.1.x3) := horder.symm
          _ < halfStepOrder (trace c y.1.x1) := by
            simpa [y] using hincrease
          _ = candidateRegularHalfStepOrder c (trace c y.1.x1) := by
            symm
            apply candidateRegularHalfStepOrder_eq_halfStepOrder
            simpa [y] using hnewRegular
          _ ≤ maximalCandidateRegularHalfStepOrder c y.1 :=
            candidateRegularHalfStepOrder_first_le_maximal c y.1

/-- For every sufficiently large prime, repeated actual one-step moves take
any point whose maximal candidate-regular order is above the opening scale
to the endgame scale. -/
theorem exists_threshold_regularMiddleGame_reaches_endgame
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaQuarter : delta ≤ (1 : ℝ) / 4) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
      ∀ (c : ZMod p), c ^ 2 ≠ 4 →
      ∀ x : SolutionSurface (coefficients c),
        (p : ℝ) ^ delta <
            maximalCandidateRegularHalfStepOrder c x.1 →
        ∃ y : SolutionSurface (coefficients c),
          Cage.SameOneStepComponent c x y ∧
            (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
              maximalCandidateRegularHalfStepOrder c y.1 := by
  obtain ⟨sizeThreshold, hsizeThreshold⟩ :=
    eventually_atTop.mp (eventually_regularMiddleGame_sizeBounds hdelta)
  refine ⟨max sizeThreshold 3, ?_⟩
  intro p hp _ c hc x hxLower
  letI : Fintype (quadraticFiniteField p) := Fintype.ofFinite _
  have hpSize : sizeThreshold ≤ p := (le_max_left _ _).trans hp
  have hpThree : 3 ≤ p := (le_max_right _ _).trans hp
  have hpTwo : p ≠ 2 := by omega
  have hsize := hsizeThreshold p hpSize
  have hpOne : (1 : ℝ) ≤ p := by
    exact_mod_cast (show 1 ≤ p by
      exact (Fact.out : p.Prime).one_le)
  have htargetUpper :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
        (p : ℝ) ^ (1 - delta) := by
    apply Real.rpow_le_rpow_of_exponent_le hpOne
    linarith
  let endgameReal : ℝ := (p : ℝ) ^ ((1 : ℝ) / 2 + delta)
  let target : ℕ := Nat.ceil endgameReal
  let MiddleState :=
    {q : SolutionSurface (coefficients c) //
      (p : ℝ) ^ delta <
        maximalCandidateRegularHalfStepOrder c q.1}
  let start : MiddleState := ⟨x, hxLower⟩
  let r : MiddleState → MiddleState → Prop :=
    fun q z => Cage.SameOneStepComponent c q.1 z.1
  let measure : MiddleState → ℕ :=
    fun q => maximalCandidateRegularHalfStepOrder c q.1.1
  have hstep : ∀ q : MiddleState, measure q < target →
      ∃ z : MiddleState, r q z ∧ measure q < measure z := by
    intro q hqTarget
    have hqBelow :
        (maximalCandidateRegularHalfStepOrder c q.1.1 : ℝ) <
          endgameReal := by
      exact Nat.lt_ceil.mp hqTarget
    have hqUpper :
        (maximalCandidateRegularHalfStepOrder c q.1.1 : ℝ) <
          (p : ℝ) ^ (1 - delta) := by
      exact hqBelow.trans_le htargetUpper
    obtain ⟨hqCube, hqLinear, hqMargin⟩ :=
      hsize (maximalCandidateRegularHalfStepOrder c q.1.1) q.2 hqUpper
    have hqPositive :
        0 < maximalCandidateRegularHalfStepOrder c q.1.1 := by
      have hpPowerPos : 0 < (p : ℝ) ^ delta := by
        apply Real.rpow_pos_of_pos
        exact_mod_cast (show 0 < p by
          exact (Fact.out : p.Prime).pos)
      have hreal :
          (0 : ℝ) <
            maximalCandidateRegularHalfStepOrder c q.1.1 :=
        hpPowerPos.trans q.2
      exact_mod_cast hreal
    obtain ⟨z, hqz, hincrease⟩ :=
      exists_sameOneStepComponent_maximalCandidateRegularOrder_increase_of_middleRange
        p hpTwo delta (by linarith) c hc q.1 hqPositive
          (by simpa [endgameReal] using hqBelow)
          hqCube hqLinear hqMargin
    have hzLower :
        (p : ℝ) ^ delta <
          maximalCandidateRegularHalfStepOrder c z.1 := by
      calc
        (p : ℝ) ^ delta <
            maximalCandidateRegularHalfStepOrder c q.1.1 := q.2
        _ < maximalCandidateRegularHalfStepOrder c z.1 := by
          exact_mod_cast hincrease
    exact ⟨⟨z, hzLower⟩, hqz, hincrease⟩
  obtain ⟨finish, hchain, htarget⟩ :=
    BGS.exists_reflTransGen_measure_ge r measure target hstep start
  have hcomponent : Cage.SameOneStepComponent c x finish.1 := by
    have hchainComponent :
        ∀ {q z : MiddleState}, Relation.ReflTransGen r q z →
          Cage.SameOneStepComponent c q.1 z.1 := by
      intro q z hqz
      induction hqz with
      | refl => exact Cage.sameOneStepComponent_refl c q.1
      | tail hqa hab ih =>
          exact Cage.sameOneStepComponent_trans ih hab
    exact hchainComponent hchain
  have hendgame :
      endgameReal ≤
        (maximalCandidateRegularHalfStepOrder c finish.1.1 : ℝ) := by
    exact Nat.ceil_le.mp htarget
  exact ⟨finish.1, hcomponent, by
    simpa [endgameReal] using hendgame⟩

end

end GenMarkoff.Symmetric.Assembly
