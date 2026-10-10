import GenMarkoff.Core.Basic
import GenMarkoff.TraceCurve.ShiftedCover.Basic

/-!
# Exceptional traces for the shifted trace curve

For an ordered coefficient frame `(A, B, C)` and a fiber trace `t`, the
adjacent shifted trace curve has parameters `orderedTraceSigma A B C t` and
`orderedTraceGamma A B C t`.  This file defines the polynomial
`orderedTraceSafePolynomial A B C`, of degree at most ten, whose nonvanishing
at `t` (`OrderedTraceCandidateRegular A B C t`) excludes the parabolic traces
`t ^ 2 = 4`, the traces with `sigma = 0` or `sigma = 1`, and the two
trace-dependent factors of the even obstruction.  The remaining coefficient
factor `B ^ 2 - 4` of the even obstruction is a separate hypothesis
(`OrderedTraceCandidateRegular.evenObstruction_ne_zero`).

The second half of the file bounds the points of a first-coordinate surface
fiber with a given second-coordinate trace by two, and bounds by twenty the
members of a finite family with two-element trace fibers whose trace is a
root of the safe polynomial.
-/

namespace GenMarkoff

open Polynomial

noncomputable section

section OrderedTracePolynomials

variable {K : Type*} [Field K]

/-- The nonparabolic discriminant `t² - 4`. -/
def orderedTraceDiscriminantPolynomial : K[X] :=
  X ^ 2 - 4

/-- The centered-conic numerator
`t² - 4 + B² + C² + BCt` for an ordered coefficient frame `(A,B,C)`. -/
def orderedTraceCenteredNormPolynomial (B C : K) : K[X] :=
  X ^ 2 + Polynomial.C (B * C) * X +
    Polynomial.C (B ^ 2 + C ^ 2 - 4)

/-- The numerator of `sigma - 1`, before division by `(t² - 4)²`. -/
def orderedTraceWeightDifferencePolynomial (A B C : K) : K[X] :=
  (X + Polynomial.C A) ^ 2 * orderedTraceCenteredNormPolynomial B C -
    orderedTraceDiscriminantPolynomial ^ 2

/-- The first trace-dependent linear factor of the candidate common-even
obstruction. -/
def orderedTraceEvenMinusPolynomial (A B C : K) : K[X] :=
  Polynomial.C (4 * (C - A)) * X +
    Polynomial.C (-A ^ 2 * B - 2 * A ^ 2 + 4 * A * C + 4 * B - 8)

/-- The second trace-dependent linear factor of the candidate common-even
obstruction. -/
def orderedTraceEvenPlusPolynomial (A B C : K) : K[X] :=
  Polynomial.C (4 * (A + C)) * X +
    Polynomial.C (-A ^ 2 * B + 2 * A ^ 2 + 4 * A * C + 4 * B + 8)

/-- The affine-center contribution to the adjacent trace. -/
def orderedTraceShiftPolynomial (A B C : K) : K[X] :=
  Polynomial.C (2 * C + A * B) * X +
    Polynomial.C (2 * A * C + 4 * B)

/-- The product of the six trace-dependent exceptional factors: `t ^ 2 - 4`,
`t + A`, the centered norm, the numerator of `sigma - 1`, and the two linear
factors of the even obstruction.  Characteristic and coefficient hypotheses
are not encoded here. -/
def orderedTraceSafePolynomial (A B C : K) : K[X] :=
  orderedTraceDiscriminantPolynomial *
    (X + Polynomial.C A) *
    orderedTraceCenteredNormPolynomial B C *
    orderedTraceWeightDifferencePolynomial A B C *
    orderedTraceEvenMinusPolynomial A B C *
    orderedTraceEvenPlusPolynomial A B C

/-- The trace `t` is not a root of any of the six factors of
`orderedTraceSafePolynomial A B C`. -/
def OrderedTraceCandidateRegular (A B C t : K) : Prop :=
  eval t orderedTraceDiscriminantPolynomial ≠ 0 ∧
    t + A ≠ 0 ∧
    eval t (orderedTraceCenteredNormPolynomial B C) ≠ 0 ∧
    eval t (orderedTraceWeightDifferencePolynomial A B C) ≠ 0 ∧
    eval t (orderedTraceEvenMinusPolynomial A B C) ≠ 0 ∧
    eval t (orderedTraceEvenPlusPolynomial A B C) ≠ 0

@[simp]
theorem eval_orderedTraceDiscriminantPolynomial (t : K) :
    eval t orderedTraceDiscriminantPolynomial = t ^ 2 - 4 := by
  simp [orderedTraceDiscriminantPolynomial]

@[simp]
theorem eval_orderedTraceCenteredNormPolynomial (B C t : K) :
    eval t (orderedTraceCenteredNormPolynomial B C) =
      t ^ 2 - 4 + B ^ 2 + C ^ 2 + t * B * C := by
  simp [orderedTraceCenteredNormPolynomial]
  ring

@[simp]
theorem eval_orderedTraceWeightDifferencePolynomial (A B C t : K) :
    eval t (orderedTraceWeightDifferencePolynomial A B C) =
      (t + A) ^ 2 * (t ^ 2 - 4 + B ^ 2 + C ^ 2 + t * B * C) -
        (t ^ 2 - 4) ^ 2 := by
  simp [orderedTraceWeightDifferencePolynomial]

/-- The quartic terms in the numerator of `sigma - 1` cancel. -/
theorem orderedTraceWeightDifferencePolynomial_eq_cubic (A B C : K) :
    orderedTraceWeightDifferencePolynomial A B C =
      Polynomial.C (B * C + 2 * A) * X ^ 3 +
        Polynomial.C (B ^ 2 + C ^ 2 + 4 + 2 * A * B * C + A ^ 2) * X ^ 2 +
        Polynomial.C
            (2 * A * B ^ 2 + 2 * A * C ^ 2 - 8 * A + A ^ 2 * B * C) * X +
        Polynomial.C (A ^ 2 * B ^ 2 + A ^ 2 * C ^ 2 - 4 * A ^ 2 - 16) := by
  rw [orderedTraceWeightDifferencePolynomial,
    orderedTraceCenteredNormPolynomial,
    orderedTraceDiscriminantPolynomial]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_sub, Polynomial.C_ofNat]
  ring

@[simp]
theorem eval_orderedTraceEvenMinusPolynomial (A B C t : K) :
    eval t (orderedTraceEvenMinusPolynomial A B C) =
      4 * (C - A) * t - A ^ 2 * B - 2 * A ^ 2 +
        4 * A * C + 4 * B - 8 := by
  simp [orderedTraceEvenMinusPolynomial]
  ring

@[simp]
theorem eval_orderedTraceEvenPlusPolynomial (A B C t : K) :
    eval t (orderedTraceEvenPlusPolynomial A B C) =
      4 * (A + C) * t - A ^ 2 * B + 2 * A ^ 2 +
        4 * A * C + 4 * B + 8 := by
  simp [orderedTraceEvenPlusPolynomial]
  ring

@[simp]
theorem eval_orderedTraceShiftPolynomial (A B C t : K) :
    eval t (orderedTraceShiftPolynomial A B C) =
      (2 * C + A * B) * t + 2 * A * C + 4 * B := by
  simp [orderedTraceShiftPolynomial]
  ring

/-- Nonvanishing of the safe polynomial at `t` is candidate regularity. -/
theorem orderedTraceSafePolynomial_eval_ne_zero_iff
    (A B C t : K) :
    eval t (orderedTraceSafePolynomial A B C) ≠ 0 ↔
      OrderedTraceCandidateRegular A B C t := by
  simp [orderedTraceSafePolynomial, OrderedTraceCandidateRegular, and_assoc]

/-- The candidate normalized product `sigma = alpha * beta` for an ordered
nonparabolic fiber trace. -/
def orderedTraceSigma (A B C t : K) : K :=
  (t + A) ^ 2 *
      (t ^ 2 - 4 + B ^ 2 + C ^ 2 + t * B * C) /
    (t ^ 2 - 4) ^ 2

/-- The candidate normalized affine shift `gamma` for the ordered target coefficient
`B`; `C` is the remaining coefficient. -/
def orderedTraceGamma (A B C t : K) : K :=
  eval t (orderedTraceShiftPolynomial A B C) / (t ^ 2 - 4)

/-- Exact specialization of the common-even obstruction to the ordered
candidate parameters. -/
theorem shiftedTraceEvenObstruction_orderedTrace
    (A B C t : K) (hD : t ^ 2 - 4 ≠ 0) :
    shiftedTraceEvenObstruction
        (orderedTraceSigma A B C t) (orderedTraceGamma A B C t) =
      (B ^ 2 - 4) *
          eval t (orderedTraceEvenMinusPolynomial A B C) *
          eval t (orderedTraceEvenPlusPolynomial A B C) /
        (t ^ 2 - 4) ^ 2 := by
  simp only [orderedTraceSigma, orderedTraceGamma,
    eval_orderedTraceEvenMinusPolynomial,
    eval_orderedTraceEvenPlusPolynomial,
    eval_orderedTraceShiftPolynomial,
    shiftedTraceEvenObstruction]
  field_simp [hD]
  ring

/-- At a candidate-regular trace, `orderedTraceSigma A B C t ≠ 0`. -/
theorem OrderedTraceCandidateRegular.sigma_ne_zero
    {A B C t : K} (h : OrderedTraceCandidateRegular A B C t) :
    orderedTraceSigma A B C t ≠ 0 := by
  rcases h with ⟨hD, htA, hN, -⟩
  simp only [eval_orderedTraceDiscriminantPolynomial] at hD
  simp only [eval_orderedTraceCenteredNormPolynomial] at hN
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 htA) hN)
    (pow_ne_zero 2 hD)

/-- At a candidate-regular trace, `orderedTraceSigma A B C t ≠ 1`. -/
theorem OrderedTraceCandidateRegular.sigma_ne_one
    {A B C t : K} (h : OrderedTraceCandidateRegular A B C t) :
    orderedTraceSigma A B C t ≠ 1 := by
  rcases h with ⟨hD, _, _, hW, -⟩
  simp only [eval_orderedTraceDiscriminantPolynomial,
    eval_orderedTraceWeightDifferencePolynomial] at hD hW
  intro hsigma
  apply hW
  rw [orderedTraceSigma] at hsigma
  field_simp [hD] at hsigma
  linear_combination hsigma

/-- At a candidate-regular trace and for `B ^ 2 ≠ 4`, the even obstruction of
the candidate parameters is nonzero. -/
theorem OrderedTraceCandidateRegular.evenObstruction_ne_zero
    {A B C t : K} (hB : B ^ 2 ≠ 4)
    (h : OrderedTraceCandidateRegular A B C t) :
    shiftedTraceEvenObstruction
        (orderedTraceSigma A B C t) (orderedTraceGamma A B C t) ≠ 0 := by
  rcases h with ⟨hD, _, _, _, hminus, hplus⟩
  simp only [eval_orderedTraceDiscriminantPolynomial] at hD
  rw [shiftedTraceEvenObstruction_orderedTrace A B C t hD]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hB) hminus) hplus)
    (pow_ne_zero 2 hD)

lemma orderedTraceDiscriminantPolynomial_ne_zero :
    (orderedTraceDiscriminantPolynomial : K[X]) ≠ 0 := by
  intro h
  have hcoeff := congrArg (coeff · 2) h
  simp [orderedTraceDiscriminantPolynomial] at hcoeff

lemma X_add_C_ne_zero (A : K) : X + C A ≠ 0 := by
  intro h
  have hcoeff := congrArg (coeff · 1) h
  simp at hcoeff

lemma orderedTraceCenteredNormPolynomial_ne_zero (B C : K) :
    orderedTraceCenteredNormPolynomial B C ≠ 0 := by
  intro h
  have hcoeff := congrArg (coeff · 2) h
  simp only [orderedTraceCenteredNormPolynomial, coeff_add, coeff_X_pow,
    coeff_C_mul, coeff_X, coeff_C] at hcoeff
  norm_num at hcoeff

lemma orderedTraceWeightDifferencePolynomial_ne_zero
    (A B C : K) (hA : A ^ 2 ≠ 4) :
    orderedTraceWeightDifferencePolynomial A B C ≠ 0 := by
  intro hzero
  have heval := congrArg (eval (-A)) hzero
  have hsquare : (A ^ 2 - 4) ^ 2 = 0 := by
    simpa [orderedTraceWeightDifferencePolynomial,
      orderedTraceDiscriminantPolynomial] using heval
  exact hA (sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare))

lemma orderedTraceEvenMinusPolynomial_ne_zero
    (A B C : K) (htwo : (2 : K) ≠ 0)
    (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4) :
    orderedTraceEvenMinusPolynomial A B C ≠ 0 := by
  intro hzero
  have h0 := congrArg (coeff · 0) hzero
  have h1 := congrArg (coeff · 1) hzero
  simp only [orderedTraceEvenMinusPolynomial, coeff_add,
    coeff_C_mul, coeff_X, coeff_C] at h0 h1
  norm_num at h0 h1
  have hfour : (4 : K) ≠ 0 := by
    -- `show` states `4 = 2 ^ 2` so that `pow_ne_zero` applies.
    rw [show (4 : K) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 htwo
  have hCA : C = A := by
    apply sub_eq_zero.mp
    exact h1.resolve_left hfour
  subst C
  have hfactor : (4 - A ^ 2) * (B - 2) = 0 := by
    linear_combination h0
  rcases mul_eq_zero.mp hfactor with hbad | hBtwo
  · exact hA (sub_eq_zero.mp hbad).symm
  · apply hB
    have : B = 2 := sub_eq_zero.mp hBtwo
    rw [this]
    norm_num

lemma orderedTraceEvenPlusPolynomial_ne_zero
    (A B C : K) (htwo : (2 : K) ≠ 0)
    (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4) :
    orderedTraceEvenPlusPolynomial A B C ≠ 0 := by
  intro hzero
  have h0 := congrArg (coeff · 0) hzero
  have h1 := congrArg (coeff · 1) hzero
  simp only [orderedTraceEvenPlusPolynomial, coeff_add,
    coeff_C_mul, coeff_X, coeff_C] at h0 h1
  norm_num at h0 h1
  have hfour : (4 : K) ≠ 0 := by
    -- `show` states `4 = 2 ^ 2` so that `pow_ne_zero` applies.
    rw [show (4 : K) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 htwo
  have hCA : C = -A := by
    have hsum : A + C = 0 := h1.resolve_left hfour
    linear_combination hsum
  subst C
  have hfactor : (4 - A ^ 2) * (B + 2) = 0 := by
    linear_combination h0
  rcases mul_eq_zero.mp hfactor with hbad | hBtwo
  · exact hA (sub_eq_zero.mp hbad).symm
  · apply hB
    have : B = -2 := eq_neg_of_add_eq_zero_left hBtwo
    rw [this]
    norm_num

/-- For `2 ≠ 0`, `A ^ 2 ≠ 4` and `B ^ 2 ≠ 4`, the safe polynomial is nonzero. -/
theorem orderedTraceSafePolynomial_ne_zero
    (A B C : K) (htwo : (2 : K) ≠ 0)
    (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4) :
    orderedTraceSafePolynomial A B C ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero orderedTraceDiscriminantPolynomial_ne_zero
            (X_add_C_ne_zero A))
          (orderedTraceCenteredNormPolynomial_ne_zero B C))
        (orderedTraceWeightDifferencePolynomial_ne_zero A B C hA))
      (orderedTraceEvenMinusPolynomial_ne_zero A B C htwo hA hB))
    (orderedTraceEvenPlusPolynomial_ne_zero A B C htwo hA hB)

/-- The safe polynomial has degree at most ten. -/
theorem orderedTraceSafePolynomial_natDegree_le (A B C : K) :
    (orderedTraceSafePolynomial A B C).natDegree ≤ 10 := by
  rw [orderedTraceSafePolynomial,
    orderedTraceWeightDifferencePolynomial_eq_cubic]
  simp only [orderedTraceDiscriminantPolynomial,
    orderedTraceCenteredNormPolynomial,
    orderedTraceEvenMinusPolynomial,
    orderedTraceEvenPlusPolynomial]
  compute_degree

/-- The safe polynomial has at most ten distinct roots. -/
theorem orderedTraceSafePolynomial_roots_card_le (A B C : K) [DecidableEq K] :
    (orderedTraceSafePolynomial A B C).roots.toFinset.card ≤ 10 := by
  calc
    (orderedTraceSafePolynomial A B C).roots.toFinset.card ≤
        (orderedTraceSafePolynomial A B C).roots.card :=
      Multiset.toFinset_card_le _
    _ ≤ (orderedTraceSafePolynomial A B C).natDegree :=
      Polynomial.card_roots' _
    _ ≤ 10 := orderedTraceSafePolynomial_natDegree_le A B C

end OrderedTracePolynomials

section FiberRouting

variable {K : Type*} [Field K]

/-- The monic quadratic `X ^ 2 + linear * X + constant`.  Above fixed values of
two coordinates, the third coordinate of a surface point is one of its roots. -/
def monicQuadraticPolynomial (linear constant : K) : K[X] :=
  X ^ 2 + Polynomial.C linear * X + Polynomial.C constant

@[simp]
theorem eval_monicQuadraticPolynomial (linear constant z : K) :
    eval z (monicQuadraticPolynomial linear constant) =
      z ^ 2 + linear * z + constant := by
  simp [monicQuadraticPolynomial]

lemma monicQuadraticPolynomial_ne_zero (linear constant : K) :
    monicQuadraticPolynomial linear constant ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (coeff · 2) hzero
  simp only [monicQuadraticPolynomial, coeff_add, coeff_X_pow,
    coeff_C_mul, coeff_X, coeff_C] at hcoeff
  norm_num at hcoeff

lemma monicQuadraticPolynomial_natDegree_le (linear constant : K) :
    (monicQuadraticPolynomial linear constant).natDegree ≤ 2 := by
  rw [monicQuadraticPolynomial]
  compute_degree

/-- A finite family injected into the roots of one monic quadratic has at
most two elements. -/
theorem card_le_two_of_injOn_isRoot
    {T : Type*} [DecidableEq T] [DecidableEq K]
    (S : Finset T) (f : T → K) (linear constant : K)
    (hinj : Set.InjOn f ↑S)
    (hroot : ∀ x ∈ S, IsRoot (monicQuadraticPolynomial linear constant) (f x)) :
    S.card ≤ 2 := by
  let q := monicQuadraticPolynomial linear constant
  have hq : q ≠ 0 := monicQuadraticPolynomial_ne_zero linear constant
  have himage : S.image f ⊆ q.roots.toFinset := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq]
    exact hroot x hx
  calc
    S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ q.roots.toFinset.card := Finset.card_le_card himage
    _ ≤ q.roots.card := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := Polynomial.card_roots' _
    _ ≤ 2 := monicQuadraticPolynomial_natDegree_le linear constant

/-- The affine trace attached to the first coordinate. -/
def coordinateTrace1 (a : Coefficients K) (x : Point K) : K :=
  a.multiplier * x.x1 - a.a1

/-- The affine trace attached to the second coordinate. -/
def coordinateTrace2 (a : Coefficients K) (x : Point K) : K :=
  a.multiplier * x.x2 - a.a2

/-- On a fixed first-coordinate surface fiber, one value of the second
coordinate trace occurs at no more than two points. -/
theorem card_le_two_of_solution_fixed_x1_trace2
    (a : Coefficients K) (S : Finset (Point K)) (u t : K)
    (hmultiplier : a.multiplier ≠ 0)
    (hsolution : ∀ x ∈ S, IsSolution a x)
    (hfixed : ∀ x ∈ S, x.x1 = u)
    (htrace : ∀ x ∈ S, coordinateTrace2 a x = t) :
    S.card ≤ 2 := by
  classical
  let y := (t + a.a2) / a.multiplier
  have hsecond : ∀ x ∈ S, x.x2 = y := by
    intro x hx
    apply (eq_div_iff hmultiplier).2
    have ht := htrace x hx
    rw [coordinateTrace2] at ht
    linear_combination ht
  apply card_le_two_of_injOn_isRoot S Point.x3
    (a.a1 * y + a.a2 * u - a.multiplier * u * y)
    (u ^ 2 + y ^ 2 + a.a3 * u * y)
  · intro x hx z hz heq
    apply Point.ext
    · exact (hfixed x hx).trans (hfixed z hz).symm
    · exact (hsecond x hx).trans (hsecond z hz).symm
    · exact heq
  · intro x hx
    rw [IsRoot, eval_monicQuadraticPolynomial]
    have hsurface := hsolution x hx
    rw [IsSolution, polynomial, hfixed x hx, hsecond x hx] at hsurface
    linear_combination hsurface

/-- If every trace fiber in `S` has at most two elements, no more than twenty
elements of `S` can annihilate the ordered safe polynomial. -/
theorem card_orderedTraceSafePolynomial_zero_le_twenty
    {T : Type*} [DecidableEq T] [DecidableEq K]
    (A B C : K) (S : Finset T) (trace : T → K)
    (htwo : (2 : K) ≠ 0) (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4)
    (hfiber : ∀ t, (S.filter fun x ↦ trace x = t).card ≤ 2) :
    (S.filter fun x ↦
      eval (trace x) (orderedTraceSafePolynomial A B C) = 0).card ≤ 20 := by
  let p := orderedTraceSafePolynomial A B C
  let bad := S.filter fun x ↦ eval (trace x) p = 0
  have hp : p ≠ 0 := orderedTraceSafePolynomial_ne_zero A B C htwo hA hB
  have hbadFiber : ∀ t ∈ bad.image trace,
      (bad.filter fun x ↦ trace x = t).card ≤ 2 := by
    intro t _
    calc
      (bad.filter fun x ↦ trace x = t).card ≤
          (S.filter fun x ↦ trace x = t).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [bad, Finset.mem_filter] at hx ⊢
        exact ⟨hx.1.1, hx.2⟩
      _ ≤ 2 := hfiber t
  have himage : bad.image trace ⊆ p.roots.toFinset := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨x, hx, rfl⟩
    have hzero : eval (trace x) p = 0 := by
      -- Unfold the local `bad` so that `Finset.mem_filter` applies to `hx`.
      change x ∈ S.filter (fun y ↦ eval (trace y) p = 0) at hx
      exact (Finset.mem_filter.mp hx).2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact hzero
  have himageCard : (bad.image trace).card ≤ p.roots.toFinset.card :=
    Finset.card_le_card himage
  have hrootCard : p.roots.toFinset.card ≤ 10 := by
    simpa [p] using orderedTraceSafePolynomial_roots_card_le A B C
  -- Fold the goal into the local abbreviations `p` and `bad` used by the bounds above.
  change bad.card ≤ 20
  calc
    bad.card ≤ 2 * (bad.image trace).card :=
      Finset.card_le_mul_card_image bad 2 hbadFiber
    _ ≤ 2 * p.roots.toFinset.card := Nat.mul_le_mul_left 2 himageCard
    _ ≤ 2 * 10 := Nat.mul_le_mul_left 2 hrootCard
    _ = 20 := by norm_num

end FiberRouting

end

end GenMarkoff
