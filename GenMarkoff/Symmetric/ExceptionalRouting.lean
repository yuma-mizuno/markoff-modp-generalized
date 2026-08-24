import GenMarkoff.Symmetric.TraceParameters

/-!
# Sharper exceptional-fiber routing for equal coefficients

In the symmetric family, one common-even factor is a nonzero constant and the
centered norm and weight-difference polynomials share factors already excluded
by the discriminant.  The reduced safe polynomial therefore has degree at
most seven, giving a fourteen-point routing bound.
-/

namespace GenMarkoff.Symmetric

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The quadratic factor left after removing the redundant `t+2` factor from
the numerator of `sigma-1`. -/
def weightDifferenceQuotientPolynomial (c : K) : K[X] :=
  Polynomial.C (c * (c + 2)) * X ^ 2 +
    Polynomial.C (2 * c ^ 3 + c ^ 2 - 4 * c + 4) * X +
    Polynomial.C (c ^ 4 - 2 * c ^ 2 - 8)

@[simp]
theorem eval_weightDifferenceQuotientPolynomial (c t : K) :
    eval t (weightDifferenceQuotientPolynomial c) =
      c * (c + 2) * t ^ 2 +
        (2 * c ^ 3 + c ^ 2 - 4 * c + 4) * t +
          c ^ 4 - 2 * c ^ 2 - 8 := by
  simp [weightDifferenceQuotientPolynomial]
  ring

/-- Symmetric factorization of the centered norm numerator. -/
theorem eval_orderedTraceCenteredNormPolynomial_symmetric (c t : K) :
    eval t (orderedTraceCenteredNormPolynomial c c) =
      (t + 2) * (t + c ^ 2 - 2) := by
  rw [eval_orderedTraceCenteredNormPolynomial]
  ring

/-- Symmetric factorization of the numerator of `sigma-1`. -/
theorem eval_orderedTraceWeightDifferencePolynomial_symmetric (c t : K) :
    eval t (orderedTraceWeightDifferencePolynomial c c c) =
      (t + 2) * eval t (weightDifferenceQuotientPolynomial c) := by
  rw [eval_orderedTraceWeightDifferencePolynomial,
    eval_weightDifferenceQuotientPolynomial]
  ring

/-- The reduced degree-seven safe polynomial for the symmetric family. -/
def safePolynomial (c : K) : K[X] :=
  orderedTraceDiscriminantPolynomial *
    (X + Polynomial.C c) *
    (X + Polynomial.C (c ^ 2 - 2)) *
    weightDifferenceQuotientPolynomial c *
    orderedTraceEvenPlusPolynomial c c c

@[simp]
theorem eval_safePolynomial (c t : K) :
    eval t (safePolynomial c) =
      (t ^ 2 - 4) * (t + c) * (t + c ^ 2 - 2) *
        eval t (weightDifferenceQuotientPolynomial c) *
          eval t (orderedTraceEvenPlusPolynomial c c c) := by
  simp only [safePolynomial, eval_mul, eval_add, eval_X, eval_C,
    eval_orderedTraceDiscriminantPolynomial]
  ring

lemma weightDifferenceQuotientPolynomial_ne_zero
    (c : K) (htwo : (2 : K) ≠ 0) (hc : c ^ 2 ≠ 4) :
    weightDifferenceQuotientPolynomial c ≠ 0 := by
  intro hzero
  have hlead := congrArg (coeff · 2) hzero
  have hlinear := congrArg (coeff · 1) hzero
  simp only [weightDifferenceQuotientPolynomial, coeff_add, coeff_C_mul,
    coeff_X_pow, coeff_X, coeff_C] at hlead hlinear
  norm_num at hlead hlinear
  rcases hlead with hcZero | hcPlusTwo
  · subst c
    have hfour : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 ^ 2 by norm_num]
      exact pow_ne_zero 2 htwo
    norm_num at hlinear
    exact hfour hlinear
  · have hcEq : c = -2 := eq_neg_of_add_eq_zero_left hcPlusTwo
    apply hc
    rw [hcEq]
    norm_num

theorem safePolynomial_ne_zero
    (c : K) (htwo : (2 : K) ≠ 0) (hc : c ^ 2 ≠ 4) :
    safePolynomial c ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero orderedTraceDiscriminantPolynomial_ne_zero
          (X_add_C_ne_zero c))
        (X_add_C_ne_zero (c ^ 2 - 2)))
      (weightDifferenceQuotientPolynomial_ne_zero c htwo hc))
    (orderedTraceEvenPlusPolynomial_ne_zero c c c htwo hc hc)

theorem safePolynomial_natDegree_le (c : K) :
    (safePolynomial c).natDegree ≤ 7 := by
  rw [safePolynomial]
  simp only [orderedTraceDiscriminantPolynomial,
    weightDifferenceQuotientPolynomial,
    orderedTraceEvenPlusPolynomial]
  compute_degree

theorem safePolynomial_roots_card_le (c : K) [DecidableEq K] :
    (safePolynomial c).roots.toFinset.card ≤ 7 := by
  calc
    (safePolynomial c).roots.toFinset.card ≤
        (safePolynomial c).roots.card := Multiset.toFinset_card_le _
    _ ≤ (safePolynomial c).natDegree := Polynomial.card_roots' _
    _ ≤ 7 := safePolynomial_natDegree_le c

/-- Nonvanishing of the reduced polynomial implies every condition in the
existing ordered candidate-regular predicate. -/
theorem candidateRegular_of_eval_safePolynomial_ne_zero
    (c t : K) (hc : c ^ 2 ≠ 4)
    (hsafe : eval t (safePolynomial c) ≠ 0) :
    OrderedTraceCandidateRegular c c c t := by
  rw [eval_safePolynomial] at hsafe
  rcases mul_ne_zero_iff.mp hsafe with ⟨hprefix, hplus⟩
  rcases mul_ne_zero_iff.mp hprefix with ⟨hprefix, hQ⟩
  rcases mul_ne_zero_iff.mp hprefix with ⟨hprefix, hcenter⟩
  rcases mul_ne_zero_iff.mp hprefix with ⟨hD, htC⟩
  have htNegTwo : t + 2 ≠ 0 := by
    intro ht
    apply hD
    have htEq : t = -2 := eq_neg_of_add_eq_zero_left ht
    rw [htEq]
    norm_num
  refine ⟨?_, htC, ?_, ?_, ?_, hplus⟩
  · simpa using hD
  · rw [eval_orderedTraceCenteredNormPolynomial_symmetric]
    exact mul_ne_zero htNegTwo hcenter
  · rw [eval_orderedTraceWeightDifferencePolynomial_symmetric]
    exact mul_ne_zero htNegTwo hQ
  · exact eval_orderedTraceEvenMinusPolynomial_symmetric_ne_zero c t hc

/-- At most fourteen points in a family with trace fibers of size at most two
can annihilate the reduced safe polynomial. -/
theorem card_safePolynomial_zero_le_fourteen
    {T : Type*} [DecidableEq T] [DecidableEq K]
    (c : K) (S : Finset T) (traceValue : T → K)
    (htwo : (2 : K) ≠ 0) (hc : c ^ 2 ≠ 4)
    (hfiber : ∀ t, (S.filter fun x ↦ traceValue x = t).card ≤ 2) :
    (S.filter fun x ↦ eval (traceValue x) (safePolynomial c) = 0).card ≤ 14 := by
  let p := safePolynomial c
  let bad := S.filter fun x ↦ eval (traceValue x) p = 0
  have hp : p ≠ 0 := safePolynomial_ne_zero c htwo hc
  have hbadFiber : ∀ t ∈ bad.image traceValue,
      (bad.filter fun x ↦ traceValue x = t).card ≤ 2 := by
    intro t _
    calc
      (bad.filter fun x ↦ traceValue x = t).card ≤
          (S.filter fun x ↦ traceValue x = t).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [bad, Finset.mem_filter] at hx ⊢
        exact ⟨hx.1.1, hx.2⟩
      _ ≤ 2 := hfiber t
  have himage : bad.image traceValue ⊆ p.roots.toFinset := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨x, hx, rfl⟩
    have hzero : eval (traceValue x) p = 0 := by
      change x ∈ S.filter (fun y ↦ eval (traceValue y) p = 0) at hx
      exact (Finset.mem_filter.mp hx).2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact hzero
  have himageCard : (bad.image traceValue).card ≤ p.roots.toFinset.card :=
    Finset.card_le_card himage
  have hrootCard : p.roots.toFinset.card ≤ 7 := by
    simpa [p] using safePolynomial_roots_card_le c
  change bad.card ≤ 14
  calc
    bad.card ≤ 2 * (bad.image traceValue).card :=
      Finset.card_le_mul_card_image bad 2 hbadFiber
    _ ≤ 2 * p.roots.toFinset.card := Nat.mul_le_mul_left 2 himageCard
    _ ≤ 2 * 7 := Nat.mul_le_mul_left 2 hrootCard
    _ = 14 := by norm_num

/-- Abstract fourteen-point escape to a candidate-regular trace. -/
theorem exists_candidateRegular_of_fourteen_lt_card
    {T : Type*} [DecidableEq T] [DecidableEq K]
    (c : K) (S : Finset T) (traceValue : T → K)
    (htwo : (2 : K) ≠ 0) (hc : c ^ 2 ≠ 4)
    (hfiber : ∀ t, (S.filter fun x ↦ traceValue x = t).card ≤ 2)
    (hcard : 14 < S.card) :
    ∃ x ∈ S, OrderedTraceCandidateRegular c c c (traceValue x) := by
  by_contra hnone
  push Not at hnone
  have hsubset : S ⊆ S.filter (fun x ↦
      eval (traceValue x) (safePolynomial c) = 0) := by
    intro x hx
    rw [Finset.mem_filter]
    refine ⟨hx, ?_⟩
    by_contra hne
    exact hnone x hx (candidateRegular_of_eval_safePolynomial_ne_zero c
      (traceValue x) hc hne)
  have hbad := card_safePolynomial_zero_le_fourteen
    c S traceValue htwo hc hfiber
  have hle := Finset.card_le_card hsubset
  omega

/-- First cyclic symmetric routing theorem. -/
theorem exists_axisOneFiber_axisTwoCandidateRegular_of_fourteen_lt_card
    (c : K) (S : Finset (Point K)) (u : K)
    (hmultiplier : (coefficients c).multiplier ≠ 0)
    (htwo : (2 : K) ≠ 0) (hc : c ^ 2 ≠ 4)
    (hsolution : ∀ x ∈ S, IsSolution (coefficients c) x)
    (hfixed : ∀ x ∈ S, x.x1 = u)
    (hcard : 14 < S.card) :
    ∃ x ∈ S, OrderedTraceCandidateRegular c c c
      (coordinateTrace2 (coefficients c) x) := by
  classical
  refine exists_candidateRegular_of_fourteen_lt_card c S
    (coordinateTrace2 (coefficients c)) htwo hc ?_ hcard
  intro t
  apply card_le_two_of_solution_fixed_x1_trace2 (coefficients c)
    (S.filter fun x ↦ coordinateTrace2 (coefficients c) x = t)
    u t hmultiplier
  · intro x hx
    exact hsolution x (Finset.mem_filter.mp hx).1
  · intro x hx
    exact hfixed x (Finset.mem_filter.mp hx).1
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

/-- Second cyclic symmetric routing theorem. -/
theorem exists_axisTwoFiber_axisThreeCandidateRegular_of_fourteen_lt_card
    (c : K) (S : Finset (Point K)) (u : K)
    (hmultiplier : (coefficients c).multiplier ≠ 0)
    (htwo : (2 : K) ≠ 0) (hc : c ^ 2 ≠ 4)
    (hsolution : ∀ x ∈ S, IsSolution (coefficients c) x)
    (hfixed : ∀ x ∈ S, x.x2 = u)
    (hcard : 14 < S.card) :
    ∃ x ∈ S, OrderedTraceCandidateRegular c c c
      (coordinateTrace3 (coefficients c) x) := by
  classical
  refine exists_candidateRegular_of_fourteen_lt_card c S
    (coordinateTrace3 (coefficients c)) htwo hc ?_ hcard
  intro t
  apply card_le_two_of_solution_fixed_x2_trace3 (coefficients c)
    (S.filter fun x ↦ coordinateTrace3 (coefficients c) x = t)
    u t hmultiplier
  · intro x hx
    exact hsolution x (Finset.mem_filter.mp hx).1
  · intro x hx
    exact hfixed x (Finset.mem_filter.mp hx).1
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

/-- Third cyclic symmetric routing theorem. -/
theorem exists_axisThreeFiber_axisOneCandidateRegular_of_fourteen_lt_card
    (c : K) (S : Finset (Point K)) (u : K)
    (hmultiplier : (coefficients c).multiplier ≠ 0)
    (htwo : (2 : K) ≠ 0) (hc : c ^ 2 ≠ 4)
    (hsolution : ∀ x ∈ S, IsSolution (coefficients c) x)
    (hfixed : ∀ x ∈ S, x.x3 = u)
    (hcard : 14 < S.card) :
    ∃ x ∈ S, OrderedTraceCandidateRegular c c c
      (coordinateTrace1 (coefficients c) x) := by
  classical
  refine exists_candidateRegular_of_fourteen_lt_card c S
    (coordinateTrace1 (coefficients c)) htwo hc ?_ hcard
  intro t
  apply card_le_two_of_solution_fixed_x3_trace1 (coefficients c)
    (S.filter fun x ↦ coordinateTrace1 (coefficients c) x = t)
    u t hmultiplier
  · intro x hx
    exact hsolution x (Finset.mem_filter.mp hx).1
  · intro x hx
    exact hfixed x (Finset.mem_filter.mp hx).1
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

end

end GenMarkoff.Symmetric
