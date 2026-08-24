import GenMarkoff.Symmetric.OneStepRouting

/-!
# Simultaneous regularity on a symmetric one-step cycle

On a fixed first-coordinate fiber, each prescribed second- or third-coordinate
trace occurs at at most two points.  The degree-seven safe polynomial therefore
excludes at most fourteen points in either adjacent direction.  A cycle with
more than twenty-eight points contains a point regular in both adjacent
directions; if its fixed trace was already regular, all three traces are
regular at that single point.
-/

namespace GenMarkoff.Symmetric.Opening

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Reverse adjacent direction: on a fixed first-coordinate surface fiber,
one value of the third-coordinate trace occurs at no more than two points. -/
theorem card_le_two_of_solution_fixed_x1_trace3
    (a : Coefficients K) (S : Finset (Point K)) (u t : K)
    (hmultiplier : a.multiplier ≠ 0)
    (hsolution : ∀ x ∈ S, IsSolution a x)
    (hfixed : ∀ x ∈ S, x.x1 = u)
    (htrace : ∀ x ∈ S, coordinateTrace3 a x = t) :
    S.card ≤ 2 := by
  classical
  let z := (t + a.a3) / a.multiplier
  have hthird : ∀ x ∈ S, x.x3 = z := by
    intro x hx
    apply (eq_div_iff hmultiplier).2
    have ht := htrace x hx
    rw [coordinateTrace3] at ht
    linear_combination ht
  apply card_le_two_of_injOn_isRoot S Point.x2
    (a.a1 * z + a.a3 * u - a.multiplier * u * z)
    (u ^ 2 + z ^ 2 + a.a2 * u * z)
  · intro x hx y hy heq
    apply Point.ext
    · exact (hfixed x hx).trans (hfixed y hy).symm
    · exact heq
    · exact (hthird x hx).trans (hthird y hy).symm
  · intro x hx
    rw [IsRoot, eval_monicQuadraticPolynomial]
    have hsurface := hsolution x hx
    rw [IsSolution, polynomial, hfixed x hx, hthird x hx] at hsurface
    linear_combination hsurface

/-- More than twenty-eight points on one symmetric fixed-coordinate fiber
contain a point whose two adjacent traces are both candidate regular. -/
theorem exists_axisOneFiber_bothAdjacentCandidateRegular_of_twentyEight_lt_card
    (c : K) (S : Finset (Point K)) (u : K)
    (hmultiplier : (coefficients c).multiplier ≠ 0)
    (htwo : (2 : K) ≠ 0) (hc : c ^ 2 ≠ 4)
    (hsolution : ∀ x ∈ S, IsSolution (coefficients c) x)
    (hfixed : ∀ x ∈ S, x.x1 = u)
    (hcard : 28 < S.card) :
    ∃ x ∈ S,
      OrderedTraceCandidateRegular c c c
          (coordinateTrace2 (coefficients c) x) ∧
        OrderedTraceCandidateRegular c c c
          (coordinateTrace3 (coefficients c) x) := by
  classical
  let bad2 := S.filter fun x ↦
    eval (coordinateTrace2 (coefficients c) x) (safePolynomial c) = 0
  let bad3 := S.filter fun x ↦
    eval (coordinateTrace3 (coefficients c) x) (safePolynomial c) = 0
  have hbad2 : bad2.card ≤ 14 := by
    apply card_safePolynomial_zero_le_fourteen c S
      (coordinateTrace2 (coefficients c)) htwo hc
    intro t
    apply card_le_two_of_solution_fixed_x1_trace2 (coefficients c)
      (S.filter fun x ↦ coordinateTrace2 (coefficients c) x = t)
      u t (by simpa using hmultiplier)
    · intro x hx
      exact hsolution x (Finset.mem_filter.mp hx).1
    · intro x hx
      exact hfixed x (Finset.mem_filter.mp hx).1
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
  have hbad3 : bad3.card ≤ 14 := by
    apply card_safePolynomial_zero_le_fourteen c S
      (coordinateTrace3 (coefficients c)) htwo hc
    intro t
    apply card_le_two_of_solution_fixed_x1_trace3 (coefficients c)
      (S.filter fun x ↦ coordinateTrace3 (coefficients c) x = t)
      u t (by simpa using hmultiplier)
    · intro x hx
      exact hsolution x (Finset.mem_filter.mp hx).1
    · intro x hx
      exact hfixed x (Finset.mem_filter.mp hx).1
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
  by_contra hnone
  have hsubset : S ⊆ bad2 ∪ bad3 := by
    intro x hx
    have hnotBoth :
        ¬(OrderedTraceCandidateRegular c c c
              (coordinateTrace2 (coefficients c) x) ∧
          OrderedTraceCandidateRegular c c c
              (coordinateTrace3 (coefficients c) x)) := by
      intro hboth
      exact hnone ⟨x, hx, hboth⟩
    by_cases hzero2 :
        eval (coordinateTrace2 (coefficients c) x) (safePolynomial c) = 0
    · exact Finset.mem_union_left _ (by
        exact Finset.mem_filter.mpr ⟨hx, hzero2⟩)
    · have hregular2 := candidateRegular_of_eval_safePolynomial_ne_zero c
        (coordinateTrace2 (coefficients c) x) hc hzero2
      have hnotRegular3 :
          ¬ OrderedTraceCandidateRegular c c c
              (coordinateTrace3 (coefficients c) x) := by
        intro hregular3
        exact hnotBoth ⟨hregular2, hregular3⟩
      have hzero3 :
          eval (coordinateTrace3 (coefficients c) x) (safePolynomial c) = 0 := by
        by_contra hne
        exact hnotRegular3
          (candidateRegular_of_eval_safePolynomial_ne_zero c
            (coordinateTrace3 (coefficients c) x) hc hne)
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hzero3⟩)
  have hleUnion : S.card ≤ (bad2 ∪ bad3).card :=
    Finset.card_le_card hsubset
  have hunion : (bad2 ∪ bad3).card ≤ bad2.card + bad3.card :=
    Finset.card_union_le _ _
  omega

variable (p : ℕ) [Fact p.Prime]

/-- If the fixed trace of a sufficiently long first-axis one-step cycle is
already candidate regular, one point on that cycle has all three traces
candidate regular simultaneously. -/
theorem exists_allCandidateRegular_in_oneStep1Cycle
    (c : ZMod p) (x : Point (ZMod p)) (N : ℕ)
    (hmultiplier : multiplier c ≠ 0) (htwo : (2 : ZMod p) ≠ 0)
    (hc : c ^ 2 ≠ 4) (hx : IsSolution (coefficients c) x)
    (hfixedRegular : OrderedTraceCandidateRegular c c c (trace c x.x1))
    (hcard : 28 < (oneStep1Cycle p c x N).card) :
    ∃ y ∈ oneStep1Cycle p c x N,
      OrderedTraceCandidateRegular c c c (trace c y.x1) ∧
        OrderedTraceCandidateRegular c c c (trace c y.x2) ∧
          OrderedTraceCandidateRegular c c c (trace c y.x3) := by
  obtain ⟨y, hy, hregular2, hregular3⟩ :=
    exists_axisOneFiber_bothAdjacentCandidateRegular_of_twentyEight_lt_card
      c (oneStep1Cycle p c x N) x.x1 (by simpa using hmultiplier)
      htwo hc
      (by
        intro z hz
        rw [oneStep1Cycle, Finset.mem_image] at hz
        obtain ⟨n, _hn, rfl⟩ := hz
        exact isSolution_iterate_oneStep1 c hx n)
      (by
        intro z hz
        rw [oneStep1Cycle, Finset.mem_image] at hz
        obtain ⟨n, _hn, rfl⟩ := hz
        exact iterate_oneStep1_x1 c x n)
      hcard
  refine ⟨y, hy, ?_, ?_, ?_⟩
  · have hyFixed : y.x1 = x.x1 := by
      rw [oneStep1Cycle, Finset.mem_image] at hy
      obtain ⟨n, _hn, rfl⟩ := hy
      exact iterate_oneStep1_x1 c x n
    simpa [hyFixed] using hfixedRegular
  · have heq : coordinateTrace2 (coefficients c) y = trace c y.x2 := by
      simp only [coordinateTrace2, coefficients, Coefficients.multiplier,
        trace, multiplier]
      ring
    rw [← heq]
    exact hregular2
  · have heq : coordinateTrace3 (coefficients c) y = trace c y.x3 := by
      simp only [coordinateTrace3, coefficients, Coefficients.multiplier,
        trace, multiplier]
      ring
    rw [← heq]
    exact hregular3

end

end GenMarkoff.Symmetric.Opening
