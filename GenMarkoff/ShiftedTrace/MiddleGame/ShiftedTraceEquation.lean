import BGS.Markoff.MiddleGame.WeightedTraceEquation

/-!
# The shifted weighted trace equation

On a rotation fiber of a generalized Markoff surface, the trace of a moving
coordinate is `alpha * h + beta * h⁻¹ + gamma` in the torus parameter `h`
(see `GenMarkoff.General.firstTrace_fiberPair`); the affine shift `gamma`
comes from the fiber center and cannot be removed.  This file treats the
coefficient-free shifted trace equation

`alpha * h + beta * h⁻¹ + gamma = k + k⁻¹`

with `h` and `k` in two finite subgroups of `Eˣ`, for arbitrary field
parameters `alpha`, `beta`, `gamma`.  It defines the solution set, its left
support, and the left support over a finite family of right subgroups, and
proves that a prescribed shifted trace has at most two lifts when
`alpha ≠ 0`.  These are the counting inputs of the general middle game and
endgame; the Corvaja--Zannier bound for the solution set is
`weightedShiftedTraceEquationSolutions_card_cast_le_corvajaZannier`.
-/

namespace GenMarkoff.ShiftedTrace.MiddleGame

open BGS.Markoff Polynomial

variable {E : Type*} [Field E] [Fintype E]

/-- Elements of one left subgroup having a prescribed shifted weighted
trace.  Unlike `shiftedWeightedTraceEquationLeftFiber`, the target is an
arbitrary field element and need not already be presented as a split torus
trace. -/
noncomputable def shiftedWeightedTraceValueFiber
    (alpha beta gamma : E) (H1 : Subgroup Eˣ) (target : E) : Finset H1 := by
  classical
  exact Finset.univ.filter fun h1 ↦
    weightedSplitTorusTrace alpha beta h1 + gamma = target

@[simp]
theorem mem_shiftedWeightedTraceValueFiber_iff
    {alpha beta gamma : E} {H1 : Subgroup Eˣ} {target : E} {h1 : H1} :
    h1 ∈ shiftedWeightedTraceValueFiber alpha beta gamma H1 target ↔
      weightedSplitTorusTrace alpha beta h1 + gamma = target := by
  classical
  simp [shiftedWeightedTraceValueFiber]

/-- Possible left subgroup elements above one fixed right trace for the
shifted weighted equation. -/
noncomputable def shiftedWeightedTraceEquationLeftFiber
    (alpha beta gamma : E) (H1 : Subgroup Eˣ) (h2 : Eˣ) : Finset H1 := by
  classical
  exact Finset.univ.filter fun h1 ↦
    weightedSplitTorusTrace alpha beta h1 + gamma = splitTorusTrace h2

/-- Solutions of the shifted weighted trace equation in two finite
subgroups. -/
noncomputable def shiftedWeightedTraceEquationSolutions
    (alpha beta gamma : E) (H1 H2 : Subgroup Eˣ) : Finset (H1 × H2) := by
  classical
  exact Finset.univ.biUnion fun h2 : H2 ↦
    (shiftedWeightedTraceEquationLeftFiber alpha beta gamma H1 h2).image
      fun h1 ↦ (h1, h2)

@[simp]
theorem mem_shiftedWeightedTraceEquationSolutions_iff
    {alpha beta gamma : E} {H1 H2 : Subgroup Eˣ} {h : H1 × H2} :
    h ∈ shiftedWeightedTraceEquationSolutions alpha beta gamma H1 H2 ↔
      weightedSplitTorusTrace alpha beta h.1 + gamma = splitTorusTrace h.2 := by
  classical
  constructor
  · intro hh
    rw [shiftedWeightedTraceEquationSolutions, Finset.mem_biUnion] at hh
    obtain ⟨h2, _, hh⟩ := hh
    obtain ⟨h1, hh1, heq⟩ := Finset.mem_image.mp hh
    have hfirst : h1 = h.1 := congrArg Prod.fst heq
    have hsecond : h2 = h.2 := congrArg Prod.snd heq
    simpa [shiftedWeightedTraceEquationLeftFiber, hfirst, hsecond] using hh1
  · intro hh
    rw [shiftedWeightedTraceEquationSolutions, Finset.mem_biUnion]
    refine ⟨h.2, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr
      ⟨h.1, by simpa [shiftedWeightedTraceEquationLeftFiber] using hh, rfl⟩

omit [Fintype E] in
/-- For `alpha ≠ 0`, the shifted weighted trace equation is equivalent to the
monic twisted-trace equation obtained by dividing by `alpha`. -/
theorem shiftedWeightedSplitTorusTrace_eq_iff_twistedUnitTrace_eq
    (alpha beta gamma trace : E) (h : Eˣ) (halpha : alpha ≠ 0) :
    weightedSplitTorusTrace alpha beta h + gamma = trace ↔
      twistedUnitTrace (beta / alpha) h = (trace - gamma) / alpha := by
  calc
    weightedSplitTorusTrace alpha beta h + gamma = trace ↔
        weightedSplitTorusTrace alpha beta h = trace - gamma := by
      constructor <;> intro heq <;> linear_combination heq
    _ ↔ twistedUnitTrace (beta / alpha) h = (trace - gamma) / alpha :=
      weightedSplitTorusTrace_eq_iff_twistedUnitTrace_eq
        alpha beta (trace - gamma) h halpha

/-- Every prescribed shifted weighted trace has at most two lifts in a
subgroup when the leading weight is nonzero. -/
theorem shiftedWeightedTraceValueFiber_card_le_two
    (alpha beta gamma : E) (H1 : Subgroup Eˣ) (target : E)
    (halpha : alpha ≠ 0) :
    (shiftedWeightedTraceValueFiber
      alpha beta gamma H1 target).card ≤ 2 := by
  classical
  let f := twistedTracePolynomial (beta / alpha)
    ((target - gamma) / alpha)
  have hf : f ≠ 0 :=
    (twistedTracePolynomial_monic (beta / alpha) _).ne_zero
  let rootEmbedding :
      ↥(shiftedWeightedTraceValueFiber alpha beta gamma H1 target) ↪
        ↥f.roots.toFinset :=
    { toFun := fun h1 ↦ ⟨((h1.1 : Eˣ) : E), by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
        apply (eval_twistedTracePolynomial_eq_zero_iff
          (beta / alpha) _ h1.1).2
        apply (shiftedWeightedSplitTorusTrace_eq_iff_twistedUnitTrace_eq
          alpha beta gamma target h1.1 halpha).mp
        simpa only [mem_shiftedWeightedTraceValueFiber_iff] using h1.2⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        apply Units.ext
        exact congrArg Subtype.val hxy }
  have hcard :
      (shiftedWeightedTraceValueFiber alpha beta gamma H1 target).card ≤
        f.roots.toFinset.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective rootEmbedding rootEmbedding.injective
  calc
    (shiftedWeightedTraceValueFiber alpha beta gamma H1 target).card ≤
        f.roots.toFinset.card := hcard
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ = 2 := twistedTracePolynomial_natDegree (beta / alpha) _

/-- Left elements occurring with some right subgroup element. -/
noncomputable def shiftedWeightedTraceEquationLeftSupport
    (alpha beta gamma : E) (H1 H2 : Subgroup Eˣ) : Finset H1 := by
  classical
  exact (shiftedWeightedTraceEquationSolutions alpha beta gamma H1 H2).image Prod.fst

@[simp]
theorem mem_shiftedWeightedTraceEquationLeftSupport_iff
    {alpha beta gamma : E} {H1 H2 : Subgroup Eˣ} {h1 : H1} :
    h1 ∈ shiftedWeightedTraceEquationLeftSupport alpha beta gamma H1 H2 ↔
      ∃ h2 : H2,
        weightedSplitTorusTrace alpha beta h1 + gamma = splitTorusTrace h2 := by
  classical
  simp only [shiftedWeightedTraceEquationLeftSupport, Finset.mem_image]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, mem_shiftedWeightedTraceEquationSolutions_iff.mp hh⟩
  · rintro ⟨h2, heq⟩
    exact ⟨(h1, h2),
      mem_shiftedWeightedTraceEquationSolutions_iff.mpr heq, rfl⟩

/-- Projection to the left coordinate cannot increase the shifted solution
count. -/
theorem shiftedWeightedTraceEquationLeftSupport_card_le_solutions
    (alpha beta gamma : E) (H1 H2 : Subgroup Eˣ) :
    (shiftedWeightedTraceEquationLeftSupport alpha beta gamma H1 H2).card ≤
      (shiftedWeightedTraceEquationSolutions alpha beta gamma H1 H2).card := by
  classical
  exact Finset.card_image_le

/-- Left elements meeting at least one member of a finite family of right
subgroups. -/
noncomputable def shiftedWeightedBadOrderTraceSupport
    (alpha beta gamma : E) (H1 : Subgroup Eˣ) (orders : Finset ℕ)
    (rightSubgroup : ℕ → Subgroup Eˣ) : Finset H1 := by
  classical
  exact orders.biUnion fun d ↦
    shiftedWeightedTraceEquationLeftSupport alpha beta gamma H1 (rightSubgroup d)

@[simp]
theorem mem_shiftedWeightedBadOrderTraceSupport_iff
    {alpha beta gamma : E} {H1 : Subgroup Eˣ} {orders : Finset ℕ}
    {rightSubgroup : ℕ → Subgroup Eˣ} {h1 : H1} :
    h1 ∈ shiftedWeightedBadOrderTraceSupport alpha beta gamma H1 orders rightSubgroup ↔
      ∃ d ∈ orders, ∃ h2 : rightSubgroup d,
        weightedSplitTorusTrace alpha beta h1 + gamma = splitTorusTrace h2 := by
  classical
  simp [shiftedWeightedBadOrderTraceSupport]

end GenMarkoff.ShiftedTrace.MiddleGame
