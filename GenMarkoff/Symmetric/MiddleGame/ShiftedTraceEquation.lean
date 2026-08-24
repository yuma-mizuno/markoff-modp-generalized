import BGS.Markoff.MiddleGame.WeightedTraceEquation

/-!
# The shifted weighted trace equation

For an equal-coefficient generalized Markoff fiber, diagonalizing the one-step
affine map produces adjacent traces of the form

`alpha * h + beta * h⁻¹ + gamma`.

The constant `gamma` is part of the geometry and cannot be dropped.  This
module supplies the finite counting and pigeonhole layer for that shifted
equation.  The Corvaja--Zannier estimate for its curve is deliberately left as
an explicit later input.
-/

namespace GenMarkoff.Symmetric.MiddleGame

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
/-- Dividing by the nonzero leading weight converts the shifted equation to
the existing monic twisted-trace equation. -/
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

/-- A fixed right trace has at most two lifts when the leading weight is
nonzero. -/
theorem shiftedWeightedTraceEquationLeftFiber_card_le_two
    (alpha beta gamma : E) (H1 : Subgroup Eˣ) (h2 : Eˣ)
    (halpha : alpha ≠ 0) :
    (shiftedWeightedTraceEquationLeftFiber alpha beta gamma H1 h2).card ≤ 2 := by
  classical
  let f := twistedTracePolynomial (beta / alpha)
    ((splitTorusTrace h2 - gamma) / alpha)
  have hf : f ≠ 0 :=
    (twistedTracePolynomial_monic (beta / alpha) _).ne_zero
  let rootEmbedding :
      ↥(shiftedWeightedTraceEquationLeftFiber alpha beta gamma H1 h2) ↪
        ↥f.roots.toFinset :=
    { toFun := fun h1 ↦ ⟨((h1.1 : Eˣ) : E), by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
        apply (eval_twistedTracePolynomial_eq_zero_iff
          (beta / alpha) _ h1.1).2
        apply (shiftedWeightedSplitTorusTrace_eq_iff_twistedUnitTrace_eq
          alpha beta gamma (splitTorusTrace h2) h1.1 halpha).mp
        simpa only [shiftedWeightedTraceEquationLeftFiber, Finset.mem_filter,
          Finset.mem_univ, true_and] using h1.2⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        apply Units.ext
        exact congrArg Subtype.val hxy }
  have hcard :
      (shiftedWeightedTraceEquationLeftFiber alpha beta gamma H1 h2).card ≤
        f.roots.toFinset.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective rootEmbedding rootEmbedding.injective
  calc
    (shiftedWeightedTraceEquationLeftFiber alpha beta gamma H1 h2).card ≤
        f.roots.toFinset.card := hcard
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ = 2 := twistedTracePolynomial_natDegree (beta / alpha) _

/-- The elementary shifted estimate: each right subgroup element has at most
two lifts. -/
theorem shiftedWeightedTraceEquationSolutions_card_le_two_mul_right
    (alpha beta gamma : E) (H1 H2 : Subgroup Eˣ) (halpha : alpha ≠ 0) :
    (shiftedWeightedTraceEquationSolutions alpha beta gamma H1 H2).card ≤
      2 * Nat.card H2 := by
  classical
  unfold shiftedWeightedTraceEquationSolutions
  calc
    (Finset.univ.biUnion fun h2 : H2 ↦
        (shiftedWeightedTraceEquationLeftFiber alpha beta gamma H1 h2).image
          fun h1 ↦ (h1, h2)).card ≤ Finset.univ.card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro h2 _
      exact Finset.card_image_le.trans
        (shiftedWeightedTraceEquationLeftFiber_card_le_two
          alpha beta gamma H1 h2 halpha)
    _ = 2 * Nat.card H2 := by
      rw [Finset.card_univ, Fintype.card_eq_nat_card]
      omega

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

/-- A uniform solution bound gives the finite-union bound used in the shifted
middle-game pigeonhole argument. -/
theorem shiftedWeightedBadOrderTraceSupport_card_le
    (alpha beta gamma : E) (H1 : Subgroup Eˣ) (orders : Finset ℕ)
    (rightSubgroup : ℕ → Subgroup Eˣ) (bound : ℕ)
    (hbound : ∀ d ∈ orders,
      (shiftedWeightedTraceEquationSolutions alpha beta gamma H1
        (rightSubgroup d)).card ≤ bound) :
    (shiftedWeightedBadOrderTraceSupport alpha beta gamma H1 orders
      rightSubgroup).card ≤ orders.card * bound := by
  classical
  unfold shiftedWeightedBadOrderTraceSupport
  apply Finset.card_biUnion_le_card_mul
  intro d hd
  exact (shiftedWeightedTraceEquationLeftSupport_card_le_solutions
    alpha beta gamma H1 (rightSubgroup d)).trans (hbound d hd)

/-- If the shifted bad set is smaller than the current subgroup, one current
parameter avoids every candidate right-order trace. -/
theorem exists_left_element_escaping_shiftedWeightedCandidateOrders
    (alpha beta gamma : E) (H1 : Subgroup Eˣ) (orders : Finset ℕ)
    (rightSubgroup : ℕ → Subgroup Eˣ) (bound : ℕ)
    (hbound : ∀ d ∈ orders,
      (shiftedWeightedTraceEquationSolutions alpha beta gamma H1
        (rightSubgroup d)).card ≤ bound)
    (hsmall : orders.card * bound < Nat.card H1) :
    ∃ h1 : H1, ∀ d ∈ orders, ∀ h2 : rightSubgroup d,
      weightedSplitTorusTrace alpha beta h1 + gamma ≠ splitTorusTrace h2 := by
  classical
  let bad := shiftedWeightedBadOrderTraceSupport
    alpha beta gamma H1 orders rightSubgroup
  have hbad : bad.card < Nat.card H1 :=
    (shiftedWeightedBadOrderTraceSupport_card_le
      alpha beta gamma H1 orders rightSubgroup bound hbound).trans_lt hsmall
  have hexists : ∃ h1 : H1, h1 ∉ bad := by
    by_contra hall
    push Not at hall
    have hle : (Finset.univ : Finset H1).card ≤ bad.card :=
      Finset.card_le_card fun h1 _ ↦ hall h1
    rw [Finset.card_univ, Fintype.card_eq_nat_card] at hle
    exact (Nat.not_le_of_lt hbad) hle
  obtain ⟨h1, hh1⟩ := hexists
  refine ⟨h1, ?_⟩
  intro d hd h2 heq
  apply hh1
  exact mem_shiftedWeightedBadOrderTraceSupport_iff.mpr
    ⟨d, hd, h2, heq⟩

end GenMarkoff.Symmetric.MiddleGame
