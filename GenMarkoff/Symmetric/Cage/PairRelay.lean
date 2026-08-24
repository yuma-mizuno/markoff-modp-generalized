import GenMarkoff.Symmetric.Cage.CommonNeighbor

/-!
# Finite relay around the pair-resultant obstruction

The pair obstruction can vanish for two distinct regular split-maximal
traces, so global cage connectivity cannot assume that every pair is directly
admissible.  For a fixed outer trace, however, the obstruction is a nonzero
quadratic in the other trace.  Hence at most two cage labels are bad, and a
five-label cage always contains a relay admissible from both sides.
-/

namespace GenMarkoff.Symmetric.Cage

open BGS.Markoff Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The pair obstruction viewed as a quadratic in its second trace. -/
def incidencePairObstructionPolynomial (c xi : K) : K[X] :=
  let k := -c ^ 3 + 6 * c ^ 2 + 4 * c + 8
  let m := c ^ 2 + 2 * c + 4
  monomial 2 (k + 8 * c * xi) +
    monomial 1 (2 * k * xi + 8 * c * xi ^ 2 +
      4 * c ^ 2 * (c + 2) * xi + 8 * c * m) +
    C (k * xi ^ 2 + 8 * c * m * xi + 16 * c ^ 2 * (c + 2))

@[simp]
theorem eval_incidencePairObstructionPolynomial
    (c xi eta : K) :
    eval eta (incidencePairObstructionPolynomial c xi) =
      incidencePairObstruction c xi eta := by
  simp only [incidencePairObstructionPolynomial, incidencePairObstruction]
  simp
  ring

theorem incidencePairObstructionPolynomial_natDegree_le
    (c xi : K) :
    (incidencePairObstructionPolynomial c xi).natDegree ≤ 2 := by
  simp only [incidencePairObstructionPolynomial]
  compute_degree

/-- Candidate regularity prevents the obstruction quadratic from vanishing
identically. -/
theorem incidencePairObstructionPolynomial_ne_zero
    (c xi : K) (h2 : (2 : K) ≠ 0) (hc : c ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular c c c xi) :
    incidencePairObstructionPolynomial c xi ≠ 0 := by
  let k : K := -c ^ 3 + 6 * c ^ 2 + 4 * c + 8
  let m : K := c ^ 2 + 2 * c + 4
  have hD : xi ^ 2 - 4 ≠ 0 := by
    simpa only [eval_orderedTraceDiscriminantPolynomial] using hregular.1
  intro hpoly
  have hcZero : c ≠ 0 := by
    intro hzero
    subst c
    have hcoeff := congrArg
        (fun q : K[X] => q.coeff 2) hpoly
    have height : (8 : K) ≠ 0 := by
      rw [show (8 : K) = 2 * (2 * 2) by norm_num]
      exact mul_ne_zero h2 (mul_ne_zero h2 h2)
    apply height
    simp only [incidencePairObstructionPolynomial, coeff_add,
      coeff_monomial, coeff_C] at hcoeff
    norm_num at hcoeff
    simpa using hcoeff
  have hcPlus : c + 2 ≠ 0 := by
    intro hzero
    apply hc
    have hc' : c = -2 := by linear_combination hzero
    rw [hc']
    ring
  have ha := congrArg (fun q : K[X] => q.coeff 2) hpoly
  have hb := congrArg (fun q : K[X] => q.coeff 1) hpoly
  have hd := congrArg (fun q : K[X] => q.coeff 0) hpoly
  simp only [incidencePairObstructionPolynomial, coeff_add,
    coeff_monomial, coeff_C] at ha hb hd
  norm_num at ha hb hd
  change k + 8 * c * xi = 0 at ha
  change
    2 * k * xi + 8 * c * xi ^ 2 +
        4 * c ^ 2 * (c + 2) * xi + 8 * c * m =
      0 at hb
  change
    k * xi ^ 2 + 8 * c * m * xi + 16 * c ^ 2 * (c + 2) =
      0 at hd
  have hfour : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have height : (8 : K) ≠ 0 := by
    rw [show (8 : K) = 2 * (2 * 2) by norm_num]
    exact mul_ne_zero h2 (mul_ne_zero h2 h2)
  have hE1raw :
      4 * c *
          (-2 * xi ^ 2 + c * (c + 2) * xi + 2 * m) =
        0 := by
    linear_combination hb - 2 * xi * ha
  have hE1 :
      -2 * xi ^ 2 + c * (c + 2) * xi + 2 * m = 0 :=
    (mul_eq_zero_iff_left (mul_ne_zero hfour hcZero)).mp hE1raw
  have hE2raw :
      8 * c *
          (-xi ^ 3 + m * xi + 2 * c * (c + 2)) =
        0 := by
    linear_combination hd - xi ^ 2 * ha
  have hE2 :
      -xi ^ 3 + m * xi + 2 * c * (c + 2) = 0 :=
    (mul_eq_zero_iff_left (mul_ne_zero height hcZero)).mp hE2raw
  have hfactor :
      c * (c + 2) * (4 - xi ^ 2) = 0 := by
    linear_combination 2 * hE2 - xi * hE1
  have hfourMinus : 4 - xi ^ 2 ≠ 0 := by
    intro hzero
    apply hD
    linear_combination -hzero
  exact (mul_ne_zero (mul_ne_zero hcZero hcPlus) hfourMinus) hfactor

/-- The at-most-two exceptional relay labels for a fixed trace. -/
def incidencePairObstructionBadTraces
    (c xi : K) : Finset K := by
  classical
  exact (incidencePairObstructionPolynomial c xi).roots.toFinset

theorem mem_incidencePairObstructionBadTraces_iff
    (c xi eta : K)
    (hpoly : incidencePairObstructionPolynomial c xi ≠ 0) :
    eta ∈ incidencePairObstructionBadTraces c xi ↔
      incidencePairObstruction c xi eta = 0 := by
  classical
  rw [incidencePairObstructionBadTraces, Multiset.mem_toFinset,
    Polynomial.mem_roots hpoly, Polynomial.IsRoot.def,
    eval_incidencePairObstructionPolynomial]

theorem incidencePairObstructionBadTraces_card_le_two
    (c xi : K) :
    (incidencePairObstructionBadTraces c xi).card ≤ 2 := by
  classical
  calc
    (incidencePairObstructionBadTraces c xi).card ≤
        (incidencePairObstructionPolynomial c xi).roots.card :=
      by
        simpa [incidencePairObstructionBadTraces] using
          Multiset.toFinset_card_le
            (incidencePairObstructionPolynomial c xi).roots
    _ ≤ (incidencePairObstructionPolynomial c xi).natDegree :=
      Polynomial.card_roots' _
    _ ≤ 2 := incidencePairObstructionPolynomial_natDegree_le c xi

/-- All regular split-maximal labels at one prime. -/
def regularSplitMaximalTraceFinset
    (p : ℕ) [Fact p.Prime] (c : ZMod p) : Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun t =>
    IsRegularSplitMaximalTrace p c t

@[simp]
theorem mem_regularSplitMaximalTraceFinset_iff
    {p : ℕ} [Fact p.Prime] {c t : ZMod p} :
    t ∈ regularSplitMaximalTraceFinset p c ↔
      IsRegularSplitMaximalTrace p c t := by
  classical
  simp [regularSplitMaximalTraceFinset]

/-- Five regular split-maximal labels suffice to route around both quadratic
pair-obstruction sets. -/
theorem exists_admissible_regularSplitMaximal_relay
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c xi eta : ZMod p) (hc : c ^ 2 ≠ 4)
    (hxi : IsRegularSplitMaximalTrace p c xi)
    (heta : IsRegularSplitMaximalTrace p c eta)
    (hcard : 4 < (regularSplitMaximalTraceFinset p c).card) :
    ∃ relay : ZMod p,
      IsRegularSplitMaximalTrace p c relay ∧
        IsAdmissibleIncidencePair c xi relay ∧
          IsAdmissibleIncidencePair c relay eta := by
  classical
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)
  let badXi := incidencePairObstructionBadTraces c xi
  let badEta := incidencePairObstructionBadTraces c eta
  have hbadXi : badXi.card ≤ 2 := by
    simpa [badXi] using
      incidencePairObstructionBadTraces_card_le_two c xi
  have hbadEta : badEta.card ≤ 2 := by
    simpa [badEta] using
      incidencePairObstructionBadTraces_card_le_two c eta
  have hunion : (badXi ∪ badEta).card ≤ 4 := by
    calc
      (badXi ∪ badEta).card ≤ badXi.card + badEta.card :=
        Finset.card_union_le _ _
      _ ≤ 2 + 2 := Nat.add_le_add hbadXi hbadEta
      _ = 4 := by norm_num
  have hexists :
      ∃ relay ∈ regularSplitMaximalTraceFinset p c,
        relay ∉ badXi ∪ badEta := by
    by_contra hnone
    have hsubset :
        regularSplitMaximalTraceFinset p c ⊆ badXi ∪ badEta := by
      intro relay hrelay
      by_contra hrelayBad
      apply hnone
      exact ⟨relay, hrelay, hrelayBad⟩
    have hle := Finset.card_le_card hsubset
    omega
  obtain ⟨relay, hrelay, hrelayBad⟩ := hexists
  have hregular :
      IsRegularSplitMaximalTrace p c relay :=
    mem_regularSplitMaximalTraceFinset_iff.mp hrelay
  have hpolyXi :=
    incidencePairObstructionPolynomial_ne_zero
      c xi htwo hc hxi.1
  have hpolyEta :=
    incidencePairObstructionPolynomial_ne_zero
      c eta htwo hc heta.1
  have hobsXi :
      incidencePairObstruction c xi relay ≠ 0 := by
    intro hzero
    apply hrelayBad
    exact Finset.mem_union_left _ <|
      (mem_incidencePairObstructionBadTraces_iff
        c xi relay hpolyXi).2 hzero
  have hobsEta :
      incidencePairObstruction c eta relay ≠ 0 := by
    intro hzero
    apply hrelayBad
    exact Finset.mem_union_right _ <|
      (mem_incidencePairObstructionBadTraces_iff
        c eta relay hpolyEta).2 hzero
  have hobsRelayEta :
      incidencePairObstruction c relay eta ≠ 0 := by
    rw [incidencePairObstruction_comm]
    exact hobsEta
  refine ⟨relay, hregular, ?_, ?_⟩
  · by_cases hEq : xi = relay
    · exact Or.inl hEq
    · exact Or.inr ⟨hEq, hobsXi⟩
  · by_cases hEq : relay = eta
    · exact Or.inl hEq
    · exact Or.inr ⟨hEq, hobsRelayEta⟩

private instance obstructionCounterexamplePrimeThirteen :
    Fact (Nat.Prime 13) :=
  ⟨by norm_num⟩

private def obstructionCounterexampleUnitSix : (ZMod 13)ˣ :=
  Units.mk0 (6 : ZMod 13) (by native_decide)

private def obstructionCounterexampleUnitTwo : (ZMod 13)ˣ :=
  Units.mk0 (2 : ZMod 13) (by native_decide)

private theorem prime_dvd_twelve_eq_two_or_three
    (q : ℕ) (hq : q.Prime) (hqdiv : q ∣ 12) :
    q = 2 ∨ q = 3 := by
  have hqle : q ≤ 12 := Nat.le_of_dvd (by norm_num) hqdiv
  interval_cases q <;> norm_num at *

private theorem obstructionCounterexampleUnitSix_orderOf :
    orderOf obstructionCounterexampleUnitSix = 12 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · native_decide
  · intro q hq hqdiv
    rcases prime_dvd_twelve_eq_two_or_three q hq hqdiv with rfl | rfl <;>
      native_decide

private theorem obstructionCounterexampleUnitTwo_orderOf :
    orderOf obstructionCounterexampleUnitTwo = 12 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · native_decide
  · intro q hq hqdiv
    rcases prime_dvd_twelve_eq_two_or_three q hq hqdiv with rfl | rfl <;>
      native_decide

private theorem natCard_units_zmod_thirteen :
    Nat.card (ZMod 13)ˣ = 12 := by
  rw [Nat.card_units, Nat.card_zmod]

private theorem four_isRegularSplitMaximalTrace_at_thirteen
    : IsRegularSplitMaximalTrace 13 (0 : ZMod 13) 4 := by
  refine ⟨?_, obstructionCounterexampleUnitSix, by native_decide, ?_⟩
  · simp only [OrderedTraceCandidateRegular,
      eval_orderedTraceDiscriminantPolynomial,
      eval_orderedTraceCenteredNormPolynomial,
      eval_orderedTraceWeightDifferencePolynomial,
      eval_orderedTraceEvenMinusPolynomial,
      eval_orderedTraceEvenPlusPolynomial]
    native_decide
  · rw [natCard_units_zmod_thirteen]
    exact obstructionCounterexampleUnitSix_orderOf

private theorem nine_isRegularSplitMaximalTrace_at_thirteen
    : IsRegularSplitMaximalTrace 13 (0 : ZMod 13) 9 := by
  refine ⟨?_, obstructionCounterexampleUnitTwo, by native_decide, ?_⟩
  · simp only [OrderedTraceCandidateRegular,
      eval_orderedTraceDiscriminantPolynomial,
      eval_orderedTraceCenteredNormPolynomial,
      eval_orderedTraceWeightDifferencePolynomial,
      eval_orderedTraceEvenMinusPolynomial,
      eval_orderedTraceEvenPlusPolynomial]
    native_decide
  · rw [natCard_units_zmod_thirteen]
    exact obstructionCounterexampleUnitTwo_orderOf

/-- The former all-pairs admissibility condition is false even in the
ordinary Markoff specialization.  At `p = 13` and `c = 0`, the distinct
regular split-maximal traces `4` and `9` annihilate the pair obstruction. -/
theorem not_allRegularSplitMaximalPairsAdmissible_thirteen_zero
    : ¬ AllRegularSplitMaximalPairsAdmissible 13 (0 : ZMod 13) := by
  intro hall
  rcases hall 4 9
      four_isRegularSplitMaximalTrace_at_thirteen
      nine_isRegularSplitMaximalTrace_at_thirteen with h | h
  · exact (by native_decide : (4 : ZMod 13) ≠ 9) h
  · exact h.2 (by native_decide)

/-- Connectivity through a third regular split-maximal label.  The
five-label hypothesis is exactly what is needed to avoid the two quadratic
bad-label sets, one from each endpoint. -/
theorem sameOneStepComponent_of_cagePair_via_relay_of_explicitInequality
    (coefficient : ℕ)
    (hEstimate : RegularIncidenceWitnessPointEstimate coefficient)
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (c xi eta : ZMod p) (hc : c ^ 2 ≠ 4)
    (hmultiplier : multiplier c ≠ 0)
    (hxi : IsRegularSplitMaximalTrace p c xi)
    (heta : IsRegularSplitMaximalTrace p c eta)
    (hcard : 4 < (regularSplitMaximalTraceFinset p c).card)
    (hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p)
    (axis other : Axis)
    (x y : SolutionSurface (coefficients c))
    (hx : traceAt c axis x.1 = xi)
    (hy : traceAt c other y.1 = eta) :
    SameOneStepComponent c x y := by
  have hpTwo : p ≠ 2 := by omega
  obtain ⟨relay, hrelay, hxiRelay, hrelayEta⟩ :=
    exists_admissible_regularSplitMaximal_relay
      p hpTwo c xi eta hc hxi heta hcard
  obtain ⟨_, _, ⟨bridge⟩⟩ :=
    exists_actual_regularSplitMaximal_bridge_of_explicitInequality
      coefficient hEstimate p hpFive c xi relay hc hmultiplier
        hxi hrelay hxiRelay hexplicit
  have hbridgeRelay :
      traceAt c Axis.first bridge.secondPoint.1 = relay := by
    simpa [traceAt, coordinateAt] using bridge.secondOuterTrace
  have hxBridge :
      SameOneStepComponent c x bridge.secondPoint :=
    sameOneStepComponent_of_cagePair_of_explicitInequality
      coefficient hEstimate p hpFive c xi relay hc hmultiplier
        hxi hrelay hxiRelay hexplicit axis Axis.first
        x bridge.secondPoint hx hbridgeRelay
  have hbridgeY :
      SameOneStepComponent c bridge.secondPoint y :=
    sameOneStepComponent_of_cagePair_of_explicitInequality
      coefficient hEstimate p hpFive c relay eta hc hmultiplier
        hrelay heta hrelayEta hexplicit Axis.first other
        bridge.secondPoint y hbridgeRelay hy
  exact sameOneStepComponent_trans hxBridge hbridgeY

/-- Uniform large-prime connectivity of a five-label regular split cage,
relative only to the explicit generalized incidence estimate.  In
particular, this removes the false all-pairs admissibility hypothesis. -/
theorem exists_threshold_regularSplitCage_connected_via_five_label_relay
    (coefficient : ℕ)
    (hEstimate : RegularIncidenceWitnessPointEstimate coefficient) :
    ∃ threshold : ℕ,
      ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
        ∀ (c : ZMod p),
          c ^ 2 ≠ 4 →
          multiplier c ≠ 0 →
          4 < (regularSplitMaximalTraceFinset p c).card →
          ∀ x y : SolutionSurface (coefficients c),
            IsInRegularSplitCage p c x →
            IsInRegularSplitCage p c y →
            SameOneStepComponent c x y := by
  obtain ⟨threshold, hthreshold⟩ :=
    BGS.Markoff.exists_threshold_endgamePrimitiveTrace_explicitInequality
      coefficient (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨max threshold 5, ?_⟩
  intro p hp _ c hc hmultiplier hcard x y hxCage hyCage
  obtain ⟨axis, hxi⟩ := hxCage
  obtain ⟨other, heta⟩ := hyCage
  let xi := traceAt c axis x.1
  let eta := traceAt c other y.1
  have hpThreshold : threshold ≤ p :=
    (le_max_left threshold 5).trans hp
  have hpOne : 1 ≤ p := by omega
  have hpOneReal : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hpOne
  have honeLe :
      ((1 : ℕ) : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2 - 1 / 4) := by
    simpa using
      (Real.one_le_rpow hpOneReal
        (show (0 : ℝ) ≤ 1 / 2 - 1 / 4 by norm_num))
  have hexplicitThreshold := hthreshold p hpThreshold 1 honeLe
  have hexplicit :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
    have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
      rw [Nat.card_units, Nat.card_zmod]
    rw [hunits]
    simpa only [Nat.cast_one, one_mul] using hexplicitThreshold
  exact
    sameOneStepComponent_of_cagePair_via_relay_of_explicitInequality
      coefficient hEstimate p (by omega) c xi eta hc hmultiplier
        hxi heta hcard hexplicit axis other x y rfl rfl

/-- Full-order elements of the split torus. -/
def primitiveSplitUnits
    (p : ℕ) [Fact p.Prime] : Finset (ZMod p)ˣ := by
  classical
  exact Finset.univ.filter fun q =>
    orderOf q = Nat.card (ZMod p)ˣ

theorem primitiveSplitUnits_card
    (p : ℕ) [Fact p.Prime] :
    (primitiveSplitUnits p).card =
      (Nat.card (ZMod p)ˣ).totient := by
  classical
  rw [primitiveSplitUnits]
  rw [Nat.card_eq_fintype_card]
  exact IsCyclic.card_orderOf_eq_totient dvd_rfl

/-- Trace labels represented by full-order split-torus elements. -/
def primitiveSplitTraceFinset
    (p : ℕ) [Fact p.Prime] : Finset (ZMod p) := by
  classical
  exact (primitiveSplitUnits p).image splitTorusTrace

/-- The map `q ↦ q + q⁻¹` has fibers of cardinality at most two, even after
restriction to the full-order elements. -/
theorem primitiveSplitUnits_trace_fiber_card_le_two
    (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    ((primitiveSplitUnits p).filter fun q =>
      splitTorusTrace q = t).card ≤ 2 := by
  classical
  let fullFiber :=
    Symmetric.MiddleGame.shiftedWeightedTraceValueFiber
      (1 : ZMod p) 1 0 (⊤ : Subgroup (ZMod p)ˣ) t
  have hsubset :
      ((primitiveSplitUnits p).filter fun q =>
          splitTorusTrace q = t).attach.image
            (fun q => (⟨q.1, Subgroup.mem_top q.1⟩ :
              (⊤ : Subgroup (ZMod p)ˣ))) ⊆
        fullFiber := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
    rw [Symmetric.MiddleGame.mem_shiftedWeightedTraceValueFiber_iff]
    simpa only [weightedSplitTorusTrace_one_one, add_zero] using
      (Finset.mem_filter.mp r.2).2
  have hinjective :
      Set.InjOn
        (fun q :
          ↥((primitiveSplitUnits p).filter fun q =>
            splitTorusTrace q = t) =>
          (⟨q.1, Subgroup.mem_top q.1⟩ :
            (⊤ : Subgroup (ZMod p)ˣ)))
        Set.univ := by
    intro a _ b _ hab
    apply Subtype.ext
    exact congrArg
      (fun z : (⊤ : Subgroup (ZMod p)ˣ) => (z : (ZMod p)ˣ)) hab
  calc
    ((primitiveSplitUnits p).filter fun q =>
        splitTorusTrace q = t).card =
        ((primitiveSplitUnits p).filter fun q =>
          splitTorusTrace q = t).attach.card := by
          simp
    _ =
        (((primitiveSplitUnits p).filter fun q =>
          splitTorusTrace q = t).attach.image
            (fun q => (⟨q.1, Subgroup.mem_top q.1⟩ :
              (⊤ : Subgroup (ZMod p)ˣ)))).card := by
          symm
          exact Finset.card_image_iff.mpr
            (hinjective.mono (Set.subset_univ _))
    _ ≤ fullFiber.card := Finset.card_le_card hsubset
    _ ≤ 2 :=
      Symmetric.MiddleGame.shiftedWeightedTraceValueFiber_card_le_two
        (1 : ZMod p) 1 0 (⊤ : Subgroup (ZMod p)ˣ) t one_ne_zero

theorem eleven_lt_primitiveSplitTraceFinset_card
    (p : ℕ) [Fact p.Prime]
    (htotient : 22 < (Nat.card (ZMod p)ˣ).totient) :
    11 < (primitiveSplitTraceFinset p).card := by
  classical
  have hfiber :
      ∀ t ∈ (primitiveSplitUnits p).image splitTorusTrace,
        ((primitiveSplitUnits p).filter fun q =>
          splitTorusTrace q = t).card ≤ 2 := by
    intro t _
    exact primitiveSplitUnits_trace_fiber_card_le_two p t
  have hsource :
      (primitiveSplitUnits p).card ≤
        2 * ((primitiveSplitUnits p).image splitTorusTrace).card :=
    Finset.card_le_mul_card_image (primitiveSplitUnits p) 2 hfiber
  rw [primitiveSplitUnits_card] at hsource
  simpa only [primitiveSplitTraceFinset] using
    (show 11 < ((primitiveSplitUnits p).image splitTorusTrace).card by
      omega)

/-- A totient larger than `22` leaves at least five full-order split trace
labels after deleting the seven roots of the symmetric safe polynomial. -/
theorem four_lt_regularSplitMaximalTraceFinset_card_of_totient
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (hc : c ^ 2 ≠ 4)
    (htotient : 22 < (Nat.card (ZMod p)ˣ).totient) :
    4 < (regularSplitMaximalTraceFinset p c).card := by
  classical
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)
  let traces := primitiveSplitTraceFinset p
  let bad := (Symmetric.safePolynomial c).roots.toFinset
  have htraces : 11 < traces.card := by
    simpa [traces] using
      eleven_lt_primitiveSplitTraceFinset_card p htotient
  have hbad : bad.card ≤ 7 := by
    simpa [bad] using Symmetric.safePolynomial_roots_card_le c
  have hintersection : (bad ∩ traces).card ≤ 7 :=
    (Finset.card_le_card Finset.inter_subset_left).trans hbad
  have hgood : 4 < (traces \ bad).card := by
    rw [Finset.card_sdiff]
    omega
  have hpoly : Symmetric.safePolynomial c ≠ 0 :=
    Symmetric.safePolynomial_ne_zero c htwo hc
  have hsubset :
      traces \ bad ⊆ regularSplitMaximalTraceFinset p c := by
    intro t ht
    have ht' := Finset.mem_sdiff.mp ht
    have htTrace : t ∈ primitiveSplitTraceFinset p := by
      simpa [traces] using ht'.1
    obtain ⟨q, hq, hqt⟩ := Finset.mem_image.mp htTrace
    have hsafe :
        Polynomial.eval t (Symmetric.safePolynomial c) ≠ 0 := by
      intro hzero
      apply ht'.2
      change t ∈ (Symmetric.safePolynomial c).roots.toFinset
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hpoly]
      exact hzero
    rw [mem_regularSplitMaximalTraceFinset_iff]
    refine ⟨Symmetric.candidateRegular_of_eval_safePolynomial_ne_zero
        c t hc hsafe, q, hqt.symm, ?_⟩
    exact (Finset.mem_filter.mp hq).2
  exact hgood.trans_le (Finset.card_le_card hsubset)

/-- Euler's totient eventually exceeds the fixed relay threshold `22`.  The
proof uses only the in-repository subpolynomial divisor bound and
`n ≤ φ(n) τ(n)`. -/
theorem exists_threshold_totient_gt_twentytwo :
    ∃ threshold : ℕ,
      ∀ n : ℕ, threshold ≤ n → 22 < n.totient := by
  obtain ⟨divisorThreshold, hdivisorThreshold⟩ :=
    BGS.NumberTheory.exists_threshold_card_divisors_le_rpow
      (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨max divisorThreshold 485, ?_⟩
  intro n hn
  have hnDivisor : divisorThreshold ≤ n :=
    (le_max_left divisorThreshold 485).trans hn
  have hnPositive : 0 < n := by omega
  have hnLarge : 484 < n := by omega
  have hdivisor := hdivisorThreshold n hnDivisor
  by_contra htotient
  have htotientLe : n.totient ≤ 22 := by omega
  have hnatural :=
    BGS.Markoff.le_totient_mul_card_divisors n hnPositive
  have hnaturalReal :
      (n : ℝ) ≤ (n.totient : ℝ) * (n.divisors.card : ℝ) := by
    exact_mod_cast hnatural
  have htotientReal : (n.totient : ℝ) ≤ 22 := by
    exact_mod_cast htotientLe
  have hbound :
      (n : ℝ) ≤ 22 * Real.sqrt n := by
    calc
      (n : ℝ) ≤ (n.totient : ℝ) * (n.divisors.card : ℝ) :=
        hnaturalReal
      _ ≤ 22 * ((n : ℝ) ^ ((1 : ℝ) / 2)) := by
        exact mul_le_mul htotientReal hdivisor
          (Nat.cast_nonneg _) (by norm_num)
      _ = 22 * Real.sqrt n := by
        rw [Real.sqrt_eq_rpow]
  have hnLargeReal : (484 : ℝ) < n := by
    exact_mod_cast hnLarge
  have hsquare :
      Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hsqrtNonnegative : 0 ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_nonneg _
  nlinarith

/-- For all sufficiently large primes, every allowed symmetric coefficient
has at least five regular split-maximal trace labels. -/
theorem exists_threshold_four_lt_regularSplitMaximalTraceFinset_card :
    ∃ threshold : ℕ,
      ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
        ∀ c : ZMod p, c ^ 2 ≠ 4 →
          4 < (regularSplitMaximalTraceFinset p c).card := by
  obtain ⟨totientThreshold, htotientThreshold⟩ :=
    exists_threshold_totient_gt_twentytwo
  refine ⟨max (totientThreshold + 1) 5, ?_⟩
  intro p hp _ c hc
  have hpFive : 5 ≤ p :=
    (le_max_right (totientThreshold + 1) 5).trans hp
  have hsub : totientThreshold ≤ p - 1 := by
    have := (le_max_left (totientThreshold + 1) 5).trans hp
    omega
  have htotient : 22 < (p - 1).totient :=
    htotientThreshold (p - 1) hsub
  have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  apply four_lt_regularSplitMaximalTraceFinset_card_of_totient
    p (by omega) c hc
  simpa only [hunits] using htotient

/-- Unconditional large-prime connectivity of the whole regular split cage
from the generalized incidence estimate.  The quadratic relay and the
eventual five-label theorem remove the false all-pairs admissibility
condition and the auxiliary cardinality hypothesis. -/
theorem exists_threshold_regularSplitCage_connected_via_relay
    (coefficient : ℕ)
    (hEstimate : RegularIncidenceWitnessPointEstimate coefficient) :
    ∃ threshold : ℕ,
      ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
        ∀ (c : ZMod p),
          c ^ 2 ≠ 4 →
          multiplier c ≠ 0 →
          ∀ x y : SolutionSurface (coefficients c),
            IsInRegularSplitCage p c x →
            IsInRegularSplitCage p c y →
            SameOneStepComponent c x y := by
  obtain ⟨connectivityThreshold, hconnectivity⟩ :=
    exists_threshold_regularSplitCage_connected_via_five_label_relay
      coefficient hEstimate
  obtain ⟨cardinalityThreshold, hcardinality⟩ :=
    exists_threshold_four_lt_regularSplitMaximalTraceFinset_card
  refine ⟨max connectivityThreshold cardinalityThreshold, ?_⟩
  intro p hp _ c hc hmultiplier x y hx hy
  have hpConnectivity : connectivityThreshold ≤ p :=
    (le_max_left connectivityThreshold cardinalityThreshold).trans hp
  have hpCardinality : cardinalityThreshold ≤ p :=
    (le_max_right connectivityThreshold cardinalityThreshold).trans hp
  exact hconnectivity p hpConnectivity c hc hmultiplier
    (hcardinality p hpCardinality c hc) x y hx hy

end

end GenMarkoff.Symmetric.Cage
