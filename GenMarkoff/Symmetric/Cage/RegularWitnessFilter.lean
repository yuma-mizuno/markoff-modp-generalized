import GenMarkoff.Symmetric.Cage.CommonNeighbor

/-!
# Removing candidate-irregular incidence witnesses

The plane model naturally counts every pair of incidence square roots.  The
one-step cage uses only witnesses whose common middle trace is candidate
regular.  This module proves that passing from the raw count to the regular
count costs at most fifty-six points:

* the symmetric safe polynomial has at most seven roots;
* above a fixed middle trace the two incidence roots give at most four
  witnesses;
* the split-torus trace has fibers of cardinality at most two.

Thus an unfiltered Hasse--Weil estimate implies the exact filtered estimate
used by `CommonNeighbor`, after increasing its coefficient by `56`.
-/

namespace GenMarkoff.Symmetric.Cage

open Polynomial BGS.Markoff

noncomputable section

noncomputable instance incidenceEquationWitness_finite
    {K : Type*} [Field K] [Finite K] (c xi eta : K) :
    Finite (IncidenceEquationWitness c xi eta) :=
  Finite.of_injective
    (fun w : IncidenceEquationWitness c xi eta =>
      (w.middle, w.firstRoot, w.secondRoot))
    (by
      intro a b hab
      cases a
      cases b
      simp_all)

/-- The middle trace of an unfiltered incidence witness. -/
def incidenceWitnessTrace
    {K : Type*} [Field K] {c xi eta : K}
    (w : IncidenceEquationWitness c xi eta) : K :=
  w.middle

/-- Raw witness-bearing solutions with the right unit restricted to a
power-map range. -/
abbrev rawIncidenceWitnessPowerRangeSolutions
    (p : ℕ) [Fact p.Prime] (c xi eta : ZMod p) (d : ℕ) :=
  BGS.rightPowerTraceRangeSolutions
    (incidenceWitnessTrace
      (c := c) (xi := xi) (eta := eta))
    (splitTorusTrace : (ZMod p)ˣ → ZMod p) d

/-- The direct unfiltered point-count interface supplied by the incidence
plane model. -/
def RawIncidenceWitnessPointEstimate (coefficient : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
    ∀ (c xi eta : ZMod p),
      c ^ 2 ≠ 4 →
      IsRegularSplitMaximalTrace p c xi →
      IsRegularSplitMaximalTrace p c eta →
      IsAdmissibleIncidencePair c xi eta →
      ∃ multiplicity : ℕ, 0 < multiplicity ∧
        ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
          |(Nat.card (rawIncidenceWitnessPowerRangeSolutions
              p c xi eta d) : ℝ) -
                (multiplicity : ℝ) * (p : ℝ) / d| ≤
            (coefficient : ℝ) * Real.sqrt (p : ℝ)

/-- A scalar in a finite field has at most two square roots. -/
theorem natCard_squareRootFiber_le_two
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] (a : K) :
    Nat.card {x : K // x ^ 2 = a} ≤ 2 := by
  let f : K[X] := X ^ 2 - C a
  have hf : f ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun q : K[X] => q.coeff 2) hzero
    simp [f] at hcoeff
  let rootEmbedding : {x : K // x ^ 2 = a} ↪ f.roots.toFinset :=
    { toFun := fun x => ⟨x, by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
        simpa [f, sub_eq_zero] using x.2⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg
          (fun z : f.roots.toFinset => (z : K)) h }
  calc
    Nat.card {x : K // x ^ 2 = a} ≤ Nat.card ↥f.roots.toFinset := by
      exact Nat.card_le_card_of_injective
        rootEmbedding.toFun rootEmbedding.injective
    _ = f.roots.toFinset.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ = 2 := by simp [f]

/-- For a fixed middle trace there are at most four unfiltered incidence
witnesses, from the two choices for each square root. -/
theorem natCard_incidenceEquationWitness_fixed_middle_le_four
    (p : ℕ) [Fact p.Prime] (c xi eta t : ZMod p) :
    Nat.card
        {w : IncidenceEquationWitness c xi eta // w.middle = t} ≤ 4 := by
  let rootPair :
      {w : IncidenceEquationWitness c xi eta // w.middle = t} →
        {r : ZMod p // r ^ 2 = incidenceDiscriminant c xi t} ×
          {r : ZMod p // r ^ 2 = incidenceDiscriminant c eta t} :=
    fun w =>
      (⟨w.1.firstRoot, by
          exact w.1.firstEquation.trans
            (congrArg (incidenceDiscriminant c xi) w.2)⟩,
        ⟨w.1.secondRoot, by
          exact w.1.secondEquation.trans
            (congrArg (incidenceDiscriminant c eta) w.2)⟩)
  have hinjective : Function.Injective rootPair := by
    intro a b hab
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    apply Subtype.ext
    have hmiddle : a.middle = b.middle :=
      ha.trans hb.symm
    have hfirst : a.firstRoot = b.firstRoot :=
      congrArg (fun q => (q.1.1 : ZMod p)) hab
    have hsecond : a.secondRoot = b.secondRoot :=
      congrArg (fun q => (q.2.1 : ZMod p)) hab
    cases a
    cases b
    rw [IncidenceEquationWitness.mk.injEq]
    exact ⟨hmiddle, hfirst, hsecond⟩
  have hcard := Nat.card_le_card_of_injective rootPair hinjective
  rw [Nat.card_prod] at hcard
  have hfirst :
      Nat.card {r : ZMod p //
        r ^ 2 = incidenceDiscriminant c xi t} ≤ 2 :=
    natCard_squareRootFiber_le_two _
  have hsecond :
      Nat.card {r : ZMod p //
        r ^ 2 = incidenceDiscriminant c eta t} ≤ 2 :=
    natCard_squareRootFiber_le_two _
  exact hcard.trans <|
    (Nat.mul_le_mul hfirst hsecond).trans (by norm_num)

/-- Restricting the split-torus trace to any subgroup still leaves fibers
of cardinality at most two. -/
theorem natCard_subgroup_splitTorusTrace_fiber_le_two
    (p : ℕ) [Fact p.Prime] (H : Subgroup (ZMod p)ˣ) (t : ZMod p) :
    Nat.card {u : H // splitTorusTrace u = t} ≤ 2 := by
  classical
  let fiber :=
    MiddleGame.shiftedWeightedTraceValueFiber
      (1 : ZMod p) 1 0 H t
  let embedding : {u : H // splitTorusTrace u = t} ↪ ↥fiber :=
    { toFun := fun u => ⟨u.1, by
        rw [MiddleGame.mem_shiftedWeightedTraceValueFiber_iff]
        simpa only [weightedSplitTorusTrace_one_one, add_zero] using u.2⟩
      inj' := by
        intro u v huv
        apply Subtype.ext
        exact congrArg (fun z : ↥fiber => z.1) huv }
  calc
    Nat.card {u : H // splitTorusTrace u = t} ≤ Nat.card ↥fiber :=
      Nat.card_le_card_of_injective embedding.toFun embedding.injective
    _ = fiber.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 2 :=
      MiddleGame.shiftedWeightedTraceValueFiber_card_le_two
        (1 : ZMod p) 1 0 H t one_ne_zero

/-- A fixed middle trace supports at most eight raw power-range solutions:
four root pairs and at most two right units. -/
theorem natCard_rawIncidenceWitnessPowerRange_fixed_middle_le_eight
    (p : ℕ) [Fact p.Prime] (c xi eta : ZMod p) (d : ℕ)
    (t : ZMod p) :
    Nat.card
        {z : rawIncidenceWitnessPowerRangeSolutions p c xi eta d //
          z.1.1.middle = t} ≤ 8 := by
  let H : Subgroup (ZMod p)ˣ :=
    (powMonoidHom d : (ZMod p)ˣ →* (ZMod p)ˣ).range
  let target :=
    {w : IncidenceEquationWitness c xi eta // w.middle = t} ×
      {u : H // splitTorusTrace u = t}
  let embedding :
      {z : rawIncidenceWitnessPowerRangeSolutions p c xi eta d //
        z.1.1.middle = t} ↪ target :=
    { toFun := fun z =>
        (⟨z.1.1.1, z.2⟩,
          ⟨z.1.1.2, z.1.2.symm.trans z.2⟩)
      inj' := by
        intro z w hzw
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · exact congrArg
            (fun q : target =>
              (q.1.1 : IncidenceEquationWitness c xi eta)) hzw
        · exact congrArg (fun q : target => (q.2.1 : H)) hzw }
  have hcard := Nat.card_le_card_of_injective
    embedding.toFun embedding.injective
  change Nat.card _ ≤ Nat.card target at hcard
  rw [Nat.card_prod] at hcard
  have hwitness :=
    natCard_incidenceEquationWitness_fixed_middle_le_four
      p c xi eta t
  have hunit := natCard_subgroup_splitTorusTrace_fiber_le_two p H t
  exact hcard.trans <|
    (Nat.mul_le_mul hwitness hunit).trans (by norm_num)

/-- Forgetting candidate regularity identifies a regular range solution
with a raw solution carrying a proof that its middle trace is regular. -/
def regularPowerRangeEquivRegularRaw
    (p : ℕ) [Fact p.Prime] (c xi eta : ZMod p) (d : ℕ) :
    regularIncidenceWitnessPowerRangeSolutions p c xi eta d ≃
      {z : rawIncidenceWitnessPowerRangeSolutions p c xi eta d //
        OrderedTraceCandidateRegular c c c z.1.1.middle} where
  toFun z :=
    ⟨⟨(z.1.1.1, z.1.2), z.2⟩, z.1.1.2⟩
  invFun z :=
    ⟨(⟨z.1.1.1, z.2⟩, z.1.1.2), z.1.2⟩
  left_inv z := by rfl
  right_inv z := by rfl

/-- At most fifty-six raw power-range solutions have candidate-irregular
middle trace. -/
theorem natCard_irregular_rawIncidenceWitnessPowerRange_le_fiftySix
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (c xi eta : ZMod p) (hc : c ^ 2 ≠ 4) (d : ℕ) :
    Nat.card
        {z : rawIncidenceWitnessPowerRangeSolutions p c xi eta d //
          ¬ OrderedTraceCandidateRegular c c c z.1.1.middle} ≤ 56 := by
  classical
  let Raw := rawIncidenceWitnessPowerRangeSolutions p c xi eta d
  let H : Subgroup (ZMod p)ˣ :=
    (powMonoidHom d : (ZMod p)ˣ →* (ZMod p)ˣ).range
  letI : Finite H :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite Raw := by
    exact Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype Raw := Fintype.ofFinite Raw
  let bad : Finset Raw :=
    Finset.univ.filter fun z =>
      ¬ OrderedTraceCandidateRegular c c c z.1.1.middle
  let traceValue : Raw → ZMod p := fun z => z.1.1.middle
  let badType :=
    {z : rawIncidenceWitnessPowerRangeSolutions p c xi eta d //
      ¬ OrderedTraceCandidateRegular c c c z.1.1.middle}
  have hbadCard : Nat.card badType = bad.card := by
    let e : badType ≃ ↥bad :=
      { toFun := fun z => ⟨z.1, by
          simp [bad, z.2]⟩
        invFun := fun z => ⟨z.1, by
          simpa [bad] using (Finset.mem_filter.mp z.2).2⟩
        left_inv := fun z => rfl
        right_inv := fun z => rfl }
    exact (Nat.card_congr e).trans (by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe])
  have hfiber :
      ∀ t, (bad.filter fun z => traceValue z = t).card ≤ 8 := by
    intro t
    let source := ↥(bad.filter fun z => traceValue z = t)
    let target :=
      {z : rawIncidenceWitnessPowerRangeSolutions p c xi eta d //
        z.1.1.middle = t}
    let embedding : source ↪ target :=
      { toFun := fun z => ⟨z.1, by
          exact (Finset.mem_filter.mp z.2).2⟩
        inj' := by
          intro z w hzw
          apply Subtype.ext
          exact congrArg (fun q : target => (q.1 : Raw)) hzw }
    calc
      (bad.filter fun z => traceValue z = t).card =
          Nat.card source := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ Nat.card target :=
        Nat.card_le_card_of_injective embedding.toFun embedding.injective
      _ ≤ 8 :=
        natCard_rawIncidenceWitnessPowerRange_fixed_middle_le_eight
          p c xi eta d t
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hsafe : safePolynomial c ≠ 0 :=
    safePolynomial_ne_zero c htwo hc
  have himage :
      bad.image traceValue ⊆ (safePolynomial c).roots.toFinset := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨z, hz, rfl⟩
    have hirregular :
        ¬ OrderedTraceCandidateRegular c c c z.1.1.middle :=
      (Finset.mem_filter.mp hz).2
    have hzero : eval z.1.1.middle (safePolynomial c) = 0 := by
      by_contra hne
      exact hirregular
        (candidateRegular_of_eval_safePolynomial_ne_zero
          c z.1.1.middle hc hne)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hsafe]
    exact hzero
  have himageCard :
      (bad.image traceValue).card ≤ (safePolynomial c).roots.toFinset.card :=
    Finset.card_le_card himage
  have hroots : (safePolynomial c).roots.toFinset.card ≤ 7 :=
    safePolynomial_roots_card_le c
  rw [hbadCard]
  calc
    bad.card ≤ 8 * (bad.image traceValue).card :=
      Finset.card_le_mul_card_image bad 8
        (fun t _ => hfiber t)
    _ ≤ 8 * (safePolynomial c).roots.toFinset.card :=
      Nat.mul_le_mul_left 8 himageCard
    _ ≤ 8 * 7 := Nat.mul_le_mul_left 8 hroots
    _ = 56 := by norm_num

/-- The raw range count is the regular range count plus its
candidate-irregular complement. -/
theorem natCard_raw_eq_regular_add_irregular
    (p : ℕ) [Fact p.Prime] (c xi eta : ZMod p) (d : ℕ) :
    Nat.card (rawIncidenceWitnessPowerRangeSolutions p c xi eta d) =
      Nat.card (regularIncidenceWitnessPowerRangeSolutions p c xi eta d) +
        Nat.card
          {z : rawIncidenceWitnessPowerRangeSolutions p c xi eta d //
            ¬ OrderedTraceCandidateRegular c c c z.1.1.middle} := by
  classical
  let Raw := rawIncidenceWitnessPowerRangeSolutions p c xi eta d
  let H : Subgroup (ZMod p)ˣ :=
    (powMonoidHom d : (ZMod p)ˣ →* (ZMod p)ˣ).range
  letI : Finite H :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite Raw :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let regular : Raw → Prop :=
    fun z => OrderedTraceCandidateRegular c c c z.1.1.middle
  calc
    Nat.card Raw =
        Nat.card ({z : Raw // regular z} ⊕ {z : Raw // ¬ regular z}) :=
      Nat.card_congr (Equiv.sumCompl regular).symm
    _ = Nat.card {z : Raw // regular z} +
        Nat.card {z : Raw // ¬ regular z} := Nat.card_sum
    _ = Nat.card
          (regularIncidenceWitnessPowerRangeSolutions p c xi eta d) +
        Nat.card {z : Raw // ¬ regular z} := by
      rw [Nat.card_congr
        (regularPowerRangeEquivRegularRaw p c xi eta d)]
    _ = _ := rfl

/-- Increasing the raw coefficient by `56` absorbs every deleted
candidate-irregular witness uniformly. -/
theorem regularIncidenceWitnessPointEstimate_of_raw
    (coefficient : ℕ)
    (hRaw : RawIncidenceWitnessPointEstimate coefficient) :
    RegularIncidenceWitnessPointEstimate (coefficient + 56) := by
  intro p _ hpFive c xi eta hc hxi heta hpair
  obtain ⟨multiplicity, hmultiplicity, hestimate⟩ :=
    hRaw p hpFive c xi eta hc hxi heta hpair
  refine ⟨multiplicity, hmultiplicity, ?_⟩
  intro d hd hdPositive
  letI : Finite (IncidenceEquationWitness c xi eta) :=
    Finite.of_injective
      (fun w : IncidenceEquationWitness c xi eta =>
        (w.middle, w.firstRoot, w.secondRoot))
      (by
        intro a b hab
        cases a
        cases b
        simp_all)
  letI : Finite (RegularIncidenceEquationWitness p c xi eta) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hraw := hestimate d hd hdPositive
  have hdecomposition :=
    natCard_raw_eq_regular_add_irregular p c xi eta d
  let badCard :=
    Nat.card
      {z : rawIncidenceWitnessPowerRangeSolutions p c xi eta d //
        ¬ OrderedTraceCandidateRegular c c c z.1.1.middle}
  have hbad : badCard ≤ 56 := by
    exact natCard_irregular_rawIncidenceWitnessPowerRange_le_fiftySix
      p hpFive c xi eta hc d
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    have hpNonnegative : (0 : ℝ) ≤ p := by positivity
    have hsquare := Real.sq_sqrt hpNonnegative
    have hsqrtNonnegative := Real.sqrt_nonneg (p : ℝ)
    have hpFiveReal : (5 : ℝ) ≤ p := by exact_mod_cast hpFive
    nlinarith
  calc
    |(Nat.card (regularIncidenceWitnessPowerRangeSolutions
          p c xi eta d) : ℝ) -
        (multiplicity : ℝ) * (p : ℝ) / d| =
      |((Nat.card (rawIncidenceWitnessPowerRangeSolutions
          p c xi eta d) : ℝ) -
        (multiplicity : ℝ) * (p : ℝ) / d) - badCard| := by
          rw [hdecomposition]
          push_cast
          congr 1
          ring
    _ ≤ |(Nat.card (rawIncidenceWitnessPowerRangeSolutions
          p c xi eta d) : ℝ) -
        (multiplicity : ℝ) * (p : ℝ) / d| + |(badCard : ℝ)| :=
      by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le
            ((Nat.card (rawIncidenceWitnessPowerRangeSolutions
              p c xi eta d) : ℝ) -
                (multiplicity : ℝ) * (p : ℝ) / d)
            (-(badCard : ℝ))
    _ = |(Nat.card (rawIncidenceWitnessPowerRangeSolutions
          p c xi eta d) : ℝ) -
        (multiplicity : ℝ) * (p : ℝ) / d| + badCard := by
      congr 1
      exact abs_of_nonneg (Nat.cast_nonneg badCard)
    _ ≤ (coefficient : ℝ) * Real.sqrt p + 56 := by
      gcongr
      exact_mod_cast hbad
    _ ≤ (coefficient : ℝ) * Real.sqrt p +
        56 * Real.sqrt p := by
      have h56 : (56 : ℝ) ≤ 56 * Real.sqrt p := by
        nlinarith
      exact add_le_add_right h56 _
    _ = ((coefficient + 56 : ℕ) : ℝ) * Real.sqrt p := by
      push_cast
      ring

/-- Existential wrapper used by the unconditional cage assembly. -/
theorem exists_regularIncidenceWitnessPointEstimate_of_raw
    (hRaw :
      ∃ coefficient : ℕ, 0 < coefficient ∧
        RawIncidenceWitnessPointEstimate coefficient) :
    ∃ coefficient : ℕ, 0 < coefficient ∧
      RegularIncidenceWitnessPointEstimate coefficient := by
  obtain ⟨coefficient, hpositive, hestimate⟩ := hRaw
  exact ⟨coefficient + 56, by omega,
    regularIncidenceWitnessPointEstimate_of_raw coefficient hestimate⟩

end

end GenMarkoff.Symmetric.Cage
