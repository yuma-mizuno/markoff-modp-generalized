module

public import GenMarkoff.General.Opening.RotationBridge
public import GenMarkoff.TraceCurve.ExceptionalRouting
public import BGS.Markoff.Assembly.NormalizedSmallOrderCount
public import BGS.Markoff.Core.TraceClassification

@[expose] public section

/-!
# Counting points with small or irregular first and second traces

For a fixed coefficient triple with nonzero multiplier, each of the first
two affine coordinate traces determines the corresponding coordinate.
Fixing those two traces leaves a monic quadratic in the third coordinate,
so there are at most two surface points (`pointsWithFirstTwoTraces_card_le_two`).

`firstTwoRegularOrSmallTraceSet` collects the trace labels of small order
together with the roots of the two ordered safe polynomials.  The low-order
trace classification is stated for the half-step matrix `A`, whereas the
linear part of an actual two-Vieta rotation is `A ^ 2`, so an actual order
below `bound` is detected through a half-step order below `2 * bound`.  The
main result, `exists_mem_rotationOrbit_with_candidateRegular_large_first_or_second_of_dvd`,
says that a `p`-divisible punctured rotation orbit contains a point whose
first or second trace is candidate regular of actual order at least `bound`,
as soon as `2 * (22 + (2 * bound - 1) * T) ^ 2 < p` with
`T = #divisors (p - 1) + #divisors (p + 1)`.
-/

namespace GenMarkoff.General.Assembly

open BGS.Markoff

noncomputable section

variable {K : Type*} [Field K] [Fintype K]

/-- General surface points with prescribed first and second affine
coordinate traces. -/
def pointsWithFirstTwoTraces
    (a : Coefficients K) (t1 t2 : K) : Finset (Point K) := by
  classical
  exact Finset.univ.filter fun x =>
    IsSolution a x ∧
      coordinateTrace1 a x = t1 ∧ coordinateTrace2 a x = t2

@[simp]
theorem mem_pointsWithFirstTwoTraces_iff
    {a : Coefficients K} {t1 t2 : K} {x : Point K} :
    x ∈ pointsWithFirstTwoTraces a t1 t2 ↔
      IsSolution a x ∧
        coordinateTrace1 a x = t1 ∧ coordinateTrace2 a x = t2 := by
  classical
  simp [pointsWithFirstTwoTraces]

/-- Fixing the first two affine coordinate traces leaves at most two
general surface points. -/
theorem pointsWithFirstTwoTraces_card_le_two
    (a : Coefficients K) (t1 t2 : K) (hmultiplier : a.multiplier ≠ 0) :
    (pointsWithFirstTwoTraces a t1 t2).card ≤ 2 := by
  classical
  let u := (t1 + a.a1) / a.multiplier
  apply card_le_two_of_solution_fixed_x1_trace2
    a (pointsWithFirstTwoTraces a t1 t2) u t2 hmultiplier
  · intro x hx
    exact (mem_pointsWithFirstTwoTraces_iff.mp hx).1
  · intro x hx
    have htrace := (mem_pointsWithFirstTwoTraces_iff.mp hx).2.1
    apply (eq_div_iff hmultiplier).2
    rw [coordinateTrace1] at htrace
    linear_combination htrace
  · intro x hx
    exact (mem_pointsWithFirstTwoTraces_iff.mp hx).2.2

/-- General surface points whose first two affine coordinate traces lie in
`S`. -/
def pointsWithFirstTwoTracesIn
    (a : Coefficients K) (S : Finset K) : Finset (Point K) := by
  classical
  exact (S.product S).biUnion fun t =>
    pointsWithFirstTwoTraces a t.1 t.2

@[simp]
theorem mem_pointsWithFirstTwoTracesIn_iff
    {a : Coefficients K} {S : Finset K} {x : Point K} :
    x ∈ pointsWithFirstTwoTracesIn a S ↔
      IsSolution a x ∧
        coordinateTrace1 a x ∈ S ∧ coordinateTrace2 a x ∈ S := by
  classical
  rw [pointsWithFirstTwoTracesIn, Finset.mem_biUnion]
  constructor
  · rintro ⟨t, ht, hx⟩
    have ht' : t.1 ∈ S ∧ t.2 ∈ S := Finset.mem_product.mp ht
    have hx' := mem_pointsWithFirstTwoTraces_iff.mp hx
    exact ⟨hx'.1, hx'.2.1 ▸ ht'.1, hx'.2.2 ▸ ht'.2⟩
  · rintro ⟨hx, hx1, hx2⟩
    refine ⟨(coordinateTrace1 a x, coordinateTrace2 a x),
      Finset.mem_product.mpr ⟨hx1, hx2⟩, ?_⟩
    exact mem_pointsWithFirstTwoTraces_iff.mpr ⟨hx, rfl, rfl⟩

/-- At most `2 * S.card ^ 2` surface points have both of their first two
affine coordinate traces in `S`. -/
theorem pointsWithFirstTwoTracesIn_card_le
    (a : Coefficients K) (S : Finset K) (hmultiplier : a.multiplier ≠ 0) :
    (pointsWithFirstTwoTracesIn a S).card ≤ 2 * S.card ^ 2 := by
  classical
  calc
    (pointsWithFirstTwoTracesIn a S).card ≤
        (S.product S).card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro t _
      exact pointsWithFirstTwoTraces_card_le_two
        a t.1 t.2 hmultiplier
    _ = 2 * S.card ^ 2 := by
      simp [Finset.card_product, pow_two, Nat.mul_comm]

section PrimeField

/-- The low-order trace labels `concreteLowOrderTraceSet p (2 * bound)`,
which contain every trace of half-step order below `2 * bound`, together with
the roots of the ordered safe polynomials of the two alternating frames
`(a₁, a₂, a₃)` and `(a₂, a₁, a₃)`.  The same set serves both axes. -/
def firstTwoRegularOrSmallTraceSet
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) (bound : ℕ) :
    Finset (ZMod p) :=
  (concreteLowOrderTraceSet p (2 * bound) ∪
      (orderedTraceSafePolynomial a.a1 a.a2 a.a3).roots.toFinset) ∪
    (orderedTraceSafePolynomial a.a2 a.a1 a.a3).roots.toFinset

/-- The coarse trace set has at most `22 + (2 * bound - 1) * T` elements:
the low-order traces contribute `2 + (2 * bound - 1) * T` and each ordered
safe polynomial at most ten roots. -/
theorem firstTwoRegularOrSmallTraceSet_card_le_divisor_sensitive
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) (bound : ℕ) :
    (firstTwoRegularOrSmallTraceSet p a bound).card ≤
      22 + (2 * bound - 1) *
        ((p - 1).divisors.card + (p + 1).divisors.card) := by
  classical
  calc
    (firstTwoRegularOrSmallTraceSet p a bound).card ≤
        (concreteLowOrderTraceSet p (2 * bound)).card +
          (orderedTraceSafePolynomial a.a1 a.a2 a.a3).roots.toFinset.card +
          (orderedTraceSafePolynomial a.a2 a.a1 a.a3).roots.toFinset.card := by
      unfold firstTwoRegularOrSmallTraceSet
      calc
        ((concreteLowOrderTraceSet p (2 * bound) ∪
              (orderedTraceSafePolynomial a.a1 a.a2 a.a3).roots.toFinset) ∪
            (orderedTraceSafePolynomial a.a2 a.a1 a.a3).roots.toFinset).card ≤
            (concreteLowOrderTraceSet p (2 * bound) ∪
              (orderedTraceSafePolynomial a.a1 a.a2 a.a3).roots.toFinset).card +
              (orderedTraceSafePolynomial a.a2 a.a1 a.a3).roots.toFinset.card :=
          Finset.card_union_le _ _
        _ ≤
            ((concreteLowOrderTraceSet p (2 * bound)).card +
              (orderedTraceSafePolynomial a.a1 a.a2 a.a3).roots.toFinset.card) +
              (orderedTraceSafePolynomial a.a2 a.a1 a.a3).roots.toFinset.card := by
          gcongr
          exact Finset.card_union_le _ _
    _ ≤
        (2 + (2 * bound - 1) *
            ((p - 1).divisors.card + (p + 1).divisors.card)) +
          10 + 10 := by
      gcongr
      · exact concreteLowOrderTraceSet_card_le_divisor_sensitive (2 * bound)
      · exact orderedTraceSafePolynomial_roots_card_le a.a1 a.a2 a.a3
      · exact orderedTraceSafePolynomial_roots_card_le a.a2 a.a1 a.a3
    _ = 22 + (2 * bound - 1) *
        ((p - 1).divisors.card + (p + 1).divisors.card) := by omega

/-- Failure of candidate regularity, or actual order below `bound`, puts a
first-axis trace in the coarse trace set. -/
theorem coordinateTrace1_mem_firstTwoRegularOrSmallTraceSet
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4) (bound : ℕ) (x : Point (ZMod p))
    (hbad :
      ¬ (OrderedTraceCandidateRegular a.a1 a.a2 a.a3
            (coordinateTrace1 a x) ∧
          bound ≤ rotationLinearOrder (coordinateTrace1 a x))) :
    coordinateTrace1 a x ∈ firstTwoRegularOrSmallTraceSet p a bound := by
  classical
  by_cases hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 (coordinateTrace1 a x)
  · have horder : rotationLinearOrder (coordinateTrace1 a x) < bound := by
      exact Nat.lt_of_not_ge (fun hge => hbad ⟨hregular, hge⟩)
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply mem_concreteLowOrderTraceSet_of_rotationOrder_lt p hpTwo
    exact Opening.bgsRotationOrder_lt_two_mul_of_rotationLinearOrder_lt
      (coordinateTrace1 a x) bound horder
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    rw [Multiset.mem_toFinset, Polynomial.mem_roots
      (orderedTraceSafePolynomial_ne_zero a.a1 a.a2 a.a3
        (by
          intro hzero
          have hpDvd : p ∣ 2 :=
            (ZMod.natCast_eq_zero_iff 2 p).mp hzero
          have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
          exact hpTwo
            (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le))
        hA1 hA2)]
    by_contra hne
    exact hregular
      ((orderedTraceSafePolynomial_eval_ne_zero_iff
        a.a1 a.a2 a.a3 (coordinateTrace1 a x)).mp hne)

/-- The second-axis version of
`coordinateTrace1_mem_firstTwoRegularOrSmallTraceSet`. -/
theorem coordinateTrace2_mem_firstTwoRegularOrSmallTraceSet
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4) (bound : ℕ) (x : Point (ZMod p))
    (hbad :
      ¬ (OrderedTraceCandidateRegular a.a2 a.a1 a.a3
            (coordinateTrace2 a x) ∧
          bound ≤ rotationLinearOrder (coordinateTrace2 a x))) :
    coordinateTrace2 a x ∈ firstTwoRegularOrSmallTraceSet p a bound := by
  classical
  by_cases hregular :
      OrderedTraceCandidateRegular a.a2 a.a1 a.a3 (coordinateTrace2 a x)
  · have horder : rotationLinearOrder (coordinateTrace2 a x) < bound := by
      exact Nat.lt_of_not_ge (fun hge => hbad ⟨hregular, hge⟩)
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply mem_concreteLowOrderTraceSet_of_rotationOrder_lt p hpTwo
    exact Opening.bgsRotationOrder_lt_two_mul_of_rotationLinearOrder_lt
      (coordinateTrace2 a x) bound horder
  · apply Finset.mem_union_right
    rw [Multiset.mem_toFinset, Polynomial.mem_roots
      (orderedTraceSafePolynomial_ne_zero a.a2 a.a1 a.a3
        (by
          intro hzero
          have hpDvd : p ∣ 2 :=
            (ZMod.natCast_eq_zero_iff 2 p).mp hzero
          have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
          exact hpTwo
            (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le))
        hA2 hA1)]
    by_contra hne
    exact hregular
      ((orderedTraceSafePolynomial_eval_ne_zero_iff
        a.a2 a.a1 a.a3 (coordinateTrace2 a x)).mp hne)

/-- If `2 * (22 + (2 * bound - 1) * T) ^ 2 < p`, then a `p`-divisible
punctured rotation orbit contains a point whose first trace is candidate
regular in `(a₁, a₂, a₃)` or whose second trace is candidate regular in
`(a₂, a₁, a₃)`, with actual order at least `bound` in either case. -/
theorem exists_mem_rotationOrbit_with_candidateRegular_large_first_or_second_of_dvd
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (hmultiplier : a.multiplier ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (bound : ℕ) (x : PuncturedSolutionSurface a)
    (hdiv : p ∣ (puncturedRotationOrbit x).ncard)
    (hsmall :
      2 * (22 + (2 * bound - 1) *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2 < p) :
    ∃ y : PuncturedSolutionSurface a,
      y ∈ puncturedRotationOrbit x ∧
        ((OrderedTraceCandidateRegular a.a1 a.a2 a.a3
              (coordinateTrace1 a y.1.1) ∧
            bound ≤ rotationLinearOrder (coordinateTrace1 a y.1.1)) ∨
          (OrderedTraceCandidateRegular a.a2 a.a1 a.a3
              (coordinateTrace2 a y.1.1) ∧
            bound ≤ rotationLinearOrder (coordinateTrace2 a y.1.1))) := by
  classical
  -- The points with both traces in the coarse set number fewer than `p`.
  let traces := firstTwoRegularOrSmallTraceSet p a bound
  let bad := pointsWithFirstTwoTracesIn a traces
  have hbadCard : bad.card < p := by
    calc
      bad.card ≤ 2 * traces.card ^ 2 :=
        pointsWithFirstTwoTracesIn_card_le a traces hmultiplier
      _ ≤ 2 * (22 + (2 * bound - 1) *
          ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2 := by
        gcongr
        exact firstTwoRegularOrSmallTraceSet_card_le_divisor_sensitive
          p a bound
      _ < p := hsmall
  -- The orbit has at least `p` points, so one of them is not bad.
  have horbitPos : 0 < (puncturedRotationOrbit x).ncard := by
    apply (Set.ncard_pos (Set.toFinite (puncturedRotationOrbit x))).mpr
    exact ⟨x, MulAction.mem_orbit_self x⟩
  have hpLeOrbit : p ≤ (puncturedRotationOrbit x).ncard :=
    Nat.le_of_dvd horbitPos hdiv
  let orbitFinset : Finset (PuncturedSolutionSurface a) :=
    (Set.toFinite (puncturedRotationOrbit x)).toFinset
  let pointEmbedding : PuncturedSolutionSurface a ↪ Point (ZMod p) :=
    ⟨(fun y => y.1.1), by
      intro y z hyz
      exact Subtype.ext (Subtype.ext hyz)⟩
  have hexists : ∃ y ∈ orbitFinset, pointEmbedding y ∉ bad := by
    by_contra hnone
    push Not at hnone
    have hsubset : orbitFinset.map pointEmbedding ⊆ bad := by
      intro z hz
      rw [Finset.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact hnone y hy
    have hle : orbitFinset.card ≤ bad.card := by
      rw [← Finset.card_map (f := pointEmbedding)]
      exact Finset.card_le_card hsubset
    have horbitCard :
        orbitFinset.card = (puncturedRotationOrbit x).ncard := by
      simpa [orbitFinset] using
        (Set.ncard_eq_toFinset_card (puncturedRotationOrbit x)
          (Set.toFinite (puncturedRotationOrbit x))).symm
    rw [horbitCard] at hle
    omega
  -- A point outside the bad set has a good first or second trace.
  obtain ⟨y, hyOrbitFinset, hyBad⟩ := hexists
  have hyOrbit : y ∈ puncturedRotationOrbit x := by
    simpa [orbitFinset] using hyOrbitFinset
  refine ⟨y, hyOrbit, ?_⟩
  by_contra hnone
  push Not at hnone
  apply hyBad
  apply mem_pointsWithFirstTwoTracesIn_iff.mpr
  refine ⟨y.1.2, ?_, ?_⟩
  · exact coordinateTrace1_mem_firstTwoRegularOrSmallTraceSet
      p hpTwo a hA1 hA2 bound y.1.1
        (fun h => (not_lt_of_ge h.2) (hnone.1 h.1))
  · exact coordinateTrace2_mem_firstTwoRegularOrSmallTraceSet
      p hpTwo a hA1 hA2 bound y.1.1
        (fun h => (not_lt_of_ge h.2) (hnone.2 h.1))

end PrimeField

end

end GenMarkoff.General.Assembly
