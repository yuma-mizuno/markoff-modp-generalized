import GenMarkoff.General.Opening.RotationBridge
import GenMarkoff.TraceCurve.ExceptionalRouting
import BGS.Markoff.Assembly.NormalizedSmallOrderCount
import BGS.Markoff.Core.TraceClassification

/-!
# Small actual-rotation-order count for a general coefficient triple

For a fixed coefficient triple with nonzero multiplier, each of the first
two affine coordinate traces determines the corresponding coordinate.
Fixing those two traces leaves a monic quadratic in the third coordinate,
so there are at most two surface points.

The trace classification is stated for the half-step matrix `A`, whereas
the linear part of an actual two-Vieta rotation is `A ^ 2`.  Thus a bound on
`orderOf (A ^ 2)` gives a bound twice as large on `orderOf A`.  This
factor-of-two passage is the new counting consideration required for the
general coefficient case.
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

/-- Sum the two-point fibers over a set of possible trace pairs. -/
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

/-- General surface points for which both of the first two actual rotation
linear orders are below `bound`. -/
def pointsWithSmallFirstTwoRotationLinearOrders
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) (bound : ℕ) :
    Finset (Point (ZMod p)) := by
  classical
  exact Finset.univ.filter fun x =>
    IsSolution a x ∧
      rotationLinearOrder (coordinateTrace1 a x) < bound ∧
      rotationLinearOrder (coordinateTrace2 a x) < bound

@[simp]
theorem mem_pointsWithSmallFirstTwoRotationLinearOrders_iff
    {p : ℕ} [Fact p.Prime] {a : Coefficients (ZMod p)} {bound : ℕ}
    {x : Point (ZMod p)} :
    x ∈ pointsWithSmallFirstTwoRotationLinearOrders p a bound ↔
      IsSolution a x ∧
        rotationLinearOrder (coordinateTrace1 a x) < bound ∧
        rotationLinearOrder (coordinateTrace2 a x) < bound := by
  classical
  simp [pointsWithSmallFirstTwoRotationLinearOrders]

/-- Small actual rotation order forces both traces into the BGS trace set
with twice the order bound. -/
theorem pointsWithSmallFirstTwoRotationLinearOrders_subset_traceSet
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (bound : ℕ) :
    pointsWithSmallFirstTwoRotationLinearOrders p a bound ⊆
      pointsWithFirstTwoTracesIn a
        (concreteLowOrderTraceSet p (2 * bound)) := by
  intro x hx
  have hx' := mem_pointsWithSmallFirstTwoRotationLinearOrders_iff.mp hx
  apply mem_pointsWithFirstTwoTracesIn_iff.mpr
  refine ⟨hx'.1, ?_, ?_⟩
  · apply mem_concreteLowOrderTraceSet_of_rotationOrder_lt p hpTwo
    exact Opening.bgsRotationOrder_lt_two_mul_of_rotationLinearOrder_lt
      (coordinateTrace1 a x) bound hx'.2.1
  · apply mem_concreteLowOrderTraceSet_of_rotationOrder_lt p hpTwo
    exact Opening.bgsRotationOrder_lt_two_mul_of_rotationLinearOrder_lt
      (coordinateTrace2 a x) bound hx'.2.2

/-- The set on which both of the first two actual two-Vieta rotations have
small linear order has the indicated quartic bound. -/
theorem pointsWithSmallFirstTwoRotationLinearOrders_card_le
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (hmultiplier : a.multiplier ≠ 0)
    (bound : ℕ) :
    (pointsWithSmallFirstTwoRotationLinearOrders p a bound).card ≤
      2 * (2 + 2 * (2 * bound) ^ 2) ^ 2 := by
  calc
    (pointsWithSmallFirstTwoRotationLinearOrders p a bound).card ≤
        (pointsWithFirstTwoTracesIn a
          (concreteLowOrderTraceSet p (2 * bound))).card :=
      Finset.card_mono
        (pointsWithSmallFirstTwoRotationLinearOrders_subset_traceSet
          p hpTwo a bound)
    _ ≤ 2 * (concreteLowOrderTraceSet p (2 * bound)).card ^ 2 :=
      pointsWithFirstTwoTracesIn_card_le a _ hmultiplier
    _ ≤ 2 * (2 + 2 * (2 * bound) ^ 2) ^ 2 := by
      gcongr
      exact concreteLowOrderTraceSet_card_le p (2 * bound)

/-- Divisor-sensitive refinement of the small actual-order point count.

The half-step trace classification still costs the factor `2 * bound`, but
the number of traces is now linear in that bound and in the simultaneous
divisor count
`τ(p - 1) + τ(p + 1)`.  This is the count needed by the coarse `T^8`
frontier; retaining the older quartic bound above keeps the eventual
asymptotic route available independently. -/
theorem pointsWithSmallFirstTwoRotationLinearOrders_card_le_divisor_sensitive
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (hmultiplier : a.multiplier ≠ 0)
    (bound : ℕ) :
    (pointsWithSmallFirstTwoRotationLinearOrders p a bound).card ≤
      2 * (2 + (2 * bound - 1) *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2 := by
  calc
    (pointsWithSmallFirstTwoRotationLinearOrders p a bound).card ≤
        (pointsWithFirstTwoTracesIn a
          (concreteLowOrderTraceSet p (2 * bound))).card :=
      Finset.card_mono
        (pointsWithSmallFirstTwoRotationLinearOrders_subset_traceSet
          p hpTwo a bound)
    _ ≤ 2 * (concreteLowOrderTraceSet p (2 * bound)).card ^ 2 :=
      pointsWithFirstTwoTracesIn_card_le a _ hmultiplier
    _ ≤ 2 * (2 + (2 * bound - 1) *
          ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2 := by
      gcongr
      exact concreteLowOrderTraceSet_card_le_divisor_sensitive (2 * bound)

/-- The trace labels which are either below the actual-order threshold or
exceptional for one of the two alternating ordered frames.

The same low-order trace set is shared by both axes.  The two ordered safe
polynomials contribute at most ten roots each.  Keeping these roots at the
trace-label level, instead of routing along another conic first, is what
avoids an additional divisor-count factor in the coarse argument. -/
def firstTwoRegularOrSmallTraceSet
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) (bound : ℕ) :
    Finset (ZMod p) :=
  (concreteLowOrderTraceSet p (2 * bound) ∪
      (orderedTraceSafePolynomial a.a1 a.a2 a.a3).roots.toFinset) ∪
    (orderedTraceSafePolynomial a.a2 a.a1 a.a3).roots.toFinset

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

/-- A `p`-divisible punctured rotation component escapes the simultaneous
small-or-irregular first/second trace set.  The resulting point already is a
candidate-regular alternating source of order at least `bound`; no
order-losing change of active axis is made. -/
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

/-- If a rotation orbit is larger than the small-order point set, it
contains a point at which at least one of the first two actual rotations
has linear order at least `bound`. -/
theorem exists_mem_rotationOrbit_with_large_first_or_second_rotationLinearOrder
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) (bound : ℕ)
    (x : PuncturedSolutionSurface a)
    (hlarge :
      (pointsWithSmallFirstTwoRotationLinearOrders p a bound).card <
        (puncturedRotationOrbit x).ncard) :
    ∃ y : PuncturedSolutionSurface a,
      y ∈ puncturedRotationOrbit x ∧
        (bound ≤ rotationLinearOrder (coordinateTrace1 a y.1.1) ∨
          bound ≤ rotationLinearOrder (coordinateTrace2 a y.1.1)) := by
  classical
  by_contra hnone
  push Not at hnone
  let orbitFinset : Finset (PuncturedSolutionSurface a) :=
    (Set.toFinite (puncturedRotationOrbit x)).toFinset
  let pointEmbedding : PuncturedSolutionSurface a ↪ Point (ZMod p) :=
    ⟨(fun y : PuncturedSolutionSurface a => y.1.1), by
      intro y z hyz
      exact Subtype.ext (Subtype.ext hyz)⟩
  have hsubset :
      orbitFinset.map pointEmbedding ⊆
        pointsWithSmallFirstTwoRotationLinearOrders p a bound := by
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨y, hyOrbit, rfl⟩ := hz
    have hySet : y ∈ puncturedRotationOrbit x := by
      simpa [orbitFinset] using hyOrbit
    apply mem_pointsWithSmallFirstTwoRotationLinearOrders_iff.mpr
    exact ⟨y.1.2, hnone y hySet⟩
  have hcardLe :
      orbitFinset.card ≤
        (pointsWithSmallFirstTwoRotationLinearOrders p a bound).card := by
    rw [← Finset.card_map (f := pointEmbedding)]
    exact Finset.card_le_card hsubset
  have horbitCard :
      orbitFinset.card = (puncturedRotationOrbit x).ncard := by
    simpa [orbitFinset] using
      (Set.ncard_eq_toFinset_card (puncturedRotationOrbit x)
        (Set.toFinite (puncturedRotationOrbit x))).symm
  omega

/-- A nonempty rotation orbit whose cardinality is divisible by `p`
escapes the small-order point set whenever that set has fewer than `p`
points. -/
theorem exists_mem_rotationOrbit_with_large_first_or_second_rotationLinearOrder_of_dvd
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) (bound : ℕ)
    (x : PuncturedSolutionSurface a)
    (hdiv : p ∣ (puncturedRotationOrbit x).ncard)
    (hsmall :
      (pointsWithSmallFirstTwoRotationLinearOrders p a bound).card < p) :
    ∃ y : PuncturedSolutionSurface a,
      y ∈ puncturedRotationOrbit x ∧
        (bound ≤ rotationLinearOrder (coordinateTrace1 a y.1.1) ∨
          bound ≤ rotationLinearOrder (coordinateTrace2 a y.1.1)) := by
  apply exists_mem_rotationOrbit_with_large_first_or_second_rotationLinearOrder
    p a bound x
  have horbitPos : 0 < (puncturedRotationOrbit x).ncard := by
    apply (Set.ncard_pos (Set.toFinite (puncturedRotationOrbit x))).mpr
    exact ⟨x, MulAction.mem_orbit_self x⟩
  have hpLe : p ≤ (puncturedRotationOrbit x).ncard :=
    Nat.le_of_dvd horbitPos hdiv
  omega

end PrimeField

end

end GenMarkoff.General.Assembly
