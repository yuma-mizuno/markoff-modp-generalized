import GenMarkoff.Symmetric.Opening.RotationBridge
import GenMarkoff.TraceCurve.ExceptionalRouting
import BGS.Markoff.Core.TraceClassification

/-!
# Small-order point count for the symmetric trace surface

When the symmetric multiplier is nonzero, each affine coordinate trace
determines the original coordinate.  Fixing the first two traces therefore
leaves a monic quadratic in the third coordinate, hence at most two surface
points.  Combining this with the pinned BGS low-order trace-set bound gives
the same crude count used in the classical giant-orbit assembly.
-/

namespace GenMarkoff.Symmetric.Assembly

open BGS.Markoff

noncomputable section

variable {K : Type*} [Field K] [Fintype K]

/-- Symmetric surface points with prescribed first and second affine traces. -/
def pointsWithFirstTwoTraces
    (c t₁ t₂ : K) : Finset (Point K) := by
  classical
  exact Finset.univ.filter fun x ↦
    IsSolution (coefficients c) x ∧
      trace c x.x1 = t₁ ∧ trace c x.x2 = t₂

@[simp]
theorem mem_pointsWithFirstTwoTraces_iff
    {c t₁ t₂ : K} {x : Point K} :
    x ∈ pointsWithFirstTwoTraces c t₁ t₂ ↔
      IsSolution (coefficients c) x ∧
        trace c x.x1 = t₁ ∧ trace c x.x2 = t₂ := by
  classical
  simp [pointsWithFirstTwoTraces]

/-- Fixing two affine traces leaves at most two symmetric surface points. -/
theorem pointsWithFirstTwoTraces_card_le_two
    (c t₁ t₂ : K) (hmultiplier : multiplier c ≠ 0) :
    (pointsWithFirstTwoTraces c t₁ t₂).card ≤ 2 := by
  classical
  let u := (t₁ + c) / multiplier c
  apply card_le_two_of_solution_fixed_x1_trace2
    (coefficients c) (pointsWithFirstTwoTraces c t₁ t₂) u t₂
  · simpa only [multiplier_eq_coefficients_multiplier] using hmultiplier
  · intro x hx
    exact (mem_pointsWithFirstTwoTraces_iff.mp hx).1
  · intro x hx
    have htrace := (mem_pointsWithFirstTwoTraces_iff.mp hx).2.1
    apply (eq_div_iff hmultiplier).2
    rw [trace] at htrace
    linear_combination htrace
  · intro x hx
    have htrace := (mem_pointsWithFirstTwoTraces_iff.mp hx).2.2
    simpa [coordinateTrace2, trace, coefficients] using htrace

/-- Symmetric surface points whose first two affine traces lie in `S`. -/
def pointsWithFirstTwoTracesIn
    (c : K) (S : Finset K) : Finset (Point K) := by
  classical
  exact (S.product S).biUnion fun t ↦
    pointsWithFirstTwoTraces c t.1 t.2

@[simp]
theorem mem_pointsWithFirstTwoTracesIn_iff
    {c : K} {S : Finset K} {x : Point K} :
    x ∈ pointsWithFirstTwoTracesIn c S ↔
      IsSolution (coefficients c) x ∧
        trace c x.x1 ∈ S ∧ trace c x.x2 ∈ S := by
  classical
  rw [pointsWithFirstTwoTracesIn, Finset.mem_biUnion]
  constructor
  · rintro ⟨t, ht, hx⟩
    have ht' : t.1 ∈ S ∧ t.2 ∈ S := Finset.mem_product.mp ht
    have hx' := mem_pointsWithFirstTwoTraces_iff.mp hx
    exact ⟨hx'.1, hx'.2.1 ▸ ht'.1, hx'.2.2 ▸ ht'.2⟩
  · rintro ⟨hx, hx₁, hx₂⟩
    refine ⟨(trace c x.x1, trace c x.x2),
      Finset.mem_product.mpr ⟨hx₁, hx₂⟩, ?_⟩
    exact mem_pointsWithFirstTwoTraces_iff.mpr ⟨hx, rfl, rfl⟩

/-- Summing the two-point fibers over a trace set. -/
theorem pointsWithFirstTwoTracesIn_card_le
    (c : K) (S : Finset K) (hmultiplier : multiplier c ≠ 0) :
    (pointsWithFirstTwoTracesIn c S).card ≤ 2 * S.card ^ 2 := by
  classical
  calc
    (pointsWithFirstTwoTracesIn c S).card ≤
        (S.product S).card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro t _
      exact pointsWithFirstTwoTraces_card_le_two
        c t.1 t.2 hmultiplier
    _ = 2 * S.card ^ 2 := by
      simp [Finset.card_product, pow_two, Nat.mul_comm]

section PrimeField

/-- Symmetric surface points whose first two one-step half-orders are below
`bound`. -/
def pointsWithSmallFirstTwoHalfStepOrders
    (p : ℕ) [Fact p.Prime] (c : ZMod p) (bound : ℕ) :
    Finset (Point (ZMod p)) := by
  classical
  exact Finset.univ.filter fun x ↦
    IsSolution (coefficients c) x ∧
      halfStepOrder (trace c x.x1) < bound ∧
      halfStepOrder (trace c x.x2) < bound

@[simp]
theorem mem_pointsWithSmallFirstTwoHalfStepOrders_iff
    {p : ℕ} [Fact p.Prime] {c : ZMod p} {bound : ℕ}
    {x : Point (ZMod p)} :
    x ∈ pointsWithSmallFirstTwoHalfStepOrders p c bound ↔
      IsSolution (coefficients c) x ∧
        halfStepOrder (trace c x.x1) < bound ∧
        halfStepOrder (trace c x.x2) < bound := by
  classical
  simp [pointsWithSmallFirstTwoHalfStepOrders]

theorem pointsWithSmallFirstTwoHalfStepOrders_subset_traceSet
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (bound : ℕ) :
    pointsWithSmallFirstTwoHalfStepOrders p c bound ⊆
      pointsWithFirstTwoTracesIn c
        (concreteLowOrderTraceSet p bound) := by
  intro x hx
  have hx' := mem_pointsWithSmallFirstTwoHalfStepOrders_iff.mp hx
  apply mem_pointsWithFirstTwoTracesIn_iff.mpr
  refine ⟨hx'.1, ?_, ?_⟩
  · apply mem_concreteLowOrderTraceSet_of_rotationOrder_lt p hpTwo
    simpa only [Opening.halfStepOrder_eq_bgsRotationOrder] using hx'.2.1
  · apply mem_concreteLowOrderTraceSet_of_rotationOrder_lt p hpTwo
    simpa only [Opening.halfStepOrder_eq_bgsRotationOrder] using hx'.2.2

/-- The generalized symmetric small-order set has the classical quadratic
trace-set bound. -/
theorem pointsWithSmallFirstTwoHalfStepOrders_card_le
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (hmultiplier : multiplier c ≠ 0) (bound : ℕ) :
    (pointsWithSmallFirstTwoHalfStepOrders p c bound).card ≤
      2 * (2 + 2 * bound ^ 2) ^ 2 := by
  calc
    (pointsWithSmallFirstTwoHalfStepOrders p c bound).card ≤
        (pointsWithFirstTwoTracesIn c
          (concreteLowOrderTraceSet p bound)).card :=
      Finset.card_mono
        (pointsWithSmallFirstTwoHalfStepOrders_subset_traceSet
          p hpTwo c bound)
    _ ≤ 2 * (concreteLowOrderTraceSet p bound).card ^ 2 :=
      pointsWithFirstTwoTracesIn_card_le c _ hmultiplier
    _ ≤ 2 * (2 + 2 * bound ^ 2) ^ 2 := by
      gcongr
      exact concreteLowOrderTraceSet_card_le p bound

end PrimeField

end

end GenMarkoff.Symmetric.Assembly
