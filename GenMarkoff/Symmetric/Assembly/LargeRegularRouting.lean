import GenMarkoff.Symmetric.Assembly.SmallOrderCount
import GenMarkoff.Symmetric.Opening.GlobalOpening
import GenMarkoff.Symmetric.MiddleGame.ActualDiagonalization

/-!
# Routing a large actual one-step cycle to a regular large-order trace

The middle-game growth theorem is iterable only after the fixed affine trace
is candidate regular.  This module supplies the missing entry point.  A
nonparabolic, noncentered first-axis cycle has its honest point-cycle
cardinality equal to the half-step matrix order.  Removing the at most
fourteen candidate-irregular points and the points above the elementary
low-order trace set still leaves a regular adjacent trace of prescribed
minimum order.
-/

namespace GenMarkoff.Symmetric.Assembly

open BGS.Markoff

noncomputable section

private theorem iterate_eq_self_of_le
    {α : Type*} (f : α → α) (hf : Function.Injective f)
    (x : α) {n m : ℕ} (hnm : n ≤ m)
    (h : (f^[n]) x = (f^[m]) x) :
    (f^[m - n]) x = x := by
  apply (hf.iterate n)
  calc
    (f^[n]) ((f^[m - n]) x) =
        (f^[n + (m - n)]) x := by
          rw [Function.iterate_add_apply]
    _ = (f^[m]) x := by rw [Nat.add_sub_of_le hnm]
    _ = (f^[n]) x := h.symm

/-- A positive return of an actual nonparabolic, noncentered first-axis
one-step divides by the exact half-step matrix order. -/
theorem halfStepOrder_dvd_of_oneStep1_return_of_nonparabolic_noncentered
    (p : ℕ) [Fact p.Prime]
    (c : ZMod p) (x : Point (ZMod p))
    (hparabolic : trace c x.x1 ^ 2 ≠ 4)
    (hnoncentered :
      centerCoordinates (fiberCenter c x.x1 (trace c x.x1))
        (movingCoordinates1 x) ≠ (0, 0))
    (d : ℕ) (hdPos : 0 < d)
    (hreturn : ((oneStep1 c)^[d]) x = x) :
    halfStepOrder (trace c x.x1) ∣ d := by
  have hpair :
      ((affineStep c x.x1 (trace c x.x1))^[d])
          (movingCoordinates1 x) =
        movingCoordinates1 x := by
    have h := congrArg movingCoordinates1 hreturn
    rw [movingCoordinates1_iterate_oneStep1] at h
    simpa only [fiberStep] using h
  let E := BGS.Markoff.OpeningResidueClosure p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let xE : Point E := Opening.mapPoint f x
  have hparabolicE : trace (f c) xE.x1 ^ 2 ≠ 4 := by
    intro hzero
    apply hparabolic
    apply f.injective
    simpa [xE, f, Opening.mapPoint, Opening.map_trace, map_ofNat] using hzero
  have hnoncenteredE :
      centerCoordinates
          (fiberCenter (f c) xE.x1 (trace (f c) xE.x1))
          (movingCoordinates1 xE) ≠
        (0, 0) := by
    intro hzero
    apply hnoncentered
    apply Opening.mapPair_injective f f.injective
    rw [Opening.mapPair_centerCoordinates_fiberCenter]
    simpa [xE, Opening.mapPoint, Opening.mapPair,
      Opening.map_trace, movingCoordinates1] using hzero
  have hpairE :
      ((affineStep (f c) xE.x1 (trace (f c) xE.x1))^[d])
          (movingCoordinates1 xE) =
        movingCoordinates1 xE := by
    have hmap := congrArg (Opening.mapPair f) hpair
    rw [Opening.mapPair_iterate_affineStep, Opening.map_trace] at hmap
    simpa [xE, Opening.mapPoint, Opening.mapPair,
      movingCoordinates1] using hmap
  have htTwo : trace (f c) xE.x1 ≠ 2 := by
    intro htwo
    apply hparabolicE
    rw [htwo]
    norm_num
  obtain ⟨w, _hwfin, hwdvd, htrace⟩ :=
    Opening.periodic_affineStep_has_torsion_eigenvalue_orderOf_dvd
      (f c) xE.x1 (trace (f c) xE.x1)
        (movingCoordinates1 xE) htTwo hparabolicE
          hnoncenteredE d hdPos hpairE
  have hD : discriminant (trace (f c) xE.x1) ≠ 0 := by
    simpa [discriminant] using sub_ne_zero.mpr hparabolicE
  have hw : (w : E) ^ 2 ≠ 1 :=
    MiddleGame.actualFiber_eigenvalue_sq_ne_one_of_discriminant_ne_zero
      (trace (f c) xE.x1) w htrace hD
  have htraceBase :
      f (trace c x.x1) = BGS.Markoff.splitTorusTrace w := by
    simpa [xE, Opening.mapPoint, Opening.map_trace] using htrace
  have horder :
      halfStepOrder (trace c x.x1) = orderOf w := by
    rw [Opening.halfStepOrder_eq_bgsRotationOrder]
    exact rotationOrder_eq_orderOf_extensionEigenvalue
      (trace c x.x1) w hw htraceBase
  simpa [horder] using hwdvd

/-- On a nonparabolic, noncentered first-coordinate fiber, the actual
one-step point cycle has exactly the half-step matrix order. -/
theorem oneStep1Cycle_card_eq_halfStepOrder_of_nonparabolic_noncentered
    (p : ℕ) [Fact p.Prime]
    (c : ZMod p) (x : Point (ZMod p))
    (hparabolic : trace c x.x1 ^ 2 ≠ 4)
    (hnoncentered :
      centerCoordinates (fiberCenter c x.x1 (trace c x.x1))
        (movingCoordinates1 x) ≠ (0, 0)) :
    (oneStep1Cycle p c x (halfStepOrder (trace c x.x1))).card =
      halfStepOrder (trace c x.x1) := by
  classical
  let M := halfStepOrder (trace c x.x1)
  let step : Point (ZMod p) ≃ Point (ZMod p) := oneStep1Equiv c
  have hstep : ∀ y, step y = oneStep1 c y := fun y ↦ coe_oneStep1Equiv c y
  have hinjective :
      Set.InjOn (fun n : ℕ ↦ ((oneStep1 c)^[n]) x)
        (Finset.range M) := by
    intro n hn m hm heq
    have hnM : n < M := by simpa [M] using hn
    have hmM : m < M := by simpa [M] using hm
    rcases lt_trichotomy n m with hnm | hnm | hmn
    · let d := m - n
      have hdPos : 0 < d := Nat.sub_pos_of_lt hnm
      have hdM : d < M :=
        (Nat.sub_le m n).trans_lt hmM
      have hreturn : ((oneStep1 c)^[d]) x = x := by
        apply iterate_eq_self_of_le (oneStep1 c)
          (by
            intro y z hyz
            apply step.injective
            simpa [hstep] using hyz)
          x (Nat.le_of_lt hnm) heq
      have hMdvd : M ∣ d := by
        simpa [M] using
          halfStepOrder_dvd_of_oneStep1_return_of_nonparabolic_noncentered
            p c x hparabolic hnoncentered d hdPos hreturn
      exfalso
      exact (Nat.not_dvd_of_pos_of_lt hdPos hdM) hMdvd
    · exact hnm
    · let d := n - m
      have hdPos : 0 < d := Nat.sub_pos_of_lt hmn
      have hdM : d < M :=
        (Nat.sub_le n m).trans_lt hnM
      have hreturn : ((oneStep1 c)^[d]) x = x := by
        apply iterate_eq_self_of_le (oneStep1 c)
          (by
            intro y z hyz
            apply step.injective
            simpa [hstep] using hyz)
          x (Nat.le_of_lt hmn) heq.symm
      have hMdvd : M ∣ d := by
        simpa [M] using
          halfStepOrder_dvd_of_oneStep1_return_of_nonparabolic_noncentered
            p c x hparabolic hnoncentered d hdPos hreturn
      exfalso
      exact (Nat.not_dvd_of_pos_of_lt hdPos hdM) hMdvd
  calc
    (oneStep1Cycle p c x M).card =
        (Finset.range M).card := by
      exact Finset.card_image_iff.mpr hinjective
    _ = M := Finset.card_range M

private theorem two_ne_zero_zmod
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
  have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
  exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)

/-- A sufficiently large honest first-axis point cycle contains an adjacent
trace which is both candidate regular and outside the elementary trace set
of orders below `bound`. -/
theorem exists_regular_adjacent_order_ge_of_large_noncentered_cycle
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (x : Point (ZMod p)) (bound : ℕ)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (hparabolic : trace c x.x1 ^ 2 ≠ 4)
    (hnoncentered :
      centerCoordinates (fiberCenter c x.x1 (trace c x.x1))
        (movingCoordinates1 x) ≠ (0, 0))
    (hlarge :
      14 + 2 * (2 + 2 * bound ^ 2) <
        halfStepOrder (trace c x.x1)) :
    ∃ y ∈ oneStep1Cycle p c x (halfStepOrder (trace c x.x1)),
      OrderedTraceCandidateRegular c c c (trace c y.x2) ∧
        bound ≤ halfStepOrder (trace c y.x2) := by
  classical
  let M := halfStepOrder (trace c x.x1)
  let S := oneStep1Cycle p c x M
  let traceValue : Point (ZMod p) → ZMod p := fun y ↦ trace c y.x2
  let lowTraceSet := concreteLowOrderTraceSet p bound
  let low := S.filter fun y ↦ traceValue y ∈ lowTraceSet
  let irregular := S.filter fun y ↦
    Polynomial.eval (traceValue y) (safePolynomial c) = 0
  have hsolution : ∀ y ∈ S, IsSolution (coefficients c) y := by
    intro y hy
    change y ∈ oneStep1Cycle p c x M at hy
    rw [oneStep1Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    exact isSolution_iterate_oneStep1 c hx n
  have hfixed : ∀ y ∈ S, y.x1 = x.x1 := by
    intro y hy
    change y ∈ oneStep1Cycle p c x M at hy
    rw [oneStep1Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    exact iterate_oneStep1_x1 c x n
  have hfiber :
      ∀ t, (S.filter fun y ↦ traceValue y = t).card ≤ 2 := by
    intro t
    apply card_le_two_of_solution_fixed_x1_trace2
      (coefficients c)
      (S.filter fun y ↦ traceValue y = t) x.x1 t
      (by simpa only [multiplier_eq_coefficients_multiplier] using
        hmultiplier)
    · intro y hy
      exact hsolution y (Finset.mem_filter.mp hy).1
    · intro y hy
      exact hfixed y (Finset.mem_filter.mp hy).1
    · intro y hy
      simpa [traceValue, coordinateTrace2, trace, coefficients] using
        (Finset.mem_filter.mp hy).2
  have hlow :
      low.card ≤ 2 * (2 + 2 * bound ^ 2) := by
    let cover := lowTraceSet.biUnion fun t ↦
      S.filter fun y ↦ traceValue y = t
    have hsubset : low ⊆ cover := by
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      change y ∈ lowTraceSet.biUnion (fun t ↦
        S.filter fun z ↦ traceValue z = t)
      rw [Finset.mem_biUnion]
      exact ⟨traceValue y, hy'.2,
        Finset.mem_filter.mpr ⟨hy'.1, rfl⟩⟩
    calc
      low.card ≤ cover.card := Finset.card_mono hsubset
      _ ≤ lowTraceSet.card * 2 := by
        apply Finset.card_biUnion_le_card_mul
        intro t _ht
        exact hfiber t
      _ ≤ (2 + 2 * bound ^ 2) * 2 := by
        gcongr
        exact concreteLowOrderTraceSet_card_le p bound
      _ = 2 * (2 + 2 * bound ^ 2) := by omega
  have hirregular : irregular.card ≤ 14 := by
    exact card_safePolynomial_zero_le_fourteen
      c S traceValue (two_ne_zero_zmod p hpTwo) hc hfiber
  have hunion : (irregular ∪ low).card < S.card := by
    calc
      (irregular ∪ low).card ≤ irregular.card + low.card :=
        Finset.card_union_le irregular low
      _ ≤ 14 + 2 * (2 + 2 * bound ^ 2) :=
        Nat.add_le_add hirregular hlow
      _ < M := hlarge
      _ = S.card := by
        symm
        exact oneStep1Cycle_card_eq_halfStepOrder_of_nonparabolic_noncentered
          p c x hparabolic hnoncentered
  have hexists : ∃ y ∈ S, y ∉ irregular ∪ low := by
    by_contra hnone
    push Not at hnone
    have hsubset : S ⊆ irregular ∪ low := by
      intro y hy
      exact hnone y hy
    exact (Nat.not_le_of_lt hunion) (Finset.card_mono hsubset)
  obtain ⟨y, hyS, hyGood⟩ := hexists
  have hyIrregular : y ∉ irregular := fun hy ↦
    hyGood (Finset.mem_union_left low hy)
  have hyLow : y ∉ low := fun hy ↦
    hyGood (Finset.mem_union_right irregular hy)
  have hsafe :
      Polynomial.eval (traceValue y) (safePolynomial c) ≠ 0 := by
    intro hzero
    apply hyIrregular
    exact Finset.mem_filter.mpr ⟨hyS, hzero⟩
  have hregular :
      OrderedTraceCandidateRegular c c c (trace c y.x2) := by
    exact candidateRegular_of_eval_safePolynomial_ne_zero
      c (traceValue y) hc hsafe
  have horder : bound ≤ halfStepOrder (trace c y.x2) := by
    by_contra hnot
    have hsmall : halfStepOrder (trace c y.x2) < bound :=
      Nat.lt_of_not_ge hnot
    apply hyLow
    apply Finset.mem_filter.mpr
    refine ⟨hyS, ?_⟩
    apply mem_concreteLowOrderTraceSet_of_rotationOrder_lt p hpTwo
    simpa only [Opening.halfStepOrder_eq_bgsRotationOrder] using hsmall
  exact ⟨y, hyS, hregular, horder⟩

/-- Abstract fixed-first-coordinate form of the regular large-order routing
count.  It is used for the parabolic cycles, whose exact cardinalities come
from their explicit affine-line parametrizations rather than semisimple
diagonalization. -/
theorem exists_regular_axisTwo_order_ge_of_fixed_axisOne_family
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (S : Finset (Point (ZMod p))) (u : ZMod p)
    (bound : ℕ)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hsolution : ∀ y ∈ S, IsSolution (coefficients c) y)
    (hfixed : ∀ y ∈ S, y.x1 = u)
    (hlarge : 14 + 2 * (2 + 2 * bound ^ 2) < S.card) :
    ∃ y ∈ S,
      OrderedTraceCandidateRegular c c c (trace c y.x2) ∧
        bound ≤ halfStepOrder (trace c y.x2) := by
  classical
  let traceValue : Point (ZMod p) → ZMod p := fun y ↦ trace c y.x2
  let lowTraceSet := concreteLowOrderTraceSet p bound
  let low := S.filter fun y ↦ traceValue y ∈ lowTraceSet
  let irregular := S.filter fun y ↦
    Polynomial.eval (traceValue y) (safePolynomial c) = 0
  have hfiber :
      ∀ t, (S.filter fun y ↦ traceValue y = t).card ≤ 2 := by
    intro t
    apply card_le_two_of_solution_fixed_x1_trace2
      (coefficients c)
      (S.filter fun y ↦ traceValue y = t) u t
      (by simpa only [multiplier_eq_coefficients_multiplier] using
        hmultiplier)
    · intro y hy
      exact hsolution y (Finset.mem_filter.mp hy).1
    · intro y hy
      exact hfixed y (Finset.mem_filter.mp hy).1
    · intro y hy
      simpa [traceValue, coordinateTrace2, trace, coefficients] using
        (Finset.mem_filter.mp hy).2
  have hlow :
      low.card ≤ 2 * (2 + 2 * bound ^ 2) := by
    let cover := lowTraceSet.biUnion fun t ↦
      S.filter fun y ↦ traceValue y = t
    have hsubset : low ⊆ cover := by
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      change y ∈ lowTraceSet.biUnion (fun t ↦
        S.filter fun z ↦ traceValue z = t)
      rw [Finset.mem_biUnion]
      exact ⟨traceValue y, hy'.2,
        Finset.mem_filter.mpr ⟨hy'.1, rfl⟩⟩
    calc
      low.card ≤ cover.card := Finset.card_mono hsubset
      _ ≤ lowTraceSet.card * 2 := by
        apply Finset.card_biUnion_le_card_mul
        intro t _ht
        exact hfiber t
      _ ≤ (2 + 2 * bound ^ 2) * 2 := by
        gcongr
        exact concreteLowOrderTraceSet_card_le p bound
      _ = 2 * (2 + 2 * bound ^ 2) := by omega
  have hirregular : irregular.card ≤ 14 := by
    exact card_safePolynomial_zero_le_fourteen
      c S traceValue (two_ne_zero_zmod p hpTwo) hc hfiber
  have hunion : (irregular ∪ low).card < S.card := by
    calc
      (irregular ∪ low).card ≤ irregular.card + low.card :=
        Finset.card_union_le irregular low
      _ ≤ 14 + 2 * (2 + 2 * bound ^ 2) :=
        Nat.add_le_add hirregular hlow
      _ < S.card := hlarge
  have hexists : ∃ y ∈ S, y ∉ irregular ∪ low := by
    by_contra hnone
    push Not at hnone
    have hsubset : S ⊆ irregular ∪ low := by
      intro y hy
      exact hnone y hy
    exact (Nat.not_le_of_lt hunion) (Finset.card_mono hsubset)
  obtain ⟨y, hyS, hyGood⟩ := hexists
  have hyIrregular : y ∉ irregular := fun hy ↦
    hyGood (Finset.mem_union_left low hy)
  have hyLow : y ∉ low := fun hy ↦
    hyGood (Finset.mem_union_right irregular hy)
  have hsafe :
      Polynomial.eval (traceValue y) (safePolynomial c) ≠ 0 := by
    intro hzero
    apply hyIrregular
    exact Finset.mem_filter.mpr ⟨hyS, hzero⟩
  have hregular :
      OrderedTraceCandidateRegular c c c (trace c y.x2) :=
    candidateRegular_of_eval_safePolynomial_ne_zero
      c (traceValue y) hc hsafe
  have horder : bound ≤ halfStepOrder (trace c y.x2) := by
    by_contra hnot
    have hsmall : halfStepOrder (trace c y.x2) < bound :=
      Nat.lt_of_not_ge hnot
    apply hyLow
    apply Finset.mem_filter.mpr
    refine ⟨hyS, ?_⟩
    apply mem_concreteLowOrderTraceSet_of_rotationOrder_lt p hpTwo
    simpa only [Opening.halfStepOrder_eq_bgsRotationOrder] using hsmall
  exact ⟨y, hyS, hregular, horder⟩

/-- A trace-`2` parabolic first-axis cycle routes to a candidate-regular
adjacent trace of order at least `bound`. -/
theorem exists_regular_adjacent_order_ge_of_oneStep1_trace_eq_two
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (x : Point (ZMod p)) (bound : ℕ)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (htrace : trace c x.x1 = 2)
    (hlarge : 14 + 2 * (2 + 2 * bound ^ 2) < p) :
    ∃ y ∈ oneStep1Cycle p c x p,
      OrderedTraceCandidateRegular c c c (trace c y.x2) ∧
        bound ≤ halfStepOrder (trace c y.x2) := by
  apply exists_regular_axisTwo_order_ge_of_fixed_axisOne_family
    p hpTwo c (oneStep1Cycle p c x p) x.x1 bound
      hmultiplier hc
  · intro y hy
    rw [oneStep1Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    exact isSolution_iterate_oneStep1 c hx n
  · intro y hy
    rw [oneStep1Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    exact iterate_oneStep1_x1 c x n
  · simpa [oneStep1Cycle_card_of_trace_eq_two
      p hpTwo c x hc htrace hx] using hlarge

/-- A trace-`-2` parabolic first-axis cycle routes to a candidate-regular
adjacent trace of order at least `bound`. -/
theorem exists_regular_adjacent_order_ge_of_oneStep1_trace_eq_neg_two
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c : ZMod p) (x : Point (ZMod p)) (bound : ℕ)
    (hmultiplier : multiplier c ≠ 0)
    (hc : c ^ 2 ≠ 4)
    (hx : IsSolution (coefficients c) x)
    (htrace : trace c x.x1 = -2)
    (hlarge : 14 + 2 * (2 + 2 * bound ^ 2) < 2 * p) :
    ∃ y ∈ oneStep1Cycle p c x (2 * p),
      OrderedTraceCandidateRegular c c c (trace c y.x2) ∧
        bound ≤ halfStepOrder (trace c y.x2) := by
  apply exists_regular_axisTwo_order_ge_of_fixed_axisOne_family
    p hpTwo c (oneStep1Cycle p c x (2 * p)) x.x1 bound
      hmultiplier hc
  · intro y hy
    rw [oneStep1Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    exact isSolution_iterate_oneStep1 c hx n
  · intro y hy
    rw [oneStep1Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    exact iterate_oneStep1_x1 c x n
  · simpa [oneStep1Cycle_card_of_trace_eq_neg_two
      p hpTwo c x hc htrace hx] using hlarge

end

end GenMarkoff.Symmetric.Assembly
