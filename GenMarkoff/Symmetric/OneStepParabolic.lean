import GenMarkoff.Symmetric.OneStepAction
import GenMarkoff.Symmetric.ParabolicCyclic

/-!
# Parabolic fibers for the symmetric one-step action

When all three coefficients are equal, the two Vieta factors occurring in a
rotation induce the same affine map on the corresponding moving-coordinate
fiber.  It is therefore useful to retain this affine half-step as a generator.

The distinction from `Parabolic.lean` matters at trace `-2`: the squared
rotation has period `p`, whereas the affine one-step action has period `2p`.
At trace `2`, both actions have period `p` over an odd prime field.
-/

namespace GenMarkoff.Symmetric

universe u

section Ring

variable {R : Type u} [CommRing R]

@[simp]
theorem oneStep1_x1 (c : R) (x : Point R) :
    (oneStep1 c x).x1 = x.x1 := by
  rfl

@[simp]
theorem iterate_oneStep1_x1 (c : R) (x : Point R) (n : ℕ) :
    (((oneStep1 c)^[n]) x).x1 = x.x1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', oneStep1_x1, ih]

/-- Moving coordinates intertwine every iterate of the global one-step map
with the corresponding iterate of the affine fiber step. -/
theorem movingCoordinates1_iterate_oneStep1
    (c : R) (x : Point R) (n : ℕ) :
    movingCoordinates1 (((oneStep1 c)^[n]) x) =
      ((fiberStep c x.x1)^[n]) (movingCoordinates1 x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', movingCoordinates1_oneStep1,
        iterate_oneStep1_x1, ih, Function.iterate_succ_apply']

/-- Cyclic relabeling conjugates the second one-step generator to the first. -/
theorem cycleLeftEquiv_oneStep2 (c : R) (x : Point R) :
    cycleLeftEquiv (oneStep2 c x) =
      oneStep1 c (cycleLeftEquiv x) := by
  ext <;>
    simp [cycleLeftEquiv, oneStep1, oneStep2, swap23, swap13,
      vieta2, vieta3, coefficients, Coefficients.multiplier]

/-- Cyclic relabeling conjugates the third one-step generator to the first. -/
theorem cycleRightEquiv_oneStep3 (c : R) (x : Point R) :
    cycleRightEquiv (oneStep3 c x) =
      oneStep1 c (cycleRightEquiv x) := by
  ext <;>
    simp [cycleRightEquiv, cycleLeftEquiv, oneStep1, oneStep3,
      swap23, swap12, vieta1, vieta2, coefficients,
      Coefficients.multiplier]

theorem cycleLeftEquiv_iterate_oneStep2
    (n : ℕ) (c : R) (x : Point R) :
    cycleLeftEquiv (((oneStep2 c)^[n]) x) =
      ((oneStep1 c)^[n]) (cycleLeftEquiv x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        cycleLeftEquiv_oneStep2, ih]

theorem cycleRightEquiv_iterate_oneStep3
    (n : ℕ) (c : R) (x : Point R) :
    cycleRightEquiv (((oneStep3 c)^[n]) x) =
      ((oneStep1 c)^[n]) (cycleRightEquiv x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        cycleRightEquiv_oneStep3, ih]

/-- The affine fiber step is injective over any commutative ring. -/
theorem affineStep_injective (c u t : R) :
    Function.Injective (affineStep c u t) := by
  rintro ⟨y, z⟩ ⟨y', z'⟩ h
  simp only [affineStep, Prod.mk.injEq] at h
  rcases h with ⟨hz, hsecond⟩
  subst z'
  have hy : y = y' := by
    linear_combination -hsecond
  apply Prod.ext
  · exact hy
  · rfl

/-- On the trace `2` fiber, the moving-coordinate difference changes by
`-c*u` at each affine one-step. -/
theorem movingDifference_iterate_affineStep_two
    (c u y z : R) (n : ℕ) :
    let v := ((affineStep c u 2)^[n]) (y, z)
    movingDifference v.1 v.2 =
      movingDifference y z - (n : R) * (c * u) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp only [affineStep, movingDifference]
      change movingDifference
          (((affineStep c u 2)^[n]) (y, z)).1
          (((affineStep c u 2)^[n]) (y, z)).2 = _ at ih
      calc
        2 * (((affineStep c u 2)^[n]) (y, z)).2 -
              (((affineStep c u 2)^[n]) (y, z)).1 - c * u -
              (((affineStep c u 2)^[n]) (y, z)).2 =
            movingDifference
                (((affineStep c u 2)^[n]) (y, z)).1
                (((affineStep c u 2)^[n]) (y, z)).2 - c * u := by
          simp only [movingDifference]
          ring
        _ = movingDifference y z - (n : R) * (c * u) - c * u := by
          rw [ih]
        _ = movingDifference y z - ((n + 1 : ℕ) : R) * (c * u) := by
          push_cast
          ring

/-- If the affine translation vanishes, the trace `2` half-step is an ordinary
translation along the diagonal. -/
theorem iterate_affineStep_two_of_cu_eq_zero
    (c u y z : R) (hcu : c * u = 0) (n : ℕ) :
    ((affineStep c u 2)^[n]) (y, z) =
      (y + (n : R) * movingDifference y z,
        z + (n : R) * movingDifference y z) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [affineStep, movingDifference]
      simp only [Nat.cast_succ]
      rw [hcu]
      apply Prod.ext <;> simp only <;> ring

/-- Explicit even iterates on the trace `-2` fiber. -/
theorem iterate_affineStep_neg_two_even
    (c u y z : R) (n : ℕ) :
    ((affineStep c u (-2))^[2 * n]) (y, z) =
      (y + (n : R) * negTwoIncrement c u y z,
        z - (n : R) * negTwoIncrement c u y z) := by
  rw [Function.iterate_mul]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      change affineStep c u (-2)
          (affineStep c u (-2)
            (y + (n : R) * negTwoIncrement c u y z,
              z - (n : R) * negTwoIncrement c u y z)) = _
      rw [affineStep_sq_neg_two]
      apply Prod.ext <;>
        simp [negTwoIncrement, Nat.cast_succ] <;>
        ring

/-- Explicit odd iterates on the trace `-2` fiber. -/
theorem iterate_affineStep_neg_two_odd
    (c u y z : R) (n : ℕ) :
    ((affineStep c u (-2))^[2 * n + 1]) (y, z) =
      affineStep c u (-2)
        (y + (n : R) * negTwoIncrement c u y z,
          z - (n : R) * negTwoIncrement c u y z) := by
  rw [Function.iterate_succ_apply', iterate_affineStep_neg_two_even]

/-- Even and odd trace `-2` iterates cannot meet when the parabolic
translation increment is nonzero. -/
theorem iterate_affineStep_neg_two_even_ne_odd
    (c u y z : R) (hincrement : negTwoIncrement c u y z ≠ 0)
    (n m : ℕ) :
    ((affineStep c u (-2))^[2 * n]) (y, z) ≠
      ((affineStep c u (-2))^[2 * m + 1]) (y, z) := by
  intro heq
  rw [iterate_affineStep_neg_two_even,
    iterate_affineStep_neg_two_odd] at heq
  have hsum := congrArg (fun v : R × R => v.1 + v.2) heq
  simp only [affineStep] at hsum
  apply hincrement
  rw [negTwoIncrement]
  linear_combination -hsum

end Ring

section PrimeField

variable (p : ℕ) [Fact p.Prime]

/-- The canonical finite segment of an affine one-step fiber orbit. -/
def affineStepCycle (c u t : ZMod p) (v : ZMod p × ZMod p) (N : ℕ) :
    Finset (ZMod p × ZMod p) :=
  (Finset.range N).image fun n => ((affineStep c u t)^[n]) v

/-- The canonical finite segment of the global first one-step orbit. -/
def oneStep1Cycle (c : ZMod p) (x : Point (ZMod p)) (N : ℕ) :
    Finset (Point (ZMod p)) :=
  (Finset.range N).image fun n => ((oneStep1 c)^[n]) x

/-- The canonical finite segment of the global second one-step orbit. -/
def oneStep2Cycle (c : ZMod p) (x : Point (ZMod p)) (N : ℕ) :
    Finset (Point (ZMod p)) :=
  (Finset.range N).image fun n => ((oneStep2 c)^[n]) x

/-- The canonical finite segment of the global third one-step orbit. -/
def oneStep3Cycle (c : ZMod p) (x : Point (ZMod p)) (N : ℕ) :
    Finset (Point (ZMod p)) :=
  (Finset.range N).image fun n => ((oneStep3 c)^[n]) x

omit [Fact p.Prime] in
theorem image_cycleLeftEquiv_oneStep2Cycle
    (c : ZMod p) (x : Point (ZMod p)) (N : ℕ) :
    (oneStep2Cycle p c x N).image cycleLeftEquiv =
      oneStep1Cycle p c (cycleLeftEquiv x) N := by
  classical
  rw [oneStep2Cycle, oneStep1Cycle, Finset.image_image]
  apply Finset.image_congr
  intro n _hn
  exact cycleLeftEquiv_iterate_oneStep2 n c x

omit [Fact p.Prime] in
theorem image_cycleRightEquiv_oneStep3Cycle
    (c : ZMod p) (x : Point (ZMod p)) (N : ℕ) :
    (oneStep3Cycle p c x N).image cycleRightEquiv =
      oneStep1Cycle p c (cycleRightEquiv x) N := by
  classical
  rw [oneStep3Cycle, oneStep1Cycle, Finset.image_image]
  apply Finset.image_congr
  intro n _hn
  exact cycleRightEquiv_iterate_oneStep3 n c x

private theorem natCast_injective_on_range
    {n m : ℕ} (hn : n < p) (hm : m < p)
    (hcast : (n : ZMod p) = (m : ZMod p)) : n = m := by
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  simpa [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] using hcast

private theorem two_ne_zero_zmod_oneStep (hpTwo : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
  have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
  exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)

/-- At trace `2`, the affine one-step orbit has exactly `p` points. -/
theorem affineStepCycle_card_of_trace_eq_two
    (_hpTwo : p ≠ 2) (c u y z : ZMod p)
    (hc : c ^ 2 ≠ 4) (htrace : trace c u = 2)
    (hsolution : IsSolution (coefficients c) ⟨u, y, z⟩) :
    (affineStepCycle p c u 2 (y, z) p).card = p := by
  classical
  have hnonfixed : c * u ≠ 0 ∨ movingDifference y z ≠ 0 :=
    posTwo_cu_or_difference_ne_zero_of_isSolution
      c u y z hc htrace hsolution
  have hinjective : Set.InjOn
      (fun n : ℕ => ((affineStep c u 2)^[n]) (y, z))
      (Finset.range p) := by
    intro n hn m hm heq
    have hnlt : n < p := by simpa using hn
    have hmlt : m < p := by simpa using hm
    apply natCast_injective_on_range p hnlt hmlt
    by_cases hcu : c * u = 0
    · have hdifference : movingDifference y z ≠ 0 := by
        rcases hnonfixed with hcu' | hdifference
        · exact (hcu' hcu).elim
        · exact hdifference
      change ((affineStep c u 2)^[n]) (y, z) =
        ((affineStep c u 2)^[m]) (y, z) at heq
      rw [iterate_affineStep_two_of_cu_eq_zero c u y z hcu,
        iterate_affineStep_two_of_cu_eq_zero c u y z hcu] at heq
      have hfirst := congrArg Prod.fst heq
      simp only at hfirst
      exact mul_right_cancel₀ hdifference (add_left_cancel hfirst)
    · have hdifference := congrArg
          (fun v : ZMod p × ZMod p => movingDifference v.1 v.2) heq
      rw [movingDifference_iterate_affineStep_two,
        movingDifference_iterate_affineStep_two] at hdifference
      have hproduct : (n : ZMod p) * (c * u) =
          (m : ZMod p) * (c * u) := by
        linear_combination -hdifference
      exact mul_right_cancel₀ hcu hproduct
  calc
    (affineStepCycle p c u 2 (y, z) p).card =
        (Finset.range p).card := Finset.card_image_iff.mpr hinjective
    _ = p := Finset.card_range p

/-- At trace `-2`, the affine one-step orbit has exactly `2p` points.  Squaring
this action loses the parity and leaves the `p`-point cycle proved in
`Parabolic.lean`. -/
theorem affineStepCycle_card_of_trace_eq_neg_two
    (hpTwo : p ≠ 2) (c u y z : ZMod p)
    (hc : c ^ 2 ≠ 4) (htrace : trace c u = -2)
    (hsolution : IsSolution (coefficients c) ⟨u, y, z⟩) :
    (affineStepCycle p c u (-2) (y, z) (2 * p)).card = 2 * p := by
  classical
  have hincrement : negTwoIncrement c u y z ≠ 0 :=
    negTwoIncrement_ne_zero_of_isSolution c u y z
      (two_ne_zero_zmod_oneStep p hpTwo) hc htrace hsolution
  have hinjective : Set.InjOn
      (fun n : ℕ => ((affineStep c u (-2))^[n]) (y, z))
      (Finset.range (2 * p)) := by
    intro n hn m hm heq
    have hnlt : n < 2 * p := by simpa using hn
    have hmlt : m < 2 * p := by simpa using hm
    rcases n.even_or_odd' with ⟨k, hk | hk⟩
    · rcases m.even_or_odd' with ⟨l, hl | hl⟩
      · subst n
        subst m
        have hklt : k < p := by omega
        have hllt : l < p := by omega
        change ((affineStep c u (-2))^[2 * k]) (y, z) =
          ((affineStep c u (-2))^[2 * l]) (y, z) at heq
        rw [iterate_affineStep_neg_two_even,
          iterate_affineStep_neg_two_even] at heq
        have hfirst := congrArg Prod.fst heq
        simp only at hfirst
        have hcast : (k : ZMod p) = (l : ZMod p) := by
          apply mul_right_cancel₀ hincrement
          exact add_left_cancel hfirst
        have hkl := natCast_injective_on_range p hklt hllt hcast
        omega
      · subst n
        subst m
        exact (iterate_affineStep_neg_two_even_ne_odd
          c u y z hincrement k l heq).elim
    · rcases m.even_or_odd' with ⟨l, hl | hl⟩
      · subst n
        subst m
        exact (iterate_affineStep_neg_two_even_ne_odd
          c u y z hincrement l k heq.symm).elim
      · subst n
        subst m
        have hklt : k < p := by omega
        have hllt : l < p := by omega
        change ((affineStep c u (-2))^[2 * k + 1]) (y, z) =
          ((affineStep c u (-2))^[2 * l + 1]) (y, z) at heq
        rw [iterate_affineStep_neg_two_odd,
          iterate_affineStep_neg_two_odd] at heq
        have heven := affineStep_injective c u (-2) heq
        have hfirst := congrArg Prod.fst heven
        simp only at hfirst
        have hcast : (k : ZMod p) = (l : ZMod p) := by
          apply mul_right_cancel₀ hincrement
          exact add_left_cancel hfirst
        have hkl := natCast_injective_on_range p hklt hllt hcast
        omega
  calc
    (affineStepCycle p c u (-2) (y, z) (2 * p)).card =
        (Finset.range (2 * p)).card :=
      Finset.card_image_iff.mpr hinjective
    _ = 2 * p := Finset.card_range (2 * p)

/-- Global axis-one form of the `p`-point trace `2` one-step cycle. -/
theorem oneStep1Cycle_card_of_trace_eq_two
    (hpTwo : p ≠ 2) (c : ZMod p) (x : Point (ZMod p))
    (hc : c ^ 2 ≠ 4) (htrace : trace c x.x1 = 2)
    (hsolution : IsSolution (coefficients c) x) :
    (oneStep1Cycle p c x p).card = p := by
  classical
  have hpairCard := affineStepCycle_card_of_trace_eq_two p hpTwo
    c x.x1 x.x2 x.x3 hc htrace hsolution
  have hpairInj : Set.InjOn
      (fun n : ℕ => ((affineStep c x.x1 2)^[n]) (x.x2, x.x3))
      (Finset.range p) := by
    apply Finset.card_image_iff.mp
    simpa only [affineStepCycle, Finset.card_range] using hpairCard
  calc
    (oneStep1Cycle p c x p).card = (Finset.range p).card := by
      apply Finset.card_image_iff.mpr
      intro n hn m hm heq
      apply hpairInj hn hm
      have hmoving := congrArg movingCoordinates1 heq
      rw [movingCoordinates1_iterate_oneStep1,
        movingCoordinates1_iterate_oneStep1] at hmoving
      simpa only [fiberStep, htrace, movingCoordinates1] using hmoving
    _ = p := Finset.card_range p

/-- Global axis-one form of the `2p`-point trace `-2` one-step cycle. -/
theorem oneStep1Cycle_card_of_trace_eq_neg_two
    (hpTwo : p ≠ 2) (c : ZMod p) (x : Point (ZMod p))
    (hc : c ^ 2 ≠ 4) (htrace : trace c x.x1 = -2)
    (hsolution : IsSolution (coefficients c) x) :
    (oneStep1Cycle p c x (2 * p)).card = 2 * p := by
  classical
  have hpairCard := affineStepCycle_card_of_trace_eq_neg_two p hpTwo
    c x.x1 x.x2 x.x3 hc htrace hsolution
  have hpairInj : Set.InjOn
      (fun n : ℕ => ((affineStep c x.x1 (-2))^[n]) (x.x2, x.x3))
      (Finset.range (2 * p)) := by
    apply Finset.card_image_iff.mp
    simpa only [affineStepCycle, Finset.card_range] using hpairCard
  calc
    (oneStep1Cycle p c x (2 * p)).card =
        (Finset.range (2 * p)).card := by
      apply Finset.card_image_iff.mpr
      intro n hn m hm heq
      apply hpairInj hn hm
      have hmoving := congrArg movingCoordinates1 heq
      rw [movingCoordinates1_iterate_oneStep1,
        movingCoordinates1_iterate_oneStep1] at hmoving
      simpa only [fiberStep, htrace, movingCoordinates1] using hmoving
    _ = 2 * p := Finset.card_range (2 * p)

omit [Fact p.Prime] in
private theorem card_image_point_equiv
    (s : Finset (Point (ZMod p)))
    (e : Point (ZMod p) ≃ Point (ZMod p)) :
    (s.image e).card = s.card := by
  apply Finset.card_image_iff.mpr
  intro a _ha b _hb hab
  exact e.injective hab

/-- Cyclic axis-two form of the `p`-point trace `2` one-step cycle. -/
theorem oneStep2Cycle_card_of_trace_eq_two
    (hpTwo : p ≠ 2) (c : ZMod p) (x : Point (ZMod p))
    (hc : c ^ 2 ≠ 4) (htrace : trace c x.x2 = 2)
    (hsolution : IsSolution (coefficients c) x) :
    (oneStep2Cycle p c x p).card = p := by
  rw [← card_image_point_equiv p (oneStep2Cycle p c x p)
    cycleLeftEquiv, image_cycleLeftEquiv_oneStep2Cycle]
  apply oneStep1Cycle_card_of_trace_eq_two p hpTwo c
    (cycleLeftEquiv x) hc
  · simpa using htrace
  · exact (isSolution_cycleLeftEquiv c x).2 hsolution

/-- Cyclic axis-two form of the `2p`-point trace `-2` one-step cycle. -/
theorem oneStep2Cycle_card_of_trace_eq_neg_two
    (hpTwo : p ≠ 2) (c : ZMod p) (x : Point (ZMod p))
    (hc : c ^ 2 ≠ 4) (htrace : trace c x.x2 = -2)
    (hsolution : IsSolution (coefficients c) x) :
    (oneStep2Cycle p c x (2 * p)).card = 2 * p := by
  rw [← card_image_point_equiv p (oneStep2Cycle p c x (2 * p))
    cycleLeftEquiv, image_cycleLeftEquiv_oneStep2Cycle]
  apply oneStep1Cycle_card_of_trace_eq_neg_two p hpTwo c
    (cycleLeftEquiv x) hc
  · simpa using htrace
  · exact (isSolution_cycleLeftEquiv c x).2 hsolution

/-- Cyclic axis-three form of the `p`-point trace `2` one-step cycle. -/
theorem oneStep3Cycle_card_of_trace_eq_two
    (hpTwo : p ≠ 2) (c : ZMod p) (x : Point (ZMod p))
    (hc : c ^ 2 ≠ 4) (htrace : trace c x.x3 = 2)
    (hsolution : IsSolution (coefficients c) x) :
    (oneStep3Cycle p c x p).card = p := by
  rw [← card_image_point_equiv p (oneStep3Cycle p c x p)
    cycleRightEquiv, image_cycleRightEquiv_oneStep3Cycle]
  apply oneStep1Cycle_card_of_trace_eq_two p hpTwo c
    (cycleRightEquiv x) hc
  · simpa using htrace
  · exact (isSolution_cycleRightEquiv c x).2 hsolution

/-- Cyclic axis-three form of the `2p`-point trace `-2` one-step cycle. -/
theorem oneStep3Cycle_card_of_trace_eq_neg_two
    (hpTwo : p ≠ 2) (c : ZMod p) (x : Point (ZMod p))
    (hc : c ^ 2 ≠ 4) (htrace : trace c x.x3 = -2)
    (hsolution : IsSolution (coefficients c) x) :
    (oneStep3Cycle p c x (2 * p)).card = 2 * p := by
  rw [← card_image_point_equiv p (oneStep3Cycle p c x (2 * p))
    cycleRightEquiv, image_cycleRightEquiv_oneStep3Cycle]
  apply oneStep1Cycle_card_of_trace_eq_neg_two p hpTwo c
    (cycleRightEquiv x) hc
  · simpa using htrace
  · exact (isSolution_cycleRightEquiv c x).2 hsolution

end PrimeField

end GenMarkoff.Symmetric
