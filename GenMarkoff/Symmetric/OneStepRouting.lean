import GenMarkoff.Symmetric.ExceptionalRouting
import GenMarkoff.Symmetric.OneStepParabolic

/-!
# Routing from a one-step fiber cycle

The degree-seven exceptional polynomial excludes at most fourteen points on
any fixed-coordinate fiber.  This file specializes that abstract count to
the three actual one-step cycles.  It is the formal bridge from a sufficiently
long one-step cycle to a shifted-cover-regular adjacent trace.
-/

namespace GenMarkoff.Symmetric

universe u

section Ring

variable {R : Type u} [CommRing R]

theorem isSolution_iterate_oneStep1
    (c : R) {x : Point R} (hx : IsSolution (coefficients c) x) (n : ℕ) :
    IsSolution (coefficients c) (((oneStep1 c)^[n]) x) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (isSolution_oneStep1 c _).2 ih

theorem isSolution_iterate_oneStep2
    (c : R) {x : Point R} (hx : IsSolution (coefficients c) x) (n : ℕ) :
    IsSolution (coefficients c) (((oneStep2 c)^[n]) x) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (isSolution_oneStep2 c _).2 ih

theorem isSolution_iterate_oneStep3
    (c : R) {x : Point R} (hx : IsSolution (coefficients c) x) (n : ℕ) :
    IsSolution (coefficients c) (((oneStep3 c)^[n]) x) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (isSolution_oneStep3 c _).2 ih

@[simp]
theorem iterate_oneStep2_x2 (c : R) (x : Point R) (n : ℕ) :
    (((oneStep2 c)^[n]) x).x2 = x.x2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change (((oneStep2 c)^[n]) x).x2 = x.x2
      exact ih

@[simp]
theorem iterate_oneStep3_x3 (c : R) (x : Point R) (n : ℕ) :
    (((oneStep3 c)^[n]) x).x3 = x.x3 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change (((oneStep3 c)^[n]) x).x3 = x.x3
      exact ih

end Ring

section PrimeField

variable (p : ℕ) [Fact p.Prime]

private theorem two_ne_zero_zmod_of_ne_two (hpTwo : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
  have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
  exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)

/-- A first-axis one-step cycle with more than fourteen points contains a
point whose second-coordinate trace satisfies every shifted-cover regularity
condition. -/
theorem exists_axisTwoCandidateRegular_in_oneStep1Cycle
    (c : ZMod p) (x : Point (ZMod p)) (N : ℕ)
    (hmultiplier : multiplier c ≠ 0) (htwo : (2 : ZMod p) ≠ 0)
    (hc : c ^ 2 ≠ 4) (hx : IsSolution (coefficients c) x)
    (hcard : 14 < (oneStep1Cycle p c x N).card) :
    ∃ y ∈ oneStep1Cycle p c x N,
      OrderedTraceCandidateRegular c c c
        (coordinateTrace2 (coefficients c) y) := by
  apply exists_axisOneFiber_axisTwoCandidateRegular_of_fourteen_lt_card
    c (oneStep1Cycle p c x N) x.x1
      (by simpa using hmultiplier) htwo hc
  · intro y hy
    rw [oneStep1Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    exact isSolution_iterate_oneStep1 c hx n
  · intro y hy
    rw [oneStep1Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    exact iterate_oneStep1_x1 c x n
  · exact hcard

/-- Cyclic second-axis version of the one-step routing theorem. -/
theorem exists_axisThreeCandidateRegular_in_oneStep2Cycle
    (c : ZMod p) (x : Point (ZMod p)) (N : ℕ)
    (hmultiplier : multiplier c ≠ 0) (htwo : (2 : ZMod p) ≠ 0)
    (hc : c ^ 2 ≠ 4) (hx : IsSolution (coefficients c) x)
    (hcard : 14 < (oneStep2Cycle p c x N).card) :
    ∃ y ∈ oneStep2Cycle p c x N,
      OrderedTraceCandidateRegular c c c
        (coordinateTrace3 (coefficients c) y) := by
  apply exists_axisTwoFiber_axisThreeCandidateRegular_of_fourteen_lt_card
    c (oneStep2Cycle p c x N) x.x2
      (by simpa using hmultiplier) htwo hc
  · intro y hy
    rw [oneStep2Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    exact isSolution_iterate_oneStep2 c hx n
  · intro y hy
    rw [oneStep2Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    exact iterate_oneStep2_x2 c x n
  · exact hcard

/-- Cyclic third-axis version of the one-step routing theorem. -/
theorem exists_axisOneCandidateRegular_in_oneStep3Cycle
    (c : ZMod p) (x : Point (ZMod p)) (N : ℕ)
    (hmultiplier : multiplier c ≠ 0) (htwo : (2 : ZMod p) ≠ 0)
    (hc : c ^ 2 ≠ 4) (hx : IsSolution (coefficients c) x)
    (hcard : 14 < (oneStep3Cycle p c x N).card) :
    ∃ y ∈ oneStep3Cycle p c x N,
      OrderedTraceCandidateRegular c c c
        (coordinateTrace1 (coefficients c) y) := by
  apply exists_axisThreeFiber_axisOneCandidateRegular_of_fourteen_lt_card
    c (oneStep3Cycle p c x N) x.x3
      (by simpa using hmultiplier) htwo hc
  · intro y hy
    rw [oneStep3Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    exact isSolution_iterate_oneStep3 c hx n
  · intro y hy
    rw [oneStep3Cycle, Finset.mem_image] at hy
    obtain ⟨n, _hn, rfl⟩ := hy
    exact iterate_oneStep3_x3 c x n
  · exact hcard

/-- A trace `2` first-axis parabolic cycle routes to a regular adjacent trace
as soon as `p > 14`. -/
theorem exists_axisTwoCandidateRegular_of_oneStep1_trace_eq_two
    (hpLarge : 14 < p) (c : ZMod p) (x : Point (ZMod p))
    (hmultiplier : multiplier c ≠ 0) (hc : c ^ 2 ≠ 4)
    (htrace : trace c x.x1 = 2)
    (hx : IsSolution (coefficients c) x) :
    ∃ y ∈ oneStep1Cycle p c x p,
      OrderedTraceCandidateRegular c c c
        (coordinateTrace2 (coefficients c) y) := by
  have hpTwo : p ≠ 2 := by omega
  apply exists_axisTwoCandidateRegular_in_oneStep1Cycle p c x p
    hmultiplier (two_ne_zero_zmod_of_ne_two p hpTwo) hc hx
  rw [oneStep1Cycle_card_of_trace_eq_two p hpTwo c x hc htrace hx]
  exact hpLarge

/-- A trace `-2` first-axis parabolic cycle routes to a regular adjacent
trace as soon as `p > 14`. -/
theorem exists_axisTwoCandidateRegular_of_oneStep1_trace_eq_neg_two
    (hpLarge : 14 < p) (c : ZMod p) (x : Point (ZMod p))
    (hmultiplier : multiplier c ≠ 0) (hc : c ^ 2 ≠ 4)
    (htrace : trace c x.x1 = -2)
    (hx : IsSolution (coefficients c) x) :
    ∃ y ∈ oneStep1Cycle p c x (2 * p),
      OrderedTraceCandidateRegular c c c
        (coordinateTrace2 (coefficients c) y) := by
  have hpTwo : p ≠ 2 := by omega
  apply exists_axisTwoCandidateRegular_in_oneStep1Cycle p c x (2 * p)
    hmultiplier (two_ne_zero_zmod_of_ne_two p hpTwo) hc hx
  rw [oneStep1Cycle_card_of_trace_eq_neg_two p hpTwo c x hc htrace hx]
  omega

end PrimeField

end GenMarkoff.Symmetric
