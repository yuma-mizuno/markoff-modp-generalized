import GenMarkoff.General.ParabolicSurface
import GenMarkoff.TraceCurve.ExceptionalRouting

/-!
# Routing from general parabolic rotation cycles

Every nondegenerate parabolic rotation cycle has `p` points.  For `p > 20`,
the six ordered exceptional-routing theorems therefore find a
candidate-regular adjacent trace on the same actual rotation cycle.  The
coefficient order is kept explicit throughout.
-/

namespace GenMarkoff.General

open Function

/-- The first `n` iterates of a self-map as a finite set. -/
def orbitSegment {α : Type*} [DecidableEq α]
    (f : α → α) (n : ℕ) (x : α) : Finset α :=
  (Finset.range n).image fun k => (f^[k]) x

theorem orbitSegment_card_of_minimalPeriod_eq
    {α : Type*} [DecidableEq α] (f : α → α) (n : ℕ) (x : α)
    (hperiod : minimalPeriod f x = n) :
    (orbitSegment f n x).card = n := by
  rw [orbitSegment]
  calc
    ((Finset.range n).image fun k => (f^[k]) x).card =
        (Finset.range n).card := by
      apply Finset.card_image_iff.mpr
      intro i hi j hj hij
      have hi' : i < minimalPeriod f x := by
        rw [hperiod]
        simpa using hi
      have hj' : j < minimalPeriod f x := by
        rw [hperiod]
        simpa using hj
      apply (iterate_eq_iterate_iff_of_lt_minimalPeriod
        (f := f) (x := x) hi' hj').mp
      exact hij
    _ = n := Finset.card_range n

theorem isSolution_iterate_rotation1
    {R : Type*} [CommRing R] (a : Coefficients R) (x : Point R)
    (hx : IsSolution a x) (n : ℕ) :
    IsSolution a (((rotation1 a)^[n]) x) := by
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (isSolution_rotation1 a _).2 ih

theorem isSolution_iterate_rotation2
    {R : Type*} [CommRing R] (a : Coefficients R) (x : Point R)
    (hx : IsSolution a x) (n : ℕ) :
    IsSolution a (((rotation2 a)^[n]) x) := by
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (isSolution_rotation2 a _).2 ih

theorem isSolution_iterate_rotation3
    {R : Type*} [CommRing R] (a : Coefficients R) (x : Point R)
    (hx : IsSolution a x) (n : ℕ) :
    IsSolution a (((rotation3 a)^[n]) x) := by
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (isSolution_rotation3 a _).2 ih

section PrimeField

variable (p : ℕ) [Fact p.Prime]

private theorem two_ne_zero_zmod (hpTwo : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
  have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
  exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)

theorem exists_axisOne_rotation_iterate_axisTwoCandidateRegular
    (hpTwenty : 20 < p) (a : Coefficients (ZMod p))
    (x : Point (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (ha2 : a.a2 ^ 2 ≠ 4) (ha3 : a.a3 ^ 2 ≠ 4)
    (hx : IsSolution a x)
    (hperiod : minimalPeriod (rotation1 a) x = p) :
    ∃ n < p,
      OrderedTraceCandidateRegular a.a2 a.a3 a.a1
        (coordinateTrace2 a (((rotation1 a)^[n]) x)) := by
  classical
  let S := orbitSegment (rotation1 a) p x
  have hcard : 20 < S.card := by
    rw [orbitSegment_card_of_minimalPeriod_eq _ _ _ hperiod]
    exact hpTwenty
  obtain ⟨y, hyS, hy⟩ :=
    exists_axisOneFiber_axisTwoCandidateRegular_of_twenty_lt_card
      a S x.x1 hmultiplier (two_ne_zero_zmod p (by omega))
        ha2 ha3
        (by
          intro y hyMem
          rcases Finset.mem_image.mp hyMem with ⟨n, _hn, rfl⟩
          exact isSolution_iterate_rotation1 a x hx n)
        (by
          intro y hyMem
          rcases Finset.mem_image.mp hyMem with ⟨n, _hn, rfl⟩
          exact iterate_rotation1_firstCoordinate a x n)
        hcard
  rcases Finset.mem_image.mp hyS with ⟨n, hn, rfl⟩
  exact ⟨n, by simpa using hn, hy⟩

theorem exists_axisOne_rotation_iterate_axisThreeCandidateRegular
    (hpTwenty : 20 < p) (a : Coefficients (ZMod p))
    (x : Point (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (ha3 : a.a3 ^ 2 ≠ 4) (ha2 : a.a2 ^ 2 ≠ 4)
    (hx : IsSolution a x)
    (hperiod : minimalPeriod (rotation1 a) x = p) :
    ∃ n < p,
      OrderedTraceCandidateRegular a.a3 a.a2 a.a1
        (coordinateTrace3 a (((rotation1 a)^[n]) x)) := by
  classical
  let S := orbitSegment (rotation1 a) p x
  have hcard : 20 < S.card := by
    rw [orbitSegment_card_of_minimalPeriod_eq _ _ _ hperiod]
    exact hpTwenty
  obtain ⟨y, hyS, hy⟩ :=
    exists_axisOneFiber_axisThreeCandidateRegular_of_twenty_lt_card
      a S x.x1 hmultiplier (two_ne_zero_zmod p (by omega))
        ha3 ha2
        (by
          intro y hyMem
          rcases Finset.mem_image.mp hyMem with ⟨n, _hn, rfl⟩
          exact isSolution_iterate_rotation1 a x hx n)
        (by
          intro y hyMem
          rcases Finset.mem_image.mp hyMem with ⟨n, _hn, rfl⟩
          exact iterate_rotation1_firstCoordinate a x n)
        hcard
  rcases Finset.mem_image.mp hyS with ⟨n, hn, rfl⟩
  exact ⟨n, by simpa using hn, hy⟩

theorem exists_axisTwo_rotation_iterate_axisThreeCandidateRegular
    (hpTwenty : 20 < p) (a : Coefficients (ZMod p))
    (x : Point (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (ha3 : a.a3 ^ 2 ≠ 4) (ha1 : a.a1 ^ 2 ≠ 4)
    (hx : IsSolution a x)
    (hperiod : minimalPeriod (rotation2 a) x = p) :
    ∃ n < p,
      OrderedTraceCandidateRegular a.a3 a.a1 a.a2
        (coordinateTrace3 a (((rotation2 a)^[n]) x)) := by
  classical
  let S := orbitSegment (rotation2 a) p x
  have hcard : 20 < S.card := by
    rw [orbitSegment_card_of_minimalPeriod_eq _ _ _ hperiod]
    exact hpTwenty
  obtain ⟨y, hyS, hy⟩ :=
    exists_axisTwoFiber_axisThreeCandidateRegular_of_twenty_lt_card
      a S x.x2 hmultiplier (two_ne_zero_zmod p (by omega))
        ha3 ha1
        (by
          intro y hyMem
          rcases Finset.mem_image.mp hyMem with ⟨n, _hn, rfl⟩
          exact isSolution_iterate_rotation2 a x hx n)
        (by
          intro y hyMem
          rcases Finset.mem_image.mp hyMem with ⟨n, _hn, rfl⟩
          exact iterate_rotation2_secondCoordinate a x n)
        hcard
  rcases Finset.mem_image.mp hyS with ⟨n, hn, rfl⟩
  exact ⟨n, by simpa using hn, hy⟩

theorem exists_axisTwo_rotation_iterate_axisOneCandidateRegular
    (hpTwenty : 20 < p) (a : Coefficients (ZMod p))
    (x : Point (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (ha1 : a.a1 ^ 2 ≠ 4) (ha3 : a.a3 ^ 2 ≠ 4)
    (hx : IsSolution a x)
    (hperiod : minimalPeriod (rotation2 a) x = p) :
    ∃ n < p,
      OrderedTraceCandidateRegular a.a1 a.a3 a.a2
        (coordinateTrace1 a (((rotation2 a)^[n]) x)) := by
  classical
  let S := orbitSegment (rotation2 a) p x
  have hcard : 20 < S.card := by
    rw [orbitSegment_card_of_minimalPeriod_eq _ _ _ hperiod]
    exact hpTwenty
  obtain ⟨y, hyS, hy⟩ :=
    exists_axisTwoFiber_axisOneCandidateRegular_of_twenty_lt_card
      a S x.x2 hmultiplier (two_ne_zero_zmod p (by omega))
        ha1 ha3
        (by
          intro y hyMem
          rcases Finset.mem_image.mp hyMem with ⟨n, _hn, rfl⟩
          exact isSolution_iterate_rotation2 a x hx n)
        (by
          intro y hyMem
          rcases Finset.mem_image.mp hyMem with ⟨n, _hn, rfl⟩
          exact iterate_rotation2_secondCoordinate a x n)
        hcard
  rcases Finset.mem_image.mp hyS with ⟨n, hn, rfl⟩
  exact ⟨n, by simpa using hn, hy⟩

theorem exists_axisThree_rotation_iterate_axisOneCandidateRegular
    (hpTwenty : 20 < p) (a : Coefficients (ZMod p))
    (x : Point (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (ha1 : a.a1 ^ 2 ≠ 4) (ha2 : a.a2 ^ 2 ≠ 4)
    (hx : IsSolution a x)
    (hperiod : minimalPeriod (rotation3 a) x = p) :
    ∃ n < p,
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3
        (coordinateTrace1 a (((rotation3 a)^[n]) x)) := by
  classical
  let S := orbitSegment (rotation3 a) p x
  have hcard : 20 < S.card := by
    rw [orbitSegment_card_of_minimalPeriod_eq _ _ _ hperiod]
    exact hpTwenty
  obtain ⟨y, hyS, hy⟩ :=
    exists_axisThreeFiber_axisOneCandidateRegular_of_twenty_lt_card
      a S x.x3 hmultiplier (two_ne_zero_zmod p (by omega))
        ha1 ha2
        (by
          intro y hyMem
          rcases Finset.mem_image.mp hyMem with ⟨n, _hn, rfl⟩
          exact isSolution_iterate_rotation3 a x hx n)
        (by
          intro y hyMem
          rcases Finset.mem_image.mp hyMem with ⟨n, _hn, rfl⟩
          exact iterate_rotation3_thirdCoordinate a x n)
        hcard
  rcases Finset.mem_image.mp hyS with ⟨n, hn, rfl⟩
  exact ⟨n, by simpa using hn, hy⟩

theorem exists_axisThree_rotation_iterate_axisTwoCandidateRegular
    (hpTwenty : 20 < p) (a : Coefficients (ZMod p))
    (x : Point (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (ha2 : a.a2 ^ 2 ≠ 4) (ha1 : a.a1 ^ 2 ≠ 4)
    (hx : IsSolution a x)
    (hperiod : minimalPeriod (rotation3 a) x = p) :
    ∃ n < p,
      OrderedTraceCandidateRegular a.a2 a.a1 a.a3
        (coordinateTrace2 a (((rotation3 a)^[n]) x)) := by
  classical
  let S := orbitSegment (rotation3 a) p x
  have hcard : 20 < S.card := by
    rw [orbitSegment_card_of_minimalPeriod_eq _ _ _ hperiod]
    exact hpTwenty
  obtain ⟨y, hyS, hy⟩ :=
    exists_axisThreeFiber_axisTwoCandidateRegular_of_twenty_lt_card
      a S x.x3 hmultiplier (two_ne_zero_zmod p (by omega))
        ha2 ha1
        (by
          intro y hyMem
          rcases Finset.mem_image.mp hyMem with ⟨n, _hn, rfl⟩
          exact isSolution_iterate_rotation3 a x hx n)
        (by
          intro y hyMem
          rcases Finset.mem_image.mp hyMem with ⟨n, _hn, rfl⟩
          exact iterate_rotation3_thirdCoordinate a x n)
        hcard
  rcases Finset.mem_image.mp hyS with ⟨n, hn, rfl⟩
  exact ⟨n, by simpa using hn, hy⟩

/-- A first-axis parabolic cycle routes to a candidate-regular second-axis
trace by an actual `rotation1` iterate. -/
theorem exists_axisOne_parabolic_iterate_axisTwoCandidateRegular
    (hpTwenty : 20 < p) (a : Coefficients (ZMod p))
    (x : Point (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (ha1 : a.a1 ^ 2 ≠ 4) (ha2 : a.a2 ^ 2 ≠ 4)
    (ha3 : a.a3 ^ 2 ≠ 4)
    (hx : IsSolution a x)
    (hparabolic :
      orderedTrace a.multiplier a.a1 x.x1 = 2 ∨
        orderedTrace a.multiplier a.a1 x.x1 = -2) :
    ∃ n < p,
      OrderedTraceCandidateRegular a.a2 a.a3 a.a1
        (coordinateTrace2 a (((rotation1 a)^[n]) x)) := by
  have hpTwo : p ≠ 2 := by omega
  have hperiod : minimalPeriod (rotation1 a) x = p := by
    rcases hparabolic with hplus | hminus
    · exact minimalPeriod_rotation1_eq_prime_of_trace_eq_two
        p hpTwo a x ha1 ha3 hplus hx
    · exact minimalPeriod_rotation1_eq_prime_of_trace_eq_neg_two
        p hpTwo a x ha1 ha3 hminus hx
  exact exists_axisOne_rotation_iterate_axisTwoCandidateRegular
    p hpTwenty a x hmultiplier ha2 ha3 hx hperiod

/-- Reverse directed routing on the same first-axis parabolic cycle. -/
theorem exists_axisOne_parabolic_iterate_axisThreeCandidateRegular
    (hpTwenty : 20 < p) (a : Coefficients (ZMod p))
    (x : Point (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (ha1 : a.a1 ^ 2 ≠ 4) (ha2 : a.a2 ^ 2 ≠ 4)
    (ha3 : a.a3 ^ 2 ≠ 4)
    (hx : IsSolution a x)
    (hparabolic :
      orderedTrace a.multiplier a.a1 x.x1 = 2 ∨
        orderedTrace a.multiplier a.a1 x.x1 = -2) :
    ∃ n < p,
      OrderedTraceCandidateRegular a.a3 a.a2 a.a1
        (coordinateTrace3 a (((rotation1 a)^[n]) x)) := by
  have hpTwo : p ≠ 2 := by omega
  have hperiod : minimalPeriod (rotation1 a) x = p := by
    rcases hparabolic with hplus | hminus
    · exact minimalPeriod_rotation1_eq_prime_of_trace_eq_two
        p hpTwo a x ha1 ha3 hplus hx
    · exact minimalPeriod_rotation1_eq_prime_of_trace_eq_neg_two
        p hpTwo a x ha1 ha3 hminus hx
  exact exists_axisOne_rotation_iterate_axisThreeCandidateRegular
    p hpTwenty a x hmultiplier ha3 ha2 hx hperiod

/-- A second-axis parabolic cycle routes forward to the third-axis trace. -/
theorem exists_axisTwo_parabolic_iterate_axisThreeCandidateRegular
    (hpTwenty : 20 < p) (a : Coefficients (ZMod p))
    (x : Point (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (ha1 : a.a1 ^ 2 ≠ 4) (ha2 : a.a2 ^ 2 ≠ 4)
    (ha3 : a.a3 ^ 2 ≠ 4)
    (hx : IsSolution a x)
    (hparabolic :
      orderedTrace a.multiplier a.a2 x.x2 = 2 ∨
        orderedTrace a.multiplier a.a2 x.x2 = -2) :
    ∃ n < p,
      OrderedTraceCandidateRegular a.a3 a.a1 a.a2
        (coordinateTrace3 a (((rotation2 a)^[n]) x)) := by
  have hpTwo : p ≠ 2 := by omega
  have hperiod : minimalPeriod (rotation2 a) x = p := by
    rcases hparabolic with hplus | hminus
    · exact minimalPeriod_rotation2_eq_prime_of_trace_eq_two
        p hpTwo a x ha2 ha1 hplus hx
    · exact minimalPeriod_rotation2_eq_prime_of_trace_eq_neg_two
        p hpTwo a x ha2 ha1 hminus hx
  exact exists_axisTwo_rotation_iterate_axisThreeCandidateRegular
    p hpTwenty a x hmultiplier ha3 ha1 hx hperiod

/-- Reverse directed routing on a second-axis parabolic cycle. -/
theorem exists_axisTwo_parabolic_iterate_axisOneCandidateRegular
    (hpTwenty : 20 < p) (a : Coefficients (ZMod p))
    (x : Point (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (ha1 : a.a1 ^ 2 ≠ 4) (ha2 : a.a2 ^ 2 ≠ 4)
    (ha3 : a.a3 ^ 2 ≠ 4)
    (hx : IsSolution a x)
    (hparabolic :
      orderedTrace a.multiplier a.a2 x.x2 = 2 ∨
        orderedTrace a.multiplier a.a2 x.x2 = -2) :
    ∃ n < p,
      OrderedTraceCandidateRegular a.a1 a.a3 a.a2
        (coordinateTrace1 a (((rotation2 a)^[n]) x)) := by
  have hpTwo : p ≠ 2 := by omega
  have hperiod : minimalPeriod (rotation2 a) x = p := by
    rcases hparabolic with hplus | hminus
    · exact minimalPeriod_rotation2_eq_prime_of_trace_eq_two
        p hpTwo a x ha2 ha1 hplus hx
    · exact minimalPeriod_rotation2_eq_prime_of_trace_eq_neg_two
        p hpTwo a x ha2 ha1 hminus hx
  exact exists_axisTwo_rotation_iterate_axisOneCandidateRegular
    p hpTwenty a x hmultiplier ha1 ha3 hx hperiod

/-- A third-axis parabolic cycle routes forward to the first-axis trace. -/
theorem exists_axisThree_parabolic_iterate_axisOneCandidateRegular
    (hpTwenty : 20 < p) (a : Coefficients (ZMod p))
    (x : Point (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (ha1 : a.a1 ^ 2 ≠ 4) (ha2 : a.a2 ^ 2 ≠ 4)
    (ha3 : a.a3 ^ 2 ≠ 4)
    (hx : IsSolution a x)
    (hparabolic :
      orderedTrace a.multiplier a.a3 x.x3 = 2 ∨
        orderedTrace a.multiplier a.a3 x.x3 = -2) :
    ∃ n < p,
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3
        (coordinateTrace1 a (((rotation3 a)^[n]) x)) := by
  have hpTwo : p ≠ 2 := by omega
  have hperiod : minimalPeriod (rotation3 a) x = p := by
    rcases hparabolic with hplus | hminus
    · exact minimalPeriod_rotation3_eq_prime_of_trace_eq_two
        p hpTwo a x ha3 ha2 hplus hx
    · exact minimalPeriod_rotation3_eq_prime_of_trace_eq_neg_two
        p hpTwo a x ha3 ha2 hminus hx
  exact exists_axisThree_rotation_iterate_axisOneCandidateRegular
    p hpTwenty a x hmultiplier ha1 ha2 hx hperiod

/-- Reverse directed routing on a third-axis parabolic cycle. -/
theorem exists_axisThree_parabolic_iterate_axisTwoCandidateRegular
    (hpTwenty : 20 < p) (a : Coefficients (ZMod p))
    (x : Point (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (ha1 : a.a1 ^ 2 ≠ 4) (ha2 : a.a2 ^ 2 ≠ 4)
    (ha3 : a.a3 ^ 2 ≠ 4)
    (hx : IsSolution a x)
    (hparabolic :
      orderedTrace a.multiplier a.a3 x.x3 = 2 ∨
        orderedTrace a.multiplier a.a3 x.x3 = -2) :
    ∃ n < p,
      OrderedTraceCandidateRegular a.a2 a.a1 a.a3
        (coordinateTrace2 a (((rotation3 a)^[n]) x)) := by
  have hpTwo : p ≠ 2 := by omega
  have hperiod : minimalPeriod (rotation3 a) x = p := by
    rcases hparabolic with hplus | hminus
    · exact minimalPeriod_rotation3_eq_prime_of_trace_eq_two
        p hpTwo a x ha3 ha2 hplus hx
    · exact minimalPeriod_rotation3_eq_prime_of_trace_eq_neg_two
        p hpTwo a x ha3 ha2 hminus hx
  exact exists_axisThree_rotation_iterate_axisTwoCandidateRegular
    p hpTwenty a x hmultiplier ha2 ha1 hx hperiod

end PrimeField

end GenMarkoff.General
