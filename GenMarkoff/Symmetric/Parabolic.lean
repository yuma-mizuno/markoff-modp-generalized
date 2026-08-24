import GenMarkoff.Symmetric.FiberDynamics

/-!
# Parabolic fibers for the squared symmetric rotations

The affine translation terms are retained.  Over an odd prime field, every
surface point on a trace `±2` fiber has an `R₁`-cycle of exactly `p` points;
the excluded fixed cases would force `c² = 4`.
-/

namespace GenMarkoff.Symmetric

universe u

section Ring

variable {R : Type u} [CommRing R]

/-- Translation increment on the trace `-2` fiber. -/
def negTwoIncrement (c u y z : R) : R :=
  -2 * (y + z) - c * u

/-- Difference of the two moving coordinates. -/
def movingDifference (y z : R) : R :=
  z - y

theorem affineStep_sq_neg_two (c u y z : R) :
    affineStep c u (-2) (affineStep c u (-2) (y, z)) =
      (y + negTwoIncrement c u y z,
        z - negTwoIncrement c u y z) := by
  ext <;> simp [affineStep, negTwoIncrement] <;> ring

theorem affineStep_sq_two (c u y z : R) :
    affineStep c u 2 (affineStep c u 2 (y, z)) =
      (y + 2 * movingDifference y z - c * u,
        z + 2 * movingDifference y z - 3 * c * u) := by
  ext <;> simp [affineStep, movingDifference] <;> ring

/-- One `R₁` step on the trace `-2` fiber. -/
theorem rotation1_of_trace_eq_neg_two
    (c : R) (x : Point R) (htrace : trace c x.x1 = -2) :
    rotation1 (coefficients c) x =
      ⟨x.x1,
        x.x2 + negTwoIncrement c x.x1 x.x2 x.x3,
        x.x3 - negTwoIncrement c x.x1 x.x2 x.x3⟩ := by
  have hm := movingCoordinates1_rotation1 c x
  simp only [fiberStep, htrace] at hm
  rw [affineStep_sq_neg_two] at hm
  apply Point.ext
  · rfl
  · exact congrArg Prod.fst hm
  · exact congrArg Prod.snd hm

/-- One `R₁` step on the trace `2` fiber. -/
theorem rotation1_of_trace_eq_two
    (c : R) (x : Point R) (htrace : trace c x.x1 = 2) :
    rotation1 (coefficients c) x =
      ⟨x.x1,
        x.x2 + 2 * movingDifference x.x2 x.x3 - c * x.x1,
        x.x3 + 2 * movingDifference x.x2 x.x3 - 3 * c * x.x1⟩ := by
  have hm := movingCoordinates1_rotation1 c x
  simp only [fiberStep, htrace] at hm
  rw [affineStep_sq_two] at hm
  apply Point.ext
  · rfl
  · exact congrArg Prod.fst hm
  · exact congrArg Prod.snd hm

/-- Explicit iterates on the trace `-2` fiber. -/
theorem iterate_rotation1_of_trace_eq_neg_two
    (c : R) (x : Point R) (htrace : trace c x.x1 = -2) (n : ℕ) :
    ((rotation1 (coefficients c))^[n]) x =
      ⟨x.x1,
        x.x2 + (n : R) * negTwoIncrement c x.x1 x.x2 x.x3,
        x.x3 - (n : R) * negTwoIncrement c x.x1 x.x2 x.x3⟩ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [rotation1_of_trace_eq_neg_two c _ (by simpa using htrace)]
      apply Point.ext <;>
        simp [negTwoIncrement] <;>
        ring

/-- Explicit iterates on the trace `2` fiber. -/
theorem iterate_rotation1_of_trace_eq_two
    (c : R) (x : Point R) (htrace : trace c x.x1 = 2) (n : ℕ) :
    ((rotation1 (coefficients c))^[n]) x =
      ⟨x.x1,
        x.x2 + 2 * (n : R) * movingDifference x.x2 x.x3 -
          (2 * (n : R) ^ 2 - (n : R)) * c * x.x1,
        x.x3 + 2 * (n : R) * movingDifference x.x2 x.x3 -
          (2 * (n : R) ^ 2 + (n : R)) * c * x.x1⟩ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [rotation1_of_trace_eq_two c _ (by simpa using htrace)]
      apply Point.ext <;>
        simp [movingDifference] <;>
        ring

end Ring

section Field

variable {K : Type u} [Field K]

theorem negTwoIncrement_ne_zero_of_isSolution
    (c u y z : K) (_htwo : (2 : K) ≠ 0) (hc : c ^ 2 ≠ 4)
    (htrace : trace c u = -2)
    (hsolution : IsSolution (coefficients c) ⟨u, y, z⟩) :
    negTwoIncrement c u y z ≠ 0 := by
  intro hincrement
  have hsurface := hsolution
  rw [IsSolution, polynomial_fixed_first] at hsurface
  rw [htrace] at hsurface
  let m := y + z
  have hm : m ^ 2 + c * u * m + u ^ 2 = 0 := by
    dsimp [m]
    linear_combination hsurface
  rw [negTwoIncrement] at hincrement
  have hrelation : 2 * m + c * u = 0 := by
    dsimp [m]
    linear_combination -hincrement
  have hfactor : (4 - c ^ 2) * u ^ 2 = 0 := by
    linear_combination
      4 * hm - (2 * m - c * u) * hrelation -
        (2 * c * u) * hrelation
  have hcoefficient : 4 - c ^ 2 ≠ 0 := sub_ne_zero.mpr hc.symm
  have huSq : u ^ 2 = 0 := (mul_eq_zero.mp hfactor).resolve_left hcoefficient
  have hu : u = 0 := sq_eq_zero_iff.mp huSq
  have hcTwo : c = 2 := by
    rw [hu, trace] at htrace
    linear_combination -htrace
  apply hc
  rw [hcTwo]
  norm_num

theorem posTwo_cu_or_difference_ne_zero_of_isSolution
    (c u y z : K) (hc : c ^ 2 ≠ 4)
    (htrace : trace c u = 2)
    (hsolution : IsSolution (coefficients c) ⟨u, y, z⟩) :
    c * u ≠ 0 ∨ movingDifference y z ≠ 0 := by
  by_contra hnone
  push Not at hnone
  rcases hnone with ⟨hcu, hdifference⟩
  have hsurface := hsolution
  rw [IsSolution, polynomial_fixed_first] at hsurface
  rw [htrace] at hsurface
  have huSq : u ^ 2 = 0 := by
    rw [movingDifference] at hdifference
    linear_combination hsurface - (y + z) * hcu -
      (z - y) * hdifference
  have hu : u = 0 := sq_eq_zero_iff.mp huSq
  have hcNegTwo : c = -2 := by
    rw [hu, trace] at htrace
    linear_combination -htrace
  apply hc
  rw [hcNegTwo]
  norm_num

end Field

section PrimeField

variable (p : ℕ) [Fact p.Prime]

/-- The first-rotation cycle cut out by the canonical range `0,...,p-1`. -/
def rotation1ParabolicCycle (c : ZMod p) (x : Point (ZMod p)) :
    Finset (Point (ZMod p)) :=
  (Finset.range p).image fun n ↦
    ((rotation1 (coefficients c))^[n]) x

private theorem two_ne_zero_zmod (hpTwo : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
  have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
  exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)

theorem rotation1ParabolicCycle_card_of_trace_eq_neg_two
    (hpTwo : p ≠ 2) (c : ZMod p) (x : Point (ZMod p))
    (hc : c ^ 2 ≠ 4) (htrace : trace c x.x1 = -2)
    (hsolution : IsSolution (coefficients c) x) :
    (rotation1ParabolicCycle p c x).card = p := by
  classical
  let f : ℕ → Point (ZMod p) := fun n ↦
    ((rotation1 (coefficients c))^[n]) x
  have hincrement : negTwoIncrement c x.x1 x.x2 x.x3 ≠ 0 := by
    rcases x with ⟨u, y, z⟩
    exact negTwoIncrement_ne_zero_of_isSolution c u y z
      (two_ne_zero_zmod p hpTwo) hc htrace hsolution
  have hinjective : Set.InjOn f (Finset.range p) := by
    intro n hn m hm heq
    have hnlt : n < p := by simpa using hn
    have hmlt : m < p := by simpa using hm
    have hcoordinate := congrArg Point.x2 heq
    change (((rotation1 (coefficients c))^[n]) x).x2 =
      (((rotation1 (coefficients c))^[m]) x).x2 at hcoordinate
    rw [iterate_rotation1_of_trace_eq_neg_two c x htrace,
      iterate_rotation1_of_trace_eq_neg_two c x htrace] at hcoordinate
    have hcasts : (n : ZMod p) = (m : ZMod p) := by
      apply mul_right_cancel₀ hincrement
      exact add_left_cancel hcoordinate
    rw [ZMod.natCast_eq_natCast_iff'] at hcasts
    simpa [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hmlt] using hcasts
  calc
    (rotation1ParabolicCycle p c x).card =
        (Finset.range p).card := by
      exact Finset.card_image_iff.mpr hinjective
    _ = p := Finset.card_range p

theorem rotation1ParabolicCycle_card_of_trace_eq_two
    (hpTwo : p ≠ 2) (c : ZMod p) (x : Point (ZMod p))
    (hc : c ^ 2 ≠ 4) (htrace : trace c x.x1 = 2)
    (hsolution : IsSolution (coefficients c) x) :
    (rotation1ParabolicCycle p c x).card = p := by
  classical
  let f : ℕ → Point (ZMod p) := fun n ↦
    ((rotation1 (coefficients c))^[n]) x
  have htwo : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p hpTwo
  have hnonfixed :
      c * x.x1 ≠ 0 ∨ movingDifference x.x2 x.x3 ≠ 0 := by
    rcases x with ⟨u, y, z⟩
    exact posTwo_cu_or_difference_ne_zero_of_isSolution
      c u y z hc htrace hsolution
  have hinjective : Set.InjOn f (Finset.range p) := by
    intro n hn m hm heq
    have hnlt : n < p := by simpa using hn
    have hmlt : m < p := by simpa using hm
    have hcasts : (n : ZMod p) = (m : ZMod p) := by
      by_cases hcuZero : c * x.x1 = 0
      · have hdifference : movingDifference x.x2 x.x3 ≠ 0 :=
          hnonfixed.resolve_left (fun hcu ↦ hcu hcuZero)
        have hcoordinate := congrArg Point.x2 heq
        change (((rotation1 (coefficients c))^[n]) x).x2 =
          (((rotation1 (coefficients c))^[m]) x).x2 at hcoordinate
        rw [iterate_rotation1_of_trace_eq_two c x htrace,
          iterate_rotation1_of_trace_eq_two c x htrace] at hcoordinate
        simp [mul_assoc, hcuZero] at hcoordinate
        rcases hcoordinate with (hcasts | hdiffZero) | htwoZero
        · exact hcasts
        · exact (hdifference hdiffZero).elim
        · exact (htwo htwoZero).elim
      · have hcoordinate := congrArg
          (fun y : Point (ZMod p) ↦ y.x3 - y.x2) heq
        change ((((rotation1 (coefficients c))^[n]) x).x3 -
            (((rotation1 (coefficients c))^[n]) x).x2) =
          ((((rotation1 (coefficients c))^[m]) x).x3 -
            (((rotation1 (coefficients c))^[m]) x).x2) at hcoordinate
        rw [iterate_rotation1_of_trace_eq_two c x htrace,
          iterate_rotation1_of_trace_eq_two c x htrace] at hcoordinate
        have hproduct : (n : ZMod p) * (2 * (c * x.x1)) =
            (m : ZMod p) * (2 * (c * x.x1)) := by
          linear_combination -hcoordinate
        exact mul_right_cancel₀ (mul_ne_zero htwo hcuZero) hproduct
    rw [ZMod.natCast_eq_natCast_iff'] at hcasts
    simpa [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hmlt] using hcasts
  calc
    (rotation1ParabolicCycle p c x).card =
        (Finset.range p).card := by
      exact Finset.card_image_iff.mpr hinjective
    _ = p := Finset.card_range p

end PrimeField

end GenMarkoff.Symmetric
