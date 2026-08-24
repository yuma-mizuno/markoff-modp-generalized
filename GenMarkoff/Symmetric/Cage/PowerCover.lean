import GenMarkoff.Symmetric.Cage.PulledRadicand
import GenMarkoff.Symmetric.Cage.RegularWitnessFilter

/-!
# The one-sided power cover of symmetric incidence witnesses

The Hasse--Weil plane model retains the unit before the `d`-th power map.
After multiplying both incidence roots by the common denominator, its two
equations are exactly the pulled-radicand equations.  This file records the
resulting equivalence and the exact `d`-fold covering multiplicity.
-/

namespace GenMarkoff.Symmetric.Cage

open BGS.Markoff Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Clearing the reciprocal-trace denominator in one incidence equation
gives the corresponding pulled radicand. -/
theorem scaled_incidenceDiscriminant_iff_pulledRadicand
    (c xi u root : K) (hu : u ≠ 0) (d : ℕ) :
    root ^ 2 =
        incidenceDiscriminant c xi (u ^ d + (u ^ d)⁻¹) ↔
      (u ^ d * root) ^ 2 =
        eval u (incidencePulledRadicand c xi d) := by
  have hud : u ^ d ≠ 0 := pow_ne_zero d hu
  rw [eval_incidencePulledRadicand,
    incidenceReciprocalQuartic_eq_mul_discriminant c xi (u ^ d) hud]
  constructor
  · intro h
    calc
      (u ^ d * root) ^ 2 = (u ^ d) ^ 2 * root ^ 2 := by ring
      _ = (u ^ d) ^ 2 *
          incidenceDiscriminant c xi (u ^ d + (u ^ d)⁻¹) := by
        rw [h]
  · intro h
    apply (mul_left_cancel₀ (pow_ne_zero 2 hud))
    calc
      (u ^ d) ^ 2 * root ^ 2 =
          (u ^ d * root) ^ 2 := by ring
      _ = (u ^ d) ^ 2 *
          incidenceDiscriminant c xi (u ^ d + (u ^ d)⁻¹) := h

/-- The exact pair of denominator-cleared incidence roots over a nonzero
power parameter. -/
structure IncidencePulledRootPair
    (p : ℕ) [Fact p.Prime] (c xi eta : ZMod p) (d : ℕ) where
  /-- The parameter before applying the `d`-th power map. -/
  parameter : (ZMod p)ˣ
  /-- The first cleared incidence root. -/
  firstRoot : ZMod p
  /-- The second cleared incidence root. -/
  secondRoot : ZMod p
  /-- The first pulled-radicand equation. -/
  firstEquation :
    firstRoot ^ 2 =
      eval (parameter : ZMod p) (incidencePulledRadicand c xi d)
  /-- The second pulled-radicand equation. -/
  secondEquation :
    secondRoot ^ 2 =
      eval (parameter : ZMod p) (incidencePulledRadicand c eta d)

@[ext]
theorem IncidencePulledRootPair.ext
    {p : ℕ} [Fact p.Prime] {c xi eta : ZMod p} {d : ℕ}
    {x y : IncidencePulledRootPair p c xi eta d}
    (hparameter : x.parameter = y.parameter)
    (hfirst : x.firstRoot = y.firstRoot)
    (hsecond : x.secondRoot = y.secondRoot) :
    x = y := by
  cases x
  cases y
  simp_all

@[ext]
theorem IncidenceEquationWitness.ext
    {c xi eta : K} {x y : IncidenceEquationWitness c xi eta}
    (hmiddle : x.middle = y.middle)
    (hfirst : x.firstRoot = y.firstRoot)
    (hsecond : x.secondRoot = y.secondRoot) :
    x = y := by
  cases x
  cases y
  simp_all

/-- The witness-bearing one-sided cover before quotienting by power-map
fibers. -/
abbrev rawIncidenceWitnessPowerCoverSolutions
    (p : ℕ) [Fact p.Prime] (c xi eta : ZMod p) (d : ℕ) :=
  BGS.rightPowerTraceCoverSolutions
    (incidenceWitnessTrace (c := c) (xi := xi) (eta := eta))
    (splitTorusTrace : (ZMod p)ˣ → ZMod p) d

/-- Scale the two incidence roots by the common reciprocal-trace
denominator. -/
def rawIncidencePowerCoverToPulled
    (p : ℕ) [Fact p.Prime] (c xi eta : ZMod p) (d : ℕ) :
    rawIncidenceWitnessPowerCoverSolutions p c xi eta d →
      IncidencePulledRootPair p c xi eta d := fun z => by
  let witness := z.1.1
  let parameter := z.1.2
  have hmiddle :
      witness.middle = splitTorusTrace (parameter ^ d) := z.2
  refine
    { parameter := parameter
      firstRoot := (parameter : ZMod p) ^ d * witness.firstRoot
      secondRoot := (parameter : ZMod p) ^ d * witness.secondRoot
      firstEquation := ?_
      secondEquation := ?_ }
  · apply
      (scaled_incidenceDiscriminant_iff_pulledRadicand
        c xi (parameter : ZMod p) witness.firstRoot
          parameter.ne_zero d).mp
    have htrace :
        (parameter : ZMod p) ^ d +
            ((parameter : ZMod p) ^ d)⁻¹ =
          splitTorusTrace (parameter ^ d) := by
      simp [splitTorusTrace]
    rw [htrace, ← hmiddle]
    exact witness.firstEquation
  · apply
      (scaled_incidenceDiscriminant_iff_pulledRadicand
        c eta (parameter : ZMod p) witness.secondRoot
          parameter.ne_zero d).mp
    have htrace :
        (parameter : ZMod p) ^ d +
            ((parameter : ZMod p) ^ d)⁻¹ =
          splitTorusTrace (parameter ^ d) := by
      simp [splitTorusTrace]
    rw [htrace, ← hmiddle]
    exact witness.secondEquation

/-- Divide the two cleared roots by the common nonzero denominator. -/
def incidencePulledToRawPowerCover
    (p : ℕ) [Fact p.Prime] (c xi eta : ZMod p) (d : ℕ) :
    IncidencePulledRootPair p c xi eta d →
      rawIncidenceWitnessPowerCoverSolutions p c xi eta d := fun z => by
  let q : ZMod p := (z.parameter : ZMod p) ^ d
  have hq : q ≠ 0 := pow_ne_zero d z.parameter.ne_zero
  let witness : IncidenceEquationWitness c xi eta :=
    { middle := splitTorusTrace (z.parameter ^ d)
      firstRoot := q⁻¹ * z.firstRoot
      secondRoot := q⁻¹ * z.secondRoot
      firstEquation := by
        have h :=
          (scaled_incidenceDiscriminant_iff_pulledRadicand
            c xi (z.parameter : ZMod p) (q⁻¹ * z.firstRoot)
              z.parameter.ne_zero d).mpr (by
            simpa [q, hq] using z.firstEquation)
        simpa [splitTorusTrace] using h
      secondEquation := by
        have h :=
          (scaled_incidenceDiscriminant_iff_pulledRadicand
            c eta (z.parameter : ZMod p) (q⁻¹ * z.secondRoot)
              z.parameter.ne_zero d).mpr (by
            simpa [q, hq] using z.secondEquation)
        simpa [splitTorusTrace] using h }
  refine ⟨(witness, z.parameter), ?_⟩
  rfl

/-- The raw one-sided incidence cover is exactly the pair of pulled
radicand equations. -/
def rawIncidencePowerCoverEquivPulled
    (p : ℕ) [Fact p.Prime] (c xi eta : ZMod p) (d : ℕ) :
    rawIncidenceWitnessPowerCoverSolutions p c xi eta d ≃
      IncidencePulledRootPair p c xi eta d where
  toFun := rawIncidencePowerCoverToPulled p c xi eta d
  invFun := incidencePulledToRawPowerCover p c xi eta d
  left_inv := by
    intro z
    apply Subtype.ext
    apply Prod.ext
    · apply IncidenceEquationWitness.ext
      · simpa [rawIncidencePowerCoverToPulled,
          incidencePulledToRawPowerCover,
          incidenceWitnessTrace] using z.2.symm
      · simp [rawIncidencePowerCoverToPulled,
          incidencePulledToRawPowerCover]
      · simp [rawIncidencePowerCoverToPulled,
          incidencePulledToRawPowerCover]
    · rfl
  right_inv := by
    intro z
    apply IncidencePulledRootPair.ext
    · rfl
    · simp [rawIncidencePowerCoverToPulled,
        incidencePulledToRawPowerCover]
    · simp [rawIncidencePowerCoverToPulled,
        incidencePulledToRawPowerCover]

/-- Exact division of the pulled cover by the `d`-th power-map fibers. -/
theorem natCard_incidencePulledRootPair_eq_mul_rawPowerRange
    (p : ℕ) [Fact p.Prime] (c xi eta : ZMod p) (d : ℕ)
    (hd : d ∣ Nat.card (ZMod p)ˣ) :
    Nat.card (IncidencePulledRootPair p c xi eta d) =
      d * Nat.card
        (rawIncidenceWitnessPowerRangeSolutions p c xi eta d) := by
  calc
    Nat.card (IncidencePulledRootPair p c xi eta d) =
        Nat.card
          (rawIncidenceWitnessPowerCoverSolutions p c xi eta d) :=
      Nat.card_congr
        (rawIncidencePowerCoverEquivPulled p c xi eta d).symm
    _ = d * Nat.card
        (rawIncidenceWitnessPowerRangeSolutions p c xi eta d) := by
      simpa [rawIncidenceWitnessPowerCoverSolutions,
        rawIncidenceWitnessPowerRangeSolutions] using
          (BGS.natCard_rightPowerTraceCoverSolutions_of_dvd
            (incidenceWitnessTrace
              (c := c) (xi := xi) (eta := eta))
            (splitTorusTrace : (ZMod p)ˣ → ZMod p) d hd)

end

end GenMarkoff.Symmetric.Cage
