import GenMarkoff.Symmetric.Opening.UnitCircle
import BGS.Markoff.Opening.CyclotomicBound

/-!
# The concrete cyclotomic opening bound for equal coefficients

This module adapts the pinned BGS norm-and-reduction argument to the
equal-coefficient generalized trace defect.  The coefficient `c` remains a
fixed integer throughout.  The conclusion has an explicit integer-valued
archimedean constant depending on `c`.
-/

open scoped NumberField

namespace GenMarkoff.Symmetric.Opening

open BGS.Markoff

/-- An integer-valued version of the embedding bound for the generalized
cyclotomic defect. -/
def integerArchimedeanBound (c : ℤ) : ℕ :=
  20 + 6 * (c * (c + 2)).natAbs + (c ^ 2 * (2 * c + 3)).natAbs

/-- The integer-valued bound is exactly the complex bound at an integral
coefficient. -/
theorem archimedeanBound_intCast (c : ℤ) :
    archimedeanBound (c : ℂ) = integerArchimedeanBound c := by
  have h₁ : (c : ℂ) + 2 = ((c + 2 : ℤ) : ℂ) := by norm_num
  have h₂ : 2 * (c : ℂ) + 3 = ((2 * c + 3 : ℤ) : ℂ) := by norm_num
  have hprod₁ :
      (c : ℂ) * ((c + 2 : ℤ) : ℂ) = ((c * (c + 2) : ℤ) : ℂ) := by
    norm_num
  have hprod₂ :
      (c : ℂ) ^ 2 * ((2 * c + 3 : ℤ) : ℂ) =
        ((c ^ 2 * (2 * c + 3) : ℤ) : ℂ) := by
    norm_num
  rw [archimedeanBound,
    show (c : ℂ) + 2 = ((c + 2 : ℤ) : ℂ) from h₁,
    show 2 * (c : ℂ) + 3 = ((2 * c + 3 : ℤ) : ℂ) from h₂,
    hprod₁, hprod₂, Complex.norm_intCast, Complex.norm_intCast,
    integerArchimedeanBound]
  norm_num

/-- The integral generalized defect formed from the three polynomial
reciprocal traces in the canonical cyclotomic field. -/
noncomputable def openingCyclotomicIntegerDefect
    (c : ℤ) (n a₁ a₂ a₃ : ℕ) [NeZero n] :
    OpeningCyclotomicIntegers n :=
  traceDefect (c : OpeningCyclotomicIntegers n)
    (BGS.Markoff.openingCyclotomicIntegerTrace n a₁)
    (BGS.Markoff.openingCyclotomicIntegerTrace n a₂)
    (BGS.Markoff.openingCyclotomicIntegerTrace n a₃)

/-- Coercing the integral generalized defect to the cyclotomic field gives
the generalized cyclotomic defect of the corresponding powers. -/
theorem coe_openingCyclotomicIntegerDefect
    (c : ℤ) (n a₁ a₂ a₃ : ℕ) [NeZero n]
    (ha₁ : a₁ ≤ n) (ha₂ : a₂ ≤ n) (ha₃ : a₃ ≤ n) :
    ((openingCyclotomicIntegerDefect c n a₁ a₂ a₃ :
        OpeningCyclotomicIntegers n) : OpeningCyclotomicField n) =
      cyclotomicDefect (c : OpeningCyclotomicField n)
        (openingCyclotomicRoot n ^ a₁)
        (openingCyclotomicRoot n ^ a₂)
        (openingCyclotomicRoot n ^ a₃) := by
  have ht₁ :
      algebraMap (OpeningCyclotomicIntegers n) (OpeningCyclotomicField n)
          (BGS.Markoff.openingCyclotomicIntegerTrace n a₁) =
        BGS.Markoff.cyclotomicTrace (openingCyclotomicRoot n ^ a₁) := by
    simpa only using
      BGS.Markoff.coe_openingCyclotomicIntegerTrace n a₁ ha₁
  have ht₂ :
      algebraMap (OpeningCyclotomicIntegers n) (OpeningCyclotomicField n)
          (BGS.Markoff.openingCyclotomicIntegerTrace n a₂) =
        BGS.Markoff.cyclotomicTrace (openingCyclotomicRoot n ^ a₂) := by
    simpa only using
      BGS.Markoff.coe_openingCyclotomicIntegerTrace n a₂ ha₂
  have ht₃ :
      algebraMap (OpeningCyclotomicIntegers n) (OpeningCyclotomicField n)
          (BGS.Markoff.openingCyclotomicIntegerTrace n a₃) =
        BGS.Markoff.cyclotomicTrace (openingCyclotomicRoot n ^ a₃) := by
    simpa only using
      BGS.Markoff.coe_openingCyclotomicIntegerTrace n a₃ ha₃
  simp only [openingCyclotomicIntegerDefect, traceDefect, cyclotomicDefect,
    map_add, map_sub, map_mul, map_pow, map_intCast, map_ofNat]
  rw [ht₁, ht₂, ht₃]
  simp [BGS.Markoff.cyclotomicTrace, cyclotomicTrace]

/-- Compatible reduction sends the integral generalized defect to the
generalized residue-field cyclotomic defect. -/
theorem openingCyclotomicReduction_integerDefect
    (c : ℤ) (p n a₁ a₂ a₃ : ℕ) [Fact p.Prime] [NeZero n]
    (hcoprime : Nat.Coprime p n)
    (omega : OpeningResidueClosure p) (homega : IsPrimitiveRoot omega n)
    (ha₁ : a₁ ≤ n) (ha₂ : a₂ ≤ n) (ha₃ : a₃ ≤ n) :
    openingCyclotomicReduction p n hcoprime omega homega
        (openingCyclotomicIntegerDefect c n a₁ a₂ a₃) =
      cyclotomicDefect (c : OpeningResidueClosure p)
        (omega ^ a₁) (omega ^ a₂) (omega ^ a₃) := by
  simp only [openingCyclotomicIntegerDefect, traceDefect, cyclotomicDefect,
    map_add, map_sub, map_mul, map_pow, map_intCast, map_ofNat]
  rw [BGS.Markoff.openingCyclotomicReduction_integerTrace
      p n a₁ hcoprime omega homega ha₁,
    BGS.Markoff.openingCyclotomicReduction_integerTrace
      p n a₂ hcoprime omega homega ha₂,
    BGS.Markoff.openingCyclotomicReduction_integerTrace
      p n a₃ hcoprime omega homega ha₃]
  simp [BGS.Markoff.cyclotomicTrace, cyclotomicTrace]

/-- A symmetric residue-surface point makes the corresponding generalized
cyclotomic defect vanish. -/
theorem residueCyclotomicDefect_eq_zero_of_solution
    {p : ℕ} [Fact p.Prime]
    (c : OpeningResidueClosure p)
    (x : Point (OpeningResidueClosure p))
    (hx : IsSolution (coefficients c) x)
    {z₁ z₂ z₃ : OpeningResidueClosure p}
    (h₁ : cyclotomicTrace z₁ = trace c x.x1)
    (h₂ : cyclotomicTrace z₂ = trace c x.x2)
    (h₃ : cyclotomicTrace z₃ = trace c x.x3) :
    cyclotomicDefect c z₁ z₂ z₃ = 0 := by
  rw [cyclotomicDefect_eq_multiplier_sq_mul_polynomial c z₁ z₂ z₃ x
    h₁ h₂ h₃]
  rw [hx]
  ring

/-- The integer norm of the integral generalized defect is bounded by the
explicit coefficient-dependent constant to the cyclotomic degree. -/
theorem openingCyclotomicIntegerDefect_integerNorm_natAbs_le
    (c : ℤ) (n a₁ a₂ a₃ : ℕ) [NeZero n]
    (ha₁ : a₁ ≤ n) (ha₂ : a₂ ≤ n) (ha₃ : a₃ ≤ n) :
    (Algebra.norm ℤ
      (openingCyclotomicIntegerDefect c n a₁ a₂ a₃)).natAbs ≤
        integerArchimedeanBound c ^ n.totient := by
  letI : NeZero (n : ℚ) := ⟨by exact_mod_cast (NeZero.ne n)⟩
  letI : IsCyclotomicExtension {n} ℚ (OpeningCyclotomicField n) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  rw [← IsCyclotomicExtension.Rat.finrank n (OpeningCyclotomicField n)]
  apply BGS.Markoff.integerNorm_natAbs_le_pow_of_embeddings
  intro sigma
  have hroot : ‖sigma (openingCyclotomicRoot n)‖ = 1 :=
    ((openingCyclotomicRoot_isPrimitive n).map_of_injective sigma.injective).norm'_eq_one
      (NeZero.pos n).ne'
  have hz₁ : ‖sigma (openingCyclotomicRoot n ^ a₁)‖ = 1 := by
    rw [map_pow, norm_pow, hroot, one_pow]
  have hz₂ : ‖sigma (openingCyclotomicRoot n ^ a₂)‖ = 1 := by
    rw [map_pow, norm_pow, hroot, one_pow]
  have hz₃ : ‖sigma (openingCyclotomicRoot n ^ a₃)‖ = 1 := by
    rw [map_pow, norm_pow, hroot, one_pow]
  rw [coe_openingCyclotomicIntegerDefect c n a₁ a₂ a₃ ha₁ ha₂ ha₃]
  have hbound := norm_cyclotomicDefect_le (c : ℂ) hz₁ hz₂ hz₃
  simpa [cyclotomicDefect, traceDefect, cyclotomicTrace,
    archimedeanBound_intCast, map_ofNat] using hbound

/-- If a characteristic-zero reciprocal trace is the affine-origin trace,
compatible reduction sends the corresponding residue trace to the same
affine-origin trace. -/
theorem residueCyclotomicTrace_eq_neg_int_of_complexTrace_eq_neg
    (c : ℤ) (p n a : ℕ) [Fact p.Prime] [NeZero n]
    (hcoprime : Nat.Coprime p n)
    (omega : OpeningResidueClosure p) (homega : IsPrimitiveRoot omega n)
    (ha : a ≤ n)
    (sigma : OpeningCyclotomicField n →ₐ[ℚ] ℂ)
    (hcomplex :
      cyclotomicTrace (sigma (openingCyclotomicRoot n ^ a)) = -(c : ℂ)) :
    cyclotomicTrace (omega ^ a) = -(c : OpeningResidueClosure p) := by
  have hfield :
      cyclotomicTrace (openingCyclotomicRoot n ^ a) =
        -(c : OpeningCyclotomicField n) := by
    apply sigma.injective
    simpa [cyclotomicTrace, map_ofNat] using hcomplex
  have hinteger :
      BGS.Markoff.openingCyclotomicIntegerTrace n a =
        -(c : OpeningCyclotomicIntegers n) := by
    apply NumberField.RingOfIntegers.coe_injective
    have ht :
        algebraMap (OpeningCyclotomicIntegers n) (OpeningCyclotomicField n)
            (BGS.Markoff.openingCyclotomicIntegerTrace n a) =
          BGS.Markoff.cyclotomicTrace (openingCyclotomicRoot n ^ a) := by
      simpa only using BGS.Markoff.coe_openingCyclotomicIntegerTrace n a ha
    rw [ht]
    simpa [BGS.Markoff.cyclotomicTrace, cyclotomicTrace, map_intCast] using hfield
  have hred := BGS.Markoff.openingCyclotomicReduction_integerTrace
    p n a hcoprime omega homega ha
  rw [hinteger] at hred
  simpa [BGS.Markoff.cyclotomicTrace, cyclotomicTrace] using hred.symm

/-- For an admissible integral coefficient, compatible cyclotomic lifts of a
punctured residue point have nonzero generalized defect.  The residue
multiplier hypothesis is essential: it is what identifies the trace `-c`
with the deleted zero coordinate after reduction. -/
theorem openingCyclotomicDefect_ne_zero_of_punctured_residuePoint
    (c : ℤ) (hs : 3 * (1 + c) ≠ 0) (hc : c ^ 2 ≠ 4)
    (p n a₁ a₂ a₃ : ℕ) [Fact p.Prime] [NeZero n]
    (hcoprime : Nat.Coprime p n)
    (omega : OpeningResidueClosure p) (homega : IsPrimitiveRoot omega n)
    (ha₁ : a₁ ≤ n) (ha₂ : a₂ ≤ n) (ha₃ : a₃ ≤ n)
    (x : Point (OpeningResidueClosure p))
    (h₁ : cyclotomicTrace (omega ^ a₁) = trace (c : OpeningResidueClosure p) x.x1)
    (h₂ : cyclotomicTrace (omega ^ a₂) = trace (c : OpeningResidueClosure p) x.x2)
    (h₃ : cyclotomicTrace (omega ^ a₃) = trace (c : OpeningResidueClosure p) x.x3)
    (hsResidue : multiplier (c : OpeningResidueClosure p) ≠ 0)
    (hxne : x ≠ origin) :
    cyclotomicDefect (c : OpeningCyclotomicField n)
      (openingCyclotomicRoot n ^ a₁)
      (openingCyclotomicRoot n ^ a₂)
      (openingCyclotomicRoot n ^ a₃) ≠ 0 := by
  let sigma : OpeningCyclotomicField n →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hroot : ‖sigma (openingCyclotomicRoot n)‖ = 1 :=
    ((openingCyclotomicRoot_isPrimitive n).map_of_injective sigma.injective).norm'_eq_one
      (NeZero.pos n).ne'
  have hz₁ : ‖sigma (openingCyclotomicRoot n ^ a₁)‖ = 1 := by
    rw [map_pow, norm_pow, hroot, one_pow]
  have hz₂ : ‖sigma (openingCyclotomicRoot n ^ a₂)‖ = 1 := by
    rw [map_pow, norm_pow, hroot, one_pow]
  have hz₃ : ‖sigma (openingCyclotomicRoot n ^ a₃)‖ = 1 := by
    rw [map_pow, norm_pow, hroot, one_pow]
  have hcoord : x.x1 ≠ 0 ∨ x.x2 ≠ 0 ∨ x.x3 ≠ 0 := by
    by_contra h
    push Not at h
    apply hxne
    ext <;> simp [origin, h]
  have hsomeResidue :
      cyclotomicTrace (omega ^ a₁) ≠ -(c : OpeningResidueClosure p) ∨
      cyclotomicTrace (omega ^ a₂) ≠ -(c : OpeningResidueClosure p) ∨
      cyclotomicTrace (omega ^ a₃) ≠ -(c : OpeningResidueClosure p) := by
    rcases hcoord with hx₁ | hx₂ | hx₃
    · left
      intro htrace
      apply hx₁
      exact (trace_eq_neg_self_iff _ _ hsResidue).mp (h₁.symm.trans htrace)
    · right; left
      intro htrace
      apply hx₂
      exact (trace_eq_neg_self_iff _ _ hsResidue).mp (h₂.symm.trans htrace)
    · right; right
      intro htrace
      apply hx₃
      exact (trace_eq_neg_self_iff _ _ hsResidue).mp (h₃.symm.trans htrace)
  have hsomeComplex :
      cyclotomicTrace (sigma (openingCyclotomicRoot n ^ a₁)) ≠ -(c : ℂ) ∨
      cyclotomicTrace (sigma (openingCyclotomicRoot n ^ a₂)) ≠ -(c : ℂ) ∨
      cyclotomicTrace (sigma (openingCyclotomicRoot n ^ a₃)) ≠ -(c : ℂ) := by
    rcases hsomeResidue with htrace | htrace | htrace
    · left
      intro hcomplex
      exact htrace (residueCyclotomicTrace_eq_neg_int_of_complexTrace_eq_neg
        c p n a₁ hcoprime omega homega ha₁ sigma hcomplex)
    · right; left
      intro hcomplex
      exact htrace (residueCyclotomicTrace_eq_neg_int_of_complexTrace_eq_neg
        c p n a₂ hcoprime omega homega ha₂ sigma hcomplex)
    · right; right
      intro hcomplex
      exact htrace (residueCyclotomicTrace_eq_neg_int_of_complexTrace_eq_neg
        c p n a₃ hcoprime omega homega ha₃ sigma hcomplex)
  have hcomplexNe :=
    cyclotomicDefect_ne_zero_of_some_trace_ne_neg_integral
      c hs hc hz₁ hz₂ hz₃ hsomeComplex
  intro hzero
  apply hcomplexNe
  simpa [cyclotomicDefect, traceDefect, cyclotomicTrace, map_ofNat] using
    congrArg sigma hzero

/-- A symmetric residue-surface point puts the integral generalized defect in
the compatible prime above `p`. -/
theorem openingCyclotomicIntegerDefect_mem_prime_of_solution
    (c : ℤ) (p n a₁ a₂ a₃ : ℕ) [Fact p.Prime] [NeZero n]
    (hcoprime : Nat.Coprime p n)
    (omega : OpeningResidueClosure p) (homega : IsPrimitiveRoot omega n)
    (ha₁ : a₁ ≤ n) (ha₂ : a₂ ≤ n) (ha₃ : a₃ ≤ n)
    (x : Point (OpeningResidueClosure p))
    (hx : IsSolution (coefficients (c : OpeningResidueClosure p)) x)
    (h₁ : cyclotomicTrace (omega ^ a₁) = trace (c : OpeningResidueClosure p) x.x1)
    (h₂ : cyclotomicTrace (omega ^ a₂) = trace (c : OpeningResidueClosure p) x.x2)
    (h₃ : cyclotomicTrace (omega ^ a₃) = trace (c : OpeningResidueClosure p) x.x3) :
    openingCyclotomicIntegerDefect c n a₁ a₂ a₃ ∈
      openingCyclotomicPrime p n hcoprime omega homega := by
  rw [openingCyclotomicPrime, RingHom.mem_ker]
  change openingCyclotomicReduction p n hcoprime omega homega
      (openingCyclotomicIntegerDefect c n a₁ a₂ a₃) = 0
  rw [show openingCyclotomicReduction p n hcoprime omega homega
      (openingCyclotomicIntegerDefect c n a₁ a₂ a₃) =
        cyclotomicDefect (c : OpeningResidueClosure p)
          (omega ^ a₁) (omega ^ a₂) (omega ^ a₃) from
    openingCyclotomicReduction_integerDefect
      c p n a₁ a₂ a₃ hcoprime omega homega ha₁ ha₂ ha₃]
  exact residueCyclotomicDefect_eq_zero_of_solution
    (c : OpeningResidueClosure p) x hx h₁ h₂ h₃

/-- The concrete generalized cyclotomic opening inequality.

For a punctured symmetric residue point whose three trace coordinates are
compatible powers of one primitive residue root, the modulus is bounded by
the explicit coefficient-dependent norm bound. -/
theorem modulus_le_integerArchimedeanBound_pow_totient_of_compatible_residue_traces
    (c : ℤ) (hs : 3 * (1 + c) ≠ 0) (hc : c ^ 2 ≠ 4)
    (p n a₁ a₂ a₃ : ℕ) [Fact p.Prime] [NeZero n]
    (hcoprime : Nat.Coprime p n)
    (omega : OpeningResidueClosure p) (homega : IsPrimitiveRoot omega n)
    (ha₁ : a₁ ≤ n) (ha₂ : a₂ ≤ n) (ha₃ : a₃ ≤ n)
    (x : Point (OpeningResidueClosure p))
    (hx : IsSolution (coefficients (c : OpeningResidueClosure p)) x)
    (h₁ : cyclotomicTrace (omega ^ a₁) = trace (c : OpeningResidueClosure p) x.x1)
    (h₂ : cyclotomicTrace (omega ^ a₂) = trace (c : OpeningResidueClosure p) x.x2)
    (h₃ : cyclotomicTrace (omega ^ a₃) = trace (c : OpeningResidueClosure p) x.x3)
    (hsResidue : multiplier (c : OpeningResidueClosure p) ≠ 0)
    (hxne : x ≠ origin) :
    p ≤ integerArchimedeanBound c ^ n.totient := by
  let P := openingCyclotomicPrime p n hcoprime omega homega
  let eta : OpeningCyclotomicIntegers n :=
    openingCyclotomicIntegerDefect c n a₁ a₂ a₃
  have hdefectNe :
      cyclotomicDefect (c : OpeningCyclotomicField n)
        (openingCyclotomicRoot n ^ a₁)
        (openingCyclotomicRoot n ^ a₂)
        (openingCyclotomicRoot n ^ a₃) ≠ 0 :=
    openingCyclotomicDefect_ne_zero_of_punctured_residuePoint
      c hs hc p n a₁ a₂ a₃ hcoprime omega homega ha₁ ha₂ ha₃
        x h₁ h₂ h₃ hsResidue hxne
  have hetaNe : eta ≠ 0 := by
    intro heta
    apply hdefectNe
    have hcoe := congrArg
      (fun q : OpeningCyclotomicIntegers n => (q : OpeningCyclotomicField n)) heta
    simpa [eta, coe_openingCyclotomicIntegerDefect
      c n a₁ a₂ a₃ ha₁ ha₂ ha₃] using hcoe
  have hetaMem : eta ∈ P := by
    simpa [eta, P] using
      openingCyclotomicIntegerDefect_mem_prime_of_solution
        c p n a₁ a₂ a₃ hcoprime omega homega ha₁ ha₂ ha₃
          x hx h₁ h₂ h₃
  have hquotient : Ideal.Quotient.mk P eta = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hetaMem
  have hpNorm : p ≤ (Algebra.norm ℤ eta).natAbs :=
    BGS.Markoff.modulus_le_integerNorm_natAbs_of_quotient_eq_zero
      P p eta
        (by simpa [P] using
          openingCyclotomicPrime_under p n hcoprime omega homega)
        hquotient hetaNe
  exact hpNorm.trans <| by
    simpa [eta] using
      openingCyclotomicIntegerDefect_integerNorm_natAbs_le
        c n a₁ a₂ a₃ ha₁ ha₂ ha₃

end GenMarkoff.Symmetric.Opening
