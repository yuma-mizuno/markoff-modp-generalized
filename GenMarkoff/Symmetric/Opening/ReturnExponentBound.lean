import GenMarkoff.Symmetric.Opening.CyclotomicBound
import GenMarkoff.Symmetric.Opening.PeriodicSemisimple
import GenMarkoff.Symmetric.Opening.SimultaneousRouting
import Mathlib.Algebra.CharP.Reduced
import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# From affine return exponents to the symmetric opening bound

This module starts with explicit positive return exponents for the three
nonparabolic, non-centered affine fiber steps at one punctured residue point.
It constructs compatible torsion eigenvalues and feeds them into the concrete
cyclotomic bound.
-/

namespace GenMarkoff.Symmetric.Opening

open BGS.Markoff

/-- Coordinatewise transport of a point along a ring homomorphism. -/
def mapPoint {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : Point R) : Point S :=
  ⟨f x.x1, f x.x2, f x.x3⟩

/-- Coordinatewise transport of a moving pair along a ring homomorphism. -/
def mapPair {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (v : R × R) : S × S :=
  (f v.1, f v.2)

theorem isSolution_mapPoint_symmetric
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c : R) (x : Point R)
    (hx : IsSolution (coefficients c) x) :
    IsSolution (coefficients (f c)) (mapPoint f x) := by
  have hmap := congrArg f hx
  simpa [IsSolution, polynomial, coefficients, multiplier,
    Coefficients.multiplier, mapPoint, map_ofNat] using hmap

theorem mapPoint_ne_origin
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (hf : Function.Injective f) (x : Point R)
    (hx : x ≠ origin) : mapPoint f x ≠ origin := by
  intro hzero
  apply hx
  apply Point.ext
  · apply hf
    simpa [mapPoint, origin] using congrArg Point.x1 hzero
  · apply hf
    simpa [mapPoint, origin] using congrArg Point.x2 hzero
  · apply hf
    simpa [mapPoint, origin] using congrArg Point.x3 hzero

theorem map_trace
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c u : R) :
    f (trace c u) = trace (f c) (f u) := by
  simp [trace, multiplier, map_ofNat]

theorem mapPair_affineStep
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c u t : R) (v : R × R) :
    mapPair f (affineStep c u t v) =
      affineStep (f c) (f u) (f t) (mapPair f v) := by
  ext <;> simp [mapPair, affineStep]

theorem mapPair_iterate_affineStep
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c u t : R) (v : R × R) (n : ℕ) :
    mapPair f (((affineStep c u t)^[n]) v) =
      ((affineStep (f c) (f u) (f t))^[n]) (mapPair f v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        mapPair_affineStep, ih]

@[simp]
theorem mapPair_movingCoordinates1
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : Point R) :
    mapPair f (movingCoordinates1 x) = movingCoordinates1 (mapPoint f x) :=
  rfl

@[simp]
theorem mapPair_movingCoordinates2
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : Point R) :
    mapPair f (movingCoordinates2 x) = movingCoordinates2 (mapPoint f x) :=
  rfl

@[simp]
theorem mapPair_movingCoordinates3
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : Point R) :
    mapPair f (movingCoordinates3 x) = movingCoordinates3 (mapPoint f x) :=
  rfl

/-- Candidate regularity is preserved by an injective field homomorphism. -/
theorem orderedTraceCandidateRegular_map
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (hf : Function.Injective f)
    {A B C t : K} (h : OrderedTraceCandidateRegular A B C t) :
    OrderedTraceCandidateRegular (f A) (f B) (f C) (f t) := by
  rcases h with ⟨hD, htA, hcenter, hweight, hminus, hplus⟩
  simp only [eval_orderedTraceDiscriminantPolynomial] at hD ⊢
  simp only [eval_orderedTraceCenteredNormPolynomial] at hcenter ⊢
  simp only [eval_orderedTraceWeightDifferencePolynomial] at hweight ⊢
  simp only [eval_orderedTraceEvenMinusPolynomial] at hminus ⊢
  simp only [eval_orderedTraceEvenPlusPolynomial] at hplus ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hD
  · simpa using (map_ne_zero_iff f hf).mpr htA
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hcenter
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hweight
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hminus
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hplus

/-- Every element of a group acting on a finite orbit has a positive local
return exponent at the base point bounded by that orbit's cardinality.

The fixed-point case has return exponent one.  Otherwise the exponent is the
order of the cycle containing the base point, not the order of the full
permutation (which need not be bounded by the size of the underlying set). -/
theorem exists_positive_return_le_orbit_ncard
    {G X : Type*} [Group G] [MulAction G X]
    (g : G) (x : X) [Finite (MulAction.orbit G x)] :
    ∃ r : ℕ, 0 < r ∧ r ≤ (MulAction.orbit G x).ncard ∧
      (g ^ r) • x = x := by
  classical
  letI := Fintype.ofFinite (MulAction.orbit G x)
  let sigma : Equiv.Perm (MulAction.orbit G x) := MulAction.toPerm g
  let x' : MulAction.orbit G x := ⟨x, MulAction.mem_orbit_self x⟩
  letI : Nonempty (MulAction.orbit G x) := ⟨x'⟩
  by_cases hfix : sigma x' = x'
  · refine ⟨1, by simp, ?_, ?_⟩
    · rw [← Nat.card_coe_set_eq]
      exact Nat.card_pos
    · have hval := congrArg Subtype.val hfix
      simpa [sigma, x'] using hval
  · let tau := sigma.cycleOf x'
    let r := orderOf tau
    have htau : tau.IsCycle := sigma.isCycle_cycleOf hfix
    have hr : 0 < r := orderOf_pos tau
    have hrle : r ≤ (MulAction.orbit G x).ncard := by
      rw [← Nat.card_coe_set_eq]
      calc
        r = tau.support.card := htau.orderOf
        _ ≤ Fintype.card (MulAction.orbit G x) := Finset.card_le_univ _
        _ = Nat.card (MulAction.orbit G x) := by simp
    refine ⟨r, hr, hrle, ?_⟩
    have hpow : tau ^ r = 1 := pow_orderOf_eq_one tau
    have happ := congrArg
      (fun q : Equiv.Perm (MulAction.orbit G x) => q x') hpow
    have hcyclepow : (tau ^ r) x' = (sigma ^ r) x' := by
      change ((sigma.cycleOf x') ^ r) x' = (sigma ^ r) x'
      exact Equiv.Perm.cycleOf_pow_apply_self sigma x' r
    have hval : ((sigma ^ r) x').1 = x := by
      rw [← hcyclepow]
      simpa using congrArg Subtype.val happ
    change ((((MulAction.toPermHom G (MulAction.orbit G x)) g) ^ r) x').1 = x
      at hval
    rw [← map_pow (MulAction.toPermHom G (MulAction.orbit G x)) g r] at hval
    simpa only [MulAction.toPermHom_apply, MulAction.toPerm_apply,
      MulAction.orbit.coe_smul] using hval

theorem coe_iterate_oneStep1SurfacePerm
    {R : Type*} [CommRing R] (c : R) (n : ℕ)
    (x : SolutionSurface (coefficients c)) :
    (((oneStep1SurfacePerm c : Equiv.Perm
      (SolutionSurface (coefficients c))) :
        SolutionSurface (coefficients c) → SolutionSurface (coefficients c))^[n] x).1 =
      ((oneStep1 c)^[n]) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        coe_oneStep1SurfacePerm, ih]

theorem coe_iterate_oneStep2SurfacePerm
    {R : Type*} [CommRing R] (c : R) (n : ℕ)
    (x : SolutionSurface (coefficients c)) :
    (((oneStep2SurfacePerm c : Equiv.Perm
      (SolutionSurface (coefficients c))) :
        SolutionSurface (coefficients c) → SolutionSurface (coefficients c))^[n] x).1 =
      ((oneStep2 c)^[n]) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        coe_oneStep2SurfacePerm, ih]

theorem coe_iterate_oneStep3SurfacePerm
    {R : Type*} [CommRing R] (c : R) (n : ℕ)
    (x : SolutionSurface (coefficients c)) :
    (((oneStep3SurfacePerm c : Equiv.Perm
      (SolutionSurface (coefficients c))) :
        SolutionSurface (coefficients c) → SolutionSurface (coefficients c))^[n] x).1 =
      ((oneStep3 c)^[n]) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        coe_oneStep3SurfacePerm, ih]

@[simp]
theorem iterate_oneStep2_x2
    {R : Type*} [CommRing R] (c : R) (x : Point R) (n : ℕ) :
    (((oneStep2 c)^[n]) x).x2 = x.x2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change (((oneStep2 c)^[n]) x).x2 = x.x2
      exact ih

@[simp]
theorem iterate_oneStep3_x3
    {R : Type*} [CommRing R] (c : R) (x : Point R) (n : ℕ) :
    (((oneStep3 c)^[n]) x).x3 = x.x3 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change (((oneStep3 c)^[n]) x).x3 = x.x3
      exact ih

theorem movingCoordinates2_iterate_oneStep2
    {R : Type*} [CommRing R] (c : R) (x : Point R) (n : ℕ) :
    movingCoordinates2 (((oneStep2 c)^[n]) x) =
      ((fiberStep c x.x2)^[n]) (movingCoordinates2 x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', movingCoordinates2_oneStep2,
        iterate_oneStep2_x2, ih, Function.iterate_succ_apply']

theorem movingCoordinates3_iterate_oneStep3
    {R : Type*} [CommRing R] (c : R) (x : Point R) (n : ℕ) :
    movingCoordinates3 (((oneStep3 c)^[n]) x) =
      ((fiberStep c x.x3)^[n]) (movingCoordinates3 x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', movingCoordinates3_oneStep3,
        iterate_oneStep3_x3, ih, Function.iterate_succ_apply']

/-- Each of the three one-step generators has a positive local return bounded
by the cardinality of the full one-step orbit. -/
theorem exists_oneStep_returns_le_puncturedOneStepOrbit_ncard
    {R : Type*} [CommRing R] (c : R)
    (x : PuncturedSolutionSurface (coefficients c))
    (hfinite : (puncturedOneStepOrbit x).Finite) :
    ∃ r₁ r₂ r₃ : ℕ,
      0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃ ∧
      r₁ ≤ (puncturedOneStepOrbit x).ncard ∧
      r₂ ≤ (puncturedOneStepOrbit x).ncard ∧
      r₃ ≤ (puncturedOneStepOrbit x).ncard ∧
      ((oneStep1 c)^[r₁]) x.1.1 = x.1.1 ∧
      ((oneStep2 c)^[r₂]) x.1.1 = x.1.1 ∧
      ((oneStep3 c)^[r₃]) x.1.1 = x.1.1 := by
  have hf : (MulAction.orbit (OneStepGroup c) x).Finite := by
    simpa only [puncturedOneStepOrbit] using hfinite
  letI : Fintype (MulAction.orbit (OneStepGroup c) x) := hf.fintype
  let g₁ : OneStepGroup c :=
    ⟨oneStep1SurfacePerm c, oneStep1SurfacePerm_mem_OneStepGroup c⟩
  let g₂ : OneStepGroup c :=
    ⟨oneStep2SurfacePerm c, oneStep2SurfacePerm_mem_OneStepGroup c⟩
  let g₃ : OneStepGroup c :=
    ⟨oneStep3SurfacePerm c, oneStep3SurfacePerm_mem_OneStepGroup c⟩
  obtain ⟨r₁, hr₁, hr₁le, hreturn₁⟩ :=
    exists_positive_return_le_orbit_ncard g₁ x
  obtain ⟨r₂, hr₂, hr₂le, hreturn₂⟩ :=
    exists_positive_return_le_orbit_ncard g₂ x
  obtain ⟨r₃, hr₃, hr₃le, hreturn₃⟩ :=
    exists_positive_return_le_orbit_ncard g₃ x
  have hpoint₁ : ((oneStep1 c)^[r₁]) x.1.1 = x.1.1 := by
    have hval := congrArg
      (fun y : PuncturedSolutionSurface (coefficients c) => y.1.1) hreturn₁
    change (((oneStep1SurfacePerm c) ^ r₁) x.1).1 = x.1.1 at hval
    rw [Equiv.Perm.coe_pow] at hval
    simpa only [coe_iterate_oneStep1SurfacePerm] using hval
  have hpoint₂ : ((oneStep2 c)^[r₂]) x.1.1 = x.1.1 := by
    have hval := congrArg
      (fun y : PuncturedSolutionSurface (coefficients c) => y.1.1) hreturn₂
    change (((oneStep2SurfacePerm c) ^ r₂) x.1).1 = x.1.1 at hval
    rw [Equiv.Perm.coe_pow] at hval
    simpa only [coe_iterate_oneStep2SurfacePerm] using hval
  have hpoint₃ : ((oneStep3 c)^[r₃]) x.1.1 = x.1.1 := by
    have hval := congrArg
      (fun y : PuncturedSolutionSurface (coefficients c) => y.1.1) hreturn₃
    change (((oneStep3SurfacePerm c) ^ r₃) x.1).1 = x.1.1 at hval
    rw [Equiv.Perm.coe_pow] at hval
    simpa only [coe_iterate_oneStep3SurfacePerm] using hval
  exact ⟨r₁, r₂, r₃, hr₁, hr₂, hr₃, hr₁le, hr₂le, hr₃le,
    hpoint₁, hpoint₂, hpoint₃⟩

/-- Point returns from the finite one-step orbit induce affine fiber returns
with the same exponents and cardinality bounds. -/
theorem exists_affineStep_returns_le_puncturedOneStepOrbit_ncard
    {R : Type*} [CommRing R] (c : R)
    (x : PuncturedSolutionSurface (coefficients c))
    (hfinite : (puncturedOneStepOrbit x).Finite) :
    ∃ r₁ r₂ r₃ : ℕ,
      0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃ ∧
      r₁ ≤ (puncturedOneStepOrbit x).ncard ∧
      r₂ ≤ (puncturedOneStepOrbit x).ncard ∧
      r₃ ≤ (puncturedOneStepOrbit x).ncard ∧
      ((affineStep c x.1.1.x1 (trace c x.1.1.x1))^[r₁])
          (movingCoordinates1 x.1.1) = movingCoordinates1 x.1.1 ∧
      ((affineStep c x.1.1.x2 (trace c x.1.1.x2))^[r₂])
          (movingCoordinates2 x.1.1) = movingCoordinates2 x.1.1 ∧
      ((affineStep c x.1.1.x3 (trace c x.1.1.x3))^[r₃])
          (movingCoordinates3 x.1.1) = movingCoordinates3 x.1.1 := by
  obtain ⟨r₁, r₂, r₃, hr₁, hr₂, hr₃, hr₁le, hr₂le, hr₃le,
      hpoint₁, hpoint₂, hpoint₃⟩ :=
    exists_oneStep_returns_le_puncturedOneStepOrbit_ncard c x hfinite
  have hpair₁ := congrArg movingCoordinates1 hpoint₁
  have hpair₂ := congrArg movingCoordinates2 hpoint₂
  have hpair₃ := congrArg movingCoordinates3 hpoint₃
  rw [movingCoordinates1_iterate_oneStep1] at hpair₁
  rw [movingCoordinates2_iterate_oneStep2] at hpair₂
  rw [movingCoordinates3_iterate_oneStep3] at hpair₃
  exact ⟨r₁, r₂, r₃, hr₁, hr₂, hr₃, hr₁le, hr₂le, hr₃le,
    by simpa only [fiberStep] using hpair₁,
    by simpa only [fiberStep] using hpair₂,
    by simpa only [fiberStep] using hpair₃⟩

private theorem eigenvalue_sq_ne_one_of_trace_nonparabolic
    {K : Type*} [Field K] (t : K) (w : Kˣ)
    (htrace : t = BGS.Markoff.splitTorusTrace w) (ht : t ^ 2 ≠ 4) :
    (w : K) ^ 2 ≠ 1 := by
  intro hw
  have hinv : ((w⁻¹ : Kˣ) : K) = (w : K) := by
    apply mul_right_cancel₀ (Units.ne_zero w)
    simpa [pow_two] using hw.symm
  apply ht
  rw [htrace, BGS.Markoff.splitTorusTrace, hinv]
  calc
    ((w : K) + (w : K)) ^ 2 = 4 * (w : K) ^ 2 := by ring
    _ = 4 := by rw [hw]; ring

private theorem some_eigenCoordinate_ne_zero
    {K : Type*} [Field K] (w : Kˣ) (hw : (w : K) ^ 2 ≠ 1)
    {v : K × K} (hv : v ≠ (0, 0)) :
    firstEigenCoordinate w v ≠ 0 ∨ secondEigenCoordinate w v ≠ 0 := by
  by_contra h
  push Not at h
  rcases h with ⟨hfirst, hsecond⟩
  apply hv
  apply Prod.ext
  · have hsum := first_add_secondEigenCoordinate w hw v
    simpa [hfirst, hsecond] using hsum.symm
  · have hsum := first_mul_add_second_mul_invEigenCoordinate w hw v
    simpa [hfirst, hsecond] using hsum.symm

/-- A positive return of a nonparabolic, non-centered affine step produces a
torsion eigenvalue whose exact order divides the stated return exponent. -/
theorem periodic_affineStep_has_torsion_eigenvalue_orderOf_dvd
    {K : Type*} [Field K] [IsAlgClosed K]
    (c u t : K) (v : K × K)
    (htTwo : t ≠ 2) (ht : t ^ 2 ≠ 4)
    (hv : centerCoordinates (fiberCenter c u t) v ≠ (0, 0))
    (n : ℕ) (hn : 0 < n)
    (hperiodic : ((affineStep c u t)^[n]) v = v) :
    ∃ w : Kˣ, IsOfFinOrder w ∧ orderOf w ∣ n ∧
      t = BGS.Markoff.splitTorusTrace w := by
  obtain ⟨w, hwfin, htrace⟩ :=
    periodic_affineStep_has_torsion_eigenvalue
      c u t v htTwo ht hv n hn hperiodic
  have hw : (w : K) ^ 2 ≠ 1 :=
    eigenvalue_sq_ne_one_of_trace_nonparabolic t w htrace ht
  have hcenterPeriodic :
      ((linearStep t)^[n]) (centerCoordinates (fiberCenter c u t) v) =
        centerCoordinates (fiberCenter c u t) v := by
    have h := congrArg (centerCoordinates (fiberCenter c u t)) hperiodic
    rwa [centerCoordinates_iterate_affineStep c u t v htTwo] at h
  have hcenterPeriodic' :
      ((linearStep (BGS.Markoff.splitTorusTrace w))^[n])
          (centerCoordinates (fiberCenter c u t) v) =
        centerCoordinates (fiberCenter c u t) v := by
    rwa [← htrace]
  rcases some_eigenCoordinate_ne_zero w hw hv with hfirst | hsecond
  · have heq := congrArg (firstEigenCoordinate w) hcenterPeriodic'
    rw [firstEigenCoordinate_iterate_linearStep w hw] at heq
    have hpow : (w : K) ^ n = 1 := by
      apply mul_left_cancel₀ hfirst
      simpa using heq
    have hpowUnits : w ^ n = 1 := by
      apply Units.ext
      exact hpow
    exact ⟨w, hwfin, orderOf_dvd_iff_pow_eq_one.mpr hpowUnits, htrace⟩
  · have heq := congrArg (secondEigenCoordinate w) hcenterPeriodic'
    rw [secondEigenCoordinate_iterate_linearStep w hw] at heq
    have hpowInv : ((w⁻¹ : Kˣ) : K) ^ n = 1 := by
      apply mul_left_cancel₀ hsecond
      simpa using heq
    have hpowInvUnits : (w⁻¹ : Kˣ) ^ n = 1 := by
      apply Units.ext
      exact hpowInv
    have hpowUnits : w ^ n = 1 := by
      have h := congrArg Inv.inv hpowInvUnits
      simpa using h
    exact ⟨w, hwfin, orderOf_dvd_iff_pow_eq_one.mpr hpowUnits, htrace⟩

/-- Every finite-order unit in the chosen characteristic-`p` residue closure
has order coprime to `p`. -/
theorem prime_coprime_orderOf_residueClosureUnit
    (p : ℕ) [Fact p.Prime]
    (w : (OpeningResidueClosure p)ˣ) (hwfin : IsOfFinOrder w) :
    Nat.Coprime p (orderOf w) := by
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.2
  intro hpOrder
  let ell := orderOf w
  let m := ell / p
  have hellPos : 0 < ell := hwfin.orderOf_pos
  have hpMul : p * m = ell := by
    exact Nat.mul_div_cancel' hpOrder
  have hpowEll : (w : OpeningResidueClosure p) ^ ell = 1 := by
    have hpowUnits : w ^ ell = 1 := by
      change w ^ orderOf w = 1
      exact pow_orderOf_eq_one w
    have hval := congrArg Units.val hpowUnits
    exact hval
  have hpowPM : (w : OpeningResidueClosure p) ^ (p ^ 1 * m) = 1 := by
    simpa [pow_one, hpMul] using hpowEll
  have hpowM : (w : OpeningResidueClosure p) ^ m = 1 :=
    (ExpChar.pow_prime_pow_mul_eq_one_iff
      p 1 m (w : OpeningResidueClosure p)).mp hpowPM
  have horderDvdM : ell ∣ m := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    apply Units.ext
    exact hpowM
  have hmPos : 0 < m := by
    simpa [m] using
      Nat.div_pos (Nat.le_of_dvd hellPos hpOrder) (Fact.out : p.Prime).pos
  have hellLeM : ell ≤ m := Nat.le_of_dvd hmPos horderDvdM
  have hmLtEll : m < ell := by
    simpa [m] using Nat.div_lt_self hellPos (Fact.out : p.Prime).one_lt
  omega

/-- Three finite-order residue eigenvalues whose exact orders divide explicit
return exponents give the cyclotomic opening bound with the lcm of those
returns as exponent.  Using the lcm retains the common-period information and
is sharper than replacing it by a product or a cube of the maximum. -/
theorem modulus_le_integerArchimedeanBound_pow_lcm_of_return_eigenvalues
    (c : ℤ) (hs : 3 * (1 + c) ≠ 0) (hc : c ^ 2 ≠ 4)
    (p : ℕ) [Fact p.Prime]
    (x : Point (OpeningResidueClosure p))
    (hx : IsSolution (coefficients (c : OpeningResidueClosure p)) x)
    (hsResidue : multiplier (c : OpeningResidueClosure p) ≠ 0)
    (hxne : x ≠ origin)
    (r₁ r₂ r₃ : ℕ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (W₁ W₂ W₃ : (OpeningResidueClosure p)ˣ)
    (hfin₁ : IsOfFinOrder W₁) (hfin₂ : IsOfFinOrder W₂)
    (hfin₃ : IsOfFinOrder W₃)
    (horder₁ : orderOf W₁ ∣ r₁) (horder₂ : orderOf W₂ ∣ r₂)
    (horder₃ : orderOf W₃ ∣ r₃)
    (htrace₁ : trace (c : OpeningResidueClosure p) x.x1 =
      BGS.Markoff.splitTorusTrace W₁)
    (htrace₂ : trace (c : OpeningResidueClosure p) x.x2 =
      BGS.Markoff.splitTorusTrace W₂)
    (htrace₃ : trace (c : OpeningResidueClosure p) x.x3 =
      BGS.Markoff.splitTorusTrace W₃) :
    p ≤ integerArchimedeanBound c ^ Nat.lcm r₁ (Nat.lcm r₂ r₃) := by
  let l₁ := orderOf W₁
  let l₂ := orderOf W₂
  let l₃ := orderOf W₃
  let n := Nat.lcm l₁ (Nat.lcm l₂ l₃)
  let R := Nat.lcm r₁ (Nat.lcm r₂ r₃)
  have hl₁ : 0 < l₁ := hfin₁.orderOf_pos
  have hl₂ : 0 < l₂ := hfin₂.orderOf_pos
  have hl₃ : 0 < l₃ := hfin₃.orderOf_pos
  have hn : 0 < n := Nat.lcm_pos hl₁ (Nat.lcm_pos hl₂ hl₃)
  letI : NeZero n := ⟨hn.ne'⟩
  have hcoprime₁ : Nat.Coprime p l₁ := by
    simpa [l₁] using prime_coprime_orderOf_residueClosureUnit p W₁ hfin₁
  have hcoprime₂ : Nat.Coprime p l₂ := by
    simpa [l₂] using prime_coprime_orderOf_residueClosureUnit p W₂ hfin₂
  have hcoprime₃ : Nat.Coprime p l₃ := by
    simpa [l₃] using prime_coprime_orderOf_residueClosureUnit p W₃ hfin₃
  have hcoprimeN : Nat.Coprime p n := by
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.2
    exact (Fact.out : p.Prime).not_dvd_lcm
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcoprime₁)
      ((Fact.out : p.Prime).not_dvd_lcm
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcoprime₂)
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcoprime₃))
  have hW₁pow : (W₁ : OpeningResidueClosure p) ^ n = 1 := by
    simpa using congrArg Units.val
      (orderOf_dvd_iff_pow_eq_one.mp
        (Nat.dvd_lcm_left l₁ (Nat.lcm l₂ l₃)))
  have hW₂pow : (W₂ : OpeningResidueClosure p) ^ n = 1 := by
    have hdvd : l₂ ∣ n :=
      (Nat.dvd_lcm_left l₂ l₃).trans
        (Nat.dvd_lcm_right l₁ (Nat.lcm l₂ l₃))
    simpa using congrArg Units.val (orderOf_dvd_iff_pow_eq_one.mp hdvd)
  have hW₃pow : (W₃ : OpeningResidueClosure p) ^ n = 1 := by
    have hdvd : l₃ ∣ n :=
      (Nat.dvd_lcm_right l₂ l₃).trans
        (Nat.dvd_lcm_right l₁ (Nat.lcm l₂ l₃))
    simpa using congrArg Units.val (orderOf_dvd_iff_pow_eq_one.mp hdvd)
  obtain ⟨omega, a₁, a₂, a₃, homega, ha₁lt, ha₂lt, ha₃lt,
      ha₁, ha₂, ha₃⟩ :=
    BGS.Markoff.exists_residue_common_primitiveRoot_powers p n hcoprimeN
      (W₁ : OpeningResidueClosure p) (W₂ : OpeningResidueClosure p)
      (W₃ : OpeningResidueClosure p) hW₁pow hW₂pow hW₃pow
  have hcoord₁ : cyclotomicTrace (omega ^ a₁) =
      trace (c : OpeningResidueClosure p) x.x1 := by
    calc
      cyclotomicTrace (omega ^ a₁) =
          cyclotomicTrace (W₁ : OpeningResidueClosure p) := by rw [ha₁]
      _ = BGS.Markoff.splitTorusTrace W₁ := by
        simp [cyclotomicTrace, BGS.Markoff.splitTorusTrace]
      _ = trace (c : OpeningResidueClosure p) x.x1 := htrace₁.symm
  have hcoord₂ : cyclotomicTrace (omega ^ a₂) =
      trace (c : OpeningResidueClosure p) x.x2 := by
    calc
      cyclotomicTrace (omega ^ a₂) =
          cyclotomicTrace (W₂ : OpeningResidueClosure p) := by rw [ha₂]
      _ = BGS.Markoff.splitTorusTrace W₂ := by
        simp [cyclotomicTrace, BGS.Markoff.splitTorusTrace]
      _ = trace (c : OpeningResidueClosure p) x.x2 := htrace₂.symm
  have hcoord₃ : cyclotomicTrace (omega ^ a₃) =
      trace (c : OpeningResidueClosure p) x.x3 := by
    calc
      cyclotomicTrace (omega ^ a₃) =
          cyclotomicTrace (W₃ : OpeningResidueClosure p) := by rw [ha₃]
      _ = BGS.Markoff.splitTorusTrace W₃ := by
        simp [cyclotomicTrace, BGS.Markoff.splitTorusTrace]
      _ = trace (c : OpeningResidueClosure p) x.x3 := htrace₃.symm
  have hpCyclotomic : p ≤ integerArchimedeanBound c ^ n.totient :=
    modulus_le_integerArchimedeanBound_pow_totient_of_compatible_residue_traces
      c hs hc p n a₁ a₂ a₃ hcoprimeN omega homega
        (Nat.le_of_lt ha₁lt) (Nat.le_of_lt ha₂lt) (Nat.le_of_lt ha₃lt)
        x hx hcoord₁ hcoord₂ hcoord₃ hsResidue hxne
  have hl₁R : l₁ ∣ R := by
    simpa [l₁, R] using
      horder₁.trans (Nat.dvd_lcm_left r₁ (Nat.lcm r₂ r₃))
  have hl₂R : l₂ ∣ R := by
    simpa [l₂, R] using horder₂.trans
      ((Nat.dvd_lcm_left r₂ r₃).trans
        (Nat.dvd_lcm_right r₁ (Nat.lcm r₂ r₃)))
  have hl₃R : l₃ ∣ R := by
    simpa [l₃, R] using horder₃.trans
      ((Nat.dvd_lcm_right r₂ r₃).trans
        (Nat.dvd_lcm_right r₁ (Nat.lcm r₂ r₃)))
  have hnR : n ∣ R := Nat.lcm_dvd hl₁R (Nat.lcm_dvd hl₂R hl₃R)
  have hR : 0 < R := Nat.lcm_pos hr₁ (Nat.lcm_pos hr₂ hr₃)
  have htotient : n.totient ≤ R :=
    (Nat.totient_le n).trans (Nat.le_of_dvd hR hnR)
  exact hpCyclotomic.trans
    (Nat.pow_le_pow_right (by simp [integerArchimedeanBound]) htotient)

/-- Explicit positive returns for the three nonparabolic, non-centered affine
fiber steps at a punctured symmetric residue point imply the concrete opening
bound with the lcm of the three return exponents.  The parabolic and centered
obstructions remain visible as hypotheses. -/
theorem modulus_le_integerArchimedeanBound_pow_lcm_of_periodic_affineSteps
    (c : ℤ) (hs : 3 * (1 + c) ≠ 0) (hc : c ^ 2 ≠ 4)
    (p : ℕ) [Fact p.Prime]
    (x : Point (OpeningResidueClosure p))
    (hx : IsSolution (coefficients (c : OpeningResidueClosure p)) x)
    (hsResidue : multiplier (c : OpeningResidueClosure p) ≠ 0)
    (hxne : x ≠ origin)
    (r₁ r₂ r₃ : ℕ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (ht₁Two : trace (c : OpeningResidueClosure p) x.x1 ≠ 2)
    (ht₂Two : trace (c : OpeningResidueClosure p) x.x2 ≠ 2)
    (ht₃Two : trace (c : OpeningResidueClosure p) x.x3 ≠ 2)
    (ht₁ : trace (c : OpeningResidueClosure p) x.x1 ^ 2 ≠ 4)
    (ht₂ : trace (c : OpeningResidueClosure p) x.x2 ^ 2 ≠ 4)
    (ht₃ : trace (c : OpeningResidueClosure p) x.x3 ^ 2 ≠ 4)
    (hv₁ : centerCoordinates
      (fiberCenter (c : OpeningResidueClosure p) x.x1
        (trace (c : OpeningResidueClosure p) x.x1))
      (movingCoordinates1 x) ≠ (0, 0))
    (hv₂ : centerCoordinates
      (fiberCenter (c : OpeningResidueClosure p) x.x2
        (trace (c : OpeningResidueClosure p) x.x2))
      (movingCoordinates2 x) ≠ (0, 0))
    (hv₃ : centerCoordinates
      (fiberCenter (c : OpeningResidueClosure p) x.x3
        (trace (c : OpeningResidueClosure p) x.x3))
      (movingCoordinates3 x) ≠ (0, 0))
    (hperiodic₁ :
      ((affineStep (c : OpeningResidueClosure p) x.x1
        (trace (c : OpeningResidueClosure p) x.x1))^[r₁])
          (movingCoordinates1 x) = movingCoordinates1 x)
    (hperiodic₂ :
      ((affineStep (c : OpeningResidueClosure p) x.x2
        (trace (c : OpeningResidueClosure p) x.x2))^[r₂])
          (movingCoordinates2 x) = movingCoordinates2 x)
    (hperiodic₃ :
      ((affineStep (c : OpeningResidueClosure p) x.x3
        (trace (c : OpeningResidueClosure p) x.x3))^[r₃])
          (movingCoordinates3 x) = movingCoordinates3 x) :
    p ≤ integerArchimedeanBound c ^ Nat.lcm r₁ (Nat.lcm r₂ r₃) := by
  obtain ⟨W₁, hfin₁, horder₁, htrace₁⟩ :=
    periodic_affineStep_has_torsion_eigenvalue_orderOf_dvd
      (c : OpeningResidueClosure p) x.x1
      (trace (c : OpeningResidueClosure p) x.x1) (movingCoordinates1 x)
      ht₁Two ht₁ hv₁ r₁ hr₁ hperiodic₁
  obtain ⟨W₂, hfin₂, horder₂, htrace₂⟩ :=
    periodic_affineStep_has_torsion_eigenvalue_orderOf_dvd
      (c : OpeningResidueClosure p) x.x2
      (trace (c : OpeningResidueClosure p) x.x2) (movingCoordinates2 x)
      ht₂Two ht₂ hv₂ r₂ hr₂ hperiodic₂
  obtain ⟨W₃, hfin₃, horder₃, htrace₃⟩ :=
    periodic_affineStep_has_torsion_eigenvalue_orderOf_dvd
      (c : OpeningResidueClosure p) x.x3
      (trace (c : OpeningResidueClosure p) x.x3) (movingCoordinates3 x)
      ht₃Two ht₃ hv₃ r₃ hr₃ hperiodic₃
  exact modulus_le_integerArchimedeanBound_pow_lcm_of_return_eigenvalues
    c hs hc p x hx hsResidue hxne r₁ r₂ r₃ hr₁ hr₂ hr₃
      W₁ W₂ W₃ hfin₁ hfin₂ hfin₃ horder₁ horder₂ horder₃
      htrace₁ htrace₂ htrace₃

/-- The lcm of three positive return exponents is bounded by the cube of
their maximum. -/
theorem lcm_three_le_max_cube
    (r₁ r₂ r₃ : ℕ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃) :
    Nat.lcm r₁ (Nat.lcm r₂ r₃) ≤ max r₁ (max r₂ r₃) ^ 3 := by
  let m := max r₁ (max r₂ r₃)
  have hr₁m : r₁ ≤ m := le_max_left _ _
  have hr₂m : r₂ ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hr₃m : r₃ ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  calc
    Nat.lcm r₁ (Nat.lcm r₂ r₃) ≤ r₁ * Nat.lcm r₂ r₃ :=
      Nat.lcm_le_mul hr₁ (Nat.lcm_pos hr₂ hr₃)
    _ ≤ r₁ * (r₂ * r₃) :=
      Nat.mul_le_mul_left r₁ (Nat.lcm_le_mul hr₂ hr₃)
    _ = r₁ * r₂ * r₃ := by ring
    _ ≤ m * m * m := Nat.mul_le_mul (Nat.mul_le_mul hr₁m hr₂m) hr₃m
    _ = m ^ 3 := by ring

/-- Arithmetic orbit-card endpoint: if the three positive return exponents
are each at most `m`, the exact lcm opening bound implies the familiar cube
bound with exponent `m ^ 3`. -/
theorem modulus_le_integerArchimedeanBound_pow_card_cube_of_lcm_returns
    (c : ℤ) (p r₁ r₂ r₃ m : ℕ)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (hr₁m : r₁ ≤ m) (hr₂m : r₂ ≤ m) (hr₃m : r₃ ≤ m)
    (hbound :
      p ≤ integerArchimedeanBound c ^ Nat.lcm r₁ (Nat.lcm r₂ r₃)) :
    p ≤ integerArchimedeanBound c ^ m ^ 3 := by
  have hmax : max r₁ (max r₂ r₃) ≤ m :=
    max_le hr₁m (max_le hr₂m hr₃m)
  have hexponent : Nat.lcm r₁ (Nat.lcm r₂ r₃) ≤ m ^ 3 :=
    (lcm_three_le_max_cube r₁ r₂ r₃ hr₁ hr₂ hr₃).trans
      (Nat.pow_le_pow_left hmax 3)
  exact hbound.trans
    (Nat.pow_le_pow_right (by simp [integerArchimedeanBound]) hexponent)

/-- An exact eigenvalue order dividing a positive return exponent is bounded
by every bound for that return exponent.  In the intended application `m` is
the cardinality of the full one-step orbit. -/
theorem orderOf_le_of_orderOf_dvd_return_le
    {K : Type*} [Monoid K] (w : K) (r m : ℕ)
    (hr : 0 < r) (horder : orderOf w ∣ r) (hrm : r ≤ m) :
    orderOf w ≤ m :=
  (Nat.le_of_dvd hr horder).trans hrm

/-- Cyclic second-axis form of candidate regularity excluding the affine
center obstruction. -/
theorem centeredMovingCoordinates2_ne_zero_of_candidateRegular
    {K : Type*} [Field K] (c : K) (x : Point K)
    (hx : IsSolution (coefficients c) x)
    (hregular : OrderedTraceCandidateRegular c c c (trace c x.x2)) :
    centerCoordinates (fiberCenter c x.x2 (trace c x.x2))
        (movingCoordinates2 x) ≠ (0, 0) := by
  have hsolution : IsSolution (coefficients c) (cycleLeftEquiv x) :=
    (isSolution_cycleLeftEquiv c x).2 hx
  have hregular' : OrderedTraceCandidateRegular c c c
      (trace c (cycleLeftEquiv x).x1) := by
    simpa [cycleLeftEquiv] using hregular
  simpa [cycleLeftEquiv, movingCoordinates1, movingCoordinates2] using
    centeredMovingCoordinates1_ne_zero_of_candidateRegular
      c (cycleLeftEquiv x) hsolution hregular'

/-- Cyclic third-axis form of candidate regularity excluding the affine
center obstruction. -/
theorem centeredMovingCoordinates3_ne_zero_of_candidateRegular
    {K : Type*} [Field K] (c : K) (x : Point K)
    (hx : IsSolution (coefficients c) x)
    (hregular : OrderedTraceCandidateRegular c c c (trace c x.x3)) :
    centerCoordinates (fiberCenter c x.x3 (trace c x.x3))
        (movingCoordinates3 x) ≠ (0, 0) := by
  have hsolution : IsSolution (coefficients c) (cycleRightEquiv x) :=
    (isSolution_cycleRightEquiv c x).2 hx
  have hregular' : OrderedTraceCandidateRegular c c c
      (trace c (cycleRightEquiv x).x1) := by
    simpa [cycleRightEquiv, cycleLeftEquiv] using hregular
  simpa [cycleRightEquiv, cycleLeftEquiv, movingCoordinates1,
    movingCoordinates3] using
    centeredMovingCoordinates1_ne_zero_of_candidateRegular
      c (cycleRightEquiv x) hsolution hregular'

/-- A prime-field point transported to the fixed algebraic residue closure. -/
noncomputable def openingResiduePoint
    (p : ℕ) [Fact p.Prime] (x : Point (ZMod p)) :
    Point (OpeningResidueClosure p) :=
  mapPoint (algebraMap (ZMod p) (OpeningResidueClosure p)) x

/-- Full one-step opening endpoint for the nonparabolic, non-centered case.

Starting with a punctured prime-field point, this theorem extracts three
positive local return exponents from its finite one-step orbit, transports
the affine returns to the algebraic residue closure, constructs the three
torsion eigenvalues, bounds each exact eigenvalue order by the one-step orbit
cardinality, constructs compatible powers of one primitive residue root, and
applies the coefficient-dependent cyclotomic norm bound.  It records both the
sharp lcm exponent and its orbit-cardinality cube corollary. -/
theorem exists_return_eigenvalues_with_oneStepOrbit_bounds
    (c : ℤ) (hs : 3 * (1 + c) ≠ 0) (hc : c ^ 2 ≠ 4)
    (p : ℕ) [Fact p.Prime]
    (x : PuncturedSolutionSurface (coefficients (c : ZMod p)))
    (hfinite : (puncturedOneStepOrbit x).Finite)
    (hsResidue : multiplier (c : OpeningResidueClosure p) ≠ 0)
    (ht₁ : trace (c : OpeningResidueClosure p)
        (openingResiduePoint p x.1.1).x1 ^ 2 ≠ 4)
    (ht₂ : trace (c : OpeningResidueClosure p)
        (openingResiduePoint p x.1.1).x2 ^ 2 ≠ 4)
    (ht₃ : trace (c : OpeningResidueClosure p)
        (openingResiduePoint p x.1.1).x3 ^ 2 ≠ 4)
    (hv₁ : centerCoordinates
      (fiberCenter (c : OpeningResidueClosure p)
        (openingResiduePoint p x.1.1).x1
        (trace (c : OpeningResidueClosure p)
          (openingResiduePoint p x.1.1).x1))
      (movingCoordinates1 (openingResiduePoint p x.1.1)) ≠ (0, 0))
    (hv₂ : centerCoordinates
      (fiberCenter (c : OpeningResidueClosure p)
        (openingResiduePoint p x.1.1).x2
        (trace (c : OpeningResidueClosure p)
          (openingResiduePoint p x.1.1).x2))
      (movingCoordinates2 (openingResiduePoint p x.1.1)) ≠ (0, 0))
    (hv₃ : centerCoordinates
      (fiberCenter (c : OpeningResidueClosure p)
        (openingResiduePoint p x.1.1).x3
        (trace (c : OpeningResidueClosure p)
          (openingResiduePoint p x.1.1).x3))
      (movingCoordinates3 (openingResiduePoint p x.1.1)) ≠ (0, 0)) :
    ∃ r₁ r₂ r₃ : ℕ,
      ∃ W₁ W₂ W₃ : (OpeningResidueClosure p)ˣ,
      0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃ ∧
      r₁ ≤ (puncturedOneStepOrbit x).ncard ∧
      r₂ ≤ (puncturedOneStepOrbit x).ncard ∧
      r₃ ≤ (puncturedOneStepOrbit x).ncard ∧
      IsOfFinOrder W₁ ∧ IsOfFinOrder W₂ ∧ IsOfFinOrder W₃ ∧
      orderOf W₁ ∣ r₁ ∧ orderOf W₂ ∣ r₂ ∧ orderOf W₃ ∣ r₃ ∧
      orderOf W₁ ≤ (puncturedOneStepOrbit x).ncard ∧
      orderOf W₂ ≤ (puncturedOneStepOrbit x).ncard ∧
      orderOf W₃ ≤ (puncturedOneStepOrbit x).ncard ∧
      trace (c : OpeningResidueClosure p)
          (openingResiduePoint p x.1.1).x1 =
        BGS.Markoff.splitTorusTrace W₁ ∧
      trace (c : OpeningResidueClosure p)
          (openingResiduePoint p x.1.1).x2 =
        BGS.Markoff.splitTorusTrace W₂ ∧
      trace (c : OpeningResidueClosure p)
          (openingResiduePoint p x.1.1).x3 =
        BGS.Markoff.splitTorusTrace W₃ ∧
      p ≤ integerArchimedeanBound c ^ Nat.lcm r₁ (Nat.lcm r₂ r₃) ∧
      p ≤ integerArchimedeanBound c ^ (puncturedOneStepOrbit x).ncard ^ 3 := by
  let f := algebraMap (ZMod p) (OpeningResidueClosure p)
  let xResidue := openingResiduePoint p x.1.1
  have hxResidue :
      IsSolution (coefficients (c : OpeningResidueClosure p)) xResidue := by
    simpa [xResidue, openingResiduePoint, f, map_intCast] using
      isSolution_mapPoint_symmetric f (c : ZMod p) x.1.1 x.1.2
  have hxPointNe : x.1.1 ≠ (origin : Point (ZMod p)) := by
    intro hzero
    apply x.2
    apply Subtype.ext
    exact hzero
  have hxResidueNe : xResidue ≠ origin := by
    simpa [xResidue, openingResiduePoint, f] using
      mapPoint_ne_origin f f.injective x.1.1 hxPointNe
  obtain ⟨r₁, r₂, r₃, hr₁, hr₂, hr₃, hr₁le, hr₂le, hr₃le,
      hreturn₁, hreturn₂, hreturn₃⟩ :=
    exists_affineStep_returns_le_puncturedOneStepOrbit_ncard
      (c : ZMod p) x hfinite
  have hreturnResidue₁ :
      ((affineStep (c : OpeningResidueClosure p) xResidue.x1
        (trace (c : OpeningResidueClosure p) xResidue.x1))^[r₁])
          (movingCoordinates1 xResidue) = movingCoordinates1 xResidue := by
    have hmap := congrArg (mapPair f) hreturn₁
    rw [mapPair_iterate_affineStep, map_trace] at hmap
    simpa [xResidue, openingResiduePoint, f, mapPoint, map_intCast] using hmap
  have hreturnResidue₂ :
      ((affineStep (c : OpeningResidueClosure p) xResidue.x2
        (trace (c : OpeningResidueClosure p) xResidue.x2))^[r₂])
          (movingCoordinates2 xResidue) = movingCoordinates2 xResidue := by
    have hmap := congrArg (mapPair f) hreturn₂
    rw [mapPair_iterate_affineStep, map_trace] at hmap
    simpa [xResidue, openingResiduePoint, f, mapPoint, map_intCast] using hmap
  have hreturnResidue₃ :
      ((affineStep (c : OpeningResidueClosure p) xResidue.x3
        (trace (c : OpeningResidueClosure p) xResidue.x3))^[r₃])
          (movingCoordinates3 xResidue) = movingCoordinates3 xResidue := by
    have hmap := congrArg (mapPair f) hreturn₃
    rw [mapPair_iterate_affineStep, map_trace] at hmap
    simpa [xResidue, openingResiduePoint, f, mapPoint, map_intCast] using hmap
  have ht₁Two : trace (c : OpeningResidueClosure p) xResidue.x1 ≠ 2 := by
    intro htwo
    apply ht₁
    change trace (c : OpeningResidueClosure p) xResidue.x1 ^ 2 = 4
    rw [htwo]
    norm_num
  have ht₂Two : trace (c : OpeningResidueClosure p) xResidue.x2 ≠ 2 := by
    intro htwo
    apply ht₂
    change trace (c : OpeningResidueClosure p) xResidue.x2 ^ 2 = 4
    rw [htwo]
    norm_num
  have ht₃Two : trace (c : OpeningResidueClosure p) xResidue.x3 ≠ 2 := by
    intro htwo
    apply ht₃
    change trace (c : OpeningResidueClosure p) xResidue.x3 ^ 2 = 4
    rw [htwo]
    norm_num
  obtain ⟨W₁, hfin₁, horder₁, htrace₁⟩ :=
    periodic_affineStep_has_torsion_eigenvalue_orderOf_dvd
      (c : OpeningResidueClosure p) xResidue.x1
      (trace (c : OpeningResidueClosure p) xResidue.x1)
      (movingCoordinates1 xResidue) ht₁Two (by simpa [xResidue] using ht₁)
        (by simpa [xResidue] using hv₁) r₁ hr₁ hreturnResidue₁
  obtain ⟨W₂, hfin₂, horder₂, htrace₂⟩ :=
    periodic_affineStep_has_torsion_eigenvalue_orderOf_dvd
      (c : OpeningResidueClosure p) xResidue.x2
      (trace (c : OpeningResidueClosure p) xResidue.x2)
      (movingCoordinates2 xResidue) ht₂Two (by simpa [xResidue] using ht₂)
        (by simpa [xResidue] using hv₂) r₂ hr₂ hreturnResidue₂
  obtain ⟨W₃, hfin₃, horder₃, htrace₃⟩ :=
    periodic_affineStep_has_torsion_eigenvalue_orderOf_dvd
      (c : OpeningResidueClosure p) xResidue.x3
      (trace (c : OpeningResidueClosure p) xResidue.x3)
      (movingCoordinates3 xResidue) ht₃Two (by simpa [xResidue] using ht₃)
        (by simpa [xResidue] using hv₃) r₃ hr₃ hreturnResidue₃
  have horder₁le : orderOf W₁ ≤ (puncturedOneStepOrbit x).ncard :=
    orderOf_le_of_orderOf_dvd_return_le W₁ r₁ _ hr₁ horder₁ hr₁le
  have horder₂le : orderOf W₂ ≤ (puncturedOneStepOrbit x).ncard :=
    orderOf_le_of_orderOf_dvd_return_le W₂ r₂ _ hr₂ horder₂ hr₂le
  have horder₃le : orderOf W₃ ≤ (puncturedOneStepOrbit x).ncard :=
    orderOf_le_of_orderOf_dvd_return_le W₃ r₃ _ hr₃ horder₃ hr₃le
  have hboundLcm :
      p ≤ integerArchimedeanBound c ^ Nat.lcm r₁ (Nat.lcm r₂ r₃) :=
    modulus_le_integerArchimedeanBound_pow_lcm_of_return_eigenvalues
      c hs hc p xResidue hxResidue hsResidue hxResidueNe
        r₁ r₂ r₃ hr₁ hr₂ hr₃ W₁ W₂ W₃ hfin₁ hfin₂ hfin₃
        horder₁ horder₂ horder₃ htrace₁ htrace₂ htrace₃
  have hboundCard :
      p ≤ integerArchimedeanBound c ^ (puncturedOneStepOrbit x).ncard ^ 3 :=
    modulus_le_integerArchimedeanBound_pow_card_cube_of_lcm_returns
      c p r₁ r₂ r₃ (puncturedOneStepOrbit x).ncard
        hr₁ hr₂ hr₃ hr₁le hr₂le hr₃le hboundLcm
  exact ⟨r₁, r₂, r₃, W₁, W₂, W₃,
    hr₁, hr₂, hr₃, hr₁le, hr₂le, hr₃le,
    hfin₁, hfin₂, hfin₃, horder₁, horder₂, horder₃,
    horder₁le, horder₂le, horder₃le,
    by simpa [xResidue] using htrace₁,
    by simpa [xResidue] using htrace₂,
    by simpa [xResidue] using htrace₃,
    hboundLcm, hboundCard⟩

/-- Point/orbit-level nonparabolic opening theorem.  Candidate regularity of
all three transported traces simultaneously removes both parabolicity and the
affine-center obstruction; finiteness of the punctured one-step orbit then
gives the coefficient-dependent cyclotomic bound with orbit-cardinality cube
exponent. -/
theorem modulus_le_integerArchimedeanBound_pow_oneStepOrbit_ncard_cube_of_allCandidateRegular
    (c : ℤ) (hs : 3 * (1 + c) ≠ 0) (hc : c ^ 2 ≠ 4)
    (p : ℕ) [Fact p.Prime]
    (x : PuncturedSolutionSurface (coefficients (c : ZMod p)))
    (hfinite : (puncturedOneStepOrbit x).Finite)
    (hsResidue : multiplier (c : OpeningResidueClosure p) ≠ 0)
    (hregular₁ : OrderedTraceCandidateRegular
      (c : OpeningResidueClosure p) (c : OpeningResidueClosure p)
      (c : OpeningResidueClosure p)
      (trace (c : OpeningResidueClosure p)
        (openingResiduePoint p x.1.1).x1))
    (hregular₂ : OrderedTraceCandidateRegular
      (c : OpeningResidueClosure p) (c : OpeningResidueClosure p)
      (c : OpeningResidueClosure p)
      (trace (c : OpeningResidueClosure p)
        (openingResiduePoint p x.1.1).x2))
    (hregular₃ : OrderedTraceCandidateRegular
      (c : OpeningResidueClosure p) (c : OpeningResidueClosure p)
      (c : OpeningResidueClosure p)
      (trace (c : OpeningResidueClosure p)
        (openingResiduePoint p x.1.1).x3)) :
    p ≤ integerArchimedeanBound c ^ (puncturedOneStepOrbit x).ncard ^ 3 := by
  let f := algebraMap (ZMod p) (OpeningResidueClosure p)
  let xResidue := openingResiduePoint p x.1.1
  have hxResidue :
      IsSolution (coefficients (c : OpeningResidueClosure p)) xResidue := by
    simpa [xResidue, openingResiduePoint, f, map_intCast] using
      isSolution_mapPoint_symmetric f (c : ZMod p) x.1.1 x.1.2
  have hregular₁' : OrderedTraceCandidateRegular
      (c : OpeningResidueClosure p) (c : OpeningResidueClosure p)
      (c : OpeningResidueClosure p)
      (trace (c : OpeningResidueClosure p) xResidue.x1) := by
    simpa [xResidue] using hregular₁
  have hregular₂' : OrderedTraceCandidateRegular
      (c : OpeningResidueClosure p) (c : OpeningResidueClosure p)
      (c : OpeningResidueClosure p)
      (trace (c : OpeningResidueClosure p) xResidue.x2) := by
    simpa [xResidue] using hregular₂
  have hregular₃' : OrderedTraceCandidateRegular
      (c : OpeningResidueClosure p) (c : OpeningResidueClosure p)
      (c : OpeningResidueClosure p)
      (trace (c : OpeningResidueClosure p) xResidue.x3) := by
    simpa [xResidue] using hregular₃
  have ht₁ : trace (c : OpeningResidueClosure p) xResidue.x1 ^ 2 ≠ 4 := by
    apply sub_ne_zero.mp
    simpa using hregular₁'.1
  have ht₂ : trace (c : OpeningResidueClosure p) xResidue.x2 ^ 2 ≠ 4 := by
    apply sub_ne_zero.mp
    simpa using hregular₂'.1
  have ht₃ : trace (c : OpeningResidueClosure p) xResidue.x3 ^ 2 ≠ 4 := by
    apply sub_ne_zero.mp
    simpa using hregular₃'.1
  have hv₁ : centerCoordinates
      (fiberCenter (c : OpeningResidueClosure p) xResidue.x1
        (trace (c : OpeningResidueClosure p) xResidue.x1))
      (movingCoordinates1 xResidue) ≠ (0, 0) :=
    centeredMovingCoordinates1_ne_zero_of_candidateRegular
      (c : OpeningResidueClosure p) xResidue hxResidue hregular₁'
  have hv₂ : centerCoordinates
      (fiberCenter (c : OpeningResidueClosure p) xResidue.x2
        (trace (c : OpeningResidueClosure p) xResidue.x2))
      (movingCoordinates2 xResidue) ≠ (0, 0) :=
    centeredMovingCoordinates2_ne_zero_of_candidateRegular
      (c : OpeningResidueClosure p) xResidue hxResidue hregular₂'
  have hv₃ : centerCoordinates
      (fiberCenter (c : OpeningResidueClosure p) xResidue.x3
        (trace (c : OpeningResidueClosure p) xResidue.x3))
      (movingCoordinates3 xResidue) ≠ (0, 0) :=
    centeredMovingCoordinates3_ne_zero_of_candidateRegular
      (c : OpeningResidueClosure p) xResidue hxResidue hregular₃'
  obtain ⟨r₁, r₂, r₃, W₁, W₂, W₃,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hboundCard⟩ :=
    exists_return_eigenvalues_with_oneStepOrbit_bounds
      c hs hc p x hfinite hsResidue
        (by simpa [xResidue] using ht₁)
        (by simpa [xResidue] using ht₂)
        (by simpa [xResidue] using ht₃)
        (by simpa [xResidue] using hv₁)
        (by simpa [xResidue] using hv₂)
        (by simpa [xResidue] using hv₃)
  exact hboundCard

/-- Prime-field form of the point/orbit opening endpoint.  This is the direct
consumer of the finite routing lemmas: regularity proved over `ZMod p` is
transported injectively to the residue closure before applying the
cyclotomic argument. -/
theorem modulus_le_integerArchimedeanBound_pow_oneStepOrbit_ncard_cube_of_primeField_allCandidateRegular
    (c : ℤ) (hs : 3 * (1 + c) ≠ 0) (hc : c ^ 2 ≠ 4)
    (p : ℕ) [Fact p.Prime]
    (x : PuncturedSolutionSurface (coefficients (c : ZMod p)))
    (hfinite : (puncturedOneStepOrbit x).Finite)
    (hsResidue : multiplier (c : OpeningResidueClosure p) ≠ 0)
    (hregular₁ : OrderedTraceCandidateRegular
      (c : ZMod p) (c : ZMod p) (c : ZMod p)
      (trace (c : ZMod p) x.1.1.x1))
    (hregular₂ : OrderedTraceCandidateRegular
      (c : ZMod p) (c : ZMod p) (c : ZMod p)
      (trace (c : ZMod p) x.1.1.x2))
    (hregular₃ : OrderedTraceCandidateRegular
      (c : ZMod p) (c : ZMod p) (c : ZMod p)
      (trace (c : ZMod p) x.1.1.x3)) :
    p ≤ integerArchimedeanBound c ^ (puncturedOneStepOrbit x).ncard ^ 3 := by
  let f := algebraMap (ZMod p) (OpeningResidueClosure p)
  have hregular₁' := orderedTraceCandidateRegular_map f f.injective hregular₁
  have hregular₂' := orderedTraceCandidateRegular_map f f.injective hregular₂
  have hregular₃' := orderedTraceCandidateRegular_map f f.injective hregular₃
  apply
    modulus_le_integerArchimedeanBound_pow_oneStepOrbit_ncard_cube_of_allCandidateRegular
      c hs hc p x hfinite hsResidue
  · simpa [openingResiduePoint, mapPoint, f, map_trace, map_intCast] using hregular₁'
  · simpa [openingResiduePoint, mapPoint, f, map_trace, map_intCast] using hregular₂'
  · simpa [openingResiduePoint, mapPoint, f, map_trace, map_intCast] using hregular₃'

/-- A regular fixed trace and a first-axis one-step cycle with more than
twenty-eight points route to a point where all three traces are regular, and
hence imply the orbit-cardinality opening bound for the original orbit. -/
theorem modulus_le_integerArchimedeanBound_pow_oneStepOrbit_ncard_cube_of_fixedTraceRegular_longCycle
    (c : ℤ) (hs : 3 * (1 + c) ≠ 0) (hc : c ^ 2 ≠ 4)
    (p : ℕ) [Fact p.Prime]
    (x : PuncturedSolutionSurface (coefficients (c : ZMod p)))
    (hfinite : (puncturedOneStepOrbit x).Finite)
    (hmultiplier : multiplier (c : ZMod p) ≠ 0)
    (htwo : (2 : ZMod p) ≠ 0) (hcResidue : (c : ZMod p) ^ 2 ≠ 4)
    (hfixedRegular : OrderedTraceCandidateRegular
      (c : ZMod p) (c : ZMod p) (c : ZMod p)
      (trace (c : ZMod p) x.1.1.x1))
    (N : ℕ) (hcard : 28 < (oneStep1Cycle p (c : ZMod p) x.1.1 N).card) :
    p ≤ integerArchimedeanBound c ^ (puncturedOneStepOrbit x).ncard ^ 3 := by
  obtain ⟨y, hyCycle, hyRegular₁, hyRegular₂, hyRegular₃⟩ :=
    exists_allCandidateRegular_in_oneStep1Cycle
      p (c : ZMod p) x.1.1 N hmultiplier htwo hcResidue x.1.2
        hfixedRegular hcard
  rw [oneStep1Cycle, Finset.mem_image] at hyCycle
  obtain ⟨n, _hn, rfl⟩ := hyCycle
  let g₁ : OneStepGroup (c : ZMod p) :=
    ⟨oneStep1SurfacePerm (c : ZMod p),
      oneStep1SurfacePerm_mem_OneStepGroup (c : ZMod p)⟩
  let yPunctured : PuncturedSolutionSurface (coefficients (c : ZMod p)) :=
    (g₁ ^ n) • x
  have hyPoint : yPunctured.1.1 =
      ((oneStep1 (c : ZMod p))^[n]) x.1.1 := by
    change (((oneStep1SurfacePerm (c : ZMod p)) ^ n) x.1).1 =
      ((oneStep1 (c : ZMod p))^[n]) x.1.1
    rw [Equiv.Perm.coe_pow]
    exact coe_iterate_oneStep1SurfacePerm (c : ZMod p) n x.1
  have hyOrbit : puncturedOneStepOrbit yPunctured = puncturedOneStepOrbit x := by
    apply MulAction.orbit_eq_iff.mpr
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨g₁ ^ n, rfl⟩
  have hyFinite : (puncturedOneStepOrbit yPunctured).Finite := by
    rw [hyOrbit]
    exact hfinite
  have hsResidue : multiplier (c : OpeningResidueClosure p) ≠ 0 := by
    let f := algebraMap (ZMod p) (OpeningResidueClosure p)
    have hmapped := (map_ne_zero_iff f f.injective).mpr hmultiplier
    simpa [f, multiplier, map_ofNat, map_intCast] using hmapped
  have hbound :=
    modulus_le_integerArchimedeanBound_pow_oneStepOrbit_ncard_cube_of_primeField_allCandidateRegular
      c hs hc p yPunctured hyFinite hsResidue
        (by simpa [hyPoint] using hyRegular₁)
        (by simpa [hyPoint] using hyRegular₂)
        (by simpa [hyPoint] using hyRegular₃)
  simpa [hyOrbit] using hbound

end GenMarkoff.Symmetric.Opening
