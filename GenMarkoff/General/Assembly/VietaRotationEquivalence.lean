import GenMarkoff.Arithmetic.EventualAdmissibility
import GenMarkoff.General.Assembly.RotationComponent
import GenMarkoff.General.Assembly.VietaParityCollapse

/-!
# Large-prime equivalence of Vieta and rotation connectedness

For a generic coefficient triple over `ZMod p`, with `7 ≤ p`, the punctured
surface contains a point fixed by the first Vieta involution.  The construction
uses the affine conic

`v² = r² + a₁ r + 1`.

Writing `δ = 4 - a₁²`, its points are parametrized by a nonzero `U` via

`V = δ / U`, `v = (U + V) / 4`, and
`r = (V - U - 2 a₁) / 4`.

At most two parameters give `r = 0`, and at most two give
`2v + a₃r + a₂ = 0`.  Since `(ZMod p)ˣ` has `p - 1 > 4` elements, one may
choose a parameter outside both bad loci.  The point

`(vz, rz, z)`, where
`z = (2v + a₃r + a₂) / (a.multiplier * r)`,

is then nonzero, lies on the surface, and is fixed by `vieta1`.

This fixed point collapses the parity index between the full Vieta group and
the even-word rotation group.  Consequently, under the same large-prime
generic hypotheses, Vieta strong approximation and rotation strong
approximation are equivalent.  Thus passing to the larger Vieta group does
not remove the remaining large-prime connectedness problem.
-/

namespace GenMarkoff.General.Assembly

open Polynomial

noncomputable section

private def vietaFixedConicDelta
    {K : Type*} [CommRing K] (a : Coefficients K) : K :=
  4 - a.a1 ^ 2

private def vietaFixedConicV
    {K : Type*} [Field K] (a : Coefficients K) (U : Kˣ) : K :=
  ((U : K) + vietaFixedConicDelta a / (U : K)) / 4

private def vietaFixedConicR
    {K : Type*} [Field K] (a : Coefficients K) (U : Kˣ) : K :=
  (vietaFixedConicDelta a / (U : K) - (U : K) - 2 * a.a1) / 4

private theorem vietaFixedConicV_sq
    {K : Type*} [Field K] (a : Coefficients K) (U : Kˣ)
    (h2 : (2 : K) ≠ 0) :
    vietaFixedConicV a U ^ 2 =
      vietaFixedConicR a U ^ 2 +
        a.a1 * vietaFixedConicR a U + 1 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  simp only [vietaFixedConicV, vietaFixedConicR,
    vietaFixedConicDelta]
  field_simp [Units.ne_zero U, h4]
  ring

private def vietaFixedConicRBadPolynomial
    {K : Type*} [CommRing K] (a : Coefficients K) : K[X] :=
  X ^ 2 + C (2 * a.a1) * X - C (vietaFixedConicDelta a)

private def vietaFixedConicNumeratorBadPolynomial
    {K : Type*} [CommRing K] (a : Coefficients K) : K[X] :=
  C (2 - a.a3) * X ^ 2 +
    C (-2 * a.a1 * a.a3 + 4 * a.a2) * X +
      C ((2 + a.a3) * vietaFixedConicDelta a)

private theorem vietaFixedConicRBadPolynomial_ne_zero
    {K : Type*} [Field K] (a : Coefficients K) :
    vietaFixedConicRBadPolynomial a ≠ 0 := by
  intro hzero
  have hcoeff :=
    congrArg (fun f : K[X] ↦ f.coeff 2) hzero
  simp [vietaFixedConicRBadPolynomial] at hcoeff

private theorem vietaFixedConicNumeratorBadPolynomial_ne_zero
    {K : Type*} [Field K] (a : Coefficients K)
    (h2 : (2 : K) ≠ 0)
    (hdelta : vietaFixedConicDelta a ≠ 0) :
    vietaFixedConicNumeratorBadPolynomial a ≠ 0 := by
  by_cases ha3 : a.a3 = 2
  · intro hzero
    have heval :=
      congrArg (Polynomial.eval (0 : K)) hzero
    simp [vietaFixedConicNumeratorBadPolynomial, ha3] at heval
    have hfour : (2 + 2 : K) ≠ 0 := by
      rw [show (2 + 2 : K) = 2 * 2 by norm_num]
      exact mul_ne_zero h2 h2
    exact heval.elim hfour hdelta
  · intro hzero
    have hcoeff :=
      congrArg (fun f : K[X] ↦ f.coeff 2) hzero
    have hcoeffValue :
        (vietaFixedConicNumeratorBadPolynomial a).coeff 2 =
          2 - a.a3 := by
      rw [vietaFixedConicNumeratorBadPolynomial]
      simp only [coeff_add, coeff_C_mul_X_pow,
        coeff_C_mul_X, coeff_C]
      norm_num
    rw [hcoeffValue] at hcoeff
    simp only [coeff_zero] at hcoeff
    exact ha3 (sub_eq_zero.mp hcoeff).symm

private theorem vietaFixedConicRBadPolynomial_natDegree_le_two
    {K : Type*} [Field K] (a : Coefficients K) :
    (vietaFixedConicRBadPolynomial a).natDegree ≤ 2 := by
  simp only [vietaFixedConicRBadPolynomial]
  compute_degree

private theorem vietaFixedConicNumeratorBadPolynomial_natDegree_le_two
    {K : Type*} [Field K] (a : Coefficients K) :
    (vietaFixedConicNumeratorBadPolynomial a).natDegree ≤ 2 := by
  simp only [vietaFixedConicNumeratorBadPolynomial]
  compute_degree

private theorem eval_vietaFixedConicRBadPolynomial_eq_zero_of_r_eq_zero
    {K : Type*} [Field K] (a : Coefficients K) (U : Kˣ)
    (h2 : (2 : K) ≠ 0)
    (hr : vietaFixedConicR a U = 0) :
    eval (U : K) (vietaFixedConicRBadPolynomial a) = 0 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  simp only [vietaFixedConicRBadPolynomial]
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_sub]
  simp only [vietaFixedConicR, vietaFixedConicDelta] at hr
  simp only [vietaFixedConicDelta]
  field_simp [Units.ne_zero U, h4] at hr ⊢
  linear_combination -hr

private theorem
    eval_vietaFixedConicNumeratorBadPolynomial_eq_zero_of_numerator_eq_zero
    {K : Type*} [Field K] (a : Coefficients K) (U : Kˣ)
    (h2 : (2 : K) ≠ 0)
    (hnumerator :
      2 * vietaFixedConicV a U +
          a.a3 * vietaFixedConicR a U + a.a2 = 0) :
    eval (U : K) (vietaFixedConicNumeratorBadPolynomial a) = 0 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  simp only [vietaFixedConicNumeratorBadPolynomial]
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
  simp only [vietaFixedConicV, vietaFixedConicR,
    vietaFixedConicDelta] at hnumerator
  simp only [vietaFixedConicDelta]
  field_simp [Units.ne_zero U, h4] at hnumerator ⊢
  linear_combination hnumerator

private def vietaFixedConicRBadUnits
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) :
    Finset (ZMod p)ˣ :=
  Finset.univ.filter fun U ↦ vietaFixedConicR a U = 0

private def vietaFixedConicNumeratorBadUnits
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) :
    Finset (ZMod p)ˣ :=
  Finset.univ.filter fun U ↦
    2 * vietaFixedConicV a U +
        a.a3 * vietaFixedConicR a U + a.a2 = 0

private theorem vietaFixedConicRBadUnits_card_le_two
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p))
    (h2 : (2 : ZMod p) ≠ 0) :
    (vietaFixedConicRBadUnits p a).card ≤ 2 := by
  classical
  let q := vietaFixedConicRBadPolynomial a
  have hq : q ≠ 0 := vietaFixedConicRBadPolynomial_ne_zero a
  have himage :
      (vietaFixedConicRBadUnits p a).image
          (fun U : (ZMod p)ˣ ↦ (U : ZMod p)) ⊆
        q.roots.toFinset := by
    intro u hu
    obtain ⟨U, hUbad, rfl⟩ := Finset.mem_image.mp hu
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq]
    exact
      eval_vietaFixedConicRBadPolynomial_eq_zero_of_r_eq_zero
        a U h2 (Finset.mem_filter.mp hUbad).2
  have hinjective :
      Set.InjOn (fun U : (ZMod p)ˣ ↦ (U : ZMod p))
        (vietaFixedConicRBadUnits p a) :=
    Units.val_injective.injOn
  calc
    (vietaFixedConicRBadUnits p a).card =
        ((vietaFixedConicRBadUnits p a).image
          (fun U : (ZMod p)ˣ ↦ (U : ZMod p))).card :=
      (Finset.card_image_of_injOn hinjective).symm
    _ ≤ q.roots.toFinset.card := Finset.card_le_card himage
    _ ≤ q.roots.card := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := Polynomial.card_roots' _
    _ ≤ 2 := vietaFixedConicRBadPolynomial_natDegree_le_two a

private theorem vietaFixedConicNumeratorBadUnits_card_le_two
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p))
    (h2 : (2 : ZMod p) ≠ 0)
    (hdelta : vietaFixedConicDelta a ≠ 0) :
    (vietaFixedConicNumeratorBadUnits p a).card ≤ 2 := by
  classical
  let q := vietaFixedConicNumeratorBadPolynomial a
  have hq : q ≠ 0 :=
    vietaFixedConicNumeratorBadPolynomial_ne_zero a h2 hdelta
  have himage :
      (vietaFixedConicNumeratorBadUnits p a).image
          (fun U : (ZMod p)ˣ ↦ (U : ZMod p)) ⊆
        q.roots.toFinset := by
    intro u hu
    obtain ⟨U, hUbad, rfl⟩ := Finset.mem_image.mp hu
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq]
    exact
      eval_vietaFixedConicNumeratorBadPolynomial_eq_zero_of_numerator_eq_zero
        a U h2 (Finset.mem_filter.mp hUbad).2
  have hinjective :
      Set.InjOn (fun U : (ZMod p)ˣ ↦ (U : ZMod p))
        (vietaFixedConicNumeratorBadUnits p a) :=
    Units.val_injective.injOn
  calc
    (vietaFixedConicNumeratorBadUnits p a).card =
        ((vietaFixedConicNumeratorBadUnits p a).image
          (fun U : (ZMod p)ˣ ↦ (U : ZMod p))).card :=
      (Finset.card_image_of_injOn hinjective).symm
    _ ≤ q.roots.toFinset.card := Finset.card_le_card himage
    _ ≤ q.roots.card := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := Polynomial.card_roots' _
    _ ≤ 2 :=
      vietaFixedConicNumeratorBadPolynomial_natDegree_le_two a

private theorem isSolution_vietaFixedConicPoint
    {K : Type*} [CommRing K] (a : Coefficients K) (r v z : K)
    (hconic : v ^ 2 = r ^ 2 + a.a1 * r + 1)
    (hzEquation :
      a.multiplier * r * z = 2 * v + a.a3 * r + a.a2) :
    IsSolution a ⟨v * z, r * z, z⟩ := by
  rw [IsSolution]
  simp only [polynomial]
  linear_combination
    -(z ^ 2) * hconic - (v * z ^ 2) * hzEquation

private theorem vieta1_vietaFixedConicPoint
    {K : Type*} [CommRing K] (a : Coefficients K) (r v z : K)
    (hzEquation :
      a.multiplier * r * z = 2 * v + a.a3 * r + a.a2) :
    vieta1 a ⟨v * z, r * z, z⟩ = ⟨v * z, r * z, z⟩ := by
  apply Point.ext
  · simp only [vieta1]
    linear_combination z * hzEquation
  · rfl
  · rfl

/-- For every generic coefficient triple over `ZMod p`, once `7 ≤ p`, the
punctured surface contains a point fixed by the first Vieta involution. -/
theorem exists_puncturedSolution_vieta1_fixed_of_genericAdmissible
    (p : ℕ) [Fact p.Prime] (hpSeven : 7 ≤ p)
    (a : Coefficients (ZMod p)) (ha : GenericAdmissible a) :
    ∃ x : PuncturedSolutionSurface a, vieta1PuncturedPerm a x = x := by
  classical
  have hpTwo : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
    omega
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hs : a.multiplier ≠ 0 := ha.1
  have hdelta : vietaFixedConicDelta a ≠ 0 := by
    rw [vietaFixedConicDelta]
    exact sub_ne_zero.mpr ha.2.1.symm
  let bad :=
    vietaFixedConicRBadUnits p a ∪
      vietaFixedConicNumeratorBadUnits p a
  have hbad : bad.card ≤ 4 := by
    calc
      bad.card ≤
          (vietaFixedConicRBadUnits p a).card +
            (vietaFixedConicNumeratorBadUnits p a).card :=
        Finset.card_union_le _ _
      _ ≤ 2 + 2 :=
        Nat.add_le_add
          (vietaFixedConicRBadUnits_card_le_two p a h2)
          (vietaFixedConicNumeratorBadUnits_card_le_two
            p a h2 hdelta)
      _ = 4 := by norm_num
  have hunits :
      (Finset.univ : Finset (ZMod p)ˣ).card = p - 1 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      Nat.card_units, Nat.card_zmod]
  have hfour : 4 < (Finset.univ : Finset (ZMod p)ˣ).card := by
    rw [hunits]
    omega
  have hexists : ∃ U : (ZMod p)ˣ, U ∉ bad := by
    by_contra hnone
    push Not at hnone
    have hsubset : (Finset.univ : Finset (ZMod p)ˣ) ⊆ bad := by
      intro U _
      exact hnone U
    have hcard := Finset.card_le_card hsubset
    omega
  obtain ⟨U, hUgood⟩ := hexists
  have hUr :
      vietaFixedConicR a U ≠ 0 := by
    intro hzero
    apply hUgood
    apply Finset.mem_union_left
    simp only [vietaFixedConicRBadUnits, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hzero
  have hUnumerator :
      2 * vietaFixedConicV a U +
          a.a3 * vietaFixedConicR a U + a.a2 ≠ 0 := by
    intro hzero
    apply hUgood
    apply Finset.mem_union_right
    simp only [vietaFixedConicNumeratorBadUnits, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hzero
  set r := vietaFixedConicR a U with r_def
  set v := vietaFixedConicV a U with v_def
  set numerator := 2 * v + a.a3 * r + a.a2 with numerator_def
  set z := numerator / (a.multiplier * r) with z_def
  set point : Point (ZMod p) := ⟨v * z, r * z, z⟩ with point_def
  have hr : r ≠ 0 := by
    simpa only [r_def] using hUr
  have hnumerator : numerator ≠ 0 := by
    simpa only [numerator_def, v_def, r_def] using hUnumerator
  have hz : z ≠ 0 :=
    div_ne_zero hnumerator (mul_ne_zero hs hr)
  have hconic :
      v ^ 2 = r ^ 2 + a.a1 * r + 1 :=
    by
      simpa only [v_def, r_def] using
        vietaFixedConicV_sq a U h2
  have hzEquation :
      a.multiplier * r * z =
        2 * v + a.a3 * r + a.a2 := by
    rw [z_def, numerator_def]
    field_simp [hs, hr]
  have hsolution : IsSolution a point := by
    rw [point_def]
    exact isSolution_vietaFixedConicPoint a r v z hconic hzEquation
  have hvieta : vieta1 a point = point := by
    rw [point_def]
    exact vieta1_vietaFixedConicPoint a r v z hzEquation
  let surfacePoint : SolutionSurface a := ⟨point, hsolution⟩
  have hpunctured : surfacePoint ≠ surfaceOrigin a := by
    intro heq
    apply hz
    have hcoordinate :=
      congrArg (fun x : SolutionSurface a ↦ x.1.x3) heq
    simpa only [surfacePoint, point_def, surfaceOrigin, origin] using hcoordinate
  let x : PuncturedSolutionSurface a := ⟨surfacePoint, hpunctured⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hvieta

/-- Rotation strong approximation always implies Vieta strong approximation,
because the rotation group is a subgroup of the full Vieta group. -/
theorem vietaStrongApproximationAt_of_rotationStrongApproximationAt
    (a : Coefficients ℤ) (p : ℕ) (hp : p.Prime)
    (hrotation : RotationStrongApproximationAt a p hp) :
    VietaStrongApproximationAt a p hp := by
  letI : Fact p.Prime := ⟨hp⟩
  intro x y
  obtain ⟨r, hr⟩ := hrotation x y
  let g : VietaGroup (modCoefficients a p) :=
    ⟨r, RotationGroup_le_VietaGroup (modCoefficients a p) r.2⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact congrArg Subtype.val hr

/-- At a generic prime `p ≥ 7`, Vieta strong approximation implies rotation
strong approximation.  A punctured first-Vieta fixed point collapses the two
word-parity classes. -/
theorem rotationStrongApproximationAt_of_vietaStrongApproximationAt
    (a : Coefficients ℤ) (p : ℕ) (hp : p.Prime)
    (hpSeven : 7 ≤ p) (ha : GenericAdmissibleAt a p)
    (hvieta : VietaStrongApproximationAt a p hp) :
    RotationStrongApproximationAt a p hp := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨base, hbaseFixed⟩ :=
    exists_puncturedSolution_vieta1_fixed_of_genericAdmissible
      p hpSeven (modCoefficients a p) ha
  apply rotationStrongApproximationAt_of_sameRotationComponent_base
    a p hp base
  intro x
  obtain ⟨g, hg⟩ := hvieta base x
  have hvietaComponent :
      SameVietaComponent base.1 x.1 := by
    refine ⟨g, ?_⟩
    exact congrArg Subtype.val hg
  have hsurfaceFixed :
      vieta1SurfacePerm (modCoefficients a p) base.1 = base.1 := by
    exact congrArg Subtype.val hbaseFixed
  exact
    (sameVietaComponent_iff_sameRotationComponent_of_vieta1_fixed
      hsurfaceFixed).mp hvietaComponent

/-- For generic `p ≥ 7`, strong approximation for the two-Vieta rotation group
is equivalent to strong approximation for the full Vieta group. -/
theorem rotationStrongApproximationAt_iff_vietaStrongApproximationAt
    (a : Coefficients ℤ) (p : ℕ) (hp : p.Prime)
    (hpSeven : 7 ≤ p) (ha : GenericAdmissibleAt a p) :
    RotationStrongApproximationAt a p hp ↔
      VietaStrongApproximationAt a p hp :=
  ⟨vietaStrongApproximationAt_of_rotationStrongApproximationAt a p hp,
    rotationStrongApproximationAt_of_vietaStrongApproximationAt
      a p hp hpSeven ha⟩

/-- For a fixed integrally nondegenerate integral coefficient triple,
eventual rotation strong approximation is equivalent to eventual full-Vieta
strong approximation. -/
theorem
    IntegrallyNondegenerate.eventuallyRotationStrongApproximation_iff_eventuallyVietaStrongApproximation
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a) :
    EventuallyRotationStrongApproximation a ↔
      EventuallyVietaStrongApproximation a := by
  constructor
  · rintro ⟨threshold, hrotation⟩
    refine ⟨threshold, ?_⟩
    intro p hp hpLarge
    exact
      vietaStrongApproximationAt_of_rotationStrongApproximationAt
        a p hp (hrotation p hp hpLarge)
  · rintro ⟨vietaThreshold, hvieta⟩
    obtain ⟨genericThreshold, hgeneric⟩ :=
      ha.eventually_genericAdmissibleAt
    refine ⟨max 7 (max vietaThreshold genericThreshold), ?_⟩
    intro p hp hpLarge
    have hpSeven : 7 ≤ p :=
      (Nat.le_max_left 7 (max vietaThreshold genericThreshold)).trans
        hpLarge
    have hpVieta : vietaThreshold ≤ p :=
      (Nat.le_max_left vietaThreshold genericThreshold).trans
        ((Nat.le_max_right 7
          (max vietaThreshold genericThreshold)).trans hpLarge)
    have hpGeneric : genericThreshold ≤ p :=
      (Nat.le_max_right vietaThreshold genericThreshold).trans
        ((Nat.le_max_right 7
          (max vietaThreshold genericThreshold)).trans hpLarge)
    exact
      rotationStrongApproximationAt_of_vietaStrongApproximationAt
        a p hp hpSeven (hgeneric p hp hpGeneric)
          (hvieta p hp hpVieta)

/-- The global eventual full-Vieta statement is equivalent to the project's
global eventual rotation-group statement. -/
theorem
    eventualStrongApproximationStatement_iff_eventualVietaStrongApproximationStatement :
    EventualStrongApproximationStatement ↔
      EventualVietaStrongApproximationStatement := by
  constructor
  · intro hrotation a ha
    exact
      (IntegrallyNondegenerate.eventuallyRotationStrongApproximation_iff_eventuallyVietaStrongApproximation
        ha).mp
        (hrotation a ha)
  · intro hvieta a ha
    exact
      (IntegrallyNondegenerate.eventuallyRotationStrongApproximation_iff_eventuallyVietaStrongApproximation
        ha).mpr
        (hvieta a ha)

end

end GenMarkoff.General.Assembly
