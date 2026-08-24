import GenMarkoff.General.MiddleGame.ActualMoveWiring
import GenMarkoff.General.MiddleGame.ActualParameters
import GenMarkoff.General.MiddleGame.RotationEigenvalueOrder
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The toric exceptional branch for a directed general fiber

The regular shifted-cover argument excludes the component
`(sigma, gamma) = (1, 0)`.  On that component the normalized adjacent trace
is an ordinary split-torus trace.  For a first-axis fiber with eigenvalue
`q`, the two directed adjacent eigenvalues at parameter `h` are

`z * h` and `q * z * h`.

The actual source rotation only reaches `h` in `zpowers (q ^ 2)`.  Squaring
one displayed eigenvalue shows a new parity issue absent from the one-step
symmetric argument: a single directed toric trace only covers the translated
subgroup `z ^ 2 * zpowers ((q ^ 2) ^ 2)`.  Its cardinality is the current
actual order divided by its gcd with `2`.

If the opposite directed trace is toric as well, the first direction covers
the even powers of `q ^ 2`, while the second direction covers the odd powers.
Together they then cover the whole translated coset

`z ^ 2 * zpowers (q ^ 2)`.

This file proves the exact trace identities, the parity-completion theorem,
the uniform one-point bound for the parabolic locus in the squared coset,
and the direct lcm/product order bound for the two directions.

The full order-preservation input is isolated here as
`TranslatedSubgroupHasLargeOrder`: for a finite cyclic ambient group, every
translate of a subgroup should contain an element whose order is at least
the subgroup cardinality.  The reduction from precisely that statement to
the two actual directed eigenvalues is proved below.  Thus no unproved
cyclic-group assertion is hidden in an order-growth endpoint.  The follow-on
module `CyclicCosetOrder` proves the stronger divisibility form of this
input by an elementary prime-factor argument.
-/

namespace GenMarkoff.General.MiddleGame

open BGS.Markoff

noncomputable section

section ActualToricTraces

variable {K : Type*} [Field K]

/-- The second directed trace normalized so that its leading weight is one.
Its normalized parameter differs from the first directed one by the fiber
eigenvalue `q`. -/
theorem shiftedWeightedTrace_secondNormalizedParameter_eq_secondTrace_fiberPair
    (s B C u t : K) (q h : Kˣ) (hs : s ≠ 0) :
    weightedSplitTorusTrace 1 (actualSigma s B C u t)
          ((actualAlphaUnit s hs * q) * h) +
        actualGammaSecond s B C u t =
      s * (fiberPair B C u t (q : K) (h : K)).2 - C := by
  rw [secondTrace_fiberPair s B C u t (q : K) (h : K)
    (Units.ne_zero q) (Units.ne_zero h)]
  simp only [weightedSplitTorusTrace, actualSigma, actualAlpha, actualBeta,
    actualAlphaUnit_val, Units.val_mul, Units.val_inv_eq_inv_val, one_mul]
  field_simp [hs, Units.ne_zero q, Units.ne_zero h]

/-- On the toric component, the first directed trace is the ordinary split
trace of the normalized translated parameter. -/
theorem firstTrace_fiberPair_mul_eq_splitTorusTrace_of_toric
    (s B C u t : K) (q r h : Kˣ) (hs : s ≠ 0)
    (hsigma : actualSigma s B C u t = 1)
    (hgamma : actualGammaFirst s B C u t = 0) :
    s * (fiberPair B C u t (q : K) ((r * h : Kˣ) : K)).1 - B =
      splitTorusTrace (actualAlphaUnit s hs * r * h) := by
  have htrace :=
    shiftedWeightedTrace_normalizedParameter_eq_firstTrace_fiberPair
      s B C u t (q : K) (r * h) hs
  rw [hsigma, hgamma, weightedSplitTorusTrace_one_one, add_zero] at htrace
  simpa only [mul_assoc] using htrace.symm

/-- On the toric component, the second directed trace is the ordinary split
trace of `q` times the first normalized parameter. -/
theorem secondTrace_fiberPair_mul_eq_splitTorusTrace_of_toric
    (s B C u t : K) (q r h : Kˣ) (hs : s ≠ 0)
    (hsigma : actualSigma s B C u t = 1)
    (hgamma : actualGammaSecond s B C u t = 0) :
    s * (fiberPair B C u t (q : K) ((r * h : Kˣ) : K)).2 - C =
      splitTorusTrace (q * (actualAlphaUnit s hs * r * h)) := by
  have htrace :=
    shiftedWeightedTrace_secondNormalizedParameter_eq_secondTrace_fiberPair
      s B C u t q (r * h) hs
  rw [hsigma, hgamma, weightedSplitTorusTrace_one_one, add_zero] at htrace
  simpa only [mul_assoc, mul_left_comm, mul_comm] using htrace.symm

/-- Point-level form of the two toric directed trace identities on an actual
first-axis translated parameter coset. -/
theorem orderedTraces_fiberPoint1_mul_eq_toric_pair
    (a : Coefficients K) (u t : K) (q r h : Kˣ)
    (hs : a.multiplier ≠ 0)
    (hsigma :
      actualSigma a.multiplier a.a2 a.a3 u t = 1)
    (hgammaFirst :
      actualGammaFirst a.multiplier a.a2 a.a3 u t = 0)
    (hgammaSecond :
      actualGammaSecond a.multiplier a.a2 a.a3 u t = 0) :
    let z := actualAlphaUnit a.multiplier hs * r * h
    orderedTrace a.multiplier a.a2
          (fiberPoint1 a u t (q : K) ((r * h : Kˣ) : K)).x2 =
        splitTorusTrace z ∧
      orderedTrace a.multiplier a.a3
          (fiberPoint1 a u t (q : K) ((r * h : Kˣ) : K)).x3 =
        splitTorusTrace (q * z) := by
  dsimp only
  constructor
  · change
      a.multiplier *
            (fiberPair a.a2 a.a3 u t (q : K)
              ((r * h : Kˣ) : K)).1 -
          a.a2 =
        splitTorusTrace (actualAlphaUnit a.multiplier hs * r * h)
    exact firstTrace_fiberPair_mul_eq_splitTorusTrace_of_toric
      a.multiplier a.a2 a.a3 u t q r h hs hsigma hgammaFirst
  · change
      a.multiplier *
            (fiberPair a.a2 a.a3 u t (q : K)
              ((r * h : Kˣ) : K)).2 -
          a.a3 =
        splitTorusTrace
          (q * (actualAlphaUnit a.multiplier hs * r * h))
    exact secondTrace_fiberPair_mul_eq_splitTorusTrace_of_toric
      a.multiplier a.a2 a.a3 u t q r h hs hsigma hgammaSecond

end ActualToricTraces

section SquareCosetParity

variable {G : Type*} [CommGroup G]

/-- A single directed toric trace covers the translate of the square of the
actual parameter subgroup. -/
theorem firstToric_squareCoset_covered
    [Finite G] (q z : G)
    (w : Subgroup.zpowers ((q ^ 2) ^ 2)) :
    ∃ h : Subgroup.zpowers (q ^ 2),
      (z * (h : G)) ^ 2 = z ^ 2 * (w : G) := by
  have hwPowers : (w : G) ∈ Submonoid.powers ((q ^ 2) ^ 2) :=
    mem_powers_iff_mem_zpowers.mpr w.property
  obtain ⟨n, hn⟩ :=
    (Submonoid.mem_powers_iff (w : G) ((q ^ 2) ^ 2)).mp hwPowers
  let h : Subgroup.zpowers (q ^ 2) :=
    ⟨(q ^ 2) ^ n, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) n⟩
  refine ⟨h, ?_⟩
  have hw : (w : G) = ((q ^ 2) ^ 2) ^ n := hn.symm
  change
    (z * (q ^ 2) ^ n) ^ 2 =
      z ^ 2 * (w : G)
  rw [hw]
  rw [mul_pow]
  exact congrArg (fun x : G => z ^ 2 * x) <| by
    calc
      ((q ^ 2) ^ n) ^ 2 =
          (q ^ 2) ^ (n * 2) := (pow_mul (q ^ 2) n 2).symm
      _ = (q ^ 2) ^ (2 * n) := by rw [Nat.mul_comm n 2]
      _ = ((q ^ 2) ^ 2) ^ n := pow_mul (q ^ 2) 2 n

/-- Exact parity loss for a single directed toric trace. -/
theorem card_firstToric_squareParameterSubgroup
    [Finite G] (q : G) :
    Nat.card (Subgroup.zpowers ((q ^ 2) ^ 2)) =
      Nat.card (Subgroup.zpowers (q ^ 2)) /
        Nat.gcd (Nat.card (Subgroup.zpowers (q ^ 2))) 2 := by
  simp only [Nat.card_zpowers, orderOf_pow]

/-- The two toric directions, after squaring their eigenvalues, cover the
even and odd powers of the actual generator respectively. -/
theorem toric_direction_squares_even_odd
    (q z : G) (k : ℕ) :
    (z * (q ^ 2) ^ k) ^ 2 =
        z ^ 2 * (q ^ 2) ^ (k * 2) ∧
      (q * z * (q ^ 2) ^ k) ^ 2 =
        z ^ 2 * (q ^ 2) ^ (k * 2 + 1) := by
  constructor
  · simp only [mul_pow, pow_mul]
  · simp only [mul_pow, pow_mul, pow_add, pow_one]
    ac_rfl

/-- Because actual reachability is through `zpowers (q ^ 2)`, neither
directed toric trace alone covers every squared-eigenvalue parameter when
that subgroup has even order.  The two adjacent directions together cover
the entire translated squared coset. -/
theorem toric_squareCoset_covered_by_two_directions
    [Finite G] (q z : G) (w : Subgroup.zpowers (q ^ 2)) :
    ∃ h : Subgroup.zpowers (q ^ 2),
      (z * (h : G)) ^ 2 = z ^ 2 * (w : G) ∨
        (q * z * (h : G)) ^ 2 = z ^ 2 * (w : G) := by
  have hwPowers : (w : G) ∈ Submonoid.powers (q ^ 2) :=
    mem_powers_iff_mem_zpowers.mpr w.property
  obtain ⟨n, hn⟩ :=
    (Submonoid.mem_powers_iff (w : G) (q ^ 2)).mp hwPowers
  rcases n.even_or_odd' with ⟨k, hk | hk⟩
  · let h : Subgroup.zpowers (q ^ 2) :=
      ⟨(q ^ 2) ^ k, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k⟩
    refine ⟨h, Or.inl ?_⟩
    have hw : (w : G) = (q ^ 2) ^ n := hn.symm
    rw [hw, hk]
    rw [Nat.mul_comm 2 k]
    exact (toric_direction_squares_even_odd q z k).1
  · let h : Subgroup.zpowers (q ^ 2) :=
      ⟨(q ^ 2) ^ k, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k⟩
    refine ⟨h, Or.inr ?_⟩
    have hw : (w : G) = (q ^ 2) ^ n := hn.symm
    rw [hw, hk]
    rw [Nat.mul_comm 2 k]
    exact (toric_direction_squares_even_odd q z k).2

/-- The exact cyclic-coset input for full toric order-preservation.  It is
deliberately a named proposition at this layer: its proof in
`CyclicCosetOrder` uses that the ambient finite group is cyclic, not merely
commutative. -/
def TranslatedSubgroupHasLargeOrder
    (H : Subgroup G) (z : G) : Prop :=
  ∃ w : H, Nat.card H ≤ orderOf (z * (w : G))

/-- Exact reduction for one directed toric trace.  The subgroup in the
remaining cyclic-coset obligation is `zpowers ((q ^ 2) ^ 2)`, so the best
uniform scale available from this direction alone includes the factor-two
parity loss recorded by `card_firstToric_squareParameterSubgroup`. -/
theorem exists_firstToric_direction_with_large_order_of_translatedSubgroup
    [Finite G] (q z : G)
    (hlarge :
      TranslatedSubgroupHasLargeOrder
        (Subgroup.zpowers ((q ^ 2) ^ 2)) (z ^ 2)) :
    ∃ h : Subgroup.zpowers (q ^ 2),
      Nat.card (Subgroup.zpowers ((q ^ 2) ^ 2)) ≤
        orderOf ((z * (h : G)) ^ 2) := by
  obtain ⟨w, hw⟩ := hlarge
  obtain ⟨h, hsq⟩ := firstToric_squareCoset_covered q z w
  exact ⟨h, hsq ▸ hw⟩

/-- Exact reduction of the missing translated-subgroup statement to the two
actual toric directions. -/
theorem exists_toric_direction_with_large_order_of_translatedSubgroup
    [Finite G] (q z : G)
    (hlarge :
      TranslatedSubgroupHasLargeOrder
        (Subgroup.zpowers (q ^ 2)) (z ^ 2)) :
    ∃ h : Subgroup.zpowers (q ^ 2),
      Nat.card (Subgroup.zpowers (q ^ 2)) ≤
          orderOf ((z * (h : G)) ^ 2) ∨
        Nat.card (Subgroup.zpowers (q ^ 2)) ≤
          orderOf ((q * z * (h : G)) ^ 2) := by
  obtain ⟨w, hw⟩ := hlarge
  obtain ⟨h, hfirst | hsecond⟩ :=
    toric_squareCoset_covered_by_two_directions q z w
  · exact ⟨h, Or.inl (hfirst ▸ hw)⟩
  · exact ⟨h, Or.inr (hsecond ▸ hw)⟩

/-- If the translated squared parameter already belongs to the actual
square-generated subgroup, exact order preservation is immediate: translate
it to the generator `q ^ 2`. -/
theorem translatedSubgroupHasLargeOrder_sq_of_sq_mem
    [Finite G] (q z : G)
    (hz : z ^ 2 ∈ Subgroup.zpowers (q ^ 2)) :
    TranslatedSubgroupHasLargeOrder
      (Subgroup.zpowers (q ^ 2)) (z ^ 2) := by
  let w : Subgroup.zpowers (q ^ 2) :=
    ⟨(z ^ 2)⁻¹ * q ^ 2,
      Subgroup.mul_mem _
        (Subgroup.inv_mem _ hz) (Subgroup.mem_zpowers _)⟩
  refine ⟨w, ?_⟩
  rw [Nat.card_zpowers]
  change orderOf (q ^ 2) ≤ orderOf (z ^ 2 * ((z ^ 2)⁻¹ * q ^ 2))
  simp

/-- Consequently, subgroup membership of the translated square gives one
of the two actual toric directions with order at least the current actual
generator order. -/
theorem exists_toric_direction_with_large_order_of_sq_mem
    [Finite G] (q z : G)
    (hz : z ^ 2 ∈ Subgroup.zpowers (q ^ 2)) :
    ∃ h : Subgroup.zpowers (q ^ 2),
      orderOf (q ^ 2) ≤ orderOf ((z * (h : G)) ^ 2) ∨
        orderOf (q ^ 2) ≤ orderOf ((q * z * (h : G)) ^ 2) := by
  simpa only [Nat.card_zpowers] using
    exists_toric_direction_with_large_order_of_translatedSubgroup
      q z (translatedSubgroupHasLargeOrder_sq_of_sq_mem q z hz)

end SquareCosetParity

section ParabolicDeletion

variable {G : Type*} [CommGroup G] [Fintype G]

/-- Unsafe squared-coset parameters are precisely those producing the
identity squared eigenvalue. -/
noncomputable def toricParabolicSquareCosetParameters
    (H : Subgroup G) (z : G) : Finset H := by
  classical
  letI := Fintype.ofFinite H
  exact Finset.univ.filter fun w => z * (w : G) = 1

/-- A translated squared coset contains at most one parabolic parameter.
This is sharper than separately counting the two signs before squaring. -/
theorem toricParabolicSquareCosetParameters_card_le_one
    (H : Subgroup G) (z : G) :
    (toricParabolicSquareCosetParameters H z).card ≤ 1 := by
  classical
  letI := Fintype.ofFinite H
  apply Finset.card_le_one_iff.mpr
  intro a b ha hb
  simp only [toricParabolicSquareCosetParameters,
    Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  apply Subtype.ext
  exact mul_left_cancel (ha.trans hb.symm)

/-- Once the actual square subgroup has more than one element, deletion of
the unique possible unsafe squared-coset parameter leaves a nonparabolic
choice. -/
theorem exists_nonparabolic_squareCosetParameter
    (H : Subgroup G) (z : G) (hcard : 1 < Nat.card H) :
    ∃ w : H, z * (w : G) ≠ 1 := by
  classical
  letI := Fintype.ofFinite H
  have hlt :
      (toricParabolicSquareCosetParameters H z).card <
        (Finset.univ : Finset H).card := by
    calc
      (toricParabolicSquareCosetParameters H z).card ≤ 1 :=
        toricParabolicSquareCosetParameters_card_le_one H z
      _ < Nat.card H := hcard
      _ = (Finset.univ : Finset H).card := by
        simp only [Finset.card_univ, Nat.card_eq_fintype_card]
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨w, ?_⟩
  simpa only [toricParabolicSquareCosetParameters, Finset.mem_filter,
    Finset.mem_univ, true_and] using hw

/-- The bounded deletion transfers through parity completion to one of the
two actual directed eigenvalues. -/
theorem exists_nonparabolic_toric_direction
    (q z : G)
    (hcard : 1 < Nat.card (Subgroup.zpowers (q ^ 2))) :
    ∃ h : Subgroup.zpowers (q ^ 2),
      (z * (h : G)) ^ 2 ≠ 1 ∨
        (q * z * (h : G)) ^ 2 ≠ 1 := by
  obtain ⟨w, hw⟩ :=
    exists_nonparabolic_squareCosetParameter
      (Subgroup.zpowers (q ^ 2)) (z ^ 2) hcard
  obtain ⟨h, hfirst | hsecond⟩ :=
    toric_squareCoset_covered_by_two_directions q z w
  · exact ⟨h, Or.inl (hfirst ▸ hw)⟩
  · exact ⟨h, Or.inr (hsecond ▸ hw)⟩

end ParabolicDeletion

section DirectOrderBounds

variable {G : Type*} [CommGroup G]

/-- For the two adjacent toric eigenvalues `z` and `q*z`, the current
actual generator order divides the lcm of their squared orders. -/
theorem orderOf_sq_dvd_lcm_adjacent_toric_sq_orders
    (q z : G) :
    orderOf (q ^ 2) ∣
      Nat.lcm (orderOf (z ^ 2)) (orderOf ((q * z) ^ 2)) := by
  have hfactor :
      q ^ 2 = (z ^ 2)⁻¹ * (q * z) ^ 2 := by
    symm
    calc
      (z ^ 2)⁻¹ * (q * z) ^ 2 =
          (z⁻¹) ^ 2 * (q ^ 2 * z ^ 2) := by
            rw [inv_pow, mul_pow]
      _ = q ^ 2 * ((z⁻¹) ^ 2 * z ^ 2) := by
            ac_rfl
      _ = q ^ 2 := by simp
  rw [hfactor]
  simpa only [orderOf_inv] using
    (Commute.all (z ^ 2)⁻¹ ((q * z) ^ 2)).orderOf_mul_dvd_lcm

/-- Product form of the direct two-direction toric order bound. -/
theorem orderOf_sq_le_mul_adjacent_toric_sq_orders
    [Finite G] (q z : G) :
    orderOf (q ^ 2) ≤
      orderOf (z ^ 2) * orderOf ((q * z) ^ 2) := by
  exact Nat.le_of_dvd
    (mul_pos (orderOf_pos (z ^ 2)) (orderOf_pos ((q * z) ^ 2)))
    ((orderOf_sq_dvd_lcm_adjacent_toric_sq_orders q z).trans
      (Nat.lcm_dvd_mul _ _))

/-- Without the still-missing translated-coset lemma, the unconditional
direct argument gives a square-root scale: at least one adjacent squared
order is at least any `bound` whose square is bounded by the current order. -/
theorem le_one_adjacent_toric_sq_order_of_sq_le
    [Finite G] (q z : G) (bound : ℕ)
    (hbound : bound ^ 2 ≤ orderOf (q ^ 2)) :
    bound ≤ orderOf (z ^ 2) ∨
      bound ≤ orderOf ((q * z) ^ 2) := by
  have hproduct :=
    orderOf_sq_le_mul_adjacent_toric_sq_orders q z
  by_contra h
  simp only [not_or, not_le] at h
  nlinarith

end DirectOrderBounds

section RotationLinearOrderBounds

/-- Eigenvalue form of the actual order bridge, with `orderOf (q ^ 2)`
exposed explicitly. -/
theorem rotationLinearOrder_eq_orderOf_sq_of_eigenvalue
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (t : ZMod p) (q : (quadraticFiniteField p)ˣ)
    (hq : (q : quadraticFiniteField p) ^ 2 ≠ 1)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q) :
    rotationLinearOrder t = orderOf (q ^ 2) := by
  have h :=
    card_zpowers_sq_eq_rotationLinearOrder_of_eigenvalue
      p t q hq heigen
  simpa only [Nat.card_zpowers] using h.symm

/-- The direct lcm bound translated from torus eigenvalues to the three
actual rotation-linear orders. -/
theorem rotationLinearOrder_dvd_lcm_adjacent_of_toricEigenvalues
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (t t₁ t₂ : ZMod p)
    (q z : (quadraticFiniteField p)ˣ)
    (hq : (q : quadraticFiniteField p) ^ 2 ≠ 1)
    (hz : (z : quadraticFiniteField p) ^ 2 ≠ 1)
    (hqz : ((q * z : (quadraticFiniteField p)ˣ) :
        quadraticFiniteField p) ^ 2 ≠ 1)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (heigen₁ :
      algebraMap (ZMod p) (quadraticFiniteField p) t₁ =
        splitTorusTrace z)
    (heigen₂ :
      algebraMap (ZMod p) (quadraticFiniteField p) t₂ =
        splitTorusTrace (q * z)) :
    rotationLinearOrder t ∣
      Nat.lcm (rotationLinearOrder t₁) (rotationLinearOrder t₂) := by
  rw [rotationLinearOrder_eq_orderOf_sq_of_eigenvalue
      p t q hq heigen,
    rotationLinearOrder_eq_orderOf_sq_of_eigenvalue
      p t₁ z hz heigen₁,
    rotationLinearOrder_eq_orderOf_sq_of_eigenvalue
      p t₂ (q * z) hqz heigen₂]
  exact orderOf_sq_dvd_lcm_adjacent_toric_sq_orders q z

/-- Square-root fallback stated directly for actual rotation-linear orders. -/
theorem le_one_adjacent_rotationLinearOrder_of_toricEigenvalues
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (t t₁ t₂ : ZMod p)
    (q z : (quadraticFiniteField p)ˣ)
    (hq : (q : quadraticFiniteField p) ^ 2 ≠ 1)
    (hz : (z : quadraticFiniteField p) ^ 2 ≠ 1)
    (hqz : ((q * z : (quadraticFiniteField p)ˣ) :
        quadraticFiniteField p) ^ 2 ≠ 1)
    (heigen :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace q)
    (heigen₁ :
      algebraMap (ZMod p) (quadraticFiniteField p) t₁ =
        splitTorusTrace z)
    (heigen₂ :
      algebraMap (ZMod p) (quadraticFiniteField p) t₂ =
        splitTorusTrace (q * z))
    (bound : ℕ) (hbound : bound ^ 2 ≤ rotationLinearOrder t) :
    bound ≤ rotationLinearOrder t₁ ∨
      bound ≤ rotationLinearOrder t₂ := by
  rw [rotationLinearOrder_eq_orderOf_sq_of_eigenvalue
      p t q hq heigen] at hbound
  rw [rotationLinearOrder_eq_orderOf_sq_of_eigenvalue
      p t₁ z hz heigen₁,
    rotationLinearOrder_eq_orderOf_sq_of_eigenvalue
      p t₂ (q * z) hqz heigen₂]
  exact le_one_adjacent_toric_sq_order_of_sq_le q z bound hbound

end RotationLinearOrderBounds

end

end GenMarkoff.General.MiddleGame
