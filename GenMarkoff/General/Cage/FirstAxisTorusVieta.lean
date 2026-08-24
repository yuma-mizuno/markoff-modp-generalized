import GenMarkoff.General.TraceParameters

/-!
# First-axis torus reflections and the Vieta parity obstruction

This file keeps the coefficient triple fixed and analyzes the two individual
Vieta involutions adjacent to a first-coordinate fiber. Put

`P = centeredFiberProduct a.a2 a.a3 u t`.

For `t = q + q⁻¹`, their exact torus-parameter actions are

* `vieta3 : h ↦ P / h`;
* `vieta2 : h ↦ P / (q² h)`.

Their order matters: the library definition
`rotation1 = vieta3 ∘ vieta2` sends `h` to `q² h`, whereas the reverse
composition sends it to `q⁻² h`.

## New considerations in the unequal-coefficient generalization

* The two affine translations are different. They must be centered
  separately before using the linear reflections; one cannot identify the
  heterogeneous rotation with the square of a single affine half-step.
* The same-chart reflection formulas require `P ≠ 0`, as well as `q ≠ 0` and
  `h ≠ 0`. The degenerate `P = 0` chart cannot be cancelled into these
  formulas.
* The exact fixed-point criteria use `q² ≠ 1`, which also makes the
  two-coordinate torus parametrization injective: `vieta3` is fixed exactly
  at `h² = P`, and `vieta2` exactly at `(q h)² = P`.
* Hence nonsquare `P` prevents either adjacent involution from having a fixed
  point anywhere on a `q²`-rotation orbit. This obstruction is absent from
  the equal-coefficient argument and does not follow from eigenvalue
  splitness.
* More precisely, for `H = zpowers (q²)`, both odd reflections send the
  rotation coset `hH` to `(P h⁻¹)H`, and the two cosets coincide exactly when
  `P h⁻² ∈ H`. Thus squarehood of `P` is sufficient only when `q²` generates
  the full square subgroup; it is not sufficient for a general nonprimitive
  eigenvalue.

The final `ZMod 5` theorem makes the obstruction concrete for the unequal
triple `(1, 0, 4)`: `q = 2`, `u = 2`, `t = 0`, and `P = 3` give a
period-two `q²` orbit with no adjacent-Vieta fixed point.
-/

namespace GenMarkoff.General.Cage

universe u

noncomputable section

open scoped Pointwise

variable {K : Type u} [Field K]

/-- The centered second-coordinate reflection sends `h` to `P / h`. -/
theorem torusPair_reflect_second
    (t q P h : K) (hq : q ≠ 0) (hP : P ≠ 0) (hh : h ≠ 0)
    (heigen : t = q + q⁻¹) :
    ((torusPair q P h).1,
        t * (torusPair q P h).1 - (torusPair q P h).2) =
      torusPair q P (P / h) := by
  subst t
  apply Prod.ext
  · simp [torusPair]
    field_simp [hP, hh]
    ring
  · simp [torusPair]
    field_simp [hq, hP, hh]
    ring

/-- The centered first-coordinate reflection sends `h` to
`P / (q² h)`. -/
theorem torusPair_reflect_first
    (t q P h : K) (hq : q ≠ 0) (hP : P ≠ 0) (hh : h ≠ 0)
    (heigen : t = q + q⁻¹) :
    (t * (torusPair q P h).2 - (torusPair q P h).1,
        (torusPair q P h).2) =
      torusPair q P (P / (q ^ 2 * h)) := by
  subst t
  apply Prod.ext
  · simp [torusPair]
    field_simp [hq, hP, hh]
    ring
  · simp [torusPair]
    field_simp [hq, hP, hh]
    ring

/-- Centering conjugates the affine reflection changing the second moving
coordinate to `(Y, Z) ↦ (Y, tY - Z)`. -/
theorem centerCoordinates_reflect_second
    (B C u t : K) (v : K × K) (hD : discriminant t ≠ 0) :
    centerCoordinates (fiberCenter B C u t)
        (v.1, t * v.1 - v.2 - B * u) =
      let w := centerCoordinates (fiberCenter B C u t) v
      (w.1, t * w.1 - w.2) := by
  apply Prod.ext
  · simp [centerCoordinates]
  · simp [centerCoordinates, fiberCenter]
    field_simp [hD]
    simp only [discriminant]
    ring

/-- Centering conjugates the affine reflection changing the first moving
coordinate to `(Y, Z) ↦ (tZ - Y, Z)`. -/
theorem centerCoordinates_reflect_first
    (B C u t : K) (v : K × K) (hD : discriminant t ≠ 0) :
    centerCoordinates (fiberCenter B C u t)
        (t * v.2 - v.1 - C * u, v.2) =
      let w := centerCoordinates (fiberCenter B C u t) v
      (t * w.2 - w.1, w.2) := by
  apply Prod.ext
  · simp [centerCoordinates, fiberCenter]
    field_simp [hD]
    simp only [discriminant]
    ring
  · simp [centerCoordinates]

/-- On the first-axis torus chart, `vieta3` sends `h` to `P / h`. -/
theorem vieta3_fiberPoint1
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0)
    (hq : q ≠ 0) (hP : centeredFiberProduct a.a2 a.a3 u t ≠ 0)
    (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u) :
    vieta3 a (fiberPoint1 a u t q h) =
      fiberPoint1 a u t q
        (centeredFiberProduct a.a2 a.a3 u t / h) := by
  let v := fiberPair a.a2 a.a3 u t q h
  have hvieta :
      movingCoordinates1 (vieta3 a (fiberPoint1 a u t q h)) =
        (v.1, t * v.1 - v.2 - a.a2 * u) := by
    apply Prod.ext
    · rfl
    · change
        a.multiplier * u * v.1 - v.2 - a.a2 * u - a.a1 * v.1 =
          t * v.1 - v.2 - a.a2 * u
      rw [hcoordinate]
      simp only [orderedTrace]
      ring
  have hmoving :
      movingCoordinates1 (vieta3 a (fiberPoint1 a u t q h)) =
        fiberPair a.a2 a.a3 u t q
          (centeredFiberProduct a.a2 a.a3 u t / h) := by
    apply centerCoordinates_injective (fiberCenter a.a2 a.a3 u t)
    rw [hvieta]
    rw [centerCoordinates_reflect_second a.a2 a.a3 u t v hD]
    change
      ((centerCoordinates (fiberCenter a.a2 a.a3 u t) v).1,
          t * (centerCoordinates (fiberCenter a.a2 a.a3 u t) v).1 -
            (centerCoordinates (fiberCenter a.a2 a.a3 u t) v).2) =
        centerCoordinates (fiberCenter a.a2 a.a3 u t)
          (fiberPair a.a2 a.a3 u t q
            (centeredFiberProduct a.a2 a.a3 u t / h))
    rw [show v = fiberPair a.a2 a.a3 u t q h by rfl]
    rw [centerCoordinates_fiberPair, centerCoordinates_fiberPair]
    exact torusPair_reflect_second t q
      (centeredFiberProduct a.a2 a.a3 u t) h hq hP hh heigen
  apply Point.ext
  · simp [vieta3]
  · change
      (movingCoordinates1
        (vieta3 a (fiberPoint1 a u t q h))).1 =
          (fiberPair a.a2 a.a3 u t q
            (centeredFiberProduct a.a2 a.a3 u t / h)).1
    exact congrArg Prod.fst hmoving
  · change
      (movingCoordinates1
        (vieta3 a (fiberPoint1 a u t q h))).2 =
          (fiberPair a.a2 a.a3 u t q
            (centeredFiberProduct a.a2 a.a3 u t / h)).2
    exact congrArg Prod.snd hmoving

/-- On the first-axis torus chart, `vieta2` sends `h` to
`P / (q² h)`. -/
theorem vieta2_fiberPoint1
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0)
    (hq : q ≠ 0) (hP : centeredFiberProduct a.a2 a.a3 u t ≠ 0)
    (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u) :
    vieta2 a (fiberPoint1 a u t q h) =
      fiberPoint1 a u t q
        (centeredFiberProduct a.a2 a.a3 u t / (q ^ 2 * h)) := by
  let v := fiberPair a.a2 a.a3 u t q h
  have hvieta :
      movingCoordinates1 (vieta2 a (fiberPoint1 a u t q h)) =
        (t * v.2 - v.1 - a.a3 * u, v.2) := by
    apply Prod.ext
    · change
        a.multiplier * v.2 * u - v.1 - a.a1 * v.2 - a.a3 * u =
          t * v.2 - v.1 - a.a3 * u
      rw [hcoordinate]
      simp only [orderedTrace]
      ring
    · rfl
  have hmoving :
      movingCoordinates1 (vieta2 a (fiberPoint1 a u t q h)) =
        fiberPair a.a2 a.a3 u t q
          (centeredFiberProduct a.a2 a.a3 u t / (q ^ 2 * h)) := by
    apply centerCoordinates_injective (fiberCenter a.a2 a.a3 u t)
    rw [hvieta]
    rw [centerCoordinates_reflect_first a.a2 a.a3 u t v hD]
    change
      (t * (centerCoordinates (fiberCenter a.a2 a.a3 u t) v).2 -
            (centerCoordinates (fiberCenter a.a2 a.a3 u t) v).1,
          (centerCoordinates (fiberCenter a.a2 a.a3 u t) v).2) =
        centerCoordinates (fiberCenter a.a2 a.a3 u t)
          (fiberPair a.a2 a.a3 u t q
            (centeredFiberProduct a.a2 a.a3 u t / (q ^ 2 * h)))
    rw [show v = fiberPair a.a2 a.a3 u t q h by rfl]
    rw [centerCoordinates_fiberPair, centerCoordinates_fiberPair]
    exact torusPair_reflect_first t q
      (centeredFiberProduct a.a2 a.a3 u t) h hq hP hh heigen
  apply Point.ext
  · simp [vieta2]
  · change
      (movingCoordinates1
        (vieta2 a (fiberPoint1 a u t q h))).1 =
          (fiberPair a.a2 a.a3 u t q
            (centeredFiberProduct a.a2 a.a3 u t / (q ^ 2 * h))).1
    exact congrArg Prod.fst hmoving
  · change
      (movingCoordinates1
        (vieta2 a (fiberPoint1 a u t q h))).2 =
          (fiberPair a.a2 a.a3 u t q
            (centeredFiberProduct a.a2 a.a3 u t / (q ^ 2 * h))).2
    exact congrArg Prod.snd hmoving

/-- Away from `q² = 1`, the two coordinates of `torusPair` determine its
nonzero parameter. -/
theorem torusPair_parameter_injective
    (q P h k : K) (hq : q ≠ 0) (hh : h ≠ 0) (hk : k ≠ 0)
    (hqSq : q ^ 2 ≠ 1)
    (heq : torusPair q P h = torusPair q P k) :
    h = k := by
  have hfst := congrArg Prod.fst heq
  have hsnd := congrArg Prod.snd heq
  simp only [torusPair] at hfst hsnd
  have hfirst : (h - k) * (h * k - P) = 0 := by
    field_simp [hh, hk] at hfst
    linear_combination hfst
  have hsecond : (h - k) * (q ^ 2 * h * k - P) = 0 := by
    field_simp [hq, hh, hk] at hsnd
    linear_combination hsnd
  rcases mul_eq_zero.mp hfirst with hdiff | hproduct
  · exact sub_eq_zero.mp hdiff
  · rcases mul_eq_zero.mp hsecond with hdiff | hqproduct
    · exact sub_eq_zero.mp hdiff
    · exfalso
      apply hqSq
      have hhk : h * k ≠ 0 := mul_ne_zero hh hk
      apply mul_right_cancel₀ hhk
      calc
        q ^ 2 * (h * k) = q ^ 2 * h * k := by ring
        _ = P := sub_eq_zero.mp hqproduct
        _ = h * k := (sub_eq_zero.mp hproduct).symm
        _ = 1 * (h * k) := by ring

/-- Away from `q² = 1`, `fiberPoint1` is injective on nonzero torus
parameters. -/
theorem fiberPoint1_parameter_injective
    (a : Coefficients K) (u t q h k : K)
    (hq : q ≠ 0) (hh : h ≠ 0) (hk : k ≠ 0)
    (hqSq : q ^ 2 ≠ 1)
    (heq : fiberPoint1 a u t q h = fiberPoint1 a u t q k) :
    h = k := by
  apply torusPair_parameter_injective q
    (centeredFiberProduct a.a2 a.a3 u t) h k hq hh hk hqSq
  have hmoving := congrArg movingCoordinates1 heq
  have hcentered :=
    congrArg (centerCoordinates (fiberCenter a.a2 a.a3 u t)) hmoving
  simpa only [movingCoordinates1_fiberPoint1,
    centerCoordinates_fiberPair] using hcentered

/-- The exact third-Vieta fixed-point criterion on a nondegenerate first-axis
torus chart. -/
theorem vieta3_fiberPoint1_fixed_iff
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0)
    (hq : q ≠ 0) (hP : centeredFiberProduct a.a2 a.a3 u t ≠ 0)
    (hh : h ≠ 0) (hqSq : q ^ 2 ≠ 1)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u) :
    vieta3 a (fiberPoint1 a u t q h) = fiberPoint1 a u t q h ↔
      h ^ 2 = centeredFiberProduct a.a2 a.a3 u t := by
  rw [vieta3_fiberPoint1 a u t q h hD hq hP hh heigen hcoordinate]
  constructor
  · intro heq
    have hparam :
        centeredFiberProduct a.a2 a.a3 u t / h = h := by
      exact fiberPoint1_parameter_injective a u t q
        (centeredFiberProduct a.a2 a.a3 u t / h) h hq
        (div_ne_zero hP hh) hh hqSq heq
    have hmul :=
      (div_eq_iff hh).mp hparam
    simpa only [pow_two] using hmul.symm
  · intro hsq
    have hparam :
        centeredFiberProduct a.a2 a.a3 u t / h = h := by
      apply (div_eq_iff hh).mpr
      simpa only [pow_two] using hsq.symm
    rw [hparam]

/-- The exact second-Vieta fixed-point criterion on a nondegenerate first-axis
torus chart. -/
theorem vieta2_fiberPoint1_fixed_iff
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0)
    (hq : q ≠ 0) (hP : centeredFiberProduct a.a2 a.a3 u t ≠ 0)
    (hh : h ≠ 0) (hqSq : q ^ 2 ≠ 1)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u) :
    vieta2 a (fiberPoint1 a u t q h) = fiberPoint1 a u t q h ↔
      (q * h) ^ 2 = centeredFiberProduct a.a2 a.a3 u t := by
  rw [vieta2_fiberPoint1 a u t q h hD hq hP hh heigen hcoordinate]
  constructor
  · intro heq
    have hdenom : q ^ 2 * h ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hq) hh
    have hparam :
        centeredFiberProduct a.a2 a.a3 u t / (q ^ 2 * h) = h := by
      exact fiberPoint1_parameter_injective a u t q
        (centeredFiberProduct a.a2 a.a3 u t / (q ^ 2 * h)) h hq
        (div_ne_zero hP hdenom) hh hqSq heq
    have hmul := (div_eq_iff hdenom).mp hparam
    calc
      (q * h) ^ 2 = h * (q ^ 2 * h) := by ring
      _ = centeredFiberProduct a.a2 a.a3 u t := hmul.symm
  · intro hsq
    have hdenom : q ^ 2 * h ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hq) hh
    have hparam :
        centeredFiberProduct a.a2 a.a3 u t / (q ^ 2 * h) = h := by
      apply (div_eq_iff hdenom).mpr
      calc
        centeredFiberProduct a.a2 a.a3 u t = (q * h) ^ 2 := hsq.symm
        _ = h * (q ^ 2 * h) := by ring
    rw [hparam]

/-- Two torus parameters lie in the same multiplicative square coset. -/
def SameSquareCoset (x y : K) : Prop :=
  ∃ r : K, x = r ^ 2 * y

/-- Rotation by `q²` preserves the square coset of a torus parameter. -/
theorem sameSquareCoset_sq_mul (q h : K) :
    SameSquareCoset (q ^ 2 * h) h :=
  ⟨q, rfl⟩

/-- Every nonnegative iterate of the rotation parameter remains in the
same square coset. -/
theorem sameSquareCoset_pow_sq_mul (q h : K) (n : ℕ) :
    SameSquareCoset ((q ^ 2) ^ n * h) h := by
  refine ⟨q ^ n, ?_⟩
  congr 1
  calc
    (q ^ 2) ^ n = q ^ (2 * n) := (pow_mul q 2 n).symm
    _ = q ^ (n * 2) := by rw [Nat.mul_comm 2 n]
    _ = (q ^ n) ^ 2 := pow_mul q n 2

/-- The second-coordinate reflection preserves the square coset exactly
when the centered product is a square. -/
theorem sameSquareCoset_div_iff_isSquare
    (P h : K) (hh : h ≠ 0) :
    SameSquareCoset (P / h) h ↔ IsSquare P := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r * h, ?_⟩
    field_simp [hh] at hr
    linear_combination hr
  · rintro ⟨z, hz⟩
    refine ⟨z / h, ?_⟩
    field_simp [hh]
    rw [hz]
    ring

/-- The first-coordinate reflection has the same square-coset criterion;
the extra `q²` denominator is itself a square. -/
theorem sameSquareCoset_div_sq_mul_iff_isSquare
    (q P h : K) (hq : q ≠ 0) (hh : h ≠ 0) :
    SameSquareCoset (P / (q ^ 2 * h)) h ↔ IsSquare P := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r * q * h, ?_⟩
    field_simp [hq, hh] at hr
    linear_combination hr
  · rintro ⟨z, hz⟩
    refine ⟨z / (q * h), ?_⟩
    field_simp [hq, hh]
    rw [hz]
    ring

/-- Exact parity package for the two adjacent first-axis Vieta reflections:
rotation stays in the current square coset, while both odd reflections leave
it precisely when `P` is nonsquare. -/
theorem firstAxis_torus_squareCoset_parity
    (q P h : K) (hq : q ≠ 0) (hh : h ≠ 0)
    (hP : ¬ IsSquare P) :
    SameSquareCoset (q ^ 2 * h) h ∧
      ¬ SameSquareCoset (P / h) h ∧
      ¬ SameSquareCoset (P / (q ^ 2 * h)) h := by
  exact ⟨sameSquareCoset_sq_mul q h,
    fun hs => hP ((sameSquareCoset_div_iff_isSquare P h hh).mp hs),
    fun hs =>
      hP ((sameSquareCoset_div_sq_mul_iff_isSquare q P h hq hh).mp hs)⟩

section RotationCoset

variable {G : Type*} [CommGroup G]

/-- The abstract third-Vieta reflection on a multiplicative torus. -/
def torusReflection3 (P x : G) : G :=
  P * x⁻¹

/-- The abstract second-Vieta reflection on a multiplicative torus. -/
def torusReflection2 (q P x : G) : G :=
  P * (q ^ 2 * x)⁻¹

private theorem image_invMul_leftCoset
    (c h : G) (H : Subgroup G) :
    (fun x => c * x⁻¹) '' (h • (H : Set G)) =
      (c * h⁻¹) • (H : Set G) := by
  ext x
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨g⁻¹, H.inv_mem hg, ?_⟩
    simp only [smul_eq_mul]
    rw [mul_inv_rev]
    ac_rfl
  · rintro ⟨g, hg, rfl⟩
    refine ⟨h * g⁻¹, ⟨g⁻¹, H.inv_mem hg, rfl⟩, ?_⟩
    simp only [smul_eq_mul]
    rw [mul_inv_rev, inv_inv]
    ac_rfl

/-- The third-Vieta reflection sends a `q²` rotation coset to its reflected
coset with representative `P h⁻¹`. -/
theorem torusReflection3_image_rotationCoset
    (q P h : G) :
    torusReflection3 P '' (h • (Subgroup.zpowers (q ^ 2) : Set G)) =
      (P * h⁻¹) • (Subgroup.zpowers (q ^ 2) : Set G) := by
  exact image_invMul_leftCoset P h (Subgroup.zpowers (q ^ 2))

/-- The second-Vieta reflection has the same image rotation coset as the
third-Vieta reflection: its additional `q⁻²` factor belongs to
`zpowers (q²)`. -/
theorem torusReflection2_image_rotationCoset
    (q P h : G) :
    torusReflection2 q P '' (h • (Subgroup.zpowers (q ^ 2) : Set G)) =
      (P * h⁻¹) • (Subgroup.zpowers (q ^ 2) : Set G) := by
  rw [show torusReflection2 q P =
      fun x => (P * (q ^ 2)⁻¹) * x⁻¹ by
        funext x
        simp only [torusReflection2]
        rw [mul_inv_rev]
        ac_rfl]
  rw [image_invMul_leftCoset]
  apply (leftCoset_eq_iff _).mpr
  have hmem :
      q ^ 2 ∈ Subgroup.zpowers (q ^ 2) :=
    Subgroup.mem_zpowers (q ^ 2)
  convert hmem using 1
  simp only [mul_inv_rev, inv_inv]
  calc
    h * (q ^ 2 * P⁻¹) * (P * h⁻¹) =
        q ^ 2 * (P⁻¹ * P) * (h * h⁻¹) := by ac_rfl
    _ = q ^ 2 := by simp

/-- Exact orbit-coset criterion.  The even rotation coset and its odd
reflected coset coincide exactly when `P h⁻²` lies in `zpowers (q²)`.
Thus squarehood of `P` is sufficient only when `q²` generates the full
square subgroup. -/
theorem rotationCoset_eq_reflectedCoset_iff
    (q P h : G) :
    h • (Subgroup.zpowers (q ^ 2) : Set G) =
        (P * h⁻¹) • (Subgroup.zpowers (q ^ 2) : Set G) ↔
      P * (h ^ 2)⁻¹ ∈ Subgroup.zpowers (q ^ 2) := by
  rw [leftCoset_eq_iff]
  have heq : h⁻¹ * (P * h⁻¹) = P * (h ^ 2)⁻¹ := by
    rw [← inv_pow, pow_two]
    ac_rfl
  rw [heq]

end RotationCoset

/-- If the centered product is nonsquare, no parameter in the `q²` rotation
orbit is fixed by either adjacent Vieta involution.  This applies in
particular to a primitive `q²` orbit; no primitivity hypothesis is needed for
the obstruction. -/
theorem no_adjacentVieta_fixed_on_firstAxis_rotationParameters_of_not_isSquare
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0)
    (hq : q ≠ 0) (hh : h ≠ 0) (hqSq : q ^ 2 ≠ 1)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u)
    (hP : ¬ IsSquare (centeredFiberProduct a.a2 a.a3 u t))
    (n : ℤ) :
    let hn := (q ^ 2) ^ n * h
    vieta2 a (fiberPoint1 a u t q hn) ≠ fiberPoint1 a u t q hn ∧
      vieta3 a (fiberPoint1 a u t q hn) ≠ fiberPoint1 a u t q hn := by
  dsimp only
  let hn := (q ^ 2) ^ n * h
  have hPne : centeredFiberProduct a.a2 a.a3 u t ≠ 0 := by
    intro hzero
    apply hP
    rw [hzero]
    exact IsSquare.zero
  have hhn : hn ≠ 0 := by
    exact mul_ne_zero (zpow_ne_zero n (pow_ne_zero 2 hq)) hh
  constructor
  · intro hfix
    have hsq :=
      (vieta2_fiberPoint1_fixed_iff a u t q hn hD hq hPne hhn
        hqSq heigen hcoordinate).mp hfix
    apply hP
    refine ⟨q * hn, ?_⟩
    simpa only [pow_two] using hsq.symm
  · intro hfix
    have hsq :=
      (vieta3_fiberPoint1_fixed_iff a u t q hn hD hq hPne hhn
        hqSq heigen hcoordinate).mp hfix
    apply hP
    refine ⟨hn, ?_⟩
    simpa only [pow_two] using hsq.symm

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The trace used in the explicit `ZMod 5` obstruction lies in the full
ordered candidate-regular regime. -/
theorem zmod5_unequal_firstAxis_candidateRegular :
    let a : Coefficients (ZMod 5) := ⟨1, 0, 4⟩
    OrderedTraceCandidateRegular a.a1 a.a2 a.a3 0 := by
  norm_num [OrderedTraceCandidateRegular,
    orderedTraceDiscriminantPolynomial,
    orderedTraceCenteredNormPolynomial,
    orderedTraceWeightDifferencePolynomial,
    orderedTraceEvenMinusPolynomial,
    orderedTraceEvenPlusPolynomial]
  all_goals decide

/-- The multiplier `q² = 4` in the explicit `ZMod 5` example has exact
period two. -/
theorem zmod5_two_sq_has_period_two :
    (((2 : ZMod 5) ^ 2) ^ 2 = 1) ∧ (2 : ZMod 5) ^ 2 ≠ 1 := by
  decide

/-- An explicit unequal-coefficient primitive-orbit obstruction:
for `a = (1,0,4)`, `u = q = 2`, and `t = 0` over `ZMod 5`, the centered
product is the nonsquare `3`, so neither adjacent Vieta involution fixes any
point of the `q²` parameter orbit. -/
theorem zmod5_unequal_firstAxis_no_adjacentVieta_fixed (n : ℤ) :
    let a : Coefficients (ZMod 5) := ⟨1, 0, 4⟩
    let q : ZMod 5 := 2
    let u : ZMod 5 := 2
    let t : ZMod 5 := 0
    let h : ZMod 5 := 1
    let hn := (q ^ 2) ^ n * h
    vieta2 a (fiberPoint1 a u t q hn) ≠ fiberPoint1 a u t q hn ∧
      vieta3 a (fiberPoint1 a u t q hn) ≠ fiberPoint1 a u t q hn := by
  dsimp only
  let a : Coefficients (ZMod 5) := ⟨1, 0, 4⟩
  have hD : discriminant (0 : ZMod 5) ≠ 0 := by
    decide
  have hq : (2 : ZMod 5) ≠ 0 := by decide
  have hh : (1 : ZMod 5) ≠ 0 := by decide
  have hqSq : (2 : ZMod 5) ^ 2 ≠ 1 := by decide
  have hinvTwo : (2 : ZMod 5)⁻¹ = 3 :=
    ZMod.inv_eq_of_mul_eq_one 5 2 3 (by decide)
  have heigen : (0 : ZMod 5) = 2 + (2 : ZMod 5)⁻¹ := by
    rw [hinvTwo]
    decide
  have hcoordinate :
      (0 : ZMod 5) = orderedTrace a.multiplier a.a1 2 := by
    decide
  have hPvalue :
      centeredFiberProduct a.a2 a.a3 2 0 = (3 : ZMod 5) := by
    dsimp [a]
    rw [centeredFiberProduct]
    field_simp [hD]
    simp only [centeredNorm, discriminant]
    decide
  have hP :
      ¬ IsSquare (centeredFiberProduct a.a2 a.a3 2 0) := by
    rw [hPvalue]
    decide
  exact
    no_adjacentVieta_fixed_on_firstAxis_rotationParameters_of_not_isSquare
      a 2 0 2 1 hD hq hh hqSq heigen hcoordinate hP n

end

end GenMarkoff.General.Cage
