import GenMarkoff.General.Cage.ConnectingFiber
import GenMarkoff.General.MiddleGame.DirectedOrderGrowth

/-!
# Directed connecting fibers on all three coordinate axes

The first-axis connecting-fiber theorem is not transported through a
permutation of a fixed unequal-coefficient surface.  Instead, this file
proves the second- and third-axis statements in their own ordered frames:

* the second-axis moving pair is `(x₃, x₁)`, with coefficients `(a₃, a₁)`;
* the third-axis moving pair is `(x₁, x₂)`, with coefficients `(a₁, a₂)`.

For these orientations the actual library rotations `rotation2` and
`rotation3` both multiply the torus parameter by `q ^ 2`.  The individual
Vieta reflections used to exchange the two square cosets are respectively
`vieta1` and `vieta2`.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff
open GenMarkoff.General.Assembly

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- On the second-axis torus chart, `vieta1` sends `h` to `P / h`.
The moving coordinates are kept in the ordered frame `(x₃, x₁)`. -/
theorem vieta1_fiberPoint2
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0)
    (hq : q ≠ 0) (hP : centeredFiberProduct a.a3 a.a1 u t ≠ 0)
    (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u) :
    vieta1 a (fiberPoint2 a u t q h) =
      fiberPoint2 a u t q
        (centeredFiberProduct a.a3 a.a1 u t / h) := by
  let v := fiberPair a.a3 a.a1 u t q h
  have hvieta :
      movingCoordinates2 (vieta1 a (fiberPoint2 a u t q h)) =
        (v.1, t * v.1 - v.2 - a.a3 * u) := by
    apply Prod.ext
    · rfl
    · change
        a.multiplier * u * v.1 - v.2 - a.a3 * u - a.a2 * v.1 =
          t * v.1 - v.2 - a.a3 * u
      rw [hcoordinate]
      simp only [orderedTrace]
      ring
  have hmoving :
      movingCoordinates2 (vieta1 a (fiberPoint2 a u t q h)) =
        fiberPair a.a3 a.a1 u t q
          (centeredFiberProduct a.a3 a.a1 u t / h) := by
    apply centerCoordinates_injective (fiberCenter a.a3 a.a1 u t)
    rw [hvieta]
    rw [centerCoordinates_reflect_second a.a3 a.a1 u t v hD]
    change
      ((centerCoordinates (fiberCenter a.a3 a.a1 u t) v).1,
          t * (centerCoordinates (fiberCenter a.a3 a.a1 u t) v).1 -
            (centerCoordinates (fiberCenter a.a3 a.a1 u t) v).2) =
        centerCoordinates (fiberCenter a.a3 a.a1 u t)
          (fiberPair a.a3 a.a1 u t q
            (centeredFiberProduct a.a3 a.a1 u t / h))
    rw [show v = fiberPair a.a3 a.a1 u t q h by rfl]
    rw [centerCoordinates_fiberPair, centerCoordinates_fiberPair]
    exact torusPair_reflect_second t q
      (centeredFiberProduct a.a3 a.a1 u t) h hq hP hh heigen
  apply Point.ext
  · change
      (movingCoordinates2
        (vieta1 a (fiberPoint2 a u t q h))).2 =
          (fiberPair a.a3 a.a1 u t q
            (centeredFiberProduct a.a3 a.a1 u t / h)).2
    exact congrArg Prod.snd hmoving
  · simp [vieta1]
  · change
      (movingCoordinates2
        (vieta1 a (fiberPoint2 a u t q h))).1 =
          (fiberPair a.a3 a.a1 u t q
            (centeredFiberProduct a.a3 a.a1 u t / h)).1
    exact congrArg Prod.fst hmoving

/-- On the third-axis torus chart, `vieta2` sends `h` to `P / h`.
The moving coordinates are kept in the ordered frame `(x₁, x₂)`. -/
theorem vieta2_fiberPoint3
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0)
    (hq : q ≠ 0) (hP : centeredFiberProduct a.a1 a.a2 u t ≠ 0)
    (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u) :
    vieta2 a (fiberPoint3 a u t q h) =
      fiberPoint3 a u t q
        (centeredFiberProduct a.a1 a.a2 u t / h) := by
  let v := fiberPair a.a1 a.a2 u t q h
  have hvieta :
      movingCoordinates3 (vieta2 a (fiberPoint3 a u t q h)) =
        (v.1, t * v.1 - v.2 - a.a1 * u) := by
    apply Prod.ext
    · rfl
    · change
        a.multiplier * u * v.1 - v.2 - a.a1 * u - a.a3 * v.1 =
          t * v.1 - v.2 - a.a1 * u
      rw [hcoordinate]
      simp only [orderedTrace]
      ring
  have hmoving :
      movingCoordinates3 (vieta2 a (fiberPoint3 a u t q h)) =
        fiberPair a.a1 a.a2 u t q
          (centeredFiberProduct a.a1 a.a2 u t / h) := by
    apply centerCoordinates_injective (fiberCenter a.a1 a.a2 u t)
    rw [hvieta]
    rw [centerCoordinates_reflect_second a.a1 a.a2 u t v hD]
    change
      ((centerCoordinates (fiberCenter a.a1 a.a2 u t) v).1,
          t * (centerCoordinates (fiberCenter a.a1 a.a2 u t) v).1 -
            (centerCoordinates (fiberCenter a.a1 a.a2 u t) v).2) =
        centerCoordinates (fiberCenter a.a1 a.a2 u t)
          (fiberPair a.a1 a.a2 u t q
            (centeredFiberProduct a.a1 a.a2 u t / h))
    rw [show v = fiberPair a.a1 a.a2 u t q h by rfl]
    rw [centerCoordinates_fiberPair, centerCoordinates_fiberPair]
    exact torusPair_reflect_second t q
      (centeredFiberProduct a.a1 a.a2 u t) h hq hP hh heigen
  apply Point.ext
  · change
      (movingCoordinates3
        (vieta2 a (fiberPoint3 a u t q h))).1 =
          (fiberPair a.a1 a.a2 u t q
            (centeredFiberProduct a.a1 a.a2 u t / h)).1
    exact congrArg Prod.fst hmoving
  · change
      (movingCoordinates3
        (vieta2 a (fiberPoint3 a u t q h))).2 =
          (fiberPair a.a1 a.a2 u t q
            (centeredFiberProduct a.a1 a.a2 u t / h)).2
    exact congrArg Prod.snd hmoving
  · simp [vieta2]

/-- One first-Vieta reflection stays in the same full-Vieta component. -/
theorem sameVietaComponent_vieta1
    {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) :
    SameVietaComponent x (vieta1SurfacePerm a x) := by
  let g : VietaGroup a :=
    ⟨vieta1SurfacePerm a, vieta1SurfacePerm_mem_VietaGroup a⟩
  exact ⟨g, rfl⟩

/-- One second-Vieta reflection stays in the same full-Vieta component. -/
theorem sameVietaComponent_vieta2
    {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) :
    SameVietaComponent x (vieta2SurfacePerm a x) := by
  let g : VietaGroup a :=
    ⟨vieta2SurfacePerm a, vieta2SurfacePerm_mem_VietaGroup a⟩
  exact ⟨g, rfl⟩

private theorem coe_iterate_rotation2SurfacePerm
    {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) (n : ℕ) :
    ((((rotation2SurfacePerm a)^[n]) x :
      SolutionSurface a) : Point R) =
        ((rotation2 a)^[n]) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        coe_rotation2SurfacePerm, ih]

private theorem coe_iterate_rotation3SurfacePerm
    {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) (n : ℕ) :
    ((((rotation3SurfacePerm a)^[n]) x :
      SolutionSurface a) : Point R) =
        ((rotation3 a)^[n]) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        coe_rotation3SurfacePerm, ih]

/-- A point equality produced by iterating the second rotation gives
full-Vieta connectivity of the corresponding surface points. -/
theorem sameVietaComponent_of_iterate_rotation2
    {R : Type u} [CommRing R] (a : Coefficients R)
    (x y : SolutionSurface a) (n : ℕ)
    (hxy : ((rotation2 a)^[n]) x.1 = y.1) :
    SameVietaComponent x y := by
  apply sameVietaComponent_of_sameRotationComponent
  obtain ⟨g, hg⟩ :=
    sameRotationComponent_iterate_rotationSurfacePermAt
      a .second x n
  refine ⟨g, hg.trans ?_⟩
  apply Subtype.ext
  simpa [rotationSurfacePermAt] using
    (coe_iterate_rotation2SurfacePerm a x n).trans hxy

/-- A point equality produced by iterating the third rotation gives
full-Vieta connectivity of the corresponding surface points. -/
theorem sameVietaComponent_of_iterate_rotation3
    {R : Type u} [CommRing R] (a : Coefficients R)
    (x y : SolutionSurface a) (n : ℕ)
    (hxy : ((rotation3 a)^[n]) x.1 = y.1) :
    SameVietaComponent x y := by
  apply sameVietaComponent_of_sameRotationComponent
  obtain ⟨g, hg⟩ :=
    sameRotationComponent_iterate_rotationSurfacePermAt
      a .third x n
  refine ⟨g, hg.trans ?_⟩
  apply Subtype.ext
  simpa [rotationSurfacePermAt] using
    (coe_iterate_rotation3SurfacePerm a x n).trans hxy

/-- A primitive second-axis split fiber with nonsquare centered product is a
single full-Vieta component.  This is proved in the fixed ordered frame
`(x₃,x₁)`, using `rotation2` and the first Vieta involution. -/
theorem sameVietaComponent_secondAxis_fiberPoints_of_primitive_of_not_isSquare
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q r s : (ZMod p)ˣ)
    (hD : discriminant t ≠ 0)
    (heigen : t = splitTorusTrace q)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u)
    (hq : orderOf q = Nat.card (ZMod p)ˣ)
    (hP :
      ¬ IsSquare (centeredFiberProduct a.a3 a.a1 u t))
    (hx :
      IsSolution a (fiberPoint2 a u t (q : ZMod p) (r : ZMod p)))
    (hy :
      IsSolution a (fiberPoint2 a u t (q : ZMod p) (s : ZMod p))) :
    SameVietaComponent
      (⟨fiberPoint2 a u t (q : ZMod p) (r : ZMod p), hx⟩ :
        SolutionSurface a)
      (⟨fiberPoint2 a u t (q : ZMod p) (s : ZMod p), hy⟩ :
        SolutionSurface a) := by
  let P : ZMod p := centeredFiberProduct a.a3 a.a1 u t
  have hP0 : P ≠ 0 := by
    intro hzero
    apply hP
    rw [show centeredFiberProduct a.a3 a.a1 u t = P by rfl, hzero]
    exact IsSquare.zero
  let PUnit : (ZMod p)ˣ := Units.mk0 P hP0
  let x : SolutionSurface a :=
    ⟨fiberPoint2 a u t (q : ZMod p) (r : ZMod p), hx⟩
  let y : SolutionSurface a :=
    ⟨fiberPoint2 a u t (q : ZMod p) (s : ZMod p), hy⟩
  have hPUnit : ¬ IsSquare (PUnit : ZMod p) := by
    simpa [PUnit, P] using hP
  rcases
      primitive_parameter_mem_rotation_or_reflected_rotation
        p hpTwo q PUnit r s hq hPUnit with
    hsame | hreflected
  · let h : Subgroup.zpowers (q ^ 2) := ⟨s * r⁻¹, hsame⟩
    obtain ⟨n, hn⟩ :=
      GenMarkoff.General.MiddleGame.exists_iterate_fiberPoint2_eq_mul_zpowers_sq
        a u t q r hD heigen hcoordinate h
    apply sameVietaComponent_of_iterate_rotation2 a x y n
    simpa [x, y, h] using hn
  · have heigenField :
        t = (q : ZMod p) + (q : ZMod p)⁻¹ := by
      simpa only [splitTorusTrace, Units.val_inv_eq_inv_val] using heigen
    have hvieta :
        vieta1 a (fiberPoint2 a u t (q : ZMod p) (r : ZMod p)) =
          fiberPoint2 a u t (q : ZMod p)
            (centeredFiberProduct a.a3 a.a1 u t / (r : ZMod p)) :=
      vieta1_fiberPoint2 a u t (q : ZMod p) (r : ZMod p)
        hD (Units.ne_zero q) hP0 (Units.ne_zero r)
          heigenField hcoordinate
    have hzSolution :
        IsSolution a
          (fiberPoint2 a u t (q : ZMod p)
            (centeredFiberProduct a.a3 a.a1 u t / (r : ZMod p))) := by
      rw [← hvieta]
      exact (isSolution_vieta1 a _).mpr hx
    let z : SolutionSurface a :=
      ⟨fiberPoint2 a u t (q : ZMod p)
        (centeredFiberProduct a.a3 a.a1 u t / (r : ZMod p)),
        hzSolution⟩
    have hxz : SameVietaComponent x z := by
      have hmove := sameVietaComponent_vieta1 a x
      convert hmove using 1
      apply Subtype.ext
      simpa [x, z] using hvieta.symm
    let reflected : (ZMod p)ˣ := PUnit * r⁻¹
    let h : Subgroup.zpowers (q ^ 2) :=
      ⟨s * reflected⁻¹, by simpa [reflected] using hreflected⟩
    obtain ⟨n, hn⟩ :=
      GenMarkoff.General.MiddleGame.exists_iterate_fiberPoint2_eq_mul_zpowers_sq
        a u t q reflected hD heigen hcoordinate h
    have hzy : SameVietaComponent z y := by
      apply sameVietaComponent_of_iterate_rotation2 a z y n
      have hreflectedVal :
          (reflected : ZMod p) =
            centeredFiberProduct a.a3 a.a1 u t / (r : ZMod p) := by
        dsimp only [reflected]
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        dsimp only [PUnit]
        change
          P * (r : ZMod p)⁻¹ =
            centeredFiberProduct a.a3 a.a1 u t / (r : ZMod p)
        rw [div_eq_mul_inv]
      simpa [z, y, h, hreflectedVal] using hn
    exact sameVietaComponent_trans hxz hzy

/-- A primitive third-axis split fiber with nonsquare centered product is a
single full-Vieta component.  This is proved in the fixed ordered frame
`(x₁,x₂)`, using `rotation3` and the second Vieta involution. -/
theorem sameVietaComponent_thirdAxis_fiberPoints_of_primitive_of_not_isSquare
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (q r s : (ZMod p)ˣ)
    (hD : discriminant t ≠ 0)
    (heigen : t = splitTorusTrace q)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u)
    (hq : orderOf q = Nat.card (ZMod p)ˣ)
    (hP :
      ¬ IsSquare (centeredFiberProduct a.a1 a.a2 u t))
    (hx :
      IsSolution a (fiberPoint3 a u t (q : ZMod p) (r : ZMod p)))
    (hy :
      IsSolution a (fiberPoint3 a u t (q : ZMod p) (s : ZMod p))) :
    SameVietaComponent
      (⟨fiberPoint3 a u t (q : ZMod p) (r : ZMod p), hx⟩ :
        SolutionSurface a)
      (⟨fiberPoint3 a u t (q : ZMod p) (s : ZMod p), hy⟩ :
        SolutionSurface a) := by
  let P : ZMod p := centeredFiberProduct a.a1 a.a2 u t
  have hP0 : P ≠ 0 := by
    intro hzero
    apply hP
    rw [show centeredFiberProduct a.a1 a.a2 u t = P by rfl, hzero]
    exact IsSquare.zero
  let PUnit : (ZMod p)ˣ := Units.mk0 P hP0
  let x : SolutionSurface a :=
    ⟨fiberPoint3 a u t (q : ZMod p) (r : ZMod p), hx⟩
  let y : SolutionSurface a :=
    ⟨fiberPoint3 a u t (q : ZMod p) (s : ZMod p), hy⟩
  have hPUnit : ¬ IsSquare (PUnit : ZMod p) := by
    simpa [PUnit, P] using hP
  rcases
      primitive_parameter_mem_rotation_or_reflected_rotation
        p hpTwo q PUnit r s hq hPUnit with
    hsame | hreflected
  · let h : Subgroup.zpowers (q ^ 2) := ⟨s * r⁻¹, hsame⟩
    obtain ⟨n, hn⟩ :=
      GenMarkoff.General.MiddleGame.exists_iterate_fiberPoint3_eq_mul_zpowers_sq
        a u t q r hD heigen hcoordinate h
    apply sameVietaComponent_of_iterate_rotation3 a x y n
    simpa [x, y, h] using hn
  · have heigenField :
        t = (q : ZMod p) + (q : ZMod p)⁻¹ := by
      simpa only [splitTorusTrace, Units.val_inv_eq_inv_val] using heigen
    have hvieta :
        vieta2 a (fiberPoint3 a u t (q : ZMod p) (r : ZMod p)) =
          fiberPoint3 a u t (q : ZMod p)
            (centeredFiberProduct a.a1 a.a2 u t / (r : ZMod p)) :=
      vieta2_fiberPoint3 a u t (q : ZMod p) (r : ZMod p)
        hD (Units.ne_zero q) hP0 (Units.ne_zero r)
          heigenField hcoordinate
    have hzSolution :
        IsSolution a
          (fiberPoint3 a u t (q : ZMod p)
            (centeredFiberProduct a.a1 a.a2 u t / (r : ZMod p))) := by
      rw [← hvieta]
      exact (isSolution_vieta2 a _).mpr hx
    let z : SolutionSurface a :=
      ⟨fiberPoint3 a u t (q : ZMod p)
        (centeredFiberProduct a.a1 a.a2 u t / (r : ZMod p)),
        hzSolution⟩
    have hxz : SameVietaComponent x z := by
      have hmove := sameVietaComponent_vieta2 a x
      convert hmove using 1
      apply Subtype.ext
      simpa [x, z] using hvieta.symm
    let reflected : (ZMod p)ˣ := PUnit * r⁻¹
    let h : Subgroup.zpowers (q ^ 2) :=
      ⟨s * reflected⁻¹, by simpa [reflected] using hreflected⟩
    obtain ⟨n, hn⟩ :=
      GenMarkoff.General.MiddleGame.exists_iterate_fiberPoint3_eq_mul_zpowers_sq
        a u t q reflected hD heigen hcoordinate h
    have hzy : SameVietaComponent z y := by
      apply sameVietaComponent_of_iterate_rotation3 a z y n
      have hreflectedVal :
          (reflected : ZMod p) =
            centeredFiberProduct a.a1 a.a2 u t / (r : ZMod p) := by
        dsimp only [reflected]
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        dsimp only [PUnit]
        change
          P * (r : ZMod p)⁻¹ =
            centeredFiberProduct a.a1 a.a2 u t / (r : ZMod p)
        rw [div_eq_mul_inv]
      simpa [z, y, h, hreflectedVal] using hn
    exact sameVietaComponent_trans hxz hzy

/-- Every two points on the same primitive second-coordinate fiber with
nonsquare centered norm lie in the same full-Vieta component as soon as the
trace is nonparabolic and the original fixed coordinate is nonzero.

Unlike the endgame-facing wrapper below, this local cage interface does not
require the four additional candidate-regular factors. -/
theorem
    sameVietaComponent_of_same_secondCoordinate_of_primitiveConnecting_basic
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (x y : SolutionSurface a)
    (hsecond : x.1.x2 = y.1.x2)
    (q : (ZMod p)ˣ)
    (heigen :
      traceAt a .second x.1 = splitTorusTrace q)
    (hq : orderOf q = Nat.card (ZMod p)ˣ)
    (hD :
      discriminant (traceAt a .second x.1) ≠ 0)
    (hcoordinateNonzero :
      traceAt a .second x.1 + a.a2 ≠ 0)
    (hconnecting :
      ¬ IsSquare
        (centeredNorm a.a3 a.a1 (traceAt a .second x.1))) :
    SameVietaComponent x y := by
  let u : ZMod p := x.1.x2
  let t : ZMod p := traceAt a .second x.1
  have hcoordinate :
      t = orderedTrace a.multiplier a.a2 u := by
    rfl
  have hD' : discriminant t ≠ 0 := by
    simpa [t] using hD
  have hu : u ≠ 0 := by
    intro huZero
    apply hcoordinateNonzero
    simp [u, huZero]
  have hP :
      ¬ IsSquare (centeredFiberProduct a.a3 a.a1 u t) := by
    intro hPsquare
    apply hconnecting
    exact
      (centeredFiberProduct_isSquare_iff_centeredNorm
        a.a3 a.a1 u t hu hD').mp hPsquare
  have hP0 : centeredFiberProduct a.a3 a.a1 u t ≠ 0 := by
    intro hzero
    apply hP
    rw [hzero]
    exact IsSquare.zero
  have hxConic :
      fiberConic a.a3 a.a1 u t x.1.x3 x.1.x1 = 0 := by
    have hxSurface := x.property
    rw [IsSolution, polynomial_fixed_second] at hxSurface
    change
      fiberConic a.a3 a.a1 x.1.x2
        (orderedTrace a.multiplier a.a2 x.1.x2)
        x.1.x3 x.1.x1 = 0
    exact hxSurface
  have hyConic :
      fiberConic a.a3 a.a1 u t y.1.x3 y.1.x1 = 0 := by
    have hySurface := y.property
    rw [IsSolution, polynomial_fixed_second] at hySurface
    change
      fiberConic a.a3 a.a1 x.1.x2
        (orderedTrace a.multiplier a.a2 x.1.x2)
        y.1.x3 y.1.x1 = 0
    rw [hsecond]
    exact hySurface
  obtain ⟨r, hrPair⟩ :=
    GenMarkoff.General.MiddleGame.exists_unit_fiberPair_eq
      a.a3 a.a1 u t q (x.1.x3, x.1.x1)
        hxConic heigen hD' hP0
  obtain ⟨s, hsPair⟩ :=
    GenMarkoff.General.MiddleGame.exists_unit_fiberPair_eq
      a.a3 a.a1 u t q (y.1.x3, y.1.x1)
        hyConic heigen hD' hP0
  have hrPoint :
      fiberPoint2 a u t (q : ZMod p) (r : ZMod p) = x.1 := by
    apply Point.ext
    · exact congrArg Prod.snd hrPair
    · rfl
    · exact congrArg Prod.fst hrPair
  have hsPoint :
      fiberPoint2 a u t (q : ZMod p) (s : ZMod p) = y.1 := by
    apply Point.ext
    · exact congrArg Prod.snd hsPair
    · exact hsecond
    · exact congrArg Prod.fst hsPair
  have hrSolution :
      IsSolution a
        (fiberPoint2 a u t (q : ZMod p) (r : ZMod p)) := by
    rw [hrPoint]
    exact x.property
  have hsSolution :
      IsSolution a
        (fiberPoint2 a u t (q : ZMod p) (s : ZMod p)) := by
    rw [hsPoint]
    exact y.property
  let xr : SolutionSurface a :=
    ⟨fiberPoint2 a u t (q : ZMod p) (r : ZMod p), hrSolution⟩
  let ys : SolutionSurface a :=
    ⟨fiberPoint2 a u t (q : ZMod p) (s : ZMod p), hsSolution⟩
  have hxr : xr = x := by
    apply Subtype.ext
    exact hrPoint
  have hys : ys = y := by
    apply Subtype.ext
    exact hsPoint
  have hconnected :
      SameVietaComponent xr ys :=
    sameVietaComponent_secondAxis_fiberPoints_of_primitive_of_not_isSquare
      p hpTwo a u t q r s hD' heigen hcoordinate hq hP
        hrSolution hsSolution
  rw [hxr, hys] at hconnected
  exact hconnected

/-- Every two points on the same regular primitive second-coordinate fiber
with nonsquare centered norm lie in the same full-Vieta component.  The
coefficient triple stays fixed; the proof uses the ordered moving frame
`(x₃,x₁)`. -/
theorem
    sameVietaComponent_of_same_secondCoordinate_of_primitiveConnecting
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (x y : SolutionSurface a)
    (hsecond : x.1.x2 = y.1.x2)
    (q : (ZMod p)ˣ)
    (heigen :
      traceAt a .second x.1 = splitTorusTrace q)
    (hq : orderOf q = Nat.card (ZMod p)ˣ)
    (hregular :
      OrderedTraceCandidateRegular a.a2 a.a3 a.a1
        (traceAt a .second x.1))
    (hconnecting :
      ¬ IsSquare
        (centeredNorm a.a3 a.a1 (traceAt a .second x.1))) :
    SameVietaComponent x y := by
  apply
    sameVietaComponent_of_same_secondCoordinate_of_primitiveConnecting_basic
      p hpTwo a x y hsecond q heigen hq
  · simpa [discriminant] using hregular.1
  · exact hregular.2.1
  · exact hconnecting

/-- Every two points on the same primitive third-coordinate fiber with
nonsquare centered norm lie in the same full-Vieta component as soon as the
trace is nonparabolic and the original fixed coordinate is nonzero.

Unlike the endgame-facing wrapper below, this local cage interface does not
require the four additional candidate-regular factors. -/
theorem
    sameVietaComponent_of_same_thirdCoordinate_of_primitiveConnecting_basic
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (x y : SolutionSurface a)
    (hthird : x.1.x3 = y.1.x3)
    (q : (ZMod p)ˣ)
    (heigen :
      traceAt a .third x.1 = splitTorusTrace q)
    (hq : orderOf q = Nat.card (ZMod p)ˣ)
    (hD :
      discriminant (traceAt a .third x.1) ≠ 0)
    (hcoordinateNonzero :
      traceAt a .third x.1 + a.a3 ≠ 0)
    (hconnecting :
      ¬ IsSquare
        (centeredNorm a.a1 a.a2 (traceAt a .third x.1))) :
    SameVietaComponent x y := by
  let u : ZMod p := x.1.x3
  let t : ZMod p := traceAt a .third x.1
  have hcoordinate :
      t = orderedTrace a.multiplier a.a3 u := by
    rfl
  have hD' : discriminant t ≠ 0 := by
    simpa [t] using hD
  have hu : u ≠ 0 := by
    intro huZero
    apply hcoordinateNonzero
    simp [u, huZero]
  have hP :
      ¬ IsSquare (centeredFiberProduct a.a1 a.a2 u t) := by
    intro hPsquare
    apply hconnecting
    exact
      (centeredFiberProduct_isSquare_iff_centeredNorm
        a.a1 a.a2 u t hu hD').mp hPsquare
  have hP0 : centeredFiberProduct a.a1 a.a2 u t ≠ 0 := by
    intro hzero
    apply hP
    rw [hzero]
    exact IsSquare.zero
  have hxConic :
      fiberConic a.a1 a.a2 u t x.1.x1 x.1.x2 = 0 := by
    have hxSurface := x.property
    rw [IsSolution, polynomial_fixed_third] at hxSurface
    change
      fiberConic a.a1 a.a2 x.1.x3
        (orderedTrace a.multiplier a.a3 x.1.x3)
        x.1.x1 x.1.x2 = 0
    exact hxSurface
  have hyConic :
      fiberConic a.a1 a.a2 u t y.1.x1 y.1.x2 = 0 := by
    have hySurface := y.property
    rw [IsSolution, polynomial_fixed_third] at hySurface
    change
      fiberConic a.a1 a.a2 x.1.x3
        (orderedTrace a.multiplier a.a3 x.1.x3)
        y.1.x1 y.1.x2 = 0
    rw [hthird]
    exact hySurface
  obtain ⟨r, hrPair⟩ :=
    GenMarkoff.General.MiddleGame.exists_unit_fiberPair_eq
      a.a1 a.a2 u t q (x.1.x1, x.1.x2)
        hxConic heigen hD' hP0
  obtain ⟨s, hsPair⟩ :=
    GenMarkoff.General.MiddleGame.exists_unit_fiberPair_eq
      a.a1 a.a2 u t q (y.1.x1, y.1.x2)
        hyConic heigen hD' hP0
  have hrPoint :
      fiberPoint3 a u t (q : ZMod p) (r : ZMod p) = x.1 := by
    apply Point.ext
    · exact congrArg Prod.fst hrPair
    · exact congrArg Prod.snd hrPair
    · rfl
  have hsPoint :
      fiberPoint3 a u t (q : ZMod p) (s : ZMod p) = y.1 := by
    apply Point.ext
    · exact congrArg Prod.fst hsPair
    · exact congrArg Prod.snd hsPair
    · exact hthird
  have hrSolution :
      IsSolution a
        (fiberPoint3 a u t (q : ZMod p) (r : ZMod p)) := by
    rw [hrPoint]
    exact x.property
  have hsSolution :
      IsSolution a
        (fiberPoint3 a u t (q : ZMod p) (s : ZMod p)) := by
    rw [hsPoint]
    exact y.property
  let xr : SolutionSurface a :=
    ⟨fiberPoint3 a u t (q : ZMod p) (r : ZMod p), hrSolution⟩
  let ys : SolutionSurface a :=
    ⟨fiberPoint3 a u t (q : ZMod p) (s : ZMod p), hsSolution⟩
  have hxr : xr = x := by
    apply Subtype.ext
    exact hrPoint
  have hys : ys = y := by
    apply Subtype.ext
    exact hsPoint
  have hconnected :
      SameVietaComponent xr ys :=
    sameVietaComponent_thirdAxis_fiberPoints_of_primitive_of_not_isSquare
      p hpTwo a u t q r s hD' heigen hcoordinate hq hP
        hrSolution hsSolution
  rw [hxr, hys] at hconnected
  exact hconnected

/-- Every two points on the same regular primitive third-coordinate fiber
with nonsquare centered norm lie in the same full-Vieta component.  The
coefficient triple stays fixed; the proof uses the ordered moving frame
`(x₁,x₂)`. -/
theorem
    sameVietaComponent_of_same_thirdCoordinate_of_primitiveConnecting
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (x y : SolutionSurface a)
    (hthird : x.1.x3 = y.1.x3)
    (q : (ZMod p)ˣ)
    (heigen :
      traceAt a .third x.1 = splitTorusTrace q)
    (hq : orderOf q = Nat.card (ZMod p)ˣ)
    (hregular :
      OrderedTraceCandidateRegular a.a3 a.a1 a.a2
        (traceAt a .third x.1))
    (hconnecting :
      ¬ IsSquare
        (centeredNorm a.a1 a.a2 (traceAt a .third x.1))) :
    SameVietaComponent x y := by
  apply
    sameVietaComponent_of_same_thirdCoordinate_of_primitiveConnecting_basic
      p hpTwo a x y hthird q heigen hq
  · simpa [discriminant] using hregular.1
  · exact hregular.2.1
  · exact hconnecting

end

end GenMarkoff.General.Cage
