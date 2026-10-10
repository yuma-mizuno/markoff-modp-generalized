import GenMarkoff.General.Cage.Connecting.Fiber
import GenMarkoff.General.MiddleGame.DirectedOrderGrowth

/-!
# The connecting-fiber theorem on the second coordinate axis

This file proves the second-axis analogue of the first-axis connecting-fiber
theorem in `GenMarkoff.General.Cage.Connecting.Fiber`, directly in the ordered
frame of the fixed coefficient triple: the moving pair is `(x₃, x₁)` with
coefficients `(a₃, a₁)`.  On the torus chart `fiberPoint2`, `rotation2`
multiplies the torus parameter by `q ^ 2` and `vieta1` sends `h` to `P / h`,
where `P = centeredFiberProduct a.a3 a.a1 u t`.

For a primitive eigenvalue `q` and nonsquare `P`, `vieta1` exchanges the two
cosets of `zpowers (q ^ 2)`, so any two points on the same second-coordinate
fiber lie in the same Vieta-group orbit
(`sameVietaComponent_of_same_secondCoordinate_of_primitiveConnecting`).
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
    -- `movingCoordinates2`, `vieta1` and `fiberPoint2` unfold the left side
    -- to the new `x₁` coordinate given by the `vieta1` formula; restate it
    -- explicitly so that `hcoordinate` and `ring` apply.
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
    -- Zeta-reduce the `let w := centerCoordinates _ v` in the statement of
    -- `centerCoordinates_reflect_second`, exposing `centerCoordinates _ v`.
    change
      ((centerCoordinates (fiberCenter a.a3 a.a1 u t) v).1,
          t * (centerCoordinates (fiberCenter a.a3 a.a1 u t) v).1 -
            (centerCoordinates (fiberCenter a.a3 a.a1 u t) v).2) =
        centerCoordinates (fiberCenter a.a3 a.a1 u t)
          (fiberPair a.a3 a.a1 u t q
            (centeredFiberProduct a.a3 a.a1 u t / h))
    -- `v` is the local name for `fiberPair a.a3 a.a1 u t q h`; unfold it so
    -- that `centerCoordinates_fiberPair` rewrites both sides.
    rw [show v = fiberPair a.a3 a.a1 u t q h by rfl]
    rw [centerCoordinates_fiberPair, centerCoordinates_fiberPair]
    exact torusPair_reflect_second t q
      (centeredFiberProduct a.a3 a.a1 u t) h hq hP hh heigen
  apply Point.ext
  -- The `x₁` coordinate is `(movingCoordinates2 _).2`, and the `x₁` of
  -- `fiberPoint2` is `(fiberPair _).2`, by definition; restate the goal in
  -- this form so that it is the second component of `hmoving`.
  · change
      (movingCoordinates2
        (vieta1 a (fiberPoint2 a u t q h))).2 =
          (fiberPair a.a3 a.a1 u t q
            (centeredFiberProduct a.a3 a.a1 u t / h)).2
    exact congrArg Prod.snd hmoving
  · simp [vieta1]
  -- Likewise the `x₃` coordinate is `(movingCoordinates2 _).1` and
  -- `(fiberPair _).1`; restate as the first component of `hmoving`.
  · change
      (movingCoordinates2
        (vieta1 a (fiberPoint2 a u t q h))).1 =
          (fiberPair a.a3 a.a1 u t q
            (centeredFiberProduct a.a3 a.a1 u t / h)).1
    exact congrArg Prod.fst hmoving

/-- One first-Vieta reflection stays in the same full-Vieta component. -/
theorem sameVietaComponent_vieta1
    {R : Type u} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) :
    SameVietaComponent x (vieta1SurfacePerm a x) := by
  let g : VietaGroup a :=
    ⟨vieta1SurfacePerm a, vieta1SurfacePerm_mem_VietaGroup a⟩
  exact ⟨g, rfl⟩

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

/-- On a second-axis split fiber with primitive eigenvalue `q` and nonsquare
centered product, any two points of the torus chart `fiberPoint2` lie in the
same Vieta-group orbit. -/
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
    -- `P` is the local name for `centeredFiberProduct a.a3 a.a1 u t`; fold it
    -- so that `hzero : P = 0` rewrites the goal.
    rw [show centeredFiberProduct a.a3 a.a1 u t = P by rfl, hzero]
    exact IsSquare.zero
  let PUnit : (ZMod p)ˣ := Units.mk0 P hP0
  let x : SolutionSurface a :=
    ⟨fiberPoint2 a u t (q : ZMod p) (r : ZMod p), hx⟩
  let y : SolutionSurface a :=
    ⟨fiberPoint2 a u t (q : ZMod p) (s : ZMod p), hy⟩
  have hPUnit : ¬ IsSquare (PUnit : ZMod p) := by
    simpa [PUnit, P] using hP
  -- Either `s * r⁻¹ ∈ zpowers (q ^ 2)`, and iterates of `rotation2` join the
  -- two points, or `s` lies in the coset of `P / r`, which `vieta1` reaches.
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
        -- The value of `Units.mk0 P hP0` is `P` by definition
        -- (`Units.val_mk0`); restate so that `div_eq_mul_inv` closes the goal,
        -- `P` being the local name for `centeredFiberProduct a.a3 a.a1 u t`.
        change
          P * (r : ZMod p)⁻¹ =
            centeredFiberProduct a.a3 a.a1 u t / (r : ZMod p)
        rw [div_eq_mul_inv]
      simpa [z, y, h, hreflectedVal] using hn
    exact sameVietaComponent_trans hxz hzy

/-- Any two points on the same primitive split second-coordinate fiber with
nonsquare centered norm lie in the same Vieta-group orbit, provided the trace
is nonparabolic and `traceAt a .second x + a₂ ≠ 0` (equivalently
`a.multiplier * x₂ ≠ 0`).

These are the first two conditions of candidate regularity; the theorem
`sameVietaComponent_of_same_secondCoordinate_of_primitiveConnecting` assumes
full candidate regularity instead. -/
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
  -- Write `x` and `y` as points `fiberPoint2 a u t q r` and
  -- `fiberPoint2 a u t q s` of the torus chart.
  have hxConic :
      fiberConic a.a3 a.a1 u t x.1.x3 x.1.x1 = 0 := by
    have hxSurface := x.property
    rw [IsSolution, polynomial_fixed_second] at hxSurface
    -- Unfold the local names `u := x.1.x2` and `t := traceAt a .second x.1`
    -- (which is `orderedTrace a.multiplier a.a2 x.1.x2`) to match the form
    -- of `hxSurface` given by `polynomial_fixed_second`.
    change
      fiberConic a.a3 a.a1 x.1.x2
        (orderedTrace a.multiplier a.a2 x.1.x2)
        x.1.x3 x.1.x1 = 0
    exact hxSurface
  have hyConic :
      fiberConic a.a3 a.a1 u t y.1.x3 y.1.x1 = 0 := by
    have hySurface := y.property
    rw [IsSolution, polynomial_fixed_second] at hySurface
    -- As above, unfold `u` and `t`; then `hsecond` turns `x.1.x2` into
    -- `y.1.x2`, matching `hySurface`.
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
  -- Apply transitivity on the torus chart.
  have hconnected :
      SameVietaComponent xr ys :=
    sameVietaComponent_secondAxis_fiberPoints_of_primitive_of_not_isSquare
      p hpTwo a u t q r s hD' heigen hcoordinate hq hP
        hrSolution hsSolution
  rw [hxr, hys] at hconnected
  exact hconnected

/-- Any two points on the same primitive split second-coordinate fiber whose
trace is candidate-regular in the frame `(a₂, a₃, a₁)` and has nonsquare
centered norm `centeredNorm a₃ a₁` lie in the same Vieta-group orbit. -/
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

end

end GenMarkoff.General.Cage
