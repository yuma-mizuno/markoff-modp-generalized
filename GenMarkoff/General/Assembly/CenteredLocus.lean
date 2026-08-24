import GenMarkoff.General.TraceParameters

/-!
# Nonparabolic centered loci for unequal coefficients

On a nonparabolic ordered fiber, the heterogeneous affine rotation has one
fixed point: its displayed affine center.  Hence an actual surface point
fixed by the corresponding rotation is centered.  Substitution of the center
into the surface conic forces the centered-fiber product to vanish.

Writing the fixed-axis trace as `t = orderedTrace s A u`, this vanishing has
two possible causes:

* `u = 0`, which gives the exceptional trace `t = -A`;
* `eval t (orderedTraceCenteredNormPolynomial B C) = 0`.

The second set has at most two elements.  If `s ≠ 0`, trace determines the
fixed coordinate, while the rotation-fixed condition determines the other
two coordinates as the affine center.  Thus each nonparabolic rotation-fixed
surface locus has at most three points.

## New consideration in the unequal-coefficient case

The symmetric centered obstruction can be classified by explicit exceptional
points.  For an arbitrary fixed coefficient triple, the affine center and
centered-norm quadratic depend on the ordered frame `(A, B, C)`.  The
zero-coordinate branch `t = -A` must be retained separately, producing the
uniform `1 + 2 = 3` bound on each axis.  All three axis statements below keep
their ordered coefficient frames explicit; no coordinate permutation is
applied to the fixed coefficient triple.  In particular, the first two
centered loci contribute at most six points to a startup error term.
-/

namespace GenMarkoff.General.Assembly

open Polynomial

noncomputable section

universe u

section AlgebraicBoundary

variable {K : Type u} [Field K]

/-- On a nonparabolic ordered fiber, any fixed point of the heterogeneous
affine rotation is its displayed affine center. -/
theorem eq_fiberCenter_of_affineRotation_eq
    (B C u t : K) (v : K × K)
    (hD : discriminant t ≠ 0)
    (hfixed : affineRotation B C u t v = v) :
    v = fiberCenter B C u t := by
  rw [affineRotation_apply] at hfixed
  have hfirst := congrArg Prod.fst hfixed
  have hsecond := congrArg Prod.snd hfixed
  have hfirstZero :
      t * v.2 - 2 * v.1 - C * u = 0 := by
    linear_combination hfirst
  have hsecondZero :
      (t ^ 2 - 2) * v.2 - t * v.1 - (t * C + B) * u = 0 := by
    linear_combination hsecond
  have hfirstCoordinate :
      discriminant t * v.1 = u * (t * B + 2 * C) := by
    simp only [discriminant]
    linear_combination
      -(t ^ 2 - 2) * hfirstZero + t * hsecondZero
  have hsecondCoordinate :
      discriminant t * v.2 = u * (t * C + 2 * B) := by
    simp only [discriminant]
    linear_combination -t * hfirstZero + 2 * hsecondZero
  apply Prod.ext
  · change v.1 = u * (t * B + 2 * C) / discriminant t
    apply (eq_div_iff hD).2
    linear_combination hfirstCoordinate
  · change v.2 = u * (t * C + 2 * B) / discriminant t
    apply (eq_div_iff hD).2
    linear_combination hsecondCoordinate

/-- A surface conic containing its affine center has zero centered-fiber
product. -/
theorem centeredFiberProduct_eq_zero_of_fiberConic_fiberCenter_eq_zero
    (B C u t : K) (hD : discriminant t ≠ 0)
    (hconic :
      fiberConic B C u t
        (fiberCenter B C u t).1 (fiberCenter B C u t).2 = 0) :
    centeredFiberProduct B C u t = 0 := by
  have hcentered := fiberConic_centered B C u t 0 0 hD
  have hcentered' :
      fiberConic B C u t
          (fiberCenter B C u t).1 (fiberCenter B C u t).2 =
        u ^ 2 * centeredNorm B C t / discriminant t := by
    simpa using hcentered
  have hquotient :
      u ^ 2 * centeredNorm B C t / discriminant t = 0 :=
    hcentered'.symm.trans hconic
  have hnumerator : u ^ 2 * centeredNorm B C t = 0 :=
    (div_eq_zero_iff.mp hquotient).resolve_right hD
  simp [centeredFiberProduct, hnumerator]

/-- The zero centered-fiber product is controlled by one exceptional trace
and the ordered centered-norm quadratic. -/
theorem trace_eq_neg_coefficient_or_eval_orderedTraceCenteredNormPolynomial_eq_zero
    (s A B C u t : K)
    (hD : discriminant t ≠ 0)
    (hcoordinate : t = orderedTrace s A u)
    (hproduct : centeredFiberProduct B C u t = 0) :
    t = -A ∨
      eval t (orderedTraceCenteredNormPolynomial B C) = 0 := by
  rw [centeredFiberProduct] at hproduct
  have hDsq : discriminant t ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have hnumerator : u ^ 2 * centeredNorm B C t = 0 :=
    (div_eq_zero_iff.mp hproduct).resolve_right hDsq
  rcases mul_eq_zero.mp hnumerator with huSquare | hnorm
  · left
    have hu : u = 0 := sq_eq_zero_iff.mp huSquare
    rw [hcoordinate, hu, orderedTrace]
    simp
  · right
    simpa [centeredNorm, discriminant] using hnorm

/-- A first-axis rotation-fixed point on a nonparabolic fiber has moving
coordinates equal to the ordered affine center `(a₂,a₃)`. -/
theorem movingCoordinates1_eq_fiberCenter_of_rotation1_fixed
    (a : Coefficients K) (x : Point K)
    (hD :
      discriminant (orderedTrace a.multiplier a.a1 x.x1) ≠ 0)
    (hfixed : rotation1 a x = x) :
    movingCoordinates1 x =
      fiberCenter a.a2 a.a3 x.x1
        (orderedTrace a.multiplier a.a1 x.x1) := by
  apply eq_fiberCenter_of_affineRotation_eq
    a.a2 a.a3 x.x1
      (orderedTrace a.multiplier a.a1 x.x1)
      (movingCoordinates1 x) hD
  rw [← movingCoordinates1_rotation1]
  exact congrArg movingCoordinates1 hfixed

/-- A second-axis rotation-fixed point on a nonparabolic fiber has moving
coordinates, ordered as `(x₃,x₁)`, equal to the affine center `(a₃,a₁)`. -/
theorem movingCoordinates2_eq_fiberCenter_of_rotation2_fixed
    (a : Coefficients K) (x : Point K)
    (hD :
      discriminant (orderedTrace a.multiplier a.a2 x.x2) ≠ 0)
    (hfixed : rotation2 a x = x) :
    movingCoordinates2 x =
      fiberCenter a.a3 a.a1 x.x2
        (orderedTrace a.multiplier a.a2 x.x2) := by
  apply eq_fiberCenter_of_affineRotation_eq
    a.a3 a.a1 x.x2
      (orderedTrace a.multiplier a.a2 x.x2)
      (movingCoordinates2 x) hD
  rw [← movingCoordinates2_rotation2]
  exact congrArg movingCoordinates2 hfixed

/-- A third-axis rotation-fixed point on a nonparabolic fiber has moving
coordinates, ordered as `(x₁,x₂)`, equal to the affine center `(a₁,a₂)`. -/
theorem movingCoordinates3_eq_fiberCenter_of_rotation3_fixed
    (a : Coefficients K) (x : Point K)
    (hD :
      discriminant (orderedTrace a.multiplier a.a3 x.x3) ≠ 0)
    (hfixed : rotation3 a x = x) :
    movingCoordinates3 x =
      fiberCenter a.a1 a.a2 x.x3
        (orderedTrace a.multiplier a.a3 x.x3) := by
  apply eq_fiberCenter_of_affineRotation_eq
    a.a1 a.a2 x.x3
      (orderedTrace a.multiplier a.a3 x.x3)
      (movingCoordinates3 x) hD
  rw [← movingCoordinates3_rotation3]
  exact congrArg movingCoordinates3 hfixed

/-- On the first axis, a nonparabolic rotation-fixed surface point has zero
centered-fiber product in the ordered frame `(a₁,a₂,a₃)`. -/
theorem centeredFiberProduct_axisOne_eq_zero_of_isSolution_rotation1_fixed
    (a : Coefficients K) (x : Point K)
    (hsolution : IsSolution a x)
    (hD :
      discriminant (orderedTrace a.multiplier a.a1 x.x1) ≠ 0)
    (hfixed : rotation1 a x = x) :
    centeredFiberProduct a.a2 a.a3 x.x1
      (orderedTrace a.multiplier a.a1 x.x1) = 0 := by
  let t := orderedTrace a.multiplier a.a1 x.x1
  have hcenter :
      movingCoordinates1 x = fiberCenter a.a2 a.a3 x.x1 t :=
    movingCoordinates1_eq_fiberCenter_of_rotation1_fixed a x hD hfixed
  have hconic :
      fiberConic a.a2 a.a3 x.x1 t x.x2 x.x3 = 0 := by
    have hp := hsolution
    rw [IsSolution, polynomial_fixed_first] at hp
    exact hp
  have hconicCenter :
      fiberConic a.a2 a.a3 x.x1 t
        (fiberCenter a.a2 a.a3 x.x1 t).1
        (fiberCenter a.a2 a.a3 x.x1 t).2 = 0 := by
    rw [← hcenter]
    simpa [movingCoordinates1] using hconic
  exact
    centeredFiberProduct_eq_zero_of_fiberConic_fiberCenter_eq_zero
      a.a2 a.a3 x.x1 t hD hconicCenter

/-- On the second axis, a nonparabolic rotation-fixed surface point has zero
centered-fiber product in the ordered frame `(a₂,a₃,a₁)`. -/
theorem centeredFiberProduct_axisTwo_eq_zero_of_isSolution_rotation2_fixed
    (a : Coefficients K) (x : Point K)
    (hsolution : IsSolution a x)
    (hD :
      discriminant (orderedTrace a.multiplier a.a2 x.x2) ≠ 0)
    (hfixed : rotation2 a x = x) :
    centeredFiberProduct a.a3 a.a1 x.x2
      (orderedTrace a.multiplier a.a2 x.x2) = 0 := by
  let t := orderedTrace a.multiplier a.a2 x.x2
  have hcenter :
      movingCoordinates2 x = fiberCenter a.a3 a.a1 x.x2 t :=
    movingCoordinates2_eq_fiberCenter_of_rotation2_fixed a x hD hfixed
  have hconic :
      fiberConic a.a3 a.a1 x.x2 t x.x3 x.x1 = 0 := by
    have hp := hsolution
    rw [IsSolution, polynomial_fixed_second] at hp
    exact hp
  have hconicCenter :
      fiberConic a.a3 a.a1 x.x2 t
        (fiberCenter a.a3 a.a1 x.x2 t).1
        (fiberCenter a.a3 a.a1 x.x2 t).2 = 0 := by
    rw [← hcenter]
    simpa [movingCoordinates2] using hconic
  exact
    centeredFiberProduct_eq_zero_of_fiberConic_fiberCenter_eq_zero
      a.a3 a.a1 x.x2 t hD hconicCenter

/-- On the third axis, a nonparabolic rotation-fixed surface point has zero
centered-fiber product in the ordered frame `(a₃,a₁,a₂)`. -/
theorem centeredFiberProduct_axisThree_eq_zero_of_isSolution_rotation3_fixed
    (a : Coefficients K) (x : Point K)
    (hsolution : IsSolution a x)
    (hD :
      discriminant (orderedTrace a.multiplier a.a3 x.x3) ≠ 0)
    (hfixed : rotation3 a x = x) :
    centeredFiberProduct a.a1 a.a2 x.x3
      (orderedTrace a.multiplier a.a3 x.x3) = 0 := by
  let t := orderedTrace a.multiplier a.a3 x.x3
  have hcenter :
      movingCoordinates3 x = fiberCenter a.a1 a.a2 x.x3 t :=
    movingCoordinates3_eq_fiberCenter_of_rotation3_fixed a x hD hfixed
  have hconic :
      fiberConic a.a1 a.a2 x.x3 t x.x1 x.x2 = 0 := by
    have hp := hsolution
    rw [IsSolution, polynomial_fixed_third] at hp
    exact hp
  have hconicCenter :
      fiberConic a.a1 a.a2 x.x3 t
        (fiberCenter a.a1 a.a2 x.x3 t).1
        (fiberCenter a.a1 a.a2 x.x3 t).2 = 0 := by
    rw [← hcenter]
    simpa [movingCoordinates3] using hconic
  exact
    centeredFiberProduct_eq_zero_of_fiberConic_fiberCenter_eq_zero
      a.a1 a.a2 x.x3 t hD hconicCenter

/-- A finite set injected by trace, with every trace either `-A` or a root of
the ordered centered-norm quadratic, has at most three elements. -/
theorem card_le_three_of_injOn_trace_controlled_by_orderedTraceCenteredNormPolynomial
    {T : Type*} [DecidableEq T] [DecidableEq K]
    (A B C : K) (S : Finset T) (trace : T → K)
    (hinjective : Set.InjOn trace ↑S)
    (hcontrol : ∀ x ∈ S,
      trace x = -A ∨
        eval (trace x) (orderedTraceCenteredNormPolynomial B C) = 0) :
    S.card ≤ 3 := by
  let q := orderedTraceCenteredNormPolynomial B C
  have hq : q ≠ 0 := orderedTraceCenteredNormPolynomial_ne_zero B C
  have himage : S.image trace ⊆ insert (-A) q.roots.toFinset := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨x, hx, rfl⟩
    rcases hcontrol x hx with hneg | hroot
    · exact Finset.mem_insert.mpr (Or.inl hneg)
    · apply Finset.mem_insert.mpr
      apply Or.inr
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hq]
      exact hroot
  have hrootCard : q.roots.toFinset.card ≤ 2 := by
    calc
      q.roots.toFinset.card ≤ q.roots.card :=
        Multiset.toFinset_card_le _
      _ ≤ q.natDegree := Polynomial.card_roots' _
      _ ≤ 2 := by
        dsimp [q]
        rw [orderedTraceCenteredNormPolynomial]
        compute_degree
  calc
    S.card = (S.image trace).card :=
      (Finset.card_image_of_injOn hinjective).symm
    _ ≤ (insert (-A) q.roots.toFinset).card :=
      Finset.card_le_card himage
    _ ≤ q.roots.toFinset.card + 1 := Finset.card_insert_le _ _
    _ ≤ 2 + 1 := Nat.add_le_add_right hrootCard 1
    _ = 3 := rfl

end AlgebraicBoundary

section FiniteLoci

/-- Nonparabolic first-axis surface points fixed by the actual first
rotation. -/
noncomputable def axisOneNonparabolicRotationFixedLocus
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) :
    Finset (Point (ZMod p)) := by
  classical
  exact Finset.univ.filter fun x ↦
    IsSolution a x ∧
      discriminant (orderedTrace a.multiplier a.a1 x.x1) ≠ 0 ∧
        rotation1 a x = x

/-- Nonparabolic second-axis surface points fixed by the actual second
rotation. -/
noncomputable def axisTwoNonparabolicRotationFixedLocus
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) :
    Finset (Point (ZMod p)) := by
  classical
  exact Finset.univ.filter fun x ↦
    IsSolution a x ∧
      discriminant (orderedTrace a.multiplier a.a2 x.x2) ≠ 0 ∧
        rotation2 a x = x

/-- Nonparabolic third-axis surface points fixed by the actual third
rotation. -/
noncomputable def axisThreeNonparabolicRotationFixedLocus
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) :
    Finset (Point (ZMod p)) := by
  classical
  exact Finset.univ.filter fun x ↦
    IsSolution a x ∧
      discriminant (orderedTrace a.multiplier a.a3 x.x3) ≠ 0 ∧
        rotation3 a x = x

@[simp]
theorem mem_axisOneNonparabolicRotationFixedLocus
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p))
    (x : Point (ZMod p)) :
    x ∈ axisOneNonparabolicRotationFixedLocus p a ↔
      IsSolution a x ∧
        discriminant (orderedTrace a.multiplier a.a1 x.x1) ≠ 0 ∧
          rotation1 a x = x := by
  simp [axisOneNonparabolicRotationFixedLocus]

@[simp]
theorem mem_axisTwoNonparabolicRotationFixedLocus
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p))
    (x : Point (ZMod p)) :
    x ∈ axisTwoNonparabolicRotationFixedLocus p a ↔
      IsSolution a x ∧
        discriminant (orderedTrace a.multiplier a.a2 x.x2) ≠ 0 ∧
          rotation2 a x = x := by
  simp [axisTwoNonparabolicRotationFixedLocus]

@[simp]
theorem mem_axisThreeNonparabolicRotationFixedLocus
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p))
    (x : Point (ZMod p)) :
    x ∈ axisThreeNonparabolicRotationFixedLocus p a ↔
      IsSolution a x ∧
        discriminant (orderedTrace a.multiplier a.a3 x.x3) ≠ 0 ∧
          rotation3 a x = x := by
  simp [axisThreeNonparabolicRotationFixedLocus]

/-- The first nonparabolic rotation-fixed surface locus has at most three
points. -/
theorem axisOneNonparabolicRotationFixedLocus_card_le_three
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0) :
    (axisOneNonparabolicRotationFixedLocus p a).card ≤ 3 := by
  classical
  let S := axisOneNonparabolicRotationFixedLocus p a
  let trace : Point (ZMod p) → ZMod p := fun x ↦
    orderedTrace a.multiplier a.a1 x.x1
  have hinjective : Set.InjOn trace ↑S := by
    intro x hx y hy htrace
    have hx' := (mem_axisOneNonparabolicRotationFixedLocus p a x).mp hx
    have hy' := (mem_axisOneNonparabolicRotationFixedLocus p a y).mp hy
    have hmul :
        a.multiplier * x.x1 = a.multiplier * y.x1 := by
      dsimp [trace] at htrace
      simp only [orderedTrace] at htrace
      linear_combination htrace
    have hfixedCoordinate : x.x1 = y.x1 :=
      mul_left_cancel₀ hmultiplier hmul
    have hcenterX :
        movingCoordinates1 x =
          fiberCenter a.a2 a.a3 x.x1 (trace x) := by
      simpa [trace] using
        movingCoordinates1_eq_fiberCenter_of_rotation1_fixed
          a x hx'.2.1 hx'.2.2
    have hcenterY :
        movingCoordinates1 y =
          fiberCenter a.a2 a.a3 y.x1 (trace y) := by
      simpa [trace] using
        movingCoordinates1_eq_fiberCenter_of_rotation1_fixed
          a y hy'.2.1 hy'.2.2
    have hmoving : movingCoordinates1 x = movingCoordinates1 y := by
      calc
        movingCoordinates1 x =
            fiberCenter a.a2 a.a3 x.x1 (trace x) := hcenterX
        _ = fiberCenter a.a2 a.a3 y.x1 (trace y) := by
          rw [hfixedCoordinate, htrace]
        _ = movingCoordinates1 y := hcenterY.symm
    apply Point.ext
    · exact hfixedCoordinate
    · exact congrArg Prod.fst hmoving
    · exact congrArg Prod.snd hmoving
  apply
    card_le_three_of_injOn_trace_controlled_by_orderedTraceCenteredNormPolynomial
      a.a1 a.a2 a.a3 S trace hinjective
  intro x hx
  have hx' := (mem_axisOneNonparabolicRotationFixedLocus p a x).mp hx
  have hproduct :=
    centeredFiberProduct_axisOne_eq_zero_of_isSolution_rotation1_fixed
      a x hx'.1 hx'.2.1 hx'.2.2
  exact
    trace_eq_neg_coefficient_or_eval_orderedTraceCenteredNormPolynomial_eq_zero
      a.multiplier a.a1 a.a2 a.a3 x.x1 (trace x)
      hx'.2.1 (by simp [trace]) (by simpa [trace] using hproduct)

/-- The second nonparabolic rotation-fixed surface locus has at most three
points. -/
theorem axisTwoNonparabolicRotationFixedLocus_card_le_three
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0) :
    (axisTwoNonparabolicRotationFixedLocus p a).card ≤ 3 := by
  classical
  let S := axisTwoNonparabolicRotationFixedLocus p a
  let trace : Point (ZMod p) → ZMod p := fun x ↦
    orderedTrace a.multiplier a.a2 x.x2
  have hinjective : Set.InjOn trace ↑S := by
    intro x hx y hy htrace
    have hx' := (mem_axisTwoNonparabolicRotationFixedLocus p a x).mp hx
    have hy' := (mem_axisTwoNonparabolicRotationFixedLocus p a y).mp hy
    have hmul :
        a.multiplier * x.x2 = a.multiplier * y.x2 := by
      dsimp [trace] at htrace
      simp only [orderedTrace] at htrace
      linear_combination htrace
    have hfixedCoordinate : x.x2 = y.x2 :=
      mul_left_cancel₀ hmultiplier hmul
    have hcenterX :
        movingCoordinates2 x =
          fiberCenter a.a3 a.a1 x.x2 (trace x) := by
      simpa [trace] using
        movingCoordinates2_eq_fiberCenter_of_rotation2_fixed
          a x hx'.2.1 hx'.2.2
    have hcenterY :
        movingCoordinates2 y =
          fiberCenter a.a3 a.a1 y.x2 (trace y) := by
      simpa [trace] using
        movingCoordinates2_eq_fiberCenter_of_rotation2_fixed
          a y hy'.2.1 hy'.2.2
    have hmoving : movingCoordinates2 x = movingCoordinates2 y := by
      calc
        movingCoordinates2 x =
            fiberCenter a.a3 a.a1 x.x2 (trace x) := hcenterX
        _ = fiberCenter a.a3 a.a1 y.x2 (trace y) := by
          rw [hfixedCoordinate, htrace]
        _ = movingCoordinates2 y := hcenterY.symm
    apply Point.ext
    · exact congrArg Prod.snd hmoving
    · exact hfixedCoordinate
    · exact congrArg Prod.fst hmoving
  apply
    card_le_three_of_injOn_trace_controlled_by_orderedTraceCenteredNormPolynomial
      a.a2 a.a3 a.a1 S trace hinjective
  intro x hx
  have hx' := (mem_axisTwoNonparabolicRotationFixedLocus p a x).mp hx
  have hproduct :=
    centeredFiberProduct_axisTwo_eq_zero_of_isSolution_rotation2_fixed
      a x hx'.1 hx'.2.1 hx'.2.2
  exact
    trace_eq_neg_coefficient_or_eval_orderedTraceCenteredNormPolynomial_eq_zero
      a.multiplier a.a2 a.a3 a.a1 x.x2 (trace x)
      hx'.2.1 (by simp [trace]) (by simpa [trace] using hproduct)

/-- The third nonparabolic rotation-fixed surface locus has at most three
points. -/
theorem axisThreeNonparabolicRotationFixedLocus_card_le_three
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0) :
    (axisThreeNonparabolicRotationFixedLocus p a).card ≤ 3 := by
  classical
  let S := axisThreeNonparabolicRotationFixedLocus p a
  let trace : Point (ZMod p) → ZMod p := fun x ↦
    orderedTrace a.multiplier a.a3 x.x3
  have hinjective : Set.InjOn trace ↑S := by
    intro x hx y hy htrace
    have hx' := (mem_axisThreeNonparabolicRotationFixedLocus p a x).mp hx
    have hy' := (mem_axisThreeNonparabolicRotationFixedLocus p a y).mp hy
    have hmul :
        a.multiplier * x.x3 = a.multiplier * y.x3 := by
      dsimp [trace] at htrace
      simp only [orderedTrace] at htrace
      linear_combination htrace
    have hfixedCoordinate : x.x3 = y.x3 :=
      mul_left_cancel₀ hmultiplier hmul
    have hcenterX :
        movingCoordinates3 x =
          fiberCenter a.a1 a.a2 x.x3 (trace x) := by
      simpa [trace] using
        movingCoordinates3_eq_fiberCenter_of_rotation3_fixed
          a x hx'.2.1 hx'.2.2
    have hcenterY :
        movingCoordinates3 y =
          fiberCenter a.a1 a.a2 y.x3 (trace y) := by
      simpa [trace] using
        movingCoordinates3_eq_fiberCenter_of_rotation3_fixed
          a y hy'.2.1 hy'.2.2
    have hmoving : movingCoordinates3 x = movingCoordinates3 y := by
      calc
        movingCoordinates3 x =
            fiberCenter a.a1 a.a2 x.x3 (trace x) := hcenterX
        _ = fiberCenter a.a1 a.a2 y.x3 (trace y) := by
          rw [hfixedCoordinate, htrace]
        _ = movingCoordinates3 y := hcenterY.symm
    apply Point.ext
    · exact congrArg Prod.fst hmoving
    · exact congrArg Prod.snd hmoving
    · exact hfixedCoordinate
  apply
    card_le_three_of_injOn_trace_controlled_by_orderedTraceCenteredNormPolynomial
      a.a3 a.a1 a.a2 S trace hinjective
  intro x hx
  have hx' := (mem_axisThreeNonparabolicRotationFixedLocus p a x).mp hx
  have hproduct :=
    centeredFiberProduct_axisThree_eq_zero_of_isSolution_rotation3_fixed
      a x hx'.1 hx'.2.1 hx'.2.2
  exact
    trace_eq_neg_coefficient_or_eval_orderedTraceCenteredNormPolynomial_eq_zero
      a.multiplier a.a3 a.a1 a.a2 x.x3 (trace x)
      hx'.2.1 (by simp [trace]) (by simpa [trace] using hproduct)

/-- The union of the first two nonparabolic centered fixed loci. -/
noncomputable def firstTwoAxesNonparabolicRotationFixedLocus
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p)) :
    Finset (Point (ZMod p)) :=
  axisOneNonparabolicRotationFixedLocus p a ∪
    axisTwoNonparabolicRotationFixedLocus p a

/-- The first two nonparabolic centered fixed loci contribute at most six
points in total. -/
theorem firstTwoAxesNonparabolicRotationFixedLocus_card_le_six
    (p : ℕ) [Fact p.Prime] (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0) :
    (firstTwoAxesNonparabolicRotationFixedLocus p a).card ≤ 6 := by
  rw [firstTwoAxesNonparabolicRotationFixedLocus]
  calc
    (axisOneNonparabolicRotationFixedLocus p a ∪
        axisTwoNonparabolicRotationFixedLocus p a).card ≤
        (axisOneNonparabolicRotationFixedLocus p a).card +
          (axisTwoNonparabolicRotationFixedLocus p a).card :=
      Finset.card_union_le _ _
    _ ≤ 3 + 3 :=
      Nat.add_le_add
        (axisOneNonparabolicRotationFixedLocus_card_le_three
          p a hmultiplier)
        (axisTwoNonparabolicRotationFixedLocus_card_le_three
          p a hmultiplier)
    _ = 6 := rfl

end FiniteLoci

end

end GenMarkoff.General.Assembly
