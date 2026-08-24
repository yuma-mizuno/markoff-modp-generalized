import GenMarkoff.Symmetric.Parabolic

/-!
# Cyclic transport of symmetric parabolic fibers

In the equal-coefficient family, cyclic coordinate permutations preserve the
surface and conjugate the second and third rotations to the first rotation.
This transports the exact prime-length parabolic-cycle calculation without
repeating the affine iterate algebra from `GenMarkoff.Symmetric.Parabolic`.
-/

namespace GenMarkoff.Symmetric

universe u

/-- Cyclically move the second coordinate to the first position. -/
def cycleLeftEquiv {R : Type u} : Point R ≃ Point R where
  toFun x := ⟨x.x2, x.x3, x.x1⟩
  invFun x := ⟨x.x3, x.x1, x.x2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- Cyclically move the third coordinate to the first position. -/
def cycleRightEquiv {R : Type u} : Point R ≃ Point R :=
  cycleLeftEquiv.symm

@[simp]
theorem cycleLeftEquiv_apply {R : Type u} (x : Point R) :
    cycleLeftEquiv x = ⟨x.x2, x.x3, x.x1⟩ :=
  rfl

@[simp]
theorem cycleRightEquiv_apply {R : Type u} (x : Point R) :
    cycleRightEquiv x = ⟨x.x3, x.x1, x.x2⟩ :=
  rfl

theorem polynomial_cycleLeftEquiv {R : Type u} [CommRing R]
    (c : R) (x : Point R) :
    polynomial (coefficients c) (cycleLeftEquiv x) =
      polynomial (coefficients c) x := by
  simp [polynomial, coefficients, Coefficients.multiplier]
  ring

theorem polynomial_cycleRightEquiv {R : Type u} [CommRing R]
    (c : R) (x : Point R) :
    polynomial (coefficients c) (cycleRightEquiv x) =
      polynomial (coefficients c) x := by
  rw [cycleRightEquiv_apply]
  simp [polynomial, coefficients, Coefficients.multiplier]
  ring

@[simp]
theorem isSolution_cycleLeftEquiv {R : Type u} [CommRing R]
    (c : R) (x : Point R) :
    IsSolution (coefficients c) (cycleLeftEquiv x) ↔
      IsSolution (coefficients c) x := by
  simp only [IsSolution, polynomial_cycleLeftEquiv]

@[simp]
theorem isSolution_cycleRightEquiv {R : Type u} [CommRing R]
    (c : R) (x : Point R) :
    IsSolution (coefficients c) (cycleRightEquiv x) ↔
      IsSolution (coefficients c) x := by
  simp only [IsSolution, polynomial_cycleRightEquiv]

/-- Cyclic coordinate transport conjugates `R₂` to `R₁`. -/
theorem cycleLeftEquiv_rotation2 {R : Type u} [CommRing R]
    (c : R) (x : Point R) :
    cycleLeftEquiv (rotation2 (coefficients c) x) =
      rotation1 (coefficients c) (cycleLeftEquiv x) := by
  ext <;>
    simp [cycleLeftEquiv, rotation1, rotation2, vieta1, vieta2, vieta3,
      coefficients, Coefficients.multiplier]

/-- Cyclic coordinate transport conjugates `R₃` to `R₁`. -/
theorem cycleRightEquiv_rotation3 {R : Type u} [CommRing R]
    (c : R) (x : Point R) :
    cycleRightEquiv (rotation3 (coefficients c) x) =
      rotation1 (coefficients c) (cycleRightEquiv x) := by
  ext <;>
    simp [cycleRightEquiv, cycleLeftEquiv, rotation1, rotation3,
      vieta1, vieta2, vieta3, coefficients, Coefficients.multiplier]

theorem cycleLeftEquiv_iterate_rotation2 {R : Type u} [CommRing R]
    (n : ℕ) (c : R) (x : Point R) :
    cycleLeftEquiv (((rotation2 (coefficients c))^[n]) x) =
      ((rotation1 (coefficients c))^[n]) (cycleLeftEquiv x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        cycleLeftEquiv_rotation2, ih]

theorem cycleRightEquiv_iterate_rotation3 {R : Type u} [CommRing R]
    (n : ℕ) (c : R) (x : Point R) :
    cycleRightEquiv (((rotation3 (coefficients c))^[n]) x) =
      ((rotation1 (coefficients c))^[n]) (cycleRightEquiv x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        cycleRightEquiv_rotation3, ih]

section Cycles

variable (p : ℕ)

/-- The second-rotation parabolic cycle over the canonical range
`0, ..., p - 1`. -/
def rotation2ParabolicCycle (c : ZMod p) (x : Point (ZMod p)) :
    Finset (Point (ZMod p)) :=
  (Finset.range p).image fun n ↦
    ((rotation2 (coefficients c))^[n]) x

/-- The third-rotation parabolic cycle over the canonical range
`0, ..., p - 1`. -/
def rotation3ParabolicCycle (c : ZMod p) (x : Point (ZMod p)) :
    Finset (Point (ZMod p)) :=
  (Finset.range p).image fun n ↦
    ((rotation3 (coefficients c))^[n]) x

theorem image_cycleLeftEquiv_rotation2ParabolicCycle
    (c : ZMod p) (x : Point (ZMod p)) :
    (rotation2ParabolicCycle p c x).image cycleLeftEquiv =
      rotation1ParabolicCycle p c (cycleLeftEquiv x) := by
  classical
  rw [rotation2ParabolicCycle, rotation1ParabolicCycle, Finset.image_image]
  apply Finset.image_congr
  intro n _hn
  exact cycleLeftEquiv_iterate_rotation2 n c x

theorem image_cycleRightEquiv_rotation3ParabolicCycle
    (c : ZMod p) (x : Point (ZMod p)) :
    (rotation3ParabolicCycle p c x).image cycleRightEquiv =
      rotation1ParabolicCycle p c (cycleRightEquiv x) := by
  classical
  rw [rotation3ParabolicCycle, rotation1ParabolicCycle, Finset.image_image]
  apply Finset.image_congr
  intro n _hn
  exact cycleRightEquiv_iterate_rotation3 n c x

variable [Fact p.Prime]

theorem rotation2ParabolicCycle_card_of_trace_eq_neg_two
    (hpTwo : p ≠ 2) (c : ZMod p) (x : Point (ZMod p))
    (hc : c ^ 2 ≠ 4) (htrace : trace c x.x2 = -2)
    (hsolution : IsSolution (coefficients c) x) :
    (rotation2ParabolicCycle p c x).card = p := by
  classical
  have hcardImage :
      ((rotation2ParabolicCycle p c x).image cycleLeftEquiv).card =
        (rotation2ParabolicCycle p c x).card := by
    apply Finset.card_image_iff.mpr
    intro a _ha b _hb hab
    exact cycleLeftEquiv.injective hab
  rw [← hcardImage, image_cycleLeftEquiv_rotation2ParabolicCycle]
  apply rotation1ParabolicCycle_card_of_trace_eq_neg_two p hpTwo c
    (cycleLeftEquiv x) hc
  · simpa using htrace
  · exact (isSolution_cycleLeftEquiv c x).2 hsolution

theorem rotation2ParabolicCycle_card_of_trace_eq_two
    (hpTwo : p ≠ 2) (c : ZMod p) (x : Point (ZMod p))
    (hc : c ^ 2 ≠ 4) (htrace : trace c x.x2 = 2)
    (hsolution : IsSolution (coefficients c) x) :
    (rotation2ParabolicCycle p c x).card = p := by
  classical
  have hcardImage :
      ((rotation2ParabolicCycle p c x).image cycleLeftEquiv).card =
        (rotation2ParabolicCycle p c x).card := by
    apply Finset.card_image_iff.mpr
    intro a _ha b _hb hab
    exact cycleLeftEquiv.injective hab
  rw [← hcardImage, image_cycleLeftEquiv_rotation2ParabolicCycle]
  apply rotation1ParabolicCycle_card_of_trace_eq_two p hpTwo c
    (cycleLeftEquiv x) hc
  · simpa using htrace
  · exact (isSolution_cycleLeftEquiv c x).2 hsolution

theorem rotation3ParabolicCycle_card_of_trace_eq_neg_two
    (hpTwo : p ≠ 2) (c : ZMod p) (x : Point (ZMod p))
    (hc : c ^ 2 ≠ 4) (htrace : trace c x.x3 = -2)
    (hsolution : IsSolution (coefficients c) x) :
    (rotation3ParabolicCycle p c x).card = p := by
  classical
  have hcardImage :
      ((rotation3ParabolicCycle p c x).image cycleRightEquiv).card =
        (rotation3ParabolicCycle p c x).card := by
    apply Finset.card_image_iff.mpr
    intro a _ha b _hb hab
    exact cycleRightEquiv.injective hab
  rw [← hcardImage, image_cycleRightEquiv_rotation3ParabolicCycle]
  apply rotation1ParabolicCycle_card_of_trace_eq_neg_two p hpTwo c
    (cycleRightEquiv x) hc
  · simpa using htrace
  · exact (isSolution_cycleRightEquiv c x).2 hsolution

theorem rotation3ParabolicCycle_card_of_trace_eq_two
    (hpTwo : p ≠ 2) (c : ZMod p) (x : Point (ZMod p))
    (hc : c ^ 2 ≠ 4) (htrace : trace c x.x3 = 2)
    (hsolution : IsSolution (coefficients c) x) :
    (rotation3ParabolicCycle p c x).card = p := by
  classical
  have hcardImage :
      ((rotation3ParabolicCycle p c x).image cycleRightEquiv).card =
        (rotation3ParabolicCycle p c x).card := by
    apply Finset.card_image_iff.mpr
    intro a _ha b _hb hab
    exact cycleRightEquiv.injective hab
  rw [← hcardImage, image_cycleRightEquiv_rotation3ParabolicCycle]
  apply rotation1ParabolicCycle_card_of_trace_eq_two p hpTwo c
    (cycleRightEquiv x) hc
  · simpa using htrace
  · exact (isSolution_cycleRightEquiv c x).2 hsolution

end Cycles

end GenMarkoff.Symmetric
