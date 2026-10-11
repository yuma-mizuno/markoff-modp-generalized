module

public import GenMarkoff.General.Cage.FirstAxisTorusVieta
public import GenMarkoff.General.Trace.Surface

@[expose] public section

/-!
# Square classes on a connecting fiber

On a first-coordinate fiber with fixed coordinate `u` and nonparabolic trace
`t`, the centered fiber product is
`centeredFiberProduct B C u t = u^2 * centeredNorm B C t / discriminant t^2`.
This file records that multiplying by a nonzero square does not change square
class, and deduces that for `u ≠ 0` the centered fiber product and the
centered norm `centeredNorm B C t` are squares simultaneously.  The
connecting-fiber arguments, for example in
`GenMarkoff.General.Cage.Connecting.Fiber`, use this to state their nonsquare
hypothesis on the centered norm, which depends only on the trace.
-/

namespace GenMarkoff.General.Cage

universe u

noncomputable section

/-- Multiplication by a nonzero square does not change square class. -/
theorem isSquare_sq_mul_iff
    {K : Type u} [Field K] (c x : K) (hc : c ≠ 0) :
    IsSquare (c ^ 2 * x) ↔ IsSquare x := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r / c, ?_⟩
    calc
      x = (c ^ 2 * x) / c ^ 2 := by field_simp [hc]
      _ = (r * r) / c ^ 2 := by rw [hr]
      _ = (r / c) * (r / c) := by field_simp [hc]
  · intro hx
    exact (IsSquare.sq c).mul hx

/-- The centered fiber product and the centered norm have the same square
class whenever the fixed coordinate `u` and the discriminant `t^2 - 4` are
nonzero. -/
theorem centeredFiberProduct_isSquare_iff_centeredNorm
    {K : Type u} [Field K] (B C u t : K)
    (hu : u ≠ 0) (hD : discriminant t ≠ 0) :
    IsSquare (centeredFiberProduct B C u t) ↔
      IsSquare (centeredNorm B C t) := by
  have hrewrite :
      centeredFiberProduct B C u t =
        (u / discriminant t) ^ 2 * centeredNorm B C t := by
    simp only [centeredFiberProduct]
    field_simp [hD]
  rw [hrewrite]
  exact isSquare_sq_mul_iff
    (u / discriminant t) (centeredNorm B C t)
      (div_ne_zero hu hD)

end

end GenMarkoff.General.Cage
