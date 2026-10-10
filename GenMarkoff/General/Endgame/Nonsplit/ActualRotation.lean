import GenMarkoff.General.Endgame.Nonsplit.RegularPrimitiveCount
import GenMarkoff.General.Endgame.ActualSplitRotation
import BGS.NumberTheory.ExplicitDivisorBound
import BGS.Markoff.Endgame.PrimitiveInclusionExclusion
import GenMarkoff.General.Arithmetic.ReasonableCutoff
import GenMarkoff.General.Assembly.RegularMiddleIteration
import GenMarkoff.General.MiddleGame.ActualOrderGrowth
import GenMarkoff.General.MiddleGame.DirectedOrderGrowth
import BGS.Markoff.Endgame.PrimitiveOrbitWiring

/-!
# Fixed-coefficient descended nonsplit actual-rotation endgame

Nonsplit analogue of `GenMarkoff.General.Endgame.ActualSplitRotation`.  Here the
trace `t` on the fixed axis is `quadraticNormOneTrace p w` for a norm-one
eigenvalue `w` in `quadraticFiniteField p`.  A base-field point on the fiber is
diagonalized over the quadratic extension in its ordered moving coordinates.
Frobenius fixes both coordinates of the ordered affine center and sends the
eigen-parameter to the reciprocal parameter (`actualFiberParameter_frobenius`),
so the initial parameter, scaled by the leading weight, is a seed in the norm
fiber of `actualSigma`.  Along the forward rotation orbit, the adjacent trace is
then the descended nonsplit shifted trace of this seed, and the descended
primitive count of `GenMarkoff.General.Endgame.Nonsplit.RegularPrimitiveCount`
gives an iterate whose adjacent trace is primitive on the split torus and
candidate regular in a prescribed target frame.

* First to second: `rotation1` acts on `fiberPoint1` with moving coordinates
  `(x₂, x₃)`; the seed is `actualAlpha s * h` and the shift is
  `actualGammaFirst`.  The current frame is `(a.a1, a.a2, a.a3)` and the
  target frame is `(a.a2, targetB, targetC)`.
* Second to first: `rotation2` acts on `fiberPoint2` with moving coordinates
  `(x₃, x₁)`; the output `x₁` is the second moving coordinate, so the seed is
  `s * w * h` and the shift is `actualGammaSecond`.  The current frame is
  `(a.a2, a.a1, a.a3)` and the target frame is `(a.a1, targetB, targetC)`.

Each rotation multiplies the eigen-parameter by `w ^ 2`, so reachability,
complementary exponents and order hypotheses are stated with `w ^ 2`.  The
reasonable-cutoff versions assume `p ^ (1/2 + delta) ≤ orderOf (w ^ 2)` with
`delta ≥ 1/4`.  The coefficient triple remains fixed throughout; no
coordinate permutation is used.
-/

namespace GenMarkoff.General.Endgame.Nonsplit

open BGS.Markoff
open GenMarkoff.General.Assembly
open GenMarkoff.General.MiddleGame
open GenMarkoff.ShiftedTrace.Endgame.Nonsplit

noncomputable section

/-- Package the nonzero ordered actual weight product as a base-field
unit. -/
def actualSigmaUnit {K : Type*} [Field K]
    (s B C u t : K) (h : actualSigma s B C u t ≠ 0) : Kˣ :=
  Units.mk0 (actualSigma s B C u t) h

@[simp]
theorem actualSigmaUnit_val {K : Type*} [Field K]
    (s B C u t : K) (h : actualSigma s B C u t ≠ 0) :
    (actualSigmaUnit s B C u t h : K) =
      actualSigma s B C u t :=
  rfl

/-- `centeredFiberProduct` commutes with field homomorphisms. -/
theorem map_centeredFiberProduct
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (B C u t : K) :
    f (centeredFiberProduct B C u t) =
      centeredFiberProduct (f B) (f C) (f u) (f t) := by
  simp [centeredFiberProduct, centeredNorm, discriminant, map_sub,
    map_add, map_mul, map_pow, map_div₀, map_ofNat]

/-- `actualAlpha` commutes with field homomorphisms. -/
theorem map_actualAlpha
    {K L : Type*} [Field K] [Field L] (f : K →+* L) (s : K) :
    f (actualAlpha s) = actualAlpha (f s) := by
  simp [actualAlpha]

/-- `actualBeta` commutes with field homomorphisms. -/
theorem map_actualBeta
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (s B C u t : K) :
    f (actualBeta s B C u t) =
      actualBeta (f s) (f B) (f C) (f u) (f t) := by
  simp [actualBeta, map_centeredFiberProduct]

/-- `actualSigma` commutes with field homomorphisms. -/
theorem map_actualSigma
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (s B C u t : K) :
    f (actualSigma s B C u t) =
      actualSigma (f s) (f B) (f C) (f u) (f t) := by
  rw [actualSigma, actualSigma, map_mul, map_actualAlpha,
    map_actualBeta]

/-- `actualGammaFirst` commutes with field homomorphisms. -/
theorem map_actualGammaFirst
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (s B C u t : K) :
    f (actualGammaFirst s B C u t) =
      actualGammaFirst (f s) (f B) (f C) (f u) (f t) := by
  simp [actualGammaFirst, fiberCenter, discriminant, map_sub,
    map_add, map_mul, map_pow, map_div₀, map_ofNat]

/-- `actualGammaSecond` commutes with field homomorphisms. -/
theorem map_actualGammaSecond
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (s B C u t : K) :
    f (actualGammaSecond s B C u t) =
      actualGammaSecond (f s) (f B) (f C) (f u) (f t) := by
  simp [actualGammaSecond, fiberCenter, discriminant, map_sub,
    map_add, map_mul, map_pow, map_div₀, map_ofNat]

/-- Frobenius exchanges the two ordered actual eigen-parameters of a
base-field moving-coordinate pair. -/
theorem actualFiberParameter_frobenius
    (p : ℕ) [Fact p.Prime]
    (B C u t : ZMod p) (w : quadraticNormOneTorus p)
    (v : ZMod p × ZMod p) :
    (actualFiberParameter
        (algebraMap (ZMod p) (quadraticFiniteField p) B)
        (algebraMap (ZMod p) (quadraticFiniteField p) C)
        (algebraMap (ZMod p) (quadraticFiniteField p) u)
        (algebraMap (ZMod p) (quadraticFiniteField p) t)
        (w : (quadraticFiniteField p)ˣ)
        (algebraMap (ZMod p) (quadraticFiniteField p) v.1,
          algebraMap (ZMod p) (quadraticFiniteField p) v.2)) ^ p =
      actualFiberReciprocalParameter
        (algebraMap (ZMod p) (quadraticFiniteField p) B)
        (algebraMap (ZMod p) (quadraticFiniteField p) C)
        (algebraMap (ZMod p) (quadraticFiniteField p) u)
        (algebraMap (ZMod p) (quadraticFiniteField p) t)
        (w : (quadraticFiniteField p)ˣ)
        (algebraMap (ZMod p) (quadraticFiniteField p) v.1,
          algebraMap (ZMod p) (quadraticFiniteField p) v.2) := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  -- Frobenius swaps `w` and `w⁻¹` and fixes base-field values, e.g. both center coordinates.
  have hwFrobenius :
      (((w : Eˣ) : E) ^ p) =
        ((((w : Eˣ)⁻¹ : Eˣ) : E)) :=
    quadraticNormOne_frobenius_eq_inv p w
  have hwInvFrobenius :
      ((((w : Eˣ)⁻¹ : Eˣ) : E) ^ p) =
        ((w : Eˣ) : E) := by
    have hscalar :
        ((((w : Eˣ) : E)⁻¹) ^ p) =
          ((w : Eˣ) : E) := by
      rw [inv_pow, hwFrobenius]
      simpa only [Units.val_inv_eq_inv_val] using
        inv_inv (((w : Eˣ) : E))
    simpa only [Units.val_inv_eq_inv_val] using hscalar
  have hbase (z : ZMod p) : (f z) ^ p = f z := by
    simpa [f, E] using algebraMap_zmod_pow_card p z
  have hcenterFirst :
      ((fiberCenter (f B) (f C) (f u) (f t)).1) ^ p =
        (fiberCenter (f B) (f C) (f u) (f t)).1 := by
    calc
      ((fiberCenter (f B) (f C) (f u) (f t)).1) ^ p =
          (f (u * (t * B + 2 * C) / discriminant t)) ^ p := by
        congr 1
        simp [fiberCenter, discriminant, map_ofNat]
      _ = f (u * (t * B + 2 * C) / discriminant t) :=
        hbase (u * (t * B + 2 * C) / discriminant t)
      _ = (fiberCenter (f B) (f C) (f u) (f t)).1 := by
        simp [fiberCenter, discriminant, map_ofNat]
  have hcenterSecond :
      ((fiberCenter (f B) (f C) (f u) (f t)).2) ^ p =
        (fiberCenter (f B) (f C) (f u) (f t)).2 := by
    calc
      ((fiberCenter (f B) (f C) (f u) (f t)).2) ^ p =
          (f (u * (t * C + 2 * B) / discriminant t)) ^ p := by
        congr 1
        simp [fiberCenter, discriminant, map_ofNat]
      _ = f (u * (t * C + 2 * B) / discriminant t) :=
        hbase (u * (t * C + 2 * B) / discriminant t)
      _ = (fiberCenter (f B) (f C) (f u) (f t)).2 := by
        simp [fiberCenter, discriminant, map_ofNat]
  -- Expand the `p`-th power of the quotient with these rules; the denominator changes sign.
  simp only [actualFiberParameter, actualFiberReciprocalParameter]
  rw [div_pow, sub_pow_char, sub_pow_char, mul_pow, sub_pow_char,
    sub_pow_char, hbase v.2, hcenterSecond, hbase v.1,
    hcenterFirst, hwInvFrobenius, hwFrobenius]
  have hden :
      ((((w : Eˣ)⁻¹ : Eˣ) : E) - ((w : Eˣ) : E)) =
        -(((w : Eˣ) : E) - (((w : Eˣ)⁻¹ : Eˣ) : E)) := by
    ring
  rw [hden, div_neg]
  ring

/-- Let `S = actualAlpha s * h` lie in the norm fiber of `actualSigma`.  For
every norm-one `g`, the descended trace `Tr (S * g) + actualGammaFirst` equals,
over `quadraticFiniteField p`, the trace of the first moving coordinate of
`fiberPair` at the parameter `h * g`. -/
theorem algebraMap_shiftedActualSeedTrace_eq_firstTrace_fiberPair
    (p : ℕ) [Fact p.Prime]
    (s B C u t : ZMod p)
    (hsigma : actualSigma s B C u t ≠ 0)
    (halpha : actualAlpha s ≠ 0)
    (h : (quadraticFiniteField p)ˣ)
    (S : ↥(quadraticNormFiber p
      (actualSigmaUnit s B C u t hsigma)))
    (hS :
      (S.1 : quadraticFiniteField p) =
        algebraMap (ZMod p) (quadraticFiniteField p) (actualAlpha s) *
          (h : quadraticFiniteField p))
    (q g : quadraticNormOneTorus p) :
    algebraMap (ZMod p) (quadraticFiniteField p)
        (Algebra.trace (ZMod p) (quadraticFiniteField p)
            ((S.1 : quadraticFiniteField p) *
              ((g : (quadraticFiniteField p)ˣ) :
                quadraticFiniteField p)) +
          actualGammaFirst s B C u t) =
      orderedTrace
        (algebraMap (ZMod p) (quadraticFiniteField p) s)
        (algebraMap (ZMod p) (quadraticFiniteField p) B)
        (fiberPair
          (algebraMap (ZMod p) (quadraticFiniteField p) B)
          (algebraMap (ZMod p) (quadraticFiniteField p) C)
          (algebraMap (ZMod p) (quadraticFiniteField p) u)
          (algebraMap (ZMod p) (quadraticFiniteField p) t)
          (((q : (quadraticFiniteField p)ˣ) :
            quadraticFiniteField p))
          (((h * (g : (quadraticFiniteField p)ˣ) :
            (quadraticFiniteField p)ˣ)) :
              quadraticFiniteField p)).1 := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  have hSFrobenius :=
    quadraticNormFiber_frobenius_eq_norm_mul_inv p
      (actualSigmaUnit s B C u t hsigma) S
  have hgFrobenius := quadraticNormOne_frobenius_eq_inv p g
  have hmapAlpha : f (actualAlpha s) = actualAlpha (f s) :=
    map_actualAlpha f s
  have hmapSigma : f (actualSigma s B C u t) =
      actualSigma (f s) (f B) (f C) (f u) (f t) :=
    map_actualSigma f s B C u t
  have hmapGamma : f (actualGammaFirst s B C u t) =
      actualGammaFirst (f s) (f B) (f C) (f u) (f t) :=
    map_actualGammaFirst f s B C u t
  have hAlphaE : f (actualAlpha s) ≠ 0 :=
    (map_ne_zero_iff f f.injective).mpr halpha
  have hAlphaTarget : actualAlpha (f s) ≠ 0 := by
    rw [← hmapAlpha]
    exact hAlphaE
  have hH : (h : E) ≠ 0 := Units.ne_zero h
  have hg : (((g : Eˣ) : E)) ≠ 0 := Units.ne_zero _
  rw [map_add, algebraMap_quadraticTrace, mul_pow, hSFrobenius,
    hgFrobenius]
  simp only [actualSigmaUnit_val, Units.val_mul]
  -- Unfold `orderedTrace`, write `algebraMap` as `f`, keep `↑(h * g)`; for `firstTrace_fiberPair`.
  change
    (S.1 : E) * ((g : Eˣ) : E) +
          (f (actualSigma s B C u t) *
              ((S.1 : E)⁻¹)) *
            ((((g : Eˣ)⁻¹ : Eˣ) : E)) +
        f (actualGammaFirst s B C u t) =
      f s *
          (fiberPair (f B) (f C) (f u) (f t)
            ((q : Eˣ) : E)
            (((h * (g : Eˣ) : Eˣ)) : E)).1 -
        f B
  rw [firstTrace_fiberPair
    (f s) (f B) (f C) (f u) (f t)
      ((q : Eˣ) : E) (((h * (g : Eˣ) : Eˣ)) : E)
      (Units.ne_zero (h * (g : Eˣ)))]
  rw [hS, hmapAlpha, hmapSigma, hmapGamma]
  dsimp [f, E] at hAlphaE hAlphaTarget ⊢
  simp only [Units.val_inv_eq_inv_val]
  simp only [actualSigma]
  field_simp [hAlphaE, hAlphaTarget, hH, hg]

/-- Let `S = s * q * h` lie in the norm fiber of `actualSigma`.  For every
norm-one `g`, the descended trace `Tr (S * g) + actualGammaSecond` equals, over
`quadraticFiniteField p`, the trace of the second moving coordinate of
`fiberPair` at the parameter `h * g`.  The factor `q` appears because the
second moving coordinate of `torusPair q P h` is `q * h + P / (q * h)`. -/
theorem algebraMap_shiftedActualSecondSeedTrace_eq_secondTrace_fiberPair
    (p : ℕ) [Fact p.Prime]
    (s B C u t : ZMod p)
    (hsigma : actualSigma s B C u t ≠ 0)
    (hs : s ≠ 0)
    (q : quadraticNormOneTorus p)
    (h : (quadraticFiniteField p)ˣ)
    (S : ↥(quadraticNormFiber p
      (actualSigmaUnit s B C u t hsigma)))
    (hS :
      (S.1 : quadraticFiniteField p) =
        algebraMap (ZMod p) (quadraticFiniteField p) s *
          (((q : quadraticNormOneTorus p) :
              (quadraticFiniteField p)ˣ) :
            quadraticFiniteField p) *
          (h : quadraticFiniteField p))
    (g : quadraticNormOneTorus p) :
    algebraMap (ZMod p) (quadraticFiniteField p)
        (Algebra.trace (ZMod p) (quadraticFiniteField p)
            ((S.1 : quadraticFiniteField p) *
              ((g : (quadraticFiniteField p)ˣ) :
                quadraticFiniteField p)) +
          actualGammaSecond s B C u t) =
      orderedTrace
        (algebraMap (ZMod p) (quadraticFiniteField p) s)
        (algebraMap (ZMod p) (quadraticFiniteField p) C)
        (fiberPair
          (algebraMap (ZMod p) (quadraticFiniteField p) B)
          (algebraMap (ZMod p) (quadraticFiniteField p) C)
          (algebraMap (ZMod p) (quadraticFiniteField p) u)
          (algebraMap (ZMod p) (quadraticFiniteField p) t)
          (((q : (quadraticFiniteField p)ˣ) :
            quadraticFiniteField p))
          (((h * (g : (quadraticFiniteField p)ˣ) :
            (quadraticFiniteField p)ˣ)) :
              quadraticFiniteField p)).2 := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  have hSFrobenius :=
    quadraticNormFiber_frobenius_eq_norm_mul_inv p
      (actualSigmaUnit s B C u t hsigma) S
  have hgFrobenius := quadraticNormOne_frobenius_eq_inv p g
  have hmapSigma : f (actualSigma s B C u t) =
      actualSigma (f s) (f B) (f C) (f u) (f t) :=
    map_actualSigma f s B C u t
  have hmapGamma : f (actualGammaSecond s B C u t) =
      actualGammaSecond (f s) (f B) (f C) (f u) (f t) :=
    map_actualGammaSecond f s B C u t
  have hsE : f s ≠ 0 :=
    (map_ne_zero_iff f f.injective).mpr hs
  have hq : ((((q : quadraticNormOneTorus p) : Eˣ) : E)) ≠ 0 :=
    Units.ne_zero _
  have hH : (h : E) ≠ 0 := Units.ne_zero h
  have hg : (((g : Eˣ) : E)) ≠ 0 := Units.ne_zero _
  rw [map_add, algebraMap_quadraticTrace, mul_pow, hSFrobenius,
    hgFrobenius]
  simp only [actualSigmaUnit_val, Units.val_mul]
  -- Unfold `orderedTrace`, write `algebraMap` as `f`, keep `↑(h * g)`; for `secondTrace_fiberPair`.
  change
    (S.1 : E) * ((g : Eˣ) : E) +
          (f (actualSigma s B C u t) *
              ((S.1 : E)⁻¹)) *
            ((((g : Eˣ)⁻¹ : Eˣ) : E)) +
        f (actualGammaSecond s B C u t) =
      f s *
          (fiberPair (f B) (f C) (f u) (f t)
            (((q : quadraticNormOneTorus p) : Eˣ) : E)
            (((h * (g : Eˣ) : Eˣ)) : E)).2 -
        f C
  rw [secondTrace_fiberPair
    (f s) (f B) (f C) (f u) (f t)
      (((q : quadraticNormOneTorus p) : Eˣ) : E)
      (((h * (g : Eˣ) : Eˣ)) : E)
      hq (Units.ne_zero (h * (g : Eˣ)))]
  rw [hS, hmapSigma, hmapGamma]
  dsimp [f, E] at hsE hq ⊢
  simp only [Units.val_inv_eq_inv_val]
  simp only [actualSigma, actualAlpha, actualBeta]
  field_simp [hsE, hq, hH, hg]

/-- A candidate-regular base-field point on the ordered first-coordinate
nonsplit fiber supplies the actual seed: over `quadraticFiniteField p` the
point is `fiberPoint1` at some unit parameter `h`, and
`actualAlpha a.multiplier * h` lies in the norm fiber of
`actualSigma a.multiplier a.a2 a.a3 u t`. -/
theorem exists_actualShiftedNonsplitSeed
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (hx : IsSolution a x) (hx1 : x.x1 = u)
    (htrace : t = orderedTrace a.multiplier a.a1 u)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t)
    (w : quadraticNormOneTorus p)
    (htraceW : quadraticNormOneTrace p w = t) :
    ∃ h : (quadraticFiniteField p)ˣ,
      ∃ S : ↥(quadraticNormFiber p
        (actualSigmaUnit a.multiplier a.a2 a.a3 u t
          (actualSigma_ne_zero_of_candidateRegular
            a.multiplier a.a1 a.a2 a.a3 u t htrace hregular))),
        Point.map
            (algebraMap (ZMod p) (quadraticFiniteField p)) x =
          fiberPoint1
            (Coefficients.map
              (algebraMap (ZMod p) (quadraticFiniteField p)) a)
            (algebraMap (ZMod p) (quadraticFiniteField p) u)
            (algebraMap (ZMod p) (quadraticFiniteField p) t)
            ((w : (quadraticFiniteField p)ˣ) :
              quadraticFiniteField p)
            (h : quadraticFiniteField p) ∧
        (S.1 : quadraticFiniteField p) =
          algebraMap (ZMod p) (quadraticFiniteField p)
              (actualAlpha a.multiplier) *
            (h : quadraticFiniteField p) := by
  -- Transport the fiber data to the quadratic extension `E`.
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := Coefficients.map f a
  let uE : E := f u
  let tE : E := f t
  let xE : Point E := Point.map f x
  let q : Eˣ := (w : Eˣ)
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a1 uE := by
    have hmap := congrArg f htrace
    simpa [tE, aE, uE, orderedTrace, Coefficients.map,
      Coefficients.multiplier, map_ofNat] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a1 aE.a2 aE.a3 tE := by
    simpa [aE, tE] using
      orderedTraceCandidateRegular_map f f.injective hregular
  have hDE : discriminant tE ≠ 0 := by
    simpa [tE, discriminant, map_ofNat] using
      (map_ne_zero_iff f f.injective).mpr hregular.1
  have hproductBase :
      centeredFiberProduct a.a2 a.a3 u t ≠ 0 :=
    centeredFiberProduct_ne_zero_of_candidateRegular
      a.multiplier a.a1 a.a2 a.a3 u t htrace hregular
  have hproductE :
      centeredFiberProduct aE.a2 aE.a3 uE tE ≠ 0 := by
    have hmap :
        f (centeredFiberProduct a.a2 a.a3 u t) ≠ 0 :=
      (map_ne_zero_iff f f.injective).mpr hproductBase
    rw [map_centeredFiberProduct] at hmap
    simpa [aE, uE, tE] using hmap
  have hconic :
      fiberConic a.a2 a.a3 u t x.x2 x.x3 = 0 := by
    rw [htrace]
    rw [← polynomial_fixed_first a u x.x2 x.x3]
    rw [← hx1]
    exact hx
  have hconicE :
      fiberConic aE.a2 aE.a3 uE tE xE.x2 xE.x3 = 0 := by
    have hmap := congrArg f hconic
    simpa [aE, uE, tE, xE, Point.map, Coefficients.map, fiberConic,
      map_ofNat] using hmap
  have heigen : tE = splitTorusTrace q := by
    dsimp [tE, q, f]
    rw [← htraceW]
    exact algebraMap_quadraticNormOneTrace p w
  -- Diagonalize: over `E` the point is `fiberPoint1` at the eigen-parameter `h`.
  let parameter : E :=
    actualFiberParameter aE.a2 aE.a3 uE tE q (xE.x2, xE.x3)
  have hparameter : parameter ≠ 0 := by
    exact actualFiberParameter_ne_zero
      aE.a2 aE.a3 uE tE q (xE.x2, xE.x3)
        hconicE heigen hDE hproductE
  let h : Eˣ := Units.mk0 parameter hparameter
  have hpair :
      fiberPair aE.a2 aE.a3 uE tE (q : E) (h : E) =
        (xE.x2, xE.x3) := by
    simpa [h, parameter] using
      fiberPair_actualFiberParameter_eq
        aE.a2 aE.a3 uE tE q (xE.x2, xE.x3)
          hconicE heigen hDE hproductE
  have hpoint :
      xE = fiberPoint1 aE uE tE (q : E) (h : E) := by
    apply Point.ext
    · simpa [xE, uE, Point.map] using congrArg f hx1
    · simpa [fiberPoint1] using congrArg Prod.fst hpair.symm
    · simpa [fiberPoint1] using congrArg Prod.snd hpair.symm
  -- The seed `actualAlpha s * h` has norm `actualSigma`, since Frobenius sends `h` to its
  -- reciprocal parameter.
  have hsigma :
      actualSigma a.multiplier a.a2 a.a3 u t ≠ 0 :=
    actualSigma_ne_zero_of_candidateRegular
      a.multiplier a.a1 a.a2 a.a3 u t htrace hregular
  have hAlphaBase : actualAlpha a.multiplier ≠ 0 := by
    have hproduct :
        actualAlpha a.multiplier *
            actualBeta a.multiplier a.a2 a.a3 u t ≠ 0 := by
      simpa [actualSigma] using hsigma
    exact (mul_ne_zero_iff.mp hproduct).1
  let seedValue : E :=
    f (actualAlpha a.multiplier) * (h : E)
  have hseedValue : seedValue ≠ 0 :=
    mul_ne_zero ((map_ne_zero_iff f f.injective).mpr hAlphaBase)
      (Units.ne_zero h)
  let seedUnit : Eˣ := Units.mk0 seedValue hseedValue
  have hparameterFrobenius :
      (parameter : E) ^ p =
        actualFiberReciprocalParameter
          aE.a2 aE.a3 uE tE q (xE.x2, xE.x3) := by
    simpa [parameter, aE, uE, tE, q, xE, Point.map, f, E] using
      actualFiberParameter_frobenius
        p a.a2 a.a3 u t w (x.x2, x.x3)
  have hparameterProduct :
      parameter *
          actualFiberReciprocalParameter
            aE.a2 aE.a3 uE tE q (xE.x2, xE.x3) =
        centeredFiberProduct aE.a2 aE.a3 uE tE :=
    actualFiberParameter_mul_reciprocal_eq_centeredFiberProduct
      aE.a2 aE.a3 uE tE q (xE.x2, xE.x3)
        hconicE heigen hDE
  have hseedNorm :
      Algebra.norm (ZMod p) (seedValue : E) =
        actualSigma a.multiplier a.a2 a.a3 u t := by
    apply f.injective
    rw [algebraMap_quadraticNorm]
    have hAlphaFrobenius :
        (f (actualAlpha a.multiplier)) ^ p =
          f (actualAlpha a.multiplier) := by
      simpa [f, E] using
        algebraMap_zmod_pow_card p (actualAlpha a.multiplier)
    -- Unfold `seedValue = f (actualAlpha _) * ↑h` and `↑h = parameter` so that the `rw` applies.
    change
      (f (actualAlpha a.multiplier) * parameter) *
          (f (actualAlpha a.multiplier) * parameter) ^ p =
        f (actualSigma a.multiplier a.a2 a.a3 u t)
    rw [mul_pow, hAlphaFrobenius, hparameterFrobenius]
    calc
      f (actualAlpha a.multiplier) * parameter *
            (f (actualAlpha a.multiplier) *
              actualFiberReciprocalParameter
                aE.a2 aE.a3 uE tE q (xE.x2, xE.x3)) =
          f (actualAlpha a.multiplier) *
            f (actualAlpha a.multiplier) *
              (parameter *
                actualFiberReciprocalParameter
                  aE.a2 aE.a3 uE tE q (xE.x2, xE.x3)) := by
        ring
      _ = f (actualAlpha a.multiplier) *
            f (actualAlpha a.multiplier) *
              centeredFiberProduct aE.a2 aE.a3 uE tE := by
        rw [hparameterProduct]
      _ = f (actualSigma a.multiplier a.a2 a.a3 u t) := by
        rw [map_actualSigma]
        simp [actualSigma, actualAlpha, actualBeta, aE, uE, tE]
        ring
  -- Package the seed as an element of the norm fiber.
  let sigmaUnit : (ZMod p)ˣ :=
    actualSigmaUnit a.multiplier a.a2 a.a3 u t hsigma
  have hseedMem : seedUnit ∈ quadraticNormFiber p sigmaUnit := by
    -- `quadraticNormFiber` is a preimage of `{sigmaUnit}`; unfold for `Set.mem_singleton_iff`.
    change
      quadraticNormUnitsHom p seedUnit ∈
        ({sigmaUnit} : Set (ZMod p)ˣ)
    rw [Set.mem_singleton_iff]
    apply Units.ext
    exact hseedNorm
  let S : ↥(quadraticNormFiber p sigmaUnit) :=
    ⟨seedUnit, hseedMem⟩
  refine ⟨h, S, ?_, ?_⟩
  · simpa [aE, uE, tE, q, xE, f, E] using hpoint
  · rfl

/-- A candidate-regular base-field point on the ordered second-coordinate
nonsplit fiber supplies the reverse actual seed: over `quadraticFiniteField p`
the point is `fiberPoint2` at some unit parameter `h`, with moving coordinates
`(x₃, x₁)`, and `a.multiplier * w * h` lies in the norm fiber of
`actualSigma a.multiplier a.a3 a.a1 u t`. -/
theorem exists_actualShiftedNonsplitSecondSeed
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (hx : IsSolution a x) (hx2 : x.x2 = u)
    (htrace : t = orderedTrace a.multiplier a.a2 u)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t)
    (w : quadraticNormOneTorus p)
    (htraceW : quadraticNormOneTrace p w = t) :
    ∃ h : (quadraticFiniteField p)ˣ,
      ∃ S : ↥(quadraticNormFiber p
        (actualSigmaUnit a.multiplier a.a3 a.a1 u t
          (actualSigma_ne_zero_of_reverseCandidateRegular
            a.multiplier a.a2 a.a3 a.a1 u t htrace hregular))),
        Point.map
            (algebraMap (ZMod p) (quadraticFiniteField p)) x =
          fiberPoint2
            (Coefficients.map
              (algebraMap (ZMod p) (quadraticFiniteField p)) a)
            (algebraMap (ZMod p) (quadraticFiniteField p) u)
            (algebraMap (ZMod p) (quadraticFiniteField p) t)
            ((w : (quadraticFiniteField p)ˣ) :
              quadraticFiniteField p)
            (h : quadraticFiniteField p) ∧
        (S.1 : quadraticFiniteField p) =
          algebraMap (ZMod p) (quadraticFiniteField p)
              a.multiplier *
            (((w : quadraticNormOneTorus p) :
                (quadraticFiniteField p)ˣ) :
              quadraticFiniteField p) *
            (h : quadraticFiniteField p) := by
  -- Transport the fiber data to the quadratic extension `E`.
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := Coefficients.map f a
  let uE : E := f u
  let tE : E := f t
  let xE : Point E := Point.map f x
  let q : Eˣ := (w : Eˣ)
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a2 uE := by
    have hmap := congrArg f htrace
    simpa [tE, aE, uE, orderedTrace, Coefficients.map,
      Coefficients.multiplier, map_ofNat] using hmap
  have hregularE :
      OrderedTraceCandidateRegular aE.a2 aE.a1 aE.a3 tE := by
    simpa [aE, tE] using
      orderedTraceCandidateRegular_map f f.injective hregular
  have hDE : discriminant tE ≠ 0 := by
    simpa [tE, discriminant, map_ofNat] using
      (map_ne_zero_iff f f.injective).mpr hregular.1
  have hsigma :
      actualSigma a.multiplier a.a3 a.a1 u t ≠ 0 :=
    actualSigma_ne_zero_of_reverseCandidateRegular
      a.multiplier a.a2 a.a3 a.a1 u t htrace hregular
  have hproductBase :
      centeredFiberProduct a.a3 a.a1 u t ≠ 0 := by
    intro hzero
    apply hsigma
    simp [actualSigma, actualBeta, hzero]
  have hproductE :
      centeredFiberProduct aE.a3 aE.a1 uE tE ≠ 0 := by
    have hmap :
        f (centeredFiberProduct a.a3 a.a1 u t) ≠ 0 :=
      (map_ne_zero_iff f f.injective).mpr hproductBase
    rw [map_centeredFiberProduct] at hmap
    simpa [aE, uE, tE] using hmap
  have hconic :
      fiberConic a.a3 a.a1 u t x.x3 x.x1 = 0 := by
    have hsurface := hx
    rw [IsSolution, polynomial_fixed_second, hx2, ← htrace] at hsurface
    exact hsurface
  have hconicE :
      fiberConic aE.a3 aE.a1 uE tE xE.x3 xE.x1 = 0 := by
    have hmap := congrArg f hconic
    simpa [aE, uE, tE, xE, Point.map, Coefficients.map, fiberConic,
      map_ofNat] using hmap
  have heigen : tE = splitTorusTrace q := by
    dsimp [tE, q, f]
    rw [← htraceW]
    exact algebraMap_quadraticNormOneTrace p w
  -- Diagonalize: over `E` the point is `fiberPoint2` at the eigen-parameter `h`.
  let parameter : E :=
    actualFiberParameter aE.a3 aE.a1 uE tE q (xE.x3, xE.x1)
  have hparameter : parameter ≠ 0 := by
    exact actualFiberParameter_ne_zero
      aE.a3 aE.a1 uE tE q (xE.x3, xE.x1)
        hconicE heigen hDE hproductE
  let h : Eˣ := Units.mk0 parameter hparameter
  have hpair :
      fiberPair aE.a3 aE.a1 uE tE (q : E) (h : E) =
        (xE.x3, xE.x1) := by
    simpa [h, parameter] using
      fiberPair_actualFiberParameter_eq
        aE.a3 aE.a1 uE tE q (xE.x3, xE.x1)
          hconicE heigen hDE hproductE
  have hpoint :
      xE = fiberPoint2 aE uE tE (q : E) (h : E) := by
    apply Point.ext
    · simpa [fiberPoint2] using congrArg Prod.snd hpair.symm
    · simpa [xE, uE, Point.map] using congrArg f hx2
    · simpa [fiberPoint2] using congrArg Prod.fst hpair.symm
  -- The seed `s * w * h` has norm `actualSigma`: Frobenius inverts `w` and sends `h` to its
  -- reciprocal parameter.
  have hs : a.multiplier ≠ 0 := by
    intro hzero
    apply hsigma
    simp [actualSigma, actualAlpha, hzero]
  let seedValue : E := f a.multiplier * (q : E) * (h : E)
  have hseedValue : seedValue ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero ((map_ne_zero_iff f f.injective).mpr hs)
        (Units.ne_zero q))
      (Units.ne_zero h)
  let seedUnit : Eˣ := Units.mk0 seedValue hseedValue
  have hparameterFrobenius :
      (parameter : E) ^ p =
        actualFiberReciprocalParameter
          aE.a3 aE.a1 uE tE q (xE.x3, xE.x1) := by
    simpa [parameter, aE, uE, tE, q, xE, Point.map, f, E] using
      actualFiberParameter_frobenius
        p a.a3 a.a1 u t w (x.x3, x.x1)
  have hparameterProduct :
      parameter *
          actualFiberReciprocalParameter
            aE.a3 aE.a1 uE tE q (xE.x3, xE.x1) =
        centeredFiberProduct aE.a3 aE.a1 uE tE :=
    actualFiberParameter_mul_reciprocal_eq_centeredFiberProduct
      aE.a3 aE.a1 uE tE q (xE.x3, xE.x1)
        hconicE heigen hDE
  have hseedNorm :
      Algebra.norm (ZMod p) (seedValue : E) =
        actualSigma a.multiplier a.a3 a.a1 u t := by
    apply f.injective
    rw [algebraMap_quadraticNorm]
    have hsFrobenius :
        (f a.multiplier) ^ p = f a.multiplier := by
      simpa [f, E] using
        algebraMap_zmod_pow_card p a.multiplier
    have hqFrobenius :
        ((q : E) ^ p) = (((q⁻¹ : Eˣ) : E)) := by
      simpa [q, E] using quadraticNormOne_frobenius_eq_inv p w
    -- Unfold `seedValue = f s * ↑q * ↑h` and `↑h = parameter` so that the `rw` applies.
    change
      (f a.multiplier * (q : E) * parameter) *
          (f a.multiplier * (q : E) * parameter) ^ p =
        f (actualSigma a.multiplier a.a3 a.a1 u t)
    rw [mul_pow, mul_pow, hsFrobenius, hqFrobenius,
      hparameterFrobenius]
    calc
      (f a.multiplier * (q : E) * parameter) *
            (f a.multiplier * ((q⁻¹ : Eˣ) : E) *
              actualFiberReciprocalParameter
                aE.a3 aE.a1 uE tE q (xE.x3, xE.x1)) =
          f a.multiplier * f a.multiplier *
            (parameter *
              actualFiberReciprocalParameter
                aE.a3 aE.a1 uE tE q (xE.x3, xE.x1)) := by
        calc
          (f a.multiplier * (q : E) * parameter) *
                (f a.multiplier * ((q⁻¹ : Eˣ) : E) *
                  actualFiberReciprocalParameter
                    aE.a3 aE.a1 uE tE q (xE.x3, xE.x1)) =
              ((q : E) * ((q⁻¹ : Eˣ) : E)) *
                (f a.multiplier * f a.multiplier *
                  (parameter *
                    actualFiberReciprocalParameter
                      aE.a3 aE.a1 uE tE q (xE.x3, xE.x1))) := by
            ring
          _ = f a.multiplier * f a.multiplier *
                (parameter *
                  actualFiberReciprocalParameter
                    aE.a3 aE.a1 uE tE q (xE.x3, xE.x1)) := by
            simp
      _ = f a.multiplier * f a.multiplier *
            centeredFiberProduct aE.a3 aE.a1 uE tE := by
        rw [hparameterProduct]
      _ = f (actualSigma a.multiplier a.a3 a.a1 u t) := by
        rw [map_actualSigma]
        simp [actualSigma, actualAlpha, actualBeta, aE, uE, tE]
        ring
  -- Package the seed as an element of the norm fiber.
  let sigmaUnit : (ZMod p)ˣ :=
    actualSigmaUnit a.multiplier a.a3 a.a1 u t hsigma
  have hseedMem : seedUnit ∈ quadraticNormFiber p sigmaUnit := by
    -- `quadraticNormFiber` is a preimage of `{sigmaUnit}`; unfold for `Set.mem_singleton_iff`.
    change
      quadraticNormUnitsHom p seedUnit ∈
        ({sigmaUnit} : Set (ZMod p)ˣ)
    rw [Set.mem_singleton_iff]
    apply Units.ext
    exact hseedNorm
  let S : ↥(quadraticNormFiber p sigmaUnit) :=
    ⟨seedUnit, hseedMem⟩
  refine ⟨h, S, ?_, ?_⟩
  · simpa [aE, uE, tE, q, xE, f, E] using hpoint
  · rfl

/-- Every parameter in the complementary power image of `w²` is reached by
a forward `rotation1` iterate, and its adjacent ordered trace is the
descended trace of the actual seed. -/
theorem exists_iterate_actualNonsplitSeedTrace
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (htrace : t = orderedTrace a.multiplier a.a1 u)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t)
    (w : quadraticNormOneTorus p)
    (htraceW : quadraticNormOneTrace p w = t)
    (h : (quadraticFiniteField p)ˣ)
    (S : ↥(quadraticNormFiber p
      (actualSigmaUnit a.multiplier a.a2 a.a3 u t
        (actualSigma_ne_zero_of_candidateRegular
          a.multiplier a.a1 a.a2 a.a3 u t htrace hregular))))
    (hpoint :
      Point.map
          (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint1
          (Coefficients.map
            (algebraMap (ZMod p) (quadraticFiniteField p)) a)
          (algebraMap (ZMod p) (quadraticFiniteField p) u)
          (algebraMap (ZMod p) (quadraticFiniteField p) t)
          (((w : (quadraticFiniteField p)ˣ) :
            quadraticFiniteField p))
          (h : quadraticFiniteField p))
    (hS :
      (S.1 : quadraticFiniteField p) =
        algebraMap (ZMod p) (quadraticFiniteField p)
            (actualAlpha a.multiplier) *
          (h : quadraticFiniteField p))
    (g : (powMonoidHom
      (Nat.card (quadraticNormOneTorus p) / orderOf (w ^ 2)) :
        quadraticNormOneTorus p →* quadraticNormOneTorus p).range) :
    ∃ n : ℕ,
      orderedTrace a.multiplier a.a2
          (((rotation1 a)^[n]) x).x2 =
        Algebra.trace (ZMod p) (quadraticFiniteField p)
            ((S.1 : quadraticFiniteField p) *
              ((g.1 : (quadraticFiniteField p)ˣ) :
                quadraticFiniteField p)) +
          actualGammaFirst a.multiplier a.a2 a.a3 u t := by
  -- Transport the fiber data to the quadratic extension `E`.
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := Coefficients.map f a
  let uE : E := f u
  let tE : E := f t
  let q : Eˣ := (w : Eˣ)
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a1 uE := by
    have hmap := congrArg f htrace
    simpa [tE, aE, uE, orderedTrace, Coefficients.map,
      Coefficients.multiplier, map_ofNat] using hmap
  have heigen : tE = splitTorusTrace q := by
    dsimp [tE, q, f]
    rw [← htraceW]
    exact algebraMap_quadraticNormOneTrace p w
  have hregularE :
      OrderedTraceCandidateRegular aE.a1 aE.a2 aE.a3 tE := by
    simpa [aE, tE] using
      orderedTraceCandidateRegular_map f f.injective hregular
  have hDE : discriminant tE ≠ 0 := by
    simpa [discriminant] using hregularE.1
  have halpha : actualAlpha a.multiplier ≠ 0 := by
    have hsigma :=
      actualSigma_ne_zero_of_candidateRegular
        a.multiplier a.a1 a.a2 a.a3 u t htrace hregular
    have hproduct :
        actualAlpha a.multiplier *
            actualBeta a.multiplier a.a2 a.a3 u t ≠ 0 := by
      simpa [actualSigma] using hsigma
    exact (mul_ne_zero_iff.mp hproduct).1
  -- Choose `n` with `(w ^ 2) ^ n = g` and compare the traces after mapping to `E`.
  obtain ⟨n, hn⟩ :=
    BGS.Markoff.exists_pow_eq_of_mem_complementaryPowerRange (w ^ 2) g
  refine ⟨n, ?_⟩
  apply f.injective
  -- Over `E`, the `n`-th iterate is `fiberPoint1` at the parameter `h * g`.
  have hmapIterate :=
    Point.map_iterate_rotation1 f a x n
  have hiterated :
      Point.map f (((rotation1 a)^[n]) x) =
        fiberPoint1 aE uE tE (q : E)
          (((h * (g.1 : Eˣ)) : Eˣ) : E) := by
    rw [hmapIterate, hpoint]
    rw [iterate_rotation1_fiberPoint1_eq_pow_mul
      aE uE tE (q : E) (h : E) hDE
      (Units.ne_zero q) (Units.ne_zero h)
      (by
        simpa only [splitTorusTrace, Units.val_inv_eq_inv_val] using
          heigen)
      htraceE n]
    congr 1
    have hnE :
        ((((q ^ 2) ^ n : Eˣ) : E)) =
          (((g.1 : Eˣ)) : E) := by
      simpa [q] using
        congrArg
          (fun z : quadraticNormOneTorus p ↦
            (((z : Eˣ)) : E)) hn
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, mul_comm] using
      congrArg (fun z : E ↦ z * (h : E)) hnE
  -- Identify the trace with the descended seed trace.
  calc
    f (orderedTrace a.multiplier a.a2
          (((rotation1 a)^[n]) x).x2) =
        orderedTrace aE.multiplier aE.a2
          (Point.map f (((rotation1 a)^[n]) x)).x2 := by
      simp [orderedTrace, aE, Coefficients.map, Point.map,
        Coefficients.multiplier, map_ofNat]
    _ = orderedTrace aE.multiplier aE.a2
        (fiberPoint1 aE uE tE (q : E)
          (((h * (g.1 : Eˣ)) : Eˣ) : E)).x2 := by
      rw [hiterated]
    _ = f
        (Algebra.trace (ZMod p) (quadraticFiniteField p)
            ((S.1 : quadraticFiniteField p) *
              ((g.1 : (quadraticFiniteField p)ˣ) :
                quadraticFiniteField p)) +
          actualGammaFirst a.multiplier a.a2 a.a3 u t) := by
      symm
      simpa [aE, uE, tE, q, f, E, fiberPoint1] using
        algebraMap_shiftedActualSeedTrace_eq_firstTrace_fiberPair
          p a.multiplier a.a2 a.a3 u t
          (actualSigma_ne_zero_of_candidateRegular
            a.multiplier a.a1 a.a2 a.a3 u t htrace hregular)
          halpha h S hS w g.1

/-- Every parameter in the complementary power image of `w²` is reached by
a forward `rotation2` iterate in the reverse ordered frame.  The resulting
first-axis trace is the descended trace of the second-coordinate seed. -/
theorem exists_iterate_actualNonsplitSecondSeedTrace
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (htrace : t = orderedTrace a.multiplier a.a2 u)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t)
    (w : quadraticNormOneTorus p)
    (htraceW : quadraticNormOneTrace p w = t)
    (h : (quadraticFiniteField p)ˣ)
    (S : ↥(quadraticNormFiber p
      (actualSigmaUnit a.multiplier a.a3 a.a1 u t
        (actualSigma_ne_zero_of_reverseCandidateRegular
          a.multiplier a.a2 a.a3 a.a1 u t htrace hregular))))
    (hpoint :
      Point.map
          (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint2
          (Coefficients.map
            (algebraMap (ZMod p) (quadraticFiniteField p)) a)
          (algebraMap (ZMod p) (quadraticFiniteField p) u)
          (algebraMap (ZMod p) (quadraticFiniteField p) t)
          (((w : (quadraticFiniteField p)ˣ) :
            quadraticFiniteField p))
          (h : quadraticFiniteField p))
    (hS :
      (S.1 : quadraticFiniteField p) =
        algebraMap (ZMod p) (quadraticFiniteField p) a.multiplier *
          (((w : quadraticNormOneTorus p) :
              (quadraticFiniteField p)ˣ) :
            quadraticFiniteField p) *
          (h : quadraticFiniteField p))
    (g : (powMonoidHom
      (Nat.card (quadraticNormOneTorus p) / orderOf (w ^ 2)) :
        quadraticNormOneTorus p →* quadraticNormOneTorus p).range) :
    ∃ n : ℕ,
      orderedTrace a.multiplier a.a1
          (((rotation2 a)^[n]) x).x1 =
        Algebra.trace (ZMod p) (quadraticFiniteField p)
            ((S.1 : quadraticFiniteField p) *
              ((g.1 : (quadraticFiniteField p)ˣ) :
                quadraticFiniteField p)) +
          actualGammaSecond a.multiplier a.a3 a.a1 u t := by
  -- Transport the fiber data to the quadratic extension `E`.
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let aE : Coefficients E := Coefficients.map f a
  let uE : E := f u
  let tE : E := f t
  let q : Eˣ := (w : Eˣ)
  have htraceE :
      tE = orderedTrace aE.multiplier aE.a2 uE := by
    have hmap := congrArg f htrace
    simpa [tE, aE, uE, orderedTrace, Coefficients.map,
      Coefficients.multiplier, map_ofNat] using hmap
  have heigen : tE = splitTorusTrace q := by
    dsimp [tE, q, f]
    rw [← htraceW]
    exact algebraMap_quadraticNormOneTrace p w
  have hregularE :
      OrderedTraceCandidateRegular aE.a2 aE.a1 aE.a3 tE := by
    simpa [aE, tE] using
      orderedTraceCandidateRegular_map f f.injective hregular
  have hDE : discriminant tE ≠ 0 := by
    simpa [discriminant] using hregularE.1
  have hs : a.multiplier ≠ 0 := by
    have hsigma :=
      actualSigma_ne_zero_of_reverseCandidateRegular
        a.multiplier a.a2 a.a3 a.a1 u t htrace hregular
    intro hzero
    apply hsigma
    simp [actualSigma, actualAlpha, hzero]
  -- Choose `n` with `(w ^ 2) ^ n = g` and compare the traces after mapping to `E`.
  obtain ⟨n, hn⟩ :=
    BGS.Markoff.exists_pow_eq_of_mem_complementaryPowerRange (w ^ 2) g
  refine ⟨n, ?_⟩
  apply f.injective
  -- Over `E`, the `n`-th iterate is `fiberPoint2` at the parameter `h * g`.
  have hmapIterate :=
    Point.map_iterate_rotation2 f a x n
  have hiterated :
      Point.map f (((rotation2 a)^[n]) x) =
        fiberPoint2 aE uE tE (q : E)
          (((h * (g.1 : Eˣ)) : Eˣ) : E) := by
    rw [hmapIterate, hpoint]
    rw [iterate_rotation2_fiberPoint2_eq_pow_mul
      aE uE tE (q : E) (h : E) hDE
      (Units.ne_zero q) (Units.ne_zero h)
      (by
        simpa only [splitTorusTrace, Units.val_inv_eq_inv_val] using
          heigen)
      htraceE n]
    congr 1
    have hnE :
        ((((q ^ 2) ^ n : Eˣ) : E)) =
          (((g.1 : Eˣ)) : E) := by
      simpa [q] using
        congrArg
          (fun z : quadraticNormOneTorus p ↦
            (((z : Eˣ)) : E)) hn
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, mul_comm] using
      congrArg (fun z : E ↦ z * (h : E)) hnE
  -- Identify the trace with the descended seed trace.
  calc
    f (orderedTrace a.multiplier a.a1
          (((rotation2 a)^[n]) x).x1) =
        orderedTrace aE.multiplier aE.a1
          (Point.map f (((rotation2 a)^[n]) x)).x1 := by
      simp [orderedTrace, aE, Coefficients.map, Point.map,
        Coefficients.multiplier, map_ofNat]
    _ = orderedTrace aE.multiplier aE.a1
        (fiberPoint2 aE uE tE (q : E)
          (((h * (g.1 : Eˣ)) : Eˣ) : E)).x1 := by
      rw [hiterated]
    _ = f
        (Algebra.trace (ZMod p) (quadraticFiniteField p)
            ((S.1 : quadraticFiniteField p) *
              ((g.1 : (quadraticFiniteField p)ˣ) :
                quadraticFiniteField p)) +
          actualGammaSecond a.multiplier a.a3 a.a1 u t) := by
      symm
      simpa [aE, uE, tE, q, f, E, fiberPoint2] using
        algebraMap_shiftedActualSecondSeedTrace_eq_secondTrace_fiberPair
          p a.multiplier a.a3 a.a1 u t
          (actualSigma_ne_zero_of_reverseCandidateRegular
            a.multiplier a.a2 a.a3 a.a1 u t htrace hregular)
          hs w h S hS g.1

/-- Under the forty-pair descended-count margin, a candidate-regular point on
the first-coordinate nonsplit fiber has a forward `rotation1` iterate whose
second-axis trace is primitive on the split torus and candidate regular in
the target frame `(a.a2, targetB, targetC)`. -/
theorem
    exists_iterate_actualNonsplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (hx : IsSolution a x) (hx1 : x.x1 = u)
    (htrace : t = orderedTrace a.multiplier a.a1 u)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (targetB targetC : ZMod p)
    (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t)
    (w : quadraticNormOneTorus p)
    (htraceW : quadraticNormOneTrace p w = t)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) + 40 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p
            (Nat.card (quadraticNormOneTorus p) /
              orderOf (w ^ 2))) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a2
          (((rotation1 a)^[n]) x).x2 =
        splitTorusTrace v ∧
      orderOf v = Nat.card (ZMod p)ˣ ∧
        OrderedTraceCandidateRegular
          a.a2 targetB targetC (splitTorusTrace v) := by
  -- The seed norm `k = actualSigma ≠ 1` and the even obstruction, from candidate regularity.
  have hsigma :
      actualSigma a.multiplier a.a2 a.a3 u t ≠ 0 :=
    actualSigma_ne_zero_of_candidateRegular
      a.multiplier a.a1 a.a2 a.a3 u t htrace hregular
  let k : (ZMod p)ˣ :=
    actualSigmaUnit a.multiplier a.a2 a.a3 u t hsigma
  have hk : k ≠ 1 := by
    intro hunit
    apply actualSigma_ne_one_of_candidateRegular
      a.multiplier a.a1 a.a2 a.a3 u t htrace hregular
    have hval :=
      congrArg (fun z : (ZMod p)ˣ ↦ (z : ZMod p)) hunit
    simpa [k] using hval
  have hD2 :
      shiftedTraceEvenObstruction (k : ZMod p)
          (actualGammaFirst a.multiplier a.a2 a.a3 u t) ≠ 0 := by
    simpa [k] using
      actualEvenObstruction_ne_zero_of_candidateRegular
        a.multiplier a.a1 a.a2 a.a3 u t
          htrace hA2 hregular
  -- Seed the descended count, take a primitive candidate-regular pair, and reach it.
  obtain ⟨h, S, hpoint, hS⟩ :=
    exists_actualShiftedNonsplitSeed
      p a u t x hx hx1 htrace hregular w htraceW
  let orbitExponent :=
    Nat.card (quadraticNormOneTorus p) / orderOf (w ^ 2)
  obtain ⟨z, hzTrace, hzOrder, hzRegular⟩ :=
    exists_shiftedSeededNonsplitPrimitiveTracePair_candidateRegular_of_error_add_forty_lt_main
      p coefficient hWeil hpTwo
        a.a2 targetB targetC hA2 hTargetB
        k hk S (actualGammaFirst a.multiplier a.a2 a.a3 u t)
        hD2 orbitExponent
        (BGS.Markoff.complementaryExponent_pos (w ^ 2))
        (BGS.Markoff.nonsplitComplementaryExponent_cast_ne_zero p
          (w ^ 2))
        (BGS.Markoff.complementaryExponent_dvd_natCard (w ^ 2))
        (by simpa [orbitExponent] using hmargin)
  obtain ⟨n, hn⟩ :=
    exists_iterate_actualNonsplitSeedTrace
      p a u t x htrace hregular w htraceW
        h S hpoint hS z.1
  refine ⟨n, z.2, ?_, hzOrder, hzRegular⟩
  calc
    orderedTrace a.multiplier a.a2
        (((rotation1 a)^[n]) x).x2 =
      Algebra.trace (ZMod p) (quadraticFiniteField p)
          ((S.1 : quadraticFiniteField p) *
            ((z.1.1 : (quadraticFiniteField p)ˣ) :
              quadraticFiniteField p)) +
        actualGammaFirst a.multiplier a.a2 a.a3 u t := hn
    _ = shiftedSeededNonsplitTorusTrace
          p k S
            (actualGammaFirst a.multiplier a.a2 a.a3 u t)
            z.1 := rfl
    _ = splitTorusTrace z.2 := hzTrace

/-- Under the forty-pair descended-count margin, a candidate-regular point on
the second-coordinate nonsplit fiber has a forward `rotation2` iterate whose
first-axis trace is primitive on the split torus and candidate regular in the
target frame `(a.a1, targetB, targetC)`. -/
theorem
    exists_iterate_actualNonsplitPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ)
    (hWeil : ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p))
    (hx : IsSolution a x) (hx2 : x.x2 = u)
    (htrace : t = orderedTrace a.multiplier a.a2 u)
    (hA1 : a.a1 ^ 2 ≠ 4)
    (targetB targetC : ZMod p)
    (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t)
    (w : quadraticNormOneTorus p)
    (htraceW : quadraticNormOneTrace p w = t)
    (hmargin :
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) + 40 <
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p
            (Nat.card (quadraticNormOneTorus p) /
              orderOf (w ^ 2))) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a1
          (((rotation2 a)^[n]) x).x1 =
        splitTorusTrace v ∧
      orderOf v = Nat.card (ZMod p)ˣ ∧
        OrderedTraceCandidateRegular
          a.a1 targetB targetC (splitTorusTrace v) := by
  -- The seed norm `k = actualSigma ≠ 1` and the even obstruction, from reverse regularity.
  have hsigma :
      actualSigma a.multiplier a.a3 a.a1 u t ≠ 0 :=
    actualSigma_ne_zero_of_reverseCandidateRegular
      a.multiplier a.a2 a.a3 a.a1 u t htrace hregular
  let k : (ZMod p)ˣ :=
    actualSigmaUnit a.multiplier a.a3 a.a1 u t hsigma
  have hk : k ≠ 1 := by
    intro hunit
    have hval :=
      congrArg (fun z : (ZMod p)ˣ ↦ (z : ZMod p)) hunit
    have hsigmaOne :
        actualSigma a.multiplier a.a3 a.a1 u t = 1 := by
      simpa [k] using hval
    apply hregular.sigma_ne_one
    rw [← orderedTraceSigma_swap a.a2 a.a3 a.a1]
    rw [← actualSigma_eq_orderedTraceSigma
      a.multiplier a.a2 a.a3 a.a1 u t htrace]
    exact hsigmaOne
  have hD2 :
      shiftedTraceEvenObstruction (k : ZMod p)
          (actualGammaSecond a.multiplier a.a3 a.a1 u t) ≠ 0 := by
    simpa [k] using
      actualSecondEvenObstruction_ne_zero_of_candidateRegular
        a.multiplier a.a2 a.a3 a.a1 u t
          htrace hA1 hregular
  -- Seed the descended count, take a primitive candidate-regular pair, and reach it.
  obtain ⟨h, S, hpoint, hS⟩ :=
    exists_actualShiftedNonsplitSecondSeed
      p a u t x hx hx2 htrace hregular w htraceW
  let orbitExponent :=
    Nat.card (quadraticNormOneTorus p) / orderOf (w ^ 2)
  obtain ⟨z, hzTrace, hzOrder, hzRegular⟩ :=
    exists_shiftedSeededNonsplitPrimitiveTracePair_candidateRegular_of_error_add_forty_lt_main
      p coefficient hWeil hpTwo
        a.a1 targetB targetC hA1 hTargetB
        k hk S (actualGammaSecond a.multiplier a.a3 a.a1 u t)
        hD2 orbitExponent
        (BGS.Markoff.complementaryExponent_pos (w ^ 2))
        (BGS.Markoff.nonsplitComplementaryExponent_cast_ne_zero p
          (w ^ 2))
        (BGS.Markoff.complementaryExponent_dvd_natCard (w ^ 2))
        (by simpa [orbitExponent] using hmargin)
  obtain ⟨n, hn⟩ :=
    exists_iterate_actualNonsplitSecondSeedTrace
      p a u t x htrace hregular w htraceW
        h S hpoint hS z.1
  refine ⟨n, z.2, ?_, hzOrder, hzRegular⟩
  calc
    orderedTrace a.multiplier a.a1
        (((rotation2 a)^[n]) x).x1 =
      Algebra.trace (ZMod p) (quadraticFiniteField p)
          ((S.1 : quadraticFiniteField p) *
            ((z.1.1 : (quadraticFiniteField p)ˣ) :
              quadraticFiniteField p)) +
        actualGammaSecond a.multiplier a.a3 a.a1 u t := hn
    _ = shiftedSeededNonsplitTorusTrace
          p k S
            (actualGammaSecond a.multiplier a.a3 a.a1 u t)
            z.1 := rfl
    _ = splitTorusTrace z.2 := hzTrace

/-- The explicit inequality for the coefficient `coefficient + 40` gives the
forty-pair margin: the divisor-count error term plus `40` is below
`primitiveTraceMoebiusMainTerm`. -/
private theorem
    error_add_forty_lt_primitiveMain_of_augmented_explicitInequality
    (groupOrder fieldCard fixedExponent coefficient : ℕ)
    (hgroup : 0 < groupOrder) (hfield : 0 < fieldCard)
    (hfixed : 0 < fixedExponent)
    (hexplicit :
      (fixedExponent : ℝ) * (groupOrder.divisors.card : ℝ) ^ 2 *
          (((coefficient + 40 : ℕ) : ℝ) *
            Real.sqrt (fieldCard : ℝ)) < fieldCard) :
    (groupOrder.divisors.card : ℝ) *
          ((coefficient : ℝ) * Real.sqrt (fieldCard : ℝ)) + 40 <
      primitiveTraceMoebiusMainTerm
        groupOrder fieldCard fixedExponent := by
  have hdomination :=
    BGS.Markoff.divisorsError_lt_primitiveTraceMoebiusMainTerm_of_explicitInequality
      groupOrder fieldCard fixedExponent (coefficient + 40)
      hgroup hfixed hexplicit
  -- Since `1 ≤ #divisors * √fieldCard`, the additive `40` is absorbed into the coefficient.
  have hdivisorsOne :
      (1 : ℝ) ≤ (groupOrder.divisors.card : ℝ) := by
    exact_mod_cast
      (Nat.nonempty_divisors.mpr hgroup.ne').card_pos
  have hfieldOne : (1 : ℝ) ≤ (fieldCard : ℝ) := by
    exact_mod_cast hfield
  have hsqrtOne :
      (1 : ℝ) ≤ Real.sqrt (fieldCard : ℝ) :=
    Real.one_le_sqrt.mpr hfieldOne
  have hproductOne :
      (1 : ℝ) ≤
        (groupOrder.divisors.card : ℝ) *
          Real.sqrt (fieldCard : ℝ) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (groupOrder.divisors.card : ℝ) *
          Real.sqrt (fieldCard : ℝ) := by gcongr
  calc
    (groupOrder.divisors.card : ℝ) *
            ((coefficient : ℝ) * Real.sqrt (fieldCard : ℝ)) + 40 =
        (coefficient : ℝ) *
            ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ)) + 40 := by ring
    _ ≤ (coefficient : ℝ) *
            ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ)) +
          40 * ((groupOrder.divisors.card : ℝ) *
            Real.sqrt (fieldCard : ℝ)) := by
      have hforty :
          (40 : ℝ) ≤
            40 * ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ)) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hproductOne
            -- `show` only fixes the side goal `0 ≤ 40` in `ℝ`; nothing is unfolded.
            (show (0 : ℝ) ≤ 40 by norm_num))
      exact add_le_add
        (le_refl
          ((coefficient : ℝ) *
            ((groupOrder.divisors.card : ℝ) *
              Real.sqrt (fieldCard : ℝ))))
        hforty
    _ = (groupOrder.divisors.card : ℝ) *
          (((coefficient + 40 : ℕ) : ℝ) *
            Real.sqrt (fieldCard : ℝ)) := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      ring
    _ < primitiveTraceMoebiusMainTerm
        groupOrder fieldCard fixedExponent := hdomination

/-- Reasonable-cutoff version of the first-to-second nonsplit-source endgame:
for `p ≥ reasonableAnalyticCutoff`, `coefficient + 40 ≤ 1032` and
`p ^ (1/2 + delta) ≤ orderOf (w ^ 2)` with `delta ≥ 1/4`, the forty-pair
margin holds and the descended-count endgame applies. -/
theorem
    actualNonsplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame_of_reasonableCutoff
    (coefficient : ℕ)
    (hWeil : ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : (1 : ℝ) / 4 ≤ delta)
    (hcoefficient : coefficient + 40 ≤ 1032)
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p)) (w : quadraticNormOneTorus p)
    (targetB targetC : ZMod p)
    (hx : IsSolution a x) (hx1 : x.x1 = u)
    (htrace : t = orderedTrace a.multiplier a.a1 u)
    (hA2 : a.a2 ^ 2 ≠ 4) (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t)
    (htraceW : quadraticNormOneTrace p w = t)
    (hlarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (w ^ 2)) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a2 (((rotation1 a)^[n]) x).x2 =
          splitTorusTrace v ∧
        orderOf v = Nat.card (ZMod p)ˣ ∧
          OrderedTraceCandidateRegular
            a.a2 targetB targetC (splitTorusTrace v) := by
  have hpThree : 3 ≤ p := by
    have :=
      GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans hp
    omega
  have hpTwo : p ≠ 2 := by omega
  let orbitExponent :=
    Nat.card (quadraticNormOneTorus p) / orderOf (w ^ 2)
  have hmul :
      orbitExponent * orderOf (w ^ 2) = p + 1 := by
    dsimp [orbitExponent]
    rw [Nat.div_mul_cancel (orderOf_dvd_natCard (w ^ 2)),
      quadraticNormOneTorus_natCard]
  have hexplicit :=
    GenMarkoff.General.Explicit.reasonable_primitiveTrace_explicitInequality_of_card_add_one
      hp hmul hlarge hdelta hcoefficient
  have hcardUnits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have hexplicit' :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
            (((coefficient + 40 : ℕ) : ℝ) *
              Real.sqrt (p : ℝ)) < p := by
    simpa only [hcardUnits] using hexplicit
  have hgroupPositive : 0 < Nat.card (ZMod p)ˣ := by
    rw [hcardUnits]
    omega
  have hmargin :=
    error_add_forty_lt_primitiveMain_of_augmented_explicitInequality
      (Nat.card (ZMod p)ˣ) p orbitExponent coefficient
        hgroupPositive (by omega)
        (BGS.Markoff.complementaryExponent_pos (w ^ 2)) hexplicit'
  exact
    exists_iterate_actualNonsplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame
      p coefficient hWeil hpTwo a u t x hx hx1 htrace
        hA2 targetB targetC hTargetB hregular w htraceW
        (by simpa [orbitExponent] using hmargin)

/-- Reasonable-cutoff version of the second-to-first nonsplit-source endgame,
under the same hypotheses on `p` and `orderOf (w ^ 2)`. -/
theorem
    actualNonsplitPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame_of_reasonableCutoff
    (coefficient : ℕ)
    (hWeil : ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : (1 : ℝ) / 4 ≤ delta)
    (hcoefficient : coefficient + 40 ≤ 1032)
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p)) (u t : ZMod p)
    (x : Point (ZMod p)) (w : quadraticNormOneTorus p)
    (targetB targetC : ZMod p)
    (hx : IsSolution a x) (hx2 : x.x2 = u)
    (htrace : t = orderedTrace a.multiplier a.a2 u)
    (hA1 : a.a1 ^ 2 ≠ 4) (hTargetB : targetB ^ 2 ≠ 4)
    (hregular : OrderedTraceCandidateRegular a.a2 a.a1 a.a3 t)
    (htraceW : quadraticNormOneTrace p w = t)
    (hlarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (w ^ 2)) :
    ∃ n : ℕ, ∃ v : (ZMod p)ˣ,
      orderedTrace a.multiplier a.a1 (((rotation2 a)^[n]) x).x1 =
          splitTorusTrace v ∧
        orderOf v = Nat.card (ZMod p)ˣ ∧
          OrderedTraceCandidateRegular
            a.a1 targetB targetC (splitTorusTrace v) := by
  have hpThree : 3 ≤ p := by
    have :=
      GenMarkoff.General.Explicit.five_le_reasonableAnalyticCutoff.trans hp
    omega
  have hpTwo : p ≠ 2 := by omega
  let orbitExponent :=
    Nat.card (quadraticNormOneTorus p) / orderOf (w ^ 2)
  have hmul :
      orbitExponent * orderOf (w ^ 2) = p + 1 := by
    dsimp [orbitExponent]
    rw [Nat.div_mul_cancel (orderOf_dvd_natCard (w ^ 2)),
      quadraticNormOneTorus_natCard]
  have hexplicit :=
    GenMarkoff.General.Explicit.reasonable_primitiveTrace_explicitInequality_of_card_add_one
      hp hmul hlarge hdelta hcoefficient
  have hcardUnits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have hexplicit' :
      (orbitExponent : ℝ) *
          ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) ^ 2 *
            (((coefficient + 40 : ℕ) : ℝ) *
              Real.sqrt (p : ℝ)) < p := by
    simpa only [hcardUnits] using hexplicit
  have hgroupPositive : 0 < Nat.card (ZMod p)ˣ := by
    rw [hcardUnits]
    omega
  have hmargin :=
    error_add_forty_lt_primitiveMain_of_augmented_explicitInequality
      (Nat.card (ZMod p)ˣ) p orbitExponent coefficient
        hgroupPositive (by omega)
        (BGS.Markoff.complementaryExponent_pos (w ^ 2)) hexplicit'
  exact
    exists_iterate_actualNonsplitPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame
      p coefficient hWeil hpTwo a u t x hx hx2 htrace
        hA1 targetB targetC hTargetB hregular w htraceW
        (by simpa [orbitExponent] using hmargin)

/-- Reasonable-cutoff endgame for an alternating regular state whose fixed
trace is `quadraticNormOneTrace p w`, in either direction; the output is the
split result `alternatingPrimitiveSplitEndgameResult`. -/
theorem alternatingRegularState_actualNonsplitSourcePrimitiveSplitEndgame_of_reasonableCutoff
    (coefficient : ℕ)
    (hWeil : ShiftedSeededNonsplitTraceWeilBoundAssumption coefficient)
    {delta : ℝ} (hdelta : (1 : ℝ) / 4 ≤ delta)
    (hcoefficient : coefficient + 40 ≤ 1032)
    (p : ℕ)
    (hp : GenMarkoff.General.Explicit.reasonableAnalyticCutoff ≤ p)
    [Fact p.Prime]
    (a : Coefficients (ZMod p))
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (state : AlternatingRegularState a)
    (w : quadraticNormOneTorus p)
    (heigen :
      traceAt a state.direction.fixed state.point.1 =
        quadraticNormOneTrace p w)
    (hlarge :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orderOf (w ^ 2)) :
    alternatingPrimitiveSplitEndgameResult
      p a state.direction state.point.1 := by
  rcases state with ⟨direction, point, hregular⟩
  cases direction with
  | firstSecond =>
      exact
        actualNonsplitPoint_with_primitiveCandidateRegularAxisTwoTrace_in_targetFrame_of_reasonableCutoff
          coefficient hWeil hdelta hcoefficient p hp
          a point.1.x1 (traceAt a .first point.1) point.1 w
          a.a1 a.a3 point.2 rfl rfl hA2 hA1
          (by simpa [alternatingTraceRegular] using hregular)
          (by simpa [AlternatingDirectedAxis.fixed] using heigen.symm)
          hlarge
  | secondFirst =>
      exact
        actualNonsplitPoint_with_primitiveCandidateRegularAxisOneTrace_in_targetFrame_of_reasonableCutoff
          coefficient hWeil hdelta hcoefficient p hp
          a point.1.x2 (traceAt a .second point.1) point.1 w
          a.a2 a.a3 point.2 rfl rfl hA1 hA2
          (by simpa [alternatingTraceRegular] using hregular)
          (by simpa [AlternatingDirectedAxis.fixed] using heigen.symm)
          hlarge

end

end GenMarkoff.General.Endgame.Nonsplit
