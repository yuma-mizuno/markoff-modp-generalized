import GenMarkoff.Symmetric.Endgame.Nonsplit.ShiftedSeededCover
import GenMarkoff.Symmetric.MiddleGame.ActualDiagonalization
import GenMarkoff.Symmetric.MiddleGame.ActualMoveWiring
import GenMarkoff.Symmetric.MiddleGame.ActualOrderGrowth
import GenMarkoff.Symmetric.Opening.ReturnExponentBound
import BGS.Markoff.Endgame.PrimitiveOrbitWiring

/-!
# The actual nonsplit seed of a symmetric fiber

A base-field point on a nonsplit fiber acquires two eigen-coordinates over
the canonical quadratic extension.  Frobenius exchanges those coordinates.
Consequently the first actual eigen-coordinate has norm
`centeredFiberProduct`; after multiplication by `actualAlpha` it has norm
`actualSigma`.  This is the seed required by the shifted nonsplit cover.
-/

namespace GenMarkoff.Symmetric.Endgame.Nonsplit

open BGS.Markoff

noncomputable section

/-- Package the nonzero actual weight product as a unit. -/
def actualSigmaUnit {K : Type*} [Field K]
    (c u t : K) (h : actualSigma c u t ≠ 0) : Kˣ :=
  Units.mk0 (actualSigma c u t) h

@[simp]
theorem actualSigmaUnit_val {K : Type*} [Field K]
    (c u t : K) (h : actualSigma c u t ≠ 0) :
    (actualSigmaUnit c u t h : K) = actualSigma c u t :=
  rfl

theorem map_centeredFiberProduct
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (c u t : K) :
    f (centeredFiberProduct c u t) =
      centeredFiberProduct (f c) (f u) (f t) := by
  simp [centeredFiberProduct, discriminant, map_sub, map_mul, map_pow,
    map_div₀, map_ofNat]

theorem map_actualAlpha
    {K L : Type*} [Field K] [Field L] (f : K →+* L) (c : K) :
    f (actualAlpha c) = actualAlpha (f c) := by
  simp [actualAlpha, multiplier, map_ofNat]

theorem map_actualBeta
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (c u t : K) :
    f (actualBeta c u t) =
      actualBeta (f c) (f u) (f t) := by
  change f (actualAlpha c * centeredFiberProduct c u t) =
    actualAlpha (f c) * centeredFiberProduct (f c) (f u) (f t)
  rw [map_mul, map_actualAlpha, map_centeredFiberProduct]

theorem map_actualSigma
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (c u t : K) :
    f (actualSigma c u t) =
      actualSigma (f c) (f u) (f t) := by
  rw [actualSigma, actualSigma, map_mul, map_actualAlpha, map_actualBeta]

theorem map_actualGamma
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (c u t : K) :
    f (actualGamma c u t) =
      actualGamma (f c) (f u) (f t) := by
  simp [actualGamma, fiberCenter, multiplier, map_sub, map_mul, map_div₀,
    map_ofNat]

/-- Frobenius exchanges the two actual eigen-coordinates of a base-field
point on a nonsplit fiber. -/
theorem actualFiberParameter_frobenius
    (p : ℕ) [Fact p.Prime]
    (c u t : ZMod p) (w : quadraticNormOneTorus p)
    (x : Point (ZMod p)) :
    (MiddleGame.actualFiberParameter
        (algebraMap (ZMod p) (quadraticFiniteField p) c)
        (algebraMap (ZMod p) (quadraticFiniteField p) u)
        (algebraMap (ZMod p) (quadraticFiniteField p) t)
        (w : (quadraticFiniteField p)ˣ)
        (Opening.mapPoint
          (algebraMap (ZMod p) (quadraticFiniteField p)) x)) ^ p =
      MiddleGame.actualFiberReciprocalParameter
        (algebraMap (ZMod p) (quadraticFiniteField p) c)
        (algebraMap (ZMod p) (quadraticFiniteField p) u)
        (algebraMap (ZMod p) (quadraticFiniteField p) t)
        (w : (quadraticFiniteField p)ˣ)
        (Opening.mapPoint
          (algebraMap (ZMod p) (quadraticFiniteField p)) x) := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  have hwFrobenius :
      (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ p) =
        ((((w : (quadraticFiniteField p)ˣ)⁻¹ :
          (quadraticFiniteField p)ˣ) : quadraticFiniteField p)) :=
    quadraticNormOne_frobenius_eq_inv p w
  have hwInvFrobenius :
      ((((w : (quadraticFiniteField p)ˣ)⁻¹ :
          (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ p) =
        ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) := by
    have hscalar :
        ((((w : (quadraticFiniteField p)ˣ) :
          quadraticFiniteField p)⁻¹) ^ p) =
          ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) := by
      rw [inv_pow, hwFrobenius]
      simpa only [Units.val_inv_eq_inv_val] using
        inv_inv (((w : (quadraticFiniteField p)ˣ) :
          quadraticFiniteField p))
    simpa only [Units.val_inv_eq_inv_val] using hscalar
  have hbase (a : ZMod p) : (f a) ^ p = f a := by
    simpa [f, E] using algebraMap_zmod_pow_card p a
  have hcenter :
      (fiberCenter (f c) (f u) (f t)) ^ p =
        fiberCenter (f c) (f u) (f t) := by
    have htwo : (2 : E) ^ p = 2 := by
      change (f (2 : ZMod p)) ^ p = f (2 : ZMod p)
      exact hbase 2
    rw [fiberCenter, div_pow, mul_pow, hbase c, hbase u, sub_pow_char,
      hbase t, htwo]
  simp only [MiddleGame.actualFiberParameter,
    MiddleGame.actualFiberReciprocalParameter, Opening.mapPoint]
  rw [div_pow, sub_pow_char, sub_pow_char, mul_pow, sub_pow_char,
    sub_pow_char,
    hwFrobenius, hwInvFrobenius, hcenter, hbase x.x2, hbase x.x3]
  have hden :
      (((((w : (quadraticFiniteField p)ˣ)⁻¹ :
          (quadraticFiniteField p)ˣ) : quadraticFiniteField p)) -
          ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)) =
        -(((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) -
          ((((w : (quadraticFiniteField p)ˣ)⁻¹ :
            (quadraticFiniteField p)ˣ) : quadraticFiniteField p))) := by
    ring
  rw [hden, div_neg]
  ring

/-- The quadratic trace of the norm-`sigma` seed, multiplied by a norm-one
parameter, is exactly the adjacent trace of the corresponding actual
extension-field fiber point. -/
theorem algebraMap_shiftedActualSeedTrace_eq_trace_fiberPoint_x2
    (p : ℕ) [Fact p.Prime]
    (c u t : ZMod p)
    (hsigma : actualSigma c u t ≠ 0)
    (halpha : actualAlpha c ≠ 0)
    (h : (quadraticFiniteField p)ˣ)
    (S : ↥(quadraticNormFiber p (actualSigmaUnit c u t hsigma)))
    (hS :
      (S.1 : quadraticFiniteField p) =
        algebraMap (ZMod p) (quadraticFiniteField p) (actualAlpha c) *
          (h : quadraticFiniteField p))
    (q g : quadraticNormOneTorus p) :
    algebraMap (ZMod p) (quadraticFiniteField p)
        (Algebra.trace (ZMod p) (quadraticFiniteField p)
            ((S.1 : quadraticFiniteField p) *
              ((g : (quadraticFiniteField p)ˣ) :
                quadraticFiniteField p)) +
          actualGamma c u t) =
      trace (algebraMap (ZMod p) (quadraticFiniteField p) c)
        (fiberPoint
          (algebraMap (ZMod p) (quadraticFiniteField p) c)
          (algebraMap (ZMod p) (quadraticFiniteField p) u)
          (algebraMap (ZMod p) (quadraticFiniteField p) t)
          (((q : (quadraticFiniteField p)ˣ) :
            quadraticFiniteField p))
          (((h * (g : (quadraticFiniteField p)ˣ) :
            (quadraticFiniteField p)ˣ)) :
              quadraticFiniteField p)).x2 := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  have hSFrobenius :=
    quadraticNormFiber_frobenius_eq_norm_mul_inv p
      (actualSigmaUnit c u t hsigma) S
  have hgFrobenius := quadraticNormOne_frobenius_eq_inv p g
  have hmapAlpha : f (actualAlpha c) = actualAlpha (f c) :=
    map_actualAlpha f c
  have hmapBeta : f (actualBeta c u t) =
      actualBeta (f c) (f u) (f t) :=
    map_actualBeta f c u t
  have hmapSigma : f (actualSigma c u t) =
      actualSigma (f c) (f u) (f t) :=
    map_actualSigma f c u t
  have hmapGamma : f (actualGamma c u t) =
      actualGamma (f c) (f u) (f t) :=
    map_actualGamma f c u t
  have hAlphaE : f (actualAlpha c) ≠ 0 :=
    (map_ne_zero_iff f f.injective).mpr halpha
  have hAlphaTarget : actualAlpha (f c) ≠ 0 := by
    rw [← hmapAlpha]
    exact hAlphaE
  have hH : (h : E) ≠ 0 := Units.ne_zero h
  have hg : (((g : Eˣ) : E)) ≠ 0 := Units.ne_zero _
  rw [map_add, algebraMap_quadraticTrace, mul_pow, hSFrobenius,
    hgFrobenius]
  simp only [actualSigmaUnit_val, Units.val_mul]
  rw [trace_fiberPoint_x2 _ _ _ _ _
    (mul_ne_zero hH hg)]
  rw [hS, hmapAlpha, hmapSigma, hmapGamma]
  dsimp [f, E] at hAlphaE hAlphaTarget ⊢
  simp only [Units.val_inv_eq_inv_val]
  simp only [actualSigma]
  field_simp [hAlphaE, hAlphaTarget, hH, hg]

/-- A candidate-regular base-field point on a nonsplit fiber supplies an
actual quadratic norm-`sigma` seed.  The extension-field fiber parameter is
retained explicitly, so later orbit wiring can multiply it by powers of the
nonsplit eigenvalue. -/
theorem exists_actualShiftedNonsplitSeed
    (p : ℕ) [Fact p.Prime]
    (c u t : ZMod p) (x : Point (ZMod p))
    (hx : IsSolution (coefficients c) x) (hx1 : x.x1 = u)
    (htrace : t = trace c u)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (w : quadraticNormOneTorus p)
    (htraceW : quadraticNormOneTrace p w = t) :
    ∃ h : (quadraticFiniteField p)ˣ,
      ∃ S : ↥(quadraticNormFiber p
        (actualSigmaUnit c u t
          (MiddleGame.actualSigma_ne_zero_of_candidateRegular
            c u t htrace hregular))),
        Opening.mapPoint
            (algebraMap (ZMod p) (quadraticFiniteField p)) x =
          fiberPoint
            (algebraMap (ZMod p) (quadraticFiniteField p) c)
            (algebraMap (ZMod p) (quadraticFiniteField p) u)
            (algebraMap (ZMod p) (quadraticFiniteField p) t)
            ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)
            (h : quadraticFiniteField p) ∧
        (S.1 : quadraticFiniteField p) =
          algebraMap (ZMod p) (quadraticFiniteField p) (actualAlpha c) *
            (h : quadraticFiniteField p) := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let cE : E := f c
  let uE : E := f u
  let tE : E := f t
  let xE : Point E := Opening.mapPoint f x
  let q : Eˣ := (w : Eˣ)
  have hxE : IsSolution (coefficients cE) xE := by
    simpa [cE, xE] using Opening.isSolution_mapPoint_symmetric f c x hx
  have hx1E : xE.x1 = uE := by
    simpa [xE, uE, Opening.mapPoint] using congrArg f hx1
  have htraceE : tE = trace cE uE := by
    dsimp [tE, cE, uE]
    rw [htrace, Opening.map_trace]
  have hregularE : OrderedTraceCandidateRegular cE cE cE tE :=
    Opening.orderedTraceCandidateRegular_map f f.injective hregular
  have hDE : discriminant tE ≠ 0 := by
    simpa [discriminant] using hregularE.1
  have hproductE : centeredFiberProduct cE uE tE ≠ 0 :=
    MiddleGame.centeredFiberProduct_ne_zero_of_candidateRegular
      cE uE tE htraceE hregularE
  have heigen : tE = splitTorusTrace q := by
    dsimp [tE, q, f, E]
    rw [← htraceW]
    exact algebraMap_quadraticNormOneTrace p w
  let parameter : E :=
    MiddleGame.actualFiberParameter cE uE tE q xE
  have hparameter : parameter ≠ 0 := by
    exact MiddleGame.actualFiberParameter_ne_zero
      cE uE tE q xE hx1E hxE htraceE heigen hDE hproductE
  let h : Eˣ := Units.mk0 parameter hparameter
  have hpoint :
      fiberPoint cE uE tE (q : E) (h : E) = xE := by
    simpa [h, parameter] using
      MiddleGame.fiberPoint_actualFiberParameter_eq
        cE uE tE q xE hx1E hxE htraceE heigen hDE hproductE
  let seedValue : E := f (actualAlpha c) * (h : E)
  have hAlphaBase : actualAlpha c ≠ 0 := by
    exact MiddleGame.actualAlpha_ne_zero c
      (MiddleGame.multiplier_ne_zero_of_candidateRegular
        c u t htrace hregular)
  have hseedValue : seedValue ≠ 0 :=
    mul_ne_zero ((map_ne_zero_iff f f.injective).mpr hAlphaBase)
      (Units.ne_zero h)
  let seedUnit : Eˣ := Units.mk0 seedValue hseedValue
  have hparameterFrobenius :
      (parameter : E) ^ p =
        MiddleGame.actualFiberReciprocalParameter cE uE tE q xE := by
    simpa [parameter, cE, uE, tE, q, xE, f, E] using
      actualFiberParameter_frobenius p c u t w x
  have hparameterProduct :
      parameter *
          MiddleGame.actualFiberReciprocalParameter cE uE tE q xE =
        centeredFiberProduct cE uE tE := by
    exact MiddleGame.actualFiberParameter_mul_reciprocal_eq_centeredFiberProduct
      cE uE tE q xE hx1E hxE htraceE heigen hDE
  have hseedNorm :
      Algebra.norm (ZMod p) (seedValue : E) = actualSigma c u t := by
    apply f.injective
    rw [algebraMap_quadraticNorm]
    have hAlphaFrobenius : (f (actualAlpha c)) ^ p = f (actualAlpha c) := by
      simpa [f, E] using algebraMap_zmod_pow_card p (actualAlpha c)
    change
      (f (actualAlpha c) * parameter) *
          (f (actualAlpha c) * parameter) ^ p =
        f (actualSigma c u t)
    rw [mul_pow, hAlphaFrobenius, hparameterFrobenius]
    calc
      f (actualAlpha c) * parameter *
            (f (actualAlpha c) *
              MiddleGame.actualFiberReciprocalParameter cE uE tE q xE) =
          f (actualAlpha c) * f (actualAlpha c) *
            (parameter *
              MiddleGame.actualFiberReciprocalParameter cE uE tE q xE) := by
            ring
      _ = f (actualAlpha c) * f (actualAlpha c) *
            centeredFiberProduct cE uE tE := by
          rw [hparameterProduct]
      _ = f (actualSigma c u t) := by
          rw [map_actualSigma]
          simp [actualSigma, actualAlpha, actualBeta, multiplier,
            cE, uE, tE]
          rw [map_ofNat]
          ring
  let sigmaUnit : (ZMod p)ˣ :=
    actualSigmaUnit c u t
      (MiddleGame.actualSigma_ne_zero_of_candidateRegular
        c u t htrace hregular)
  have hseedMem : seedUnit ∈ quadraticNormFiber p sigmaUnit := by
    change quadraticNormUnitsHom p seedUnit ∈ ({sigmaUnit} : Set (ZMod p)ˣ)
    rw [Set.mem_singleton_iff]
    apply Units.ext
    exact hseedNorm
  let S : ↥(quadraticNormFiber p sigmaUnit) := ⟨seedUnit, hseedMem⟩
  refine ⟨h, S, ?_, ?_⟩
  · simpa [cE, uE, tE, q, xE, f, E] using hpoint.symm
  · rfl

/-- Every parameter in the complementary power image of a nonsplit
eigenvalue is reached by a forward actual one-step iterate, and its adjacent
trace is the shifted quadratic trace of the actual norm-`sigma` seed. -/
theorem exists_iterate_actualNonsplitSeedTrace
    (p : ℕ) [Fact p.Prime]
    (c u t : ZMod p) (x : Point (ZMod p))
    (htrace : t = trace c u)
    (hregular : OrderedTraceCandidateRegular c c c t)
    (w : quadraticNormOneTorus p)
    (htraceW : quadraticNormOneTrace p w = t)
    (h : (quadraticFiniteField p)ˣ)
    (S : ↥(quadraticNormFiber p
      (actualSigmaUnit c u t
        (MiddleGame.actualSigma_ne_zero_of_candidateRegular
          c u t htrace hregular))))
    (hpoint :
      Opening.mapPoint
          (algebraMap (ZMod p) (quadraticFiniteField p)) x =
        fiberPoint
          (algebraMap (ZMod p) (quadraticFiniteField p) c)
          (algebraMap (ZMod p) (quadraticFiniteField p) u)
          (algebraMap (ZMod p) (quadraticFiniteField p) t)
          (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p))
          (h : quadraticFiniteField p))
    (hS :
      (S.1 : quadraticFiniteField p) =
        algebraMap (ZMod p) (quadraticFiniteField p) (actualAlpha c) *
          (h : quadraticFiniteField p))
    (g : (powMonoidHom
      (Nat.card (quadraticNormOneTorus p) / orderOf w) :
        quadraticNormOneTorus p →* quadraticNormOneTorus p).range) :
    ∃ n : ℕ,
      trace c (((oneStep1 c)^[n]) x).x2 =
        Algebra.trace (ZMod p) (quadraticFiniteField p)
            ((S.1 : quadraticFiniteField p) *
              ((g.1 : (quadraticFiniteField p)ˣ) :
                quadraticFiniteField p)) +
          actualGamma c u t := by
  let E := quadraticFiniteField p
  let f : ZMod p →+* E := algebraMap (ZMod p) E
  let cE : E := f c
  let uE : E := f u
  let tE : E := f t
  let q : Eˣ := (w : Eˣ)
  have htraceE : tE = trace cE uE := by
    dsimp [tE, cE, uE]
    rw [htrace, Opening.map_trace]
  have heigen : tE = splitTorusTrace q := by
    dsimp [tE, q, f, E]
    rw [← htraceW]
    exact algebraMap_quadraticNormOneTrace p w
  have hregularE : OrderedTraceCandidateRegular cE cE cE tE :=
    Opening.orderedTraceCandidateRegular_map f f.injective hregular
  have hDE : discriminant tE ≠ 0 := by
    simpa [discriminant] using hregularE.1
  have htE : tE ≠ 2 := ne_two_of_discriminant_ne_zero hDE
  obtain ⟨n, hn⟩ :=
    BGS.Markoff.exists_pow_eq_of_mem_complementaryPowerRange w g
  refine ⟨n, ?_⟩
  apply f.injective
  have hmapIterate :=
    MiddleGame.mapPoint_iterate_oneStep1 f c x n
  have hiterated :
      Opening.mapPoint f (((oneStep1 c)^[n]) x) =
        fiberPoint cE uE tE (q : E)
          (((h * (g.1 : (quadraticFiniteField p)ˣ)) : Eˣ) : E) := by
    rw [hmapIterate, hpoint]
    rw [MiddleGame.iterate_oneStep1_fiberPoint_eq_pow_mul
      cE uE tE (q : E) (h : E)
      (Units.ne_zero q) (Units.ne_zero h)
      (by
        simpa only [splitTorusTrace, Units.val_inv_eq_inv_val] using
          heigen)
      htraceE htE n]
    congr 1
    have hnE :
        ((q ^ n : Eˣ) : E) =
          (((g.1 : (quadraticFiniteField p)ˣ)) : E) := by
      exact congrArg
        (fun z : quadraticNormOneTorus p =>
          (((z : (quadraticFiniteField p)ˣ)) : E)) hn
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, mul_comm] using
      congrArg (fun z : E => z * (h : E)) hnE
  calc
    f (trace c (((oneStep1 c)^[n]) x).x2) =
        trace cE (Opening.mapPoint f (((oneStep1 c)^[n]) x)).x2 := by
          exact Opening.map_trace f c (((oneStep1 c)^[n]) x).x2
    _ = trace cE
        (fiberPoint cE uE tE (q : E)
          (((h * (g.1 : (quadraticFiniteField p)ˣ)) : Eˣ) : E)).x2 := by
          rw [hiterated]
    _ = f
        (Algebra.trace (ZMod p) (quadraticFiniteField p)
            ((S.1 : quadraticFiniteField p) *
              ((g.1 : (quadraticFiniteField p)ˣ) :
                quadraticFiniteField p)) +
          actualGamma c u t) := by
          symm
          simpa [cE, uE, tE, q, f, E] using
            algebraMap_shiftedActualSeedTrace_eq_trace_fiberPoint_x2
              p c u t
              (MiddleGame.actualSigma_ne_zero_of_candidateRegular
                c u t htrace hregular)
              (MiddleGame.actualAlpha_ne_zero c
                (MiddleGame.multiplier_ne_zero_of_candidateRegular
                  c u t htrace hregular))
              h S hS w g.1

end

end GenMarkoff.Symmetric.Endgame.Nonsplit
