import GenMarkoff.TraceCurve.ShiftedCoverIrreducibility
import BGS.Algebra.KummerEigencharacterDescent

/-!
# Common-prime Kummer independence for shifted trace covers

This module adapts the pinned BGS eigencharacter-descent argument to the
shifted trace curve.  It handles primes which divide both covering exponents.
The odd-prime branch uses the mixed-power obstruction already proved for the
shifted base coordinates.  The common prime `2` is controlled by the explicit
quadratic obstruction `shiftedTraceEvenObstruction`.
-/

namespace GenMarkoff

open Polynomial AdjoinRoot

noncomputable section

variable {K : Type*} [Field K]

private lemma shiftedTraceBaseUV_not_square
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (c : ShiftedTraceBaseFunctionField sigma gamma) :
    letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    c ^ 2 ≠
      shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible
    sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  let baseField := ShiftedTraceBaseFunctionField sigma gamma
  let U : baseField := shiftedTraceBaseU sigma gamma
  let V : baseField := shiftedTraceBaseV sigma gamma
  have hV : V ≠ 0 := by
    intro hzero
    have hquadratic := shiftedTraceBaseV_quadraticEquation
      sigma gamma h2 hsigma
    change shiftedTraceBaseV sigma gamma = 0 at hzero
    rw [hzero] at hquadratic
    have hrootNormZero : shiftedTraceRootNorm sigma = 0 :=
      (algebraMap (RatFunc K) baseField).injective (by simpa using hquadratic)
    exact shiftedTraceRootNorm_ne_zero sigma hsigma hrootNormZero
  have hU : U ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc K) baseField).injective).mpr
      RatFunc.X_ne_zero
  have hUV : U * V ≠ 0 := mul_ne_zero hU hV
  intro hpow
  have hc : c ≠ 0 := by
    intro hzero
    apply hUV
    simpa [hzero] using hpow.symm
  letI : Module.Finite (RatFunc K) baseField :=
    (shiftedTraceBasePolynomial_monic sigma gamma).finite_adjoinRoot
  have hnorm := congrArg (Algebra.norm (RatFunc K)) hpow
  rw [map_pow] at hnorm
  have hnormC : Algebra.norm (RatFunc K) c ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hc
  have hdegree := congrArg RatFunc.intDegree hnorm
  rw [RatFunc.intDegree_pow _ hnormC,
    norm_shiftedTraceBaseU_mul_V_intDegree sigma gamma h2 hsigma] at hdegree
  omega

/-- The second shifted radicand is not a `q`-th power after adjoining an
`e`-th root of `V`, when the prime `q` divides `e`.  The characteristic
hypothesis is retained explicitly for the later separable cover boundary. -/
theorem shiftedTraceXiRadicand_not_primePower_of_commonPrime
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hsigmaOne : sigma ≠ 1)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (i : K) (hi : i ^ 2 = -1)
    (e : ℕ) (he : 0 < e) (_heChar : (e : K) ≠ 0)
    (zeta : K) (hzeta : IsPrimitiveRoot zeta e)
    (q : ℕ) (hq : q.Prime) (hqe : q ∣ e)
    (z : letI : Fact
          (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
          ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
        letI : Fact (Irreducible
          (shiftedTraceEtaKummerPolynomial sigma gamma e)) :=
          ⟨shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
            sigma gamma h2 hsigma i hi e he⟩
        ShiftedTraceEtaFunctionField sigma gamma e) :
    letI : Fact (Irreducible
        (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    letI : Fact (Irreducible
        (shiftedTraceEtaKummerPolynomial sigma gamma e)) :=
      ⟨shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
        sigma gamma h2 hsigma i hi e he⟩
    z ^ q ≠ shiftedTraceXiRadicand sigma gamma e := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible
    sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  let hEtaIrred := shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma gamma h2 hsigma i hi e he
  letI : Fact (Irreducible
      (shiftedTraceEtaKummerPolynomial sigma gamma e)) := ⟨hEtaIrred⟩
  let baseField := ShiftedTraceBaseFunctionField sigma gamma
  let etaField := ShiftedTraceEtaFunctionField sigma gamma e
  let U : baseField := shiftedTraceBaseU sigma gamma
  let V : baseField := shiftedTraceBaseV sigma gamma
  have hV : V ≠ 0 := by
    intro hzero
    have hquadratic := shiftedTraceBaseV_quadraticEquation
      sigma gamma h2 hsigma
    change shiftedTraceBaseV sigma gamma = 0 at hzero
    rw [hzero] at hquadratic
    have hrootNormZero : shiftedTraceRootNorm sigma = 0 :=
      (algebraMap (RatFunc K) baseField).injective (by simpa using hquadratic)
    exact shiftedTraceRootNorm_ne_zero sigma hsigma hrootNormZero
  have hU : U ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc K) baseField).injective).mpr
      RatFunc.X_ne_zero
  have hUV : U * V ≠ 0 := mul_ne_zero hU hV
  intro hpow
  have hzetaBase : IsPrimitiveRoot (algebraMap K baseField zeta) e :=
    hzeta.map_of_injective (algebraMap K baseField).injective
  have hpowBase : z ^ q = algebraMap baseField etaField (U * V) := by
    change z ^ q = algebraMap
      (ShiftedTraceBaseFunctionField sigma gamma)
      (ShiftedTraceEtaFunctionField sigma gamma e)
      (shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma)
    exact hpow
  obtain ⟨k, hklt, hdiv, c, hc⟩ :=
    BGS.Algebra.exists_rootMonomial_of_primePower_mem_base
      (v := shiftedTraceBaseV sigma gamma)
      (ζ := algebraMap K (ShiftedTraceBaseFunctionField sigma gamma) zeta)
      (a := shiftedTraceBaseU sigma gamma * shiftedTraceBaseV sigma gamma)
      he hzetaBase (by
        simpa [shiftedTraceEtaKummerPolynomial] using hEtaIrred)
      hq hqe z hpowBase
  have hc' : z = algebraMap baseField etaField c *
      AdjoinRoot.root
        (shiftedTraceEtaKummerPolynomial sigma gamma e) ^ k := by
    change z = algebraMap baseField etaField c *
      AdjoinRoot.root
        (shiftedTraceEtaKummerPolynomial sigma gamma e) ^ k at hc
    exact hc
  let r := q * k / e
  have hrlt : r < q := by
    apply (Nat.div_lt_iff_lt_mul he).2
    simpa [Nat.mul_comm] using (Nat.mul_lt_mul_left hq.pos).2 hklt
  have hqk : e * r = q * k := Nat.mul_div_cancel' hdiv
  have hetaRoot :
      (AdjoinRoot.root
        (shiftedTraceEtaKummerPolynomial sigma gamma e)) ^ e =
        algebraMap baseField etaField V := by
    apply sub_eq_zero.mp
    have h := AdjoinRoot.eval₂_root
      (shiftedTraceEtaKummerPolynomial sigma gamma e)
    rw [shiftedTraceEtaKummerPolynomial] at h
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at h
    rw [← AdjoinRoot.algebraMap_eq] at h
    exact h
  have hetaPow :
      (AdjoinRoot.root
        (shiftedTraceEtaKummerPolynomial sigma gamma e)) ^ (q * k) =
        algebraMap baseField etaField (V ^ r) := by
    calc
      (AdjoinRoot.root
          (shiftedTraceEtaKummerPolynomial sigma gamma e)) ^ (q * k) =
          (AdjoinRoot.root
            (shiftedTraceEtaKummerPolynomial sigma gamma e)) ^ (e * r) := by
            rw [hqk]
      _ = ((AdjoinRoot.root
          (shiftedTraceEtaKummerPolynomial sigma gamma e)) ^ e) ^ r := by
            rw [pow_mul]
      _ = (algebraMap baseField etaField V) ^ r := by rw [hetaRoot]
      _ = algebraMap baseField etaField (V ^ r) := by rw [map_pow]
  have hbaseEq : c ^ q * V ^ r = U * V := by
    apply (algebraMap baseField etaField).injective
    calc
      algebraMap baseField etaField (c ^ q * V ^ r) =
          (algebraMap baseField etaField c) ^ q *
            (AdjoinRoot.root
              (shiftedTraceEtaKummerPolynomial sigma gamma e)) ^
                (q * k) := by
              rw [map_mul, map_pow, hetaPow]
      _ = (algebraMap baseField etaField c *
            AdjoinRoot.root
              (shiftedTraceEtaKummerPolynomial sigma gamma e) ^ k) ^ q := by
              rw [mul_pow, ← pow_mul, Nat.mul_comm q k]
      _ = z ^ q := by rw [← hc']
      _ = algebraMap baseField etaField (U * V) := by
        simpa [shiftedTraceXiRadicand, U, V, baseField, etaField] using hpow
  by_cases hqTwo : q = 2
  · subst q
    have hrCases : r = 0 ∨ r = 1 := by
      generalize hrr : r = rr at hrlt ⊢
      omega
    rcases hrCases with hrZero | hrOne
    · apply shiftedTraceBaseUV_not_square sigma gamma h2 hsigma c
      simpa [hrZero, U, V, baseField] using hbaseEq
    · have hcSquareU : c ^ 2 = U := by
        apply mul_right_cancel₀ hV
        simpa [hrOne, pow_one, mul_assoc] using hbaseEq
      apply shiftedTraceBaseU_not_isSquare
        sigma gamma h2 hsigma hD2
      refine ⟨c, ?_⟩
      simpa [pow_two] using hcSquareU.symm
  · by_cases hrZero : r = 0
    · apply shiftedTraceBaseCoordinates_mixedPower_ne_oddPrimePower
        sigma gamma h2 hsigma hsigmaOne q 1 0 hq hqTwo
          hq.one_lt hq.pos (by simp) c
      simpa [hrZero, U, V, baseField] using hbaseEq
    · have hrPositive : 0 < r := Nat.pos_of_ne_zero hrZero
      have hrLe : r ≤ q := Nat.le_of_lt hrlt
      have hEq : (c * V) ^ q = (U * V) ^ 1 * V ^ (q - r) := by
        rw [mul_pow, pow_one]
        have hv : V ^ q = V ^ r * V ^ (q - r) := by
          rw [← pow_add, Nat.add_sub_of_le hrLe]
        calc
          c ^ q * V ^ q = c ^ q * (V ^ r * V ^ (q - r)) := by rw [hv]
          _ = (c ^ q * V ^ r) * V ^ (q - r) := by rw [mul_assoc]
          _ = (U * V) * V ^ (q - r) := by rw [hbaseEq]
      apply shiftedTraceBaseCoordinates_mixedPower_ne_oddPrimePower
        sigma gamma h2 hsigma hsigmaOne q 1 (q - r) hq hqTwo
          hq.one_lt
          (Nat.sub_lt (Nat.pos_of_ne_zero hq.ne_zero) hrPositive)
          (by simp) (c * V)
      simpa [U, V, baseField] using hEq

/-- With the required roots of unity in the constant field, the second
shifted Kummer polynomial is irreducible for arbitrary positive exponents. -/
theorem shiftedTraceXiKummerPolynomial_irreducible_of_primitiveRoot
    (sigma gamma : K) (h2 : (2 : K) ≠ 0) (hsigma : sigma ≠ 0)
    (hsigmaOne : sigma ≠ 1)
    (hD2 : shiftedTraceEvenObstruction sigma gamma ≠ 0)
    (i : K) (hi : i ^ 2 = -1)
    (e d : ℕ) (he : 0 < e) (heChar : (e : K) ≠ 0) (hd : 0 < d)
    (zeta : K) (hzeta : IsPrimitiveRoot zeta e) :
    letI : Fact (Irreducible
        (shiftedTraceBasePolynomial sigma gamma)) :=
      ⟨shiftedTraceBasePolynomial_irreducible sigma gamma h2 hsigma⟩
    letI : Fact (Irreducible
        (shiftedTraceEtaKummerPolynomial sigma gamma e)) :=
      ⟨shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
        sigma gamma h2 hsigma i hi e he⟩
    Irreducible (shiftedTraceXiKummerPolynomial sigma gamma e d) := by
  let hBaseIrred := shiftedTraceBasePolynomial_irreducible
    sigma gamma h2 hsigma
  letI : Fact (Irreducible (shiftedTraceBasePolynomial sigma gamma)) :=
    ⟨hBaseIrred⟩
  let hEtaIrred := shiftedTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma gamma h2 hsigma i hi e he
  letI : Fact (Irreducible
      (shiftedTraceEtaKummerPolynomial sigma gamma e)) := ⟨hEtaIrred⟩
  rw [shiftedTraceXiKummerPolynomial]
  apply BGS.Markoff.X_pow_sub_C_irreducible_of_sqrt_neg_one
    (algebraMap K (ShiftedTraceEtaFunctionField sigma gamma e) i)
  · rw [← map_pow, hi, map_neg, map_one]
  · exact hd.ne'
  · intro q hq _hqd z
    by_cases hqe : q ∣ e
    · exact shiftedTraceXiRadicand_not_primePower_of_commonPrime
        sigma gamma h2 hsigma hsigmaOne hD2 i hi e he heChar
        zeta hzeta q hq hqe z
    · exact shiftedTraceXiRadicand_not_primePower_of_not_dvd
        sigma gamma h2 hsigma i hi e he q hq hqe z

end

end GenMarkoff
