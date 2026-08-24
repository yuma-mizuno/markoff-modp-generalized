import BGS.NumberTheory.ExplicitDivisorBound
import BGS.Markoff.Endgame.PrimitiveInclusionExclusion

namespace GenMarkoff.General.Explicit

open scoped Topology

opaque analyticDivisorMomentExponentData :
    {n : ℕ // n = 2 ^ 512} :=
  ⟨2 ^ 512, rfl⟩

def analyticDivisorMomentExponent : ℕ :=
  analyticDivisorMomentExponentData.1

theorem analyticDivisorMomentExponent_eq :
    analyticDivisorMomentExponent = 2 ^ 512 :=
  analyticDivisorMomentExponentData.2

opaque analyticDivisorMomentBaseData :
    {n : ℕ // n = 512 ^ 512} :=
  ⟨512 ^ 512, rfl⟩

def analyticDivisorMomentBase : ℕ :=
  analyticDivisorMomentBaseData.1

theorem analyticDivisorMomentBase_eq :
    analyticDivisorMomentBase = 512 ^ 512 :=
  analyticDivisorMomentBaseData.2

theorem analyticDivisorMomentBase_pos :
    0 < analyticDivisorMomentBase := by
  rw [analyticDivisorMomentBase_eq]
  positivity

opaque analyticDivisorMomentCoreData :
    {n : ℕ //
      n = analyticDivisorMomentBase ^ analyticDivisorMomentExponent} :=
  ⟨analyticDivisorMomentBase ^ analyticDivisorMomentExponent, rfl⟩

def analyticDivisorMomentCore : ℕ :=
  analyticDivisorMomentCoreData.1

theorem analyticDivisorMomentCore_eq :
    analyticDivisorMomentCore =
      analyticDivisorMomentBase ^ analyticDivisorMomentExponent :=
  analyticDivisorMomentCoreData.2

theorem analyticDivisorMomentCore_pos :
    0 < analyticDivisorMomentCore := by
  rw [analyticDivisorMomentCore_eq]
  exact pow_pos analyticDivisorMomentBase_pos _

opaque analyticDivisorMomentConstantData :
    {n : ℕ //
      n = 2 ^ 512 * analyticDivisorMomentCore} :=
  ⟨2 ^ 512 * analyticDivisorMomentCore, rfl⟩

def analyticDivisorMomentConstant : ℕ :=
  analyticDivisorMomentConstantData.1

theorem analyticDivisorMomentConstant_eq :
    analyticDivisorMomentConstant =
      2 ^ 512 * analyticDivisorMomentCore :=
  analyticDivisorMomentConstantData.2

theorem analyticDivisorMomentConstant_eq_direct :
    analyticDivisorMomentConstant =
      2 ^ 512 * (512 ^ 512) ^ (2 ^ 512) := by
  rw [analyticDivisorMomentConstant_eq,
    analyticDivisorMomentCore_eq,
    analyticDivisorMomentBase_eq,
    analyticDivisorMomentExponent_eq]

theorem analyticDivisorMomentConstant_pos :
    0 < analyticDivisorMomentConstant := by
  rw [analyticDivisorMomentConstant_eq]
  exact Nat.mul_pos (pow_pos (by norm_num) _)
    analyticDivisorMomentCore_pos

opaque analyticCutoffData :
    {n : ℕ // n = analyticDivisorMomentConstant + 1} :=
  ⟨analyticDivisorMomentConstant + 1, rfl⟩

def analyticCutoff : ℕ := analyticCutoffData.1

theorem analyticCutoff_eq :
    analyticCutoff = analyticDivisorMomentConstant + 1 :=
  analyticCutoffData.2

theorem analyticCutoff_gt_one : 1 < analyticCutoff := by
  rw [analyticCutoff_eq]
  have hpositive := analyticDivisorMomentConstant_pos
  omega

#guard_msgs (drop warning) in
theorem five_le_analyticCutoff : 5 ≤ analyticCutoff := by
  rw [analyticCutoff_eq, analyticDivisorMomentConstant_eq]
  have hcoreOne : 1 ≤ analyticDivisorMomentCore :=
    analyticDivisorMomentCore_pos
  have hfour : 4 ≤ 2 ^ 512 := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 512 :=
        Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hproduct :
      4 ≤ 2 ^ 512 * analyticDivisorMomentCore := by
    calc
      4 = 4 * 1 := by omega
      _ ≤ 2 ^ 512 * analyticDivisorMomentCore :=
        Nat.mul_le_mul hfour hcoreOne
  omega

#guard_msgs (drop warning) in
theorem seven_le_analyticCutoff : 7 ≤ analyticCutoff := by
  rw [analyticCutoff_eq, analyticDivisorMomentConstant_eq]
  have hcoreOne : 1 ≤ analyticDivisorMomentCore :=
    analyticDivisorMomentCore_pos
  have hsix : 6 ≤ 2 ^ 512 := by
    calc
      6 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ 512 :=
        Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hproduct :
      6 ≤ 2 ^ 512 * analyticDivisorMomentCore := by
    calc
      6 = 6 * 1 := by omega
      _ ≤ 2 ^ 512 * analyticDivisorMomentCore :=
        Nat.mul_le_mul hsix hcoreOne
  omega

theorem analyticDivisorMomentConstant_lt_of_cutoff_le
    {p : ℕ} (hp : analyticCutoff ≤ p) :
    analyticDivisorMomentConstant < p := by
  rw [analyticCutoff_eq] at hp
  omega

#guard_msgs (drop warning) in
theorem card_divisors_pow_fiveHundredTwelve_le
    (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card ^ 512 ≤ analyticDivisorMomentCore * n := by
  let D := analyticDivisorMomentBase
  have hD : 0 < D := analyticDivisorMomentBase_pos
  have hfactor : ∀ p ∈ n.primeFactors,
      (n.factorization p + 1) ^ 512 ≤
        (if p < 2 ^ 512 then D else 1) * p ^ n.factorization p := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpTwo : 2 ≤ p := hpPrime.two_le
    have haPos : 0 < n.factorization p :=
      hpPrime.factorization_pos_of_dvd hn
        (Nat.dvd_of_mem_primeFactors hp)
    by_cases hpSmall : p < 2 ^ 512
    · rw [if_pos hpSmall]
      have hbase :
          (n.factorization p + 1) ^ 512 ≤
            (512 ^ 512) * 2 ^ n.factorization p := by
        exact
          BGS.NumberTheory.pow_succ_le_self_pow_mul_two_pow
            512 (by norm_num) (n.factorization p)
      rw [← analyticDivisorMomentBase_eq] at hbase
      exact hbase.trans
        (Nat.mul_le_mul_left D
          (Nat.pow_le_pow_left hpTwo _))
    · rw [if_neg hpSmall, one_mul]
      have hsucc : n.factorization p + 1 ≤ 2 ^ n.factorization p :=
        Nat.succ_le_of_lt (n.factorization p).lt_two_pow_self
      calc
        (n.factorization p + 1) ^ 512 ≤
            (2 ^ n.factorization p) ^ 512 :=
          Nat.pow_le_pow_left hsucc 512
        _ = (2 ^ 512) ^ n.factorization p := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ p ^ n.factorization p :=
          Nat.pow_le_pow_left (le_of_not_gt hpSmall) _
  have hsmallCard :
      (n.primeFactors.filter fun p => p < 2 ^ 512).card ≤
        analyticDivisorMomentExponent := by
    rw [analyticDivisorMomentExponent_eq]
    calc
      (n.primeFactors.filter fun p => p < 2 ^ 512).card ≤
          (Finset.range (2 ^ 512)).card :=
        Finset.card_le_card (by
          intro p hp
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = 2 ^ 512 := Finset.card_range _
  rw [Nat.card_divisors hn, ← Finset.prod_pow]
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 512) ≤
        ∏ p ∈ n.primeFactors,
          ((if p < 2 ^ 512 then D else 1) *
            p ^ n.factorization p) :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hfactor
    _ = D ^ (n.primeFactors.filter fun p => p < 2 ^ 512).card * n := by
      rw [Finset.prod_mul_distrib,
        ← Nat.prod_primeFactors_pow_factorization hn]
      simp [Finset.prod_ite]
    _ ≤ D ^ analyticDivisorMomentExponent * n := by
      exact Nat.mul_le_mul_right n
        (Nat.pow_le_pow_right hD hsmallCard)
    _ = analyticDivisorMomentCore * n := by
      rw [analyticDivisorMomentCore_eq]

#guard_msgs (drop warning) in
theorem divisor_sum_pow_fiveHundredTwelve_le
    {p : ℕ} (hp : 2 ≤ p) :
    ((p - 1).divisors.card + (p + 1).divisors.card) ^ 512 ≤
      analyticDivisorMomentConstant * p := by
  have hminusNe : p - 1 ≠ 0 := by omega
  have hplusNe : p + 1 ≠ 0 := by omega
  have hminus :=
    card_divisors_pow_fiveHundredTwelve_le (p - 1) hminusNe
  have hplus :=
    card_divisors_pow_fiveHundredTwelve_le (p + 1) hplusNe
  calc
    ((p - 1).divisors.card + (p + 1).divisors.card) ^ 512 ≤
        2 ^ (512 - 1) *
          ((p - 1).divisors.card ^ 512 +
            (p + 1).divisors.card ^ 512) :=
      add_pow_le (Nat.zero_le _) (Nat.zero_le _) 512
    _ ≤ 2 ^ (512 - 1) *
        ((analyticDivisorMomentCore * (p - 1)) +
          (analyticDivisorMomentCore * (p + 1))) := by
      gcongr
    _ = analyticDivisorMomentConstant * p := by
      let D := analyticDivisorMomentCore
      have hsub : p - 1 + (p + 1) = 2 * p := by omega
      rw [analyticDivisorMomentConstant_eq]
      change 2 ^ (512 - 1) * (D * (p - 1) + D * (p + 1)) =
        (2 ^ 512 * D) * p
      calc
        2 ^ (512 - 1) * (D * (p - 1) + D * (p + 1)) =
            2 ^ 511 * D * (p - 1 + (p + 1)) := by
          norm_num
          ring
        _ = 2 ^ 511 * D * (2 * p) := by rw [hsub]
        _ = (2 ^ 512 * D) * p := by
          have hpow : 2 ^ 512 = 2 ^ 511 * 2 := by
            simpa only using (pow_succ 2 511)
          rw [hpow]
          ring

#guard_msgs (drop warning) in
theorem divisor_sum_lt_rpow_one_div_twoHundredFiftySix
    {p : ℕ} (hp : analyticCutoff ≤ p) :
    (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) <
      (p : ℝ) ^ (1 / 256 : ℝ) := by
  let T := (p - 1).divisors.card + (p + 1).divisors.card
  have hpTwo : 2 ≤ p := by
    have : 2 ≤ analyticCutoff := analyticCutoff_gt_one
    omega
  have hmoment : T ^ 512 ≤ analyticDivisorMomentConstant * p :=
    divisor_sum_pow_fiveHundredTwelve_le hpTwo
  have hconstant : analyticDivisorMomentConstant < p :=
    analyticDivisorMomentConstant_lt_of_cutoff_le hp
  have hpowNat : T ^ 512 < p ^ 2 := by
    calc
      T ^ 512 ≤ analyticDivisorMomentConstant * p := hmoment
      _ < p * p := Nat.mul_lt_mul_of_pos_right hconstant (by omega)
      _ = p ^ 2 := by ring
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : (T : ℝ) ^ 512 < (p : ℝ) ^ 2 := by
    exact_mod_cast hpowNat
  have hrootPow :
      ((p : ℝ) ^ (1 / 256 : ℝ)) ^ 512 = (p : ℝ) ^ 2 := by
    calc
      ((p : ℝ) ^ (1 / 256 : ℝ)) ^ 512 =
          (p : ℝ) ^ ((1 / 256 : ℝ) * 512) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 256 : ℝ) 512).symm
      _ = (p : ℝ) ^ 2 := by norm_num
  change (T : ℝ) < (p : ℝ) ^ (1 / 256 : ℝ)
  apply lt_of_pow_lt_pow_left₀ 512 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

#guard_msgs (drop warning) in
theorem small_fixed_lt_rpow_one_div_twoHundredFiftySix
    {p fixed : ℕ} (hp : analyticCutoff ≤ p)
    (hfixed : fixed ≤ 200000000) :
    (fixed : ℝ) < (p : ℝ) ^ (1 / 256 : ℝ) := by
  have hbase : fixed ≤ analyticDivisorMomentBase := by
    rw [analyticDivisorMomentBase_eq]
    calc
      fixed ≤ 200000000 := hfixed
      _ ≤ 512 ^ 4 := by norm_num
      _ ≤ 512 ^ 512 :=
        Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hexponent : 256 ≤ analyticDivisorMomentExponent := by
    rw [analyticDivisorMomentExponent_eq]
    calc
      256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ 512 :=
        Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hcore :
      fixed ^ 256 ≤ analyticDivisorMomentCore := by
    calc
      fixed ^ 256 ≤ analyticDivisorMomentBase ^ 256 :=
        Nat.pow_le_pow_left hbase _
      _ ≤ analyticDivisorMomentBase ^ analyticDivisorMomentExponent :=
        Nat.pow_le_pow_right analyticDivisorMomentBase_pos hexponent
      _ = analyticDivisorMomentCore := analyticDivisorMomentCore_eq.symm
  have hconstant :
      analyticDivisorMomentCore ≤ analyticDivisorMomentConstant := by
    rw [analyticDivisorMomentConstant_eq]
    have hone : 1 ≤ 2 ^ 512 :=
      Nat.one_le_pow _ _ (by norm_num)
    simpa only [one_mul] using
      Nat.mul_le_mul_right analyticDivisorMomentCore hone
  have hpowNat : fixed ^ 256 < p :=
    (hcore.trans hconstant).trans_lt
      (analyticDivisorMomentConstant_lt_of_cutoff_le hp)
  have hpNonnegative : (0 : ℝ) ≤ p := by positivity
  have hpowReal : (fixed : ℝ) ^ 256 < (p : ℝ) := by
    exact_mod_cast hpowNat
  have hrootPow :
      ((p : ℝ) ^ (1 / 256 : ℝ)) ^ 256 = (p : ℝ) := by
    calc
      ((p : ℝ) ^ (1 / 256 : ℝ)) ^ 256 =
          (p : ℝ) ^ ((1 / 256 : ℝ) * 256) :=
        (Real.rpow_mul_natCast hpNonnegative (1 / 256 : ℝ) 256).symm
      _ = (p : ℝ) := by norm_num
  apply lt_of_pow_lt_pow_left₀ 256 (Real.rpow_nonneg hpNonnegative _)
  rw [hrootPow]
  exact hpowReal

theorem primitiveTrace_explicitInequality
    {p orbitExponent coefficient : ℕ}
    (hp : analyticCutoff ≤ p)
    (horbit :
      (orbitExponent : ℝ) ≤
        2 * (p : ℝ) ^ (15 / 32 : ℝ))
    (hcoefficient : coefficient ≤ 1032) :
    (orbitExponent : ℝ) *
        ((p - 1).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  have hpRealOne : (1 : ℝ) < p := by
    exact_mod_cast analyticCutoff_gt_one.trans_le hp
  have hpRealPos : (0 : ℝ) < p := zero_lt_one.trans hpRealOne
  have hpRealNonnegative : (0 : ℝ) ≤ p := hpRealPos.le
  have hdivisorSum :=
    divisor_sum_lt_rpow_one_div_twoHundredFiftySix hp
  have hdivisor :
      ((p - 1).divisors.card : ℝ) ≤
        (p : ℝ) ^ (1 / 256 : ℝ) := by
    norm_num only [Nat.cast_add] at hdivisorSum
    exact
      (le_add_of_nonneg_right
        (Nat.cast_nonneg (p + 1).divisors.card)).trans
        hdivisorSum.le
  have hfixed :
      (2064 : ℝ) < (p : ℝ) ^ (1 / 256 : ℝ) := by
    exact
      small_fixed_lt_rpow_one_div_twoHundredFiftySix
        hp (by norm_num)
  have hsqrt :
      Real.sqrt (p : ℝ) = (p : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  calc
    (orbitExponent : ℝ) *
          ((p - 1).divisors.card : ℝ) ^ 2 *
            ((coefficient : ℝ) * Real.sqrt (p : ℝ)) ≤
        (2 * (p : ℝ) ^ (15 / 32 : ℝ)) *
          ((p : ℝ) ^ (1 / 256 : ℝ)) ^ 2 *
            (1032 * Real.sqrt (p : ℝ)) := by
      gcongr
      exact_mod_cast hcoefficient
    _ = 2064 *
        ((p : ℝ) ^ (15 / 32 : ℝ) *
          (((p : ℝ) ^ (1 / 256 : ℝ)) ^ 2 *
            (p : ℝ) ^ (1 / 2 : ℝ))) := by
      rw [hsqrt]
      ring
    _ = 2064 * (p : ℝ) ^ (125 / 128 : ℝ) := by
      rw [← Real.rpow_mul_natCast hpRealNonnegative
        (1 / 256 : ℝ) 2,
        ← Real.rpow_add hpRealPos,
        ← Real.rpow_add hpRealPos]
      congr 2
      norm_num
    _ < (p : ℝ) ^ (1 / 256 : ℝ) *
        (p : ℝ) ^ (125 / 128 : ℝ) := by
      exact mul_lt_mul_of_pos_right hfixed
        (Real.rpow_pos_of_pos hpRealPos _)
    _ = (p : ℝ) ^ (251 / 256 : ℝ) := by
      rw [← Real.rpow_add hpRealPos]
      congr 1
      norm_num
    _ < (p : ℝ) := by
      have hexponent : (251 / 256 : ℝ) < 1 := by norm_num
      simpa only [Real.rpow_one] using
        Real.rpow_lt_rpow_of_exponent_lt hpRealOne hexponent

/-- Fixed-exponent form used by the final connecting cage. -/
theorem primitiveTrace_explicitInequality_one
    {p coefficient : ℕ}
    (hp : analyticCutoff ≤ p)
    (hcoefficient : coefficient ≤ 1032) :
    (1 : ℝ) * ((p - 1).divisors.card : ℝ) ^ 2 *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  have hpRealOne : (1 : ℝ) < p := by
    exact_mod_cast analyticCutoff_gt_one.trans_le hp
  have hpowOne :
      (1 : ℝ) ≤ (p : ℝ) ^ (15 / 32 : ℝ) :=
    Real.one_le_rpow hpRealOne.le (by norm_num)
  simpa only [Nat.cast_one] using
    (primitiveTrace_explicitInequality
      (orbitExponent := 1) hp (by linarith) hcoefficient)

/-- Split-torus form of the closed primitive-trace certificate. -/
theorem primitiveTrace_explicitInequality_of_card_sub_one
    {p orbitExponent orbitOrder coefficient : ℕ}
    {delta : ℝ}
    (hp : analyticCutoff ≤ p)
    (hmul : orbitExponent * orbitOrder = p - 1)
    (horder :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orbitOrder)
    (hdelta : (1 : ℝ) / 32 ≤ delta)
    (hcoefficient : coefficient ≤ 1032) :
    (orbitExponent : ℝ) *
        ((p - 1).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  apply primitiveTrace_explicitInequality hp ?_ hcoefficient
  have hpNat : 0 < p :=
    Nat.zero_lt_one.trans (analyticCutoff_gt_one.trans_le hp)
  have horbit :=
    BGS.Markoff.orbitExponent_le_rpow_of_mul_order_eq_card_sub_one
      p orbitExponent orbitOrder hpNat hmul horder
  have hpRealOne : (1 : ℝ) ≤ p := by
    exact_mod_cast hpNat
  calc
    (orbitExponent : ℝ) ≤
        (p : ℝ) ^ ((1 : ℝ) / 2 - delta) := horbit
    _ ≤ (p : ℝ) ^ (15 / 32 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hpRealOne
      linarith
    _ ≤ 2 * (p : ℝ) ^ (15 / 32 : ℝ) := by
      have hnonnegative :
          (0 : ℝ) ≤ (p : ℝ) ^ (15 / 32 : ℝ) :=
        Real.rpow_nonneg (Nat.cast_nonneg p) _
      linarith

/-- Nonsplit-torus form of the closed primitive-trace certificate. -/
theorem primitiveTrace_explicitInequality_of_card_add_one
    {p orbitExponent orbitOrder coefficient : ℕ}
    {delta : ℝ}
    (hp : analyticCutoff ≤ p)
    (hmul : orbitExponent * orbitOrder = p + 1)
    (horder :
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ orbitOrder)
    (hdelta : (1 : ℝ) / 32 ≤ delta)
    (hcoefficient : coefficient ≤ 1032) :
    (orbitExponent : ℝ) *
        ((p - 1).divisors.card : ℝ) ^ 2 *
          ((coefficient : ℝ) * Real.sqrt (p : ℝ)) < p := by
  apply primitiveTrace_explicitInequality hp ?_ hcoefficient
  have hpNat : 0 < p :=
    Nat.zero_lt_one.trans (analyticCutoff_gt_one.trans_le hp)
  have horbit :=
    BGS.Markoff.orbitExponent_le_two_mul_rpow_of_mul_order_eq_card_add_one
      p orbitExponent orbitOrder hpNat hmul horder
  have hpRealOne : (1 : ℝ) ≤ p := by
    exact_mod_cast hpNat
  calc
    (orbitExponent : ℝ) ≤
        2 * (p : ℝ) ^ ((1 : ℝ) / 2 - delta) := horbit
    _ ≤ 2 * (p : ℝ) ^ (15 / 32 : ℝ) := by
      gcongr
      linarith

end GenMarkoff.General.Explicit
