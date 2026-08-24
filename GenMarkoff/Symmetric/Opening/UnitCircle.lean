import GenMarkoff.Symmetric.Opening.CyclotomicDefect
import BGS.Markoff.Opening.UnitCircle

/-!
# Unit-circle rigidity for the equal-coefficient family

For an admissible integral parameter `c`, the generalized cyclotomic defect
can vanish on the complex unit torus only at the three traces of the affine
origin.  The proof uses the integrality of `c`: after excluding `-2`, `-1`,
and `2`, the four remaining ranges are `c ≤ -3`, `c = 0`, `c = 1`, and
`3 ≤ c`.
-/

namespace GenMarkoff.Symmetric.Opening

private theorem affine_nonneg_on_zero_four
    {A B x : ℝ} (hx0 : 0 ≤ x) (hx4 : x ≤ 4)
    (h0 : 0 ≤ A) (h4 : 0 ≤ A + 4 * B) :
    0 ≤ A + x * B := by
  by_cases hB : 0 ≤ B
  · nlinarith [mul_nonneg hx0 hB]
  · have hB' : B ≤ 0 := le_of_not_ge hB
    have htail : 0 ≤ (x - 4) * B :=
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx4) hB'
    nlinarith

private theorem trilinear_corner_bound
    {u v w : ℝ}
    (hu0 : 0 ≤ u) (hu4 : u ≤ 4)
    (hv0 : 0 ≤ v) (hv4 : v ≤ 4)
    (hw0 : 0 ≤ w) (hw4 : w ≤ 4) :
    0 ≤ 4 - u - v - w + 2 * (u * v + u * w + v * w) - u * v * w := by
  have hzero : 0 ≤ 4 - u - v + 2 * u * v := by
    have h := affine_nonneg_on_zero_four (A := 4 - v) (B := -1 + 2 * v)
      hu0 hu4 (by linarith) (by nlinarith)
    nlinarith
  have hfour :
      0 ≤ (4 - u - v + 2 * u * v) +
        4 * (-1 + 2 * u + 2 * v - u * v) := by
    have h := affine_nonneg_on_zero_four
      (A := 7 * v) (B := 7 - 2 * v) hu0 hu4
      (by positivity : 0 ≤ 7 * v)
      (by nlinarith : 0 ≤ 7 * v + 4 * (7 - 2 * v))
    nlinarith
  have h := affine_nonneg_on_zero_four hw0 hw4 hzero hfour
  nlinarith

private theorem traceDefect_neg_three_lt_zero
    {t₁ t₂ t₃ : ℝ}
    (ht₁ : t₁ ∈ Set.Icc (-2 : ℝ) 2)
    (ht₂ : t₂ ∈ Set.Icc (-2 : ℝ) 2)
    (ht₃ : t₃ ∈ Set.Icc (-2 : ℝ) 2) :
    traceDefect (-3 : ℝ) t₁ t₂ t₃ < 0 := by
  have ht₁sq : t₁ ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht₁.2) (by linarith [ht₁.1] : 0 ≤ 2 + t₁)]
  have ht₂sq : t₂ ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht₂.2) (by linarith [ht₂.1] : 0 ≤ 2 + t₂)]
  have ht₃sq : t₃ ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht₃.2) (by linarith [ht₃.1] : 0 ≤ 2 + t₃)]
  let u := 2 - t₁
  let v := 2 - t₂
  let w := 2 - t₃
  have hu0 : 0 ≤ u := by dsimp [u]; linarith [ht₁.2]
  have hu4 : u ≤ 4 := by dsimp [u]; linarith [ht₁.1]
  have hv0 : 0 ≤ v := by dsimp [v]; linarith [ht₂.2]
  have hv4 : v ≤ 4 := by dsimp [v]; linarith [ht₂.1]
  have hw0 : 0 ≤ w := by dsimp [w]; linarith [ht₃.2]
  have hw4 : w ≤ 4 := by dsimp [w]; linarith [ht₃.1]
  have hcorner := trilinear_corner_bound hu0 hu4 hv0 hv4 hw0 hw4
  have hmultilinear :
      3 * (t₁ + t₂ + t₃) - t₁ * t₂ * t₃ ≤ 14 := by
    dsimp [u, v, w] at hcorner
    nlinarith
  rw [traceDefect]
  norm_num
  nlinarith

private theorem traceDefect_three_pos
    {t₁ t₂ t₃ : ℝ}
    (ht₁ : t₁ ∈ Set.Icc (-2 : ℝ) 2)
    (ht₂ : t₂ ∈ Set.Icc (-2 : ℝ) 2)
    (ht₃ : t₃ ∈ Set.Icc (-2 : ℝ) 2) :
    0 < traceDefect (3 : ℝ) t₁ t₂ t₃ := by
  let u := t₁ + 2
  let v := t₂ + 2
  let w := t₃ + 2
  have hu0 : 0 ≤ u := by dsimp [u]; linarith [ht₁.1]
  have hu4 : u ≤ 4 := by dsimp [u]; linarith [ht₁.2]
  have hv0 : 0 ≤ v := by dsimp [v]; linarith [ht₂.1]
  have hv4 : v ≤ 4 := by dsimp [v]; linarith [ht₂.2]
  have hw0 : 0 ≤ w := by dsimp [w]; linarith [ht₃.1]
  have hw4 : w ≤ 4 := by dsimp [w]; linarith [ht₃.2]
  have huv0 : 0 ≤ u * v := mul_nonneg hu0 hv0
  have huvw : u * v * w ≤ 4 * (u * v) :=
    by simpa [mul_comm] using mul_le_mul_of_nonneg_left hw4 huv0
  have hfouruv : 4 * (u * v) ≤ (u + v) ^ 2 := by
    nlinarith [sq_nonneg (u - v)]
  have hsum : (u + v) ^ 2 ≤ (u + v + w) ^ 2 := by
    have htail : 0 ≤ w * (2 * (u + v) + w) := by positivity
    nlinarith
  have hmain : u * v * w ≤ (u + v + w) ^ 2 :=
    huvw.trans (hfouruv.trans hsum)
  rw [traceDefect]
  norm_num
  dsimp [u, v, w] at hmain ⊢
  nlinarith

private theorem traceDefect_pos_of_three_le
    {c t₁ t₂ t₃ : ℝ} (hc : 3 ≤ c)
    (ht₁ : t₁ ∈ Set.Icc (-2 : ℝ) 2)
    (ht₂ : t₂ ∈ Set.Icc (-2 : ℝ) 2)
    (ht₃ : t₃ ∈ Set.Icc (-2 : ℝ) 2) :
    0 < traceDefect c t₁ t₂ t₃ := by
  have hbase := traceDefect_three_pos ht₁ ht₂ ht₃
  have hsum : -6 ≤ t₁ + t₂ + t₃ := by
    linarith [ht₁.1, ht₂.1, ht₃.1]
  have hc5 : 0 ≤ c + 5 := by linarith
  have hlinear : -6 * (c + 5) ≤ (c + 5) * (t₁ + t₂ + t₃) := by
    nlinarith [mul_nonneg hc5 (by linarith : 0 ≤ t₁ + t₂ + t₃ + 6)]
  have hquadratic : 0 < 2 * c ^ 2 + 3 * c - 3 := by nlinarith
  have hbracket :
      0 < (c + 5) * (t₁ + t₂ + t₃) + 2 * c ^ 2 + 9 * c + 27 := by
    nlinarith
  have hfactor : 0 ≤ (c - 3) *
      ((c + 5) * (t₁ + t₂ + t₃) + 2 * c ^ 2 + 9 * c + 27) :=
    mul_nonneg (sub_nonneg.mpr hc) hbracket.le
  have hid :
      traceDefect c t₁ t₂ t₃ =
        traceDefect 3 t₁ t₂ t₃ + (c - 3) *
          ((c + 5) * (t₁ + t₂ + t₃) + 2 * c ^ 2 + 9 * c + 27) := by
    simp only [traceDefect]
    ring
  rw [hid]
  positivity

private theorem traceDefect_neg_of_le_neg_three
    {c t₁ t₂ t₃ : ℝ} (hc : c ≤ -3)
    (ht₁ : t₁ ∈ Set.Icc (-2 : ℝ) 2)
    (ht₂ : t₂ ∈ Set.Icc (-2 : ℝ) 2)
    (ht₃ : t₃ ∈ Set.Icc (-2 : ℝ) 2) :
    traceDefect c t₁ t₂ t₃ < 0 := by
  have hbase := traceDefect_neg_three_lt_zero ht₁ ht₂ ht₃
  have hsum : t₁ + t₂ + t₃ ≤ 6 := by
    linarith [ht₁.2, ht₂.2, ht₃.2]
  have hc1 : c - 1 ≤ 0 := by linarith
  have hlinear : 6 * (c - 1) ≤ (c - 1) * (t₁ + t₂ + t₃) := by
    have := mul_nonneg_of_nonpos_of_nonpos hc1 (sub_nonpos.mpr hsum)
    nlinarith
  have hquadratic : 0 < 2 * c ^ 2 + 3 * c + 3 := by nlinarith [sq_nonneg (c + 3)]
  have hbracket :
      0 < (c - 1) * (t₁ + t₂ + t₃) + 2 * c ^ 2 - 3 * c + 9 := by
    nlinarith
  have hfactor : (c + 3) *
      ((c - 1) * (t₁ + t₂ + t₃) + 2 * c ^ 2 - 3 * c + 9) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hbracket.le
  have hid :
      traceDefect c t₁ t₂ t₃ =
        traceDefect (-3) t₁ t₂ t₃ + (c + 3) *
          ((c - 1) * (t₁ + t₂ + t₃) + 2 * c ^ 2 - 3 * c + 9) := by
    simp only [traceDefect]
    ring
  rw [hid]
  linarith

private theorem one_shift_expression_pos_of_all_pos
    {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hw3 : w ≤ 3) :
    0 < u ^ 2 + v ^ 2 + w ^ 2 + u * v + u * w + v * w - u * v * w := by
  have hbase : 3 * (u * v) ≤ u ^ 2 + v ^ 2 + u * v := by
    nlinarith [sq_nonneg (u - v)]
  have hprod : u * v * w ≤ 3 * (u * v) :=
    by simpa [mul_comm] using mul_le_mul_of_nonneg_left hw3 (mul_pos hu hv).le
  have hextra : 0 < w ^ 2 + u * w + v * w := by positivity
  nlinarith

private theorem one_shift_expression_pos_of_pos_neg_neg
    {x y z : ℝ}
    (hyNeg : y < 0) (hyLow : -1 ≤ y)
    (hzNeg : z < 0) (hzLow : -1 ≤ z) :
    0 < x ^ 2 + y ^ 2 + z ^ 2 + x * y + x * z + y * z - x * y * z := by
  let a := -y
  let b := -z
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hab0 : 0 ≤ a * b := (mul_pos ha hb).le
  have hab1 : a * b ≤ 1 := (mul_le_mul ha1 hb1 hb.le (by norm_num)).trans_eq (by norm_num)
  have habsq : (a * b) ^ 2 ≤ a * b := by
    nlinarith [mul_nonneg hab0 (sub_nonneg.mpr hab1)]
  have hcauchy :
      (a + b + a * b) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + (a * b) ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - a * b), sq_nonneg (b - a * b)]
  have hdisc :
      (a + b + a * b) ^ 2 < 4 * (a ^ 2 + b ^ 2 + a * b) := by
    have hC : 0 < a ^ 2 + b ^ 2 + a * b := by positivity
    nlinarith
  have hsquare := sq_nonneg (2 * x - (a + b + a * b))
  dsimp [a, b] at hdisc hsquare ⊢
  nlinarith

private theorem traceDefect_one_eq_zero
    {t₁ t₂ t₃ : ℝ}
    (ht₁ : t₁ ∈ Set.Icc (-2 : ℝ) 2)
    (ht₂ : t₂ ∈ Set.Icc (-2 : ℝ) 2)
    (ht₃ : t₃ ∈ Set.Icc (-2 : ℝ) 2)
    (hzero : traceDefect (1 : ℝ) t₁ t₂ t₃ = 0) :
    t₁ = -1 ∧ t₂ = -1 ∧ t₃ = -1 := by
  let u := t₁ + 1
  let v := t₂ + 1
  let w := t₃ + 1
  have huLow : -1 ≤ u := by dsimp [u]; linarith [ht₁.1]
  have huHigh : u ≤ 3 := by dsimp [u]; linarith [ht₁.2]
  have hvLow : -1 ≤ v := by dsimp [v]; linarith [ht₂.1]
  have hvHigh : v ≤ 3 := by dsimp [v]; linarith [ht₂.2]
  have hwLow : -1 ≤ w := by dsimp [w]; linarith [ht₃.1]
  have hwHigh : w ≤ 3 := by dsimp [w]; linarith [ht₃.2]
  have hshift :
      u ^ 2 + v ^ 2 + w ^ 2 + u * v + u * w + v * w - u * v * w = 0 := by
    dsimp [u, v, w]
    rw [traceDefect] at hzero
    nlinarith
  by_cases hprod : u * v * w ≤ 0
  · have hQ : 0 ≤ u ^ 2 + v ^ 2 + w ^ 2 + u * v + u * w + v * w := by
      nlinarith [sq_nonneg (u + v + w), sq_nonneg u, sq_nonneg v, sq_nonneg w]
    have hQzero : u ^ 2 + v ^ 2 + w ^ 2 + u * v + u * w + v * w = 0 := by
      nlinarith
    have hu : u = 0 := by
      have : u ^ 2 ≤ 0 := by
        nlinarith [sq_nonneg (u + v + w), sq_nonneg v, sq_nonneg w]
      exact sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg u))
    have hv : v = 0 := by
      have : v ^ 2 ≤ 0 := by
        nlinarith [sq_nonneg (u + v + w), sq_nonneg u, sq_nonneg w]
      exact sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg v))
    have hw : w = 0 := by
      have : w ^ 2 ≤ 0 := by
        nlinarith [sq_nonneg (u + v + w), sq_nonneg u, sq_nonneg v]
      exact sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg w))
    dsimp [u, v, w] at hu hv hw
    exact ⟨by linarith, by linarith, by linarith⟩
  · have hprodPos : 0 < u * v * w := lt_of_not_ge hprod
    rcases (mul_pos_iff.mp hprodPos) with ⟨huv, hw⟩ | ⟨huv, hw⟩
    · rcases (mul_pos_iff.mp huv) with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact False.elim ((ne_of_gt
          (one_shift_expression_pos_of_all_pos hu hv hw hwHigh)) hshift)
      · exact False.elim ((ne_of_gt
          (one_shift_expression_pos_of_pos_neg_neg
            (x := w) (y := u) (z := v) hu huLow hv hvLow)) (by
            simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
              mul_assoc] using hshift))
    · rcases (mul_neg_iff.mp huv) with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact False.elim ((ne_of_gt
          (one_shift_expression_pos_of_pos_neg_neg
            (x := u) (y := v) (z := w) hv hvLow hw hwLow)) hshift)
      · exact False.elim ((ne_of_gt
          (one_shift_expression_pos_of_pos_neg_neg
            (x := v) (y := u) (z := w) hu huLow hw hwLow)) (by
            simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
              mul_assoc] using hshift))

private theorem traceDefect_zero_eq_zero
    {t₁ t₂ t₃ : ℝ} (ht₁ : t₁ ∈ Set.Icc (-2 : ℝ) 2)
    (hzero : traceDefect (0 : ℝ) t₁ t₂ t₃ = 0) :
    t₁ = 0 ∧ t₂ = 0 ∧ t₃ = 0 := by
  let x : BGS.Markoff.NormalizedPoint ℝ := ⟨t₁, t₂, t₃⟩
  have hx : BGS.Markoff.IsNormalizedMarkoff x := by
    simpa [x, BGS.Markoff.IsNormalizedMarkoff, BGS.Markoff.normalizedPolynomial,
      traceDefect] using hzero
  have horigin :=
    BGS.Markoff.real_normalizedMarkoff_eq_origin_of_firstCoordinate_mem_Icc x hx ht₁
  exact ⟨congrArg BGS.Markoff.NormalizedPoint.u1 horigin,
    congrArg BGS.Markoff.NormalizedPoint.u2 horigin,
    congrArg BGS.Markoff.NormalizedPoint.u3 horigin⟩

/-- For an admissible integral equal coefficient, the real compact zero locus
of the trace defect consists only of the three traces of the affine origin. -/
theorem traceDefect_eq_zero_iff_eq_neg_integral
    (c : ℤ) (hs : 3 * (1 + c) ≠ 0) (hc : c ^ 2 ≠ 4)
    (t₁ t₂ t₃ : ℝ)
    (ht₁ : t₁ ∈ Set.Icc (-2 : ℝ) 2)
    (ht₂ : t₂ ∈ Set.Icc (-2 : ℝ) 2)
    (ht₃ : t₃ ∈ Set.Icc (-2 : ℝ) 2) :
    traceDefect (c : ℝ) t₁ t₂ t₃ = 0 ↔
      t₁ = -(c : ℝ) ∧ t₂ = -(c : ℝ) ∧ t₃ = -(c : ℝ) := by
  constructor
  · intro hzero
    have hcNegTwo : c ≠ -2 := by
      intro h
      subst c
      norm_num at hc
    have hcNegOne : c ≠ -1 := by
      intro h
      subst c
      norm_num at hs
    have hcTwo : c ≠ 2 := by
      intro h
      subst c
      norm_num at hc
    rcases (by omega : c ≤ -3 ∨ c = 0 ∨ c = 1 ∨ 3 ≤ c) with hneg | rfl | rfl | hpos
    · have hnegReal : (c : ℝ) ≤ -3 := by exact_mod_cast hneg
      exact False.elim ((ne_of_lt
        (traceDefect_neg_of_le_neg_three hnegReal ht₁ ht₂ ht₃)) hzero)
    · have h := traceDefect_zero_eq_zero
          (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) ht₁ (by simpa using hzero)
      simpa using h
    · have h := traceDefect_one_eq_zero
          (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) ht₁ ht₂ ht₃ (by simpa using hzero)
      simpa using h
    · have hposReal : (3 : ℝ) ≤ c := by exact_mod_cast hpos
      exact False.elim ((ne_of_gt
        (traceDefect_pos_of_three_le hposReal ht₁ ht₂ ht₃)) hzero)
  · rintro ⟨rfl, rfl, rfl⟩
    exact traceDefect_neg_self ℝ (c : ℝ)

/-- Unit-circle rigidity for the generalized symmetric cyclotomic defect. -/
theorem cyclotomicTrace_eq_neg_integral_of_defect_eq_zero
    (c : ℤ) (hs : 3 * (1 + c) ≠ 0) (hc : c ^ 2 ≠ 4)
    {z₁ z₂ z₃ : ℂ}
    (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1) (hz₃ : ‖z₃‖ = 1)
    (hzero : cyclotomicDefect (c : ℂ) z₁ z₂ z₃ = 0) :
    cyclotomicTrace z₁ = -(c : ℂ) ∧
      cyclotomicTrace z₂ = -(c : ℂ) ∧
      cyclotomicTrace z₃ = -(c : ℂ) := by
  let t₁ : ℝ := 2 * z₁.re
  let t₂ : ℝ := 2 * z₂.re
  let t₃ : ℝ := 2 * z₃.re
  have htrace₁ : cyclotomicTrace z₁ = (t₁ : ℂ) := by
    simpa [t₁] using cyclotomicTrace_eq_two_mul_re hz₁
  have htrace₂ : cyclotomicTrace z₂ = (t₂ : ℂ) := by
    simpa [t₂] using cyclotomicTrace_eq_two_mul_re hz₂
  have htrace₃ : cyclotomicTrace z₃ = (t₃ : ℂ) := by
    simpa [t₃] using cyclotomicTrace_eq_two_mul_re hz₃
  have ht₁ : t₁ ∈ Set.Icc (-2 : ℝ) 2 := by
    have hre := Complex.abs_re_le_norm z₁
    rw [hz₁] at hre
    rcases abs_le.mp hre with ⟨hlo, hhi⟩
    dsimp [t₁]
    constructor <;> nlinarith
  have ht₂ : t₂ ∈ Set.Icc (-2 : ℝ) 2 := by
    have hre := Complex.abs_re_le_norm z₂
    rw [hz₂] at hre
    rcases abs_le.mp hre with ⟨hlo, hhi⟩
    dsimp [t₂]
    constructor <;> nlinarith
  have ht₃ : t₃ ∈ Set.Icc (-2 : ℝ) 2 := by
    have hre := Complex.abs_re_le_norm z₃
    rw [hz₃] at hre
    rcases abs_le.mp hre with ⟨hlo, hhi⟩
    dsimp [t₃]
    constructor <;> nlinarith
  have hzeroReal : traceDefect (c : ℝ) t₁ t₂ t₃ = 0 := by
    rw [cyclotomicDefect, htrace₁, htrace₂, htrace₃] at hzero
    simp only [traceDefect] at hzero ⊢
    exact_mod_cast hzero
  obtain ⟨ht₁c, ht₂c, ht₃c⟩ :=
    (traceDefect_eq_zero_iff_eq_neg_integral c hs hc t₁ t₂ t₃ ht₁ ht₂ ht₃).mp
      hzeroReal
  constructor
  · rw [htrace₁]
    exact_mod_cast ht₁c
  · constructor
    · rw [htrace₂]
      exact_mod_cast ht₂c
    · rw [htrace₃]
      exact_mod_cast ht₃c

/-- Unless all three reciprocal traces are the affine-origin trace, the
generalized symmetric cyclotomic defect is nonzero. -/
theorem cyclotomicDefect_ne_zero_of_some_trace_ne_neg_integral
    (c : ℤ) (hs : 3 * (1 + c) ≠ 0) (hc : c ^ 2 ≠ 4)
    {z₁ z₂ z₃ : ℂ}
    (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1) (hz₃ : ‖z₃‖ = 1)
    (htrace : cyclotomicTrace z₁ ≠ -(c : ℂ) ∨
      cyclotomicTrace z₂ ≠ -(c : ℂ) ∨
      cyclotomicTrace z₃ ≠ -(c : ℂ)) :
    cyclotomicDefect (c : ℂ) z₁ z₂ z₃ ≠ 0 := by
  intro hzero
  obtain ⟨h₁, h₂, h₃⟩ :=
    cyclotomicTrace_eq_neg_integral_of_defect_eq_zero
      c hs hc hz₁ hz₂ hz₃ hzero
  rcases htrace with htrace | htrace | htrace
  · exact htrace h₁
  · exact htrace h₂
  · exact htrace h₃

end GenMarkoff.Symmetric.Opening
