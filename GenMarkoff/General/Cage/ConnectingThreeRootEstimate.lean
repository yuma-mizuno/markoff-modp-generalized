import GenMarkoff.General.Cage.ConnectingSevenPlaneEstimates
import GenMarkoff.General.Cage.ThreeRootPowerCover

/-!
# Three-root cover estimate for the unequal connecting cage

The seven hyperelliptic-plane estimates control the affine cover carrying
three simultaneous square roots.  Primitive extraction uses the smaller
cover with nonzero power parameter and nonzero third root.  This file
accounts separately for the omitted zero-parameter fiber and for the
third-root-zero locus, bounding the latter by roots of the scaled
centered-norm polynomial.
-/

namespace GenMarkoff.General.Cage

open Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The absolute value of a sum of seven real numbers is at most the sum
of their absolute values. -/
private theorem abs_seven_sum_le_sum_abs
    (a b c d e f g : ℝ) :
    |a + b + c + d + e + f + g| ≤
      |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
  have hab := abs_add_le a b
  have habc := abs_add_le (a + b) c
  have habcd := abs_add_le (a + b + c) d
  have habcde := abs_add_le (a + b + c + d) e
  have habcdef := abs_add_le (a + b + c + d + e) f
  have habcdefg := abs_add_le (a + b + c + d + e + f) g
  linarith

/-- A third-root-zero unit-cover point determines a root of the third
radicand together with the first two square roots above that parameter. -/
private def thirdRootZeroUnitPowerCoverEmbedding
    (f g h : K[X]) :
    ThirdRootZeroUnitPowerCover f g h ↪
      Σ parameter : {t : K // h.eval t = 0},
        {r : K // r ^ 2 = f.eval parameter.1} ×
          {r : K // r ^ 2 = g.eval parameter.1} where
  toFun z :=
    ⟨⟨(z.1.parameter : K), by
        simpa [z.2] using z.1.thirdEquation.symm⟩,
      ⟨⟨z.1.firstRoot, z.1.firstEquation⟩,
        ⟨z.1.secondRoot, z.1.secondEquation⟩⟩⟩
  inj' := by
    intro z w hzw
    apply Subtype.ext
    apply UnitThreeRootPowerCover.ext
    · apply Units.ext
      exact congrArg (fun q => (q.1.1 : K)) hzw
    · exact congrArg (fun q => (q.2.1.1 : K)) hzw
    · exact congrArg (fun q => (q.2.2.1 : K)) hzw
    · exact z.2.trans w.2.symm

section FiniteField

variable [Fintype K] [DecidableEq K]

/-- A nonzero polynomial over a finite field has at most its degree many
distinct roots. -/
private theorem natCard_polynomialRootSubtype_le_natDegree
    (P : K[X]) (hP : P ≠ 0) :
    Nat.card {x : K // P.eval x = 0} ≤ P.natDegree := by
  classical
  let rootEmbedding :
      {x : K // P.eval x = 0} ↪ P.roots.toFinset :=
    { toFun := fun x => ⟨x, by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
        exact x.2⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : P.roots.toFinset => (z : K)) h }
  letI : Fintype {x : K // P.eval x = 0} := Fintype.ofFinite _
  calc
    Nat.card {x : K // P.eval x = 0} ≤ P.roots.toFinset.card := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
        Fintype.card_le_of_injective
          rootEmbedding rootEmbedding.injective
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P

/-- A scalar has at most two square roots in a field. -/
private theorem natCard_squareRootFiber_le_two (a : K) :
    Nat.card {r : K // r ^ 2 = a} ≤ 2 := by
  let P : K[X] := X ^ 2 - C a
  have hP : P ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun q : K[X] => q.coeff 2) hzero
    simp [P] at hcoeff
  let e :
      {r : K // r ^ 2 = a} ≃
        {r : K // P.eval r = 0} :=
    Equiv.subtypeEquiv (Equiv.refl K) (by
      intro r
      simp [P, sub_eq_zero])
  calc
    Nat.card {r : K // r ^ 2 = a} =
        Nat.card {r : K // P.eval r = 0} :=
      Nat.card_congr e
    _ ≤ P.natDegree :=
      natCard_polynomialRootSubtype_le_natDegree P hP
    _ ≤ 2 := by
      simp [P]

/-- Every fixed parameter contributes at most eight triples of square
roots.  This includes the affine parameter `0`. -/
theorem natCard_threeSquareRootFiber_le_eight
    (f g h : K[X]) (parameter : K) :
    Nat.card (ThreeSquareRootFiber f g h parameter) ≤ 8 := by
  calc
    Nat.card (ThreeSquareRootFiber f g h parameter) =
        Nat.card {r : K // r ^ 2 = f.eval parameter} *
          (Nat.card {r : K // r ^ 2 = g.eval parameter} *
            Nat.card {r : K // r ^ 2 = h.eval parameter}) := by
      rw [Nat.card_congr
        (threeSquareRootFiberEquivRootProduct
          f g h parameter),
        Nat.card_prod, Nat.card_prod]
    _ ≤ 2 * (2 * 2) :=
      Nat.mul_le_mul
        (natCard_squareRootFiber_le_two (f.eval parameter))
        (Nat.mul_le_mul
          (natCard_squareRootFiber_le_two (g.eval parameter))
          (natCard_squareRootFiber_le_two (h.eval parameter)))
    _ = 8 := by norm_num

/-- The third-root-zero unit locus has at most four points over each root
of the third radicand. -/
theorem natCard_thirdRootZeroUnitPowerCover_le_four_mul_natDegree
    (f g h : K[X]) (hh : h ≠ 0) :
    Nat.card (ThirdRootZeroUnitPowerCover f g h) ≤
      4 * h.natDegree := by
  let base := {t : K // h.eval t = 0}
  let fiber : base → Type u := fun t =>
    {r : K // r ^ 2 = f.eval t.1} ×
      {r : K // r ^ 2 = g.eval t.1}
  have hinj :=
    Nat.card_le_card_of_injective
      (thirdRootZeroUnitPowerCoverEmbedding f g h).toFun
      (thirdRootZeroUnitPowerCoverEmbedding f g h).injective
  change Nat.card (ThirdRootZeroUnitPowerCover f g h) ≤
    Nat.card (Σ t : base, fiber t) at hinj
  rw [Nat.card_sigma] at hinj
  have hfiber : ∀ t : base, Nat.card (fiber t) ≤ 4 := by
    intro t
    dsimp only [fiber]
    rw [Nat.card_prod]
    calc
      Nat.card {r : K // r ^ 2 = f.eval t.1} *
          Nat.card {r : K // r ^ 2 = g.eval t.1} ≤
          2 * 2 :=
        Nat.mul_le_mul
          (natCard_squareRootFiber_le_two (f.eval t.1))
          (natCard_squareRootFiber_le_two (g.eval t.1))
      _ = 4 := by norm_num
  have hsum :
      ∑ t : base, Nat.card (fiber t) ≤
        ∑ _t : base, 4 :=
    Finset.sum_le_sum fun t _ => hfiber t
  have hbase :
      Nat.card base ≤ h.natDegree :=
    natCard_polynomialRootSubtype_le_natDegree h hh
  have hsum' :
      ∑ t : base, Nat.card (fiber t) ≤
        Nat.card base * 4 := by
    simpa using hsum
  omega

/-- The three-square-root identity turns the affine three-root error into
the sum of the seven signed hyperelliptic-cover errors. -/
theorem threeSquareRootFiberProductPointCount_error_le_sum_seven
    (hchar : ringChar K ≠ 2) (f g h : K[X]) :
    abs (((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
        (Fintype.card K : ℝ)) ≤
      |squareRootCoverPointCountError f| +
        |squareRootCoverPointCountError g| +
        |squareRootCoverPointCountError h| +
        |squareRootCoverPointCountError (f * g)| +
        |squareRootCoverPointCountError (f * h)| +
        |squareRootCoverPointCountError (g * h)| +
        |squareRootCoverPointCountError (f * g * h)| := by
  have hidentity :
      threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) =
        squareRootCoverPointCount
            (fun parameter : K => f.eval parameter) +
          squareRootCoverPointCount
            (fun parameter : K => g.eval parameter) +
          squareRootCoverPointCount
            (fun parameter : K => h.eval parameter) +
          squareRootCoverPointCount
            (fun parameter : K => (f * g).eval parameter) +
          squareRootCoverPointCount
            (fun parameter : K => (f * h).eval parameter) +
          squareRootCoverPointCount
            (fun parameter : K => (g * h).eval parameter) +
          squareRootCoverPointCount
            (fun parameter : K => (f * g * h).eval parameter) -
          6 * Fintype.card K := by
    simpa only [eval_mul] using
      threeSquareRootFiberProductPointCount_eq_seven_covers
        hchar
        (fun parameter : K => f.eval parameter)
        (fun parameter : K => g.eval parameter)
        (fun parameter : K => h.eval parameter)
  have htriangle :=
    abs_seven_sum_le_sum_abs
      (squareRootCoverPointCountError f)
      (squareRootCoverPointCountError g)
      (squareRootCoverPointCountError h)
      (squareRootCoverPointCountError (f * g))
      (squareRootCoverPointCountError (f * h))
      (squareRootCoverPointCountError (g * h))
      (squareRootCoverPointCountError (f * g * h))
  unfold squareRootCoverPointCountError at htriangle ⊢
  rw [hidentity]
  push_cast
  convert htriangle using 1
  all_goals ring_nf

/-- The affine unequal connecting three-root count has Hasse error at most
`768 d sqrt(|K|)`. -/
theorem
    connectingScaledThreeSquareRootFiberProductPointCount_error_le
    (hchar : ringChar K ≠ 2)
    {a : Coefficients K} {xi eta omegaInv : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hpair : IsConnectingIncidencePair a xi eta)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0)
    (homegaInv : omegaInv ≠ 0) :
    let f := incidencePulledRadicand a xi d
    let g := incidencePulledRadicand a eta d
    let h :=
      C omegaInv * centeredNormPulledRadicand a.a3 a.a1 d
    |((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
        (Fintype.card K : ℝ)| ≤
      768 * d * Real.sqrt (Fintype.card K : ℝ) := by
  dsimp only
  exact
    (threeSquareRootFiberProductPointCount_error_le_sum_seven
      hchar
      (incidencePulledRadicand a xi d)
      (incidencePulledRadicand a eta d)
      (C omegaInv *
        centeredNormPulledRadicand a.a3 a.a1 d)).trans
      (connectingSevenScaledSquareRootCoverPointCount_sum_abs_error_le
        hchar hA1 hA2 hA3 hmoving hxi heta hpair
        hd hdegree homegaInv)

omit [Fintype K] [DecidableEq K] in
/-- A nonzero scalar multiple of the full centered-norm pullback is a
nonzero polynomial. -/
theorem scaledCenteredNormPulledRadicand_ne_zero
    {omegaInv B C0 : K} (homegaInv : omegaInv ≠ 0)
    {d : ℕ} (hd : 0 < d) :
    C omegaInv * centeredNormPulledRadicand B C0 d ≠ 0 := by
  intro hzero
  have heval := congrArg (Polynomial.eval 0) hzero
  apply homegaInv
  simpa [eval_centeredNormPulledRadicand_zero B C0 hd] using heval

/-- For the scaled centered-norm third radicand, the third-root-zero unit
locus has cardinality at most `16d`. -/
theorem
    connectingScaledThirdRootZeroUnitPowerCover_card_le
    (a : Coefficients K) (xi eta : K)
    {omegaInv : K} (homegaInv : omegaInv ≠ 0)
    {d : ℕ} (hd : 0 < d) :
    let f := incidencePulledRadicand a xi d
    let g := incidencePulledRadicand a eta d
    let h :=
      C omegaInv * centeredNormPulledRadicand a.a3 a.a1 d
    Nat.card (ThirdRootZeroUnitPowerCover f g h) ≤ 16 * d := by
  dsimp only
  have hbad :=
    natCard_thirdRootZeroUnitPowerCover_le_four_mul_natDegree
      (incidencePulledRadicand a xi d)
      (incidencePulledRadicand a eta d)
      (C omegaInv *
        centeredNormPulledRadicand a.a3 a.a1 d)
      (scaledCenteredNormPulledRadicand_ne_zero homegaInv hd)
  have hdegreeBound :=
    scaledCenteredNormPulledRadicand_natDegree_le
      omegaInv a.a3 a.a1 d
  omega

/-- The affine cover type realizes the same `768d` error estimate as its
integer-valued fiber-product point count. -/
theorem connectingScaledThreeRootPowerCover_card_error_le
    (hchar : ringChar K ≠ 2)
    {a : Coefficients K} {xi eta omegaInv : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hpair : IsConnectingIncidencePair a xi eta)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0)
    (homegaInv : omegaInv ≠ 0) :
    let f := incidencePulledRadicand a xi d
    let g := incidencePulledRadicand a eta d
    let h :=
      C omegaInv * centeredNormPulledRadicand a.a3 a.a1 d
    |((Nat.card (ThreeRootPowerCover f g h) : ℕ) : ℝ) -
        (Fintype.card K : ℝ)| ≤
      768 * d * Real.sqrt (Fintype.card K : ℝ) := by
  dsimp only
  have hcount :=
    natCard_threeRootPowerCover_eq_pointCount
      (incidencePulledRadicand a xi d)
      (incidencePulledRadicand a eta d)
      (C omegaInv *
        centeredNormPulledRadicand a.a3 a.a1 d)
  have hcountReal :
      ((Nat.card
        (ThreeRootPowerCover
          (incidencePulledRadicand a xi d)
          (incidencePulledRadicand a eta d)
          (C omegaInv *
            centeredNormPulledRadicand a.a3 a.a1 d)) : ℕ) : ℝ) =
        ((threeSquareRootFiberProductPointCount
          (fun parameter : K =>
            (incidencePulledRadicand a xi d).eval parameter)
          (fun parameter : K =>
            (incidencePulledRadicand a eta d).eval parameter)
          (fun parameter : K =>
            (C omegaInv *
              centeredNormPulledRadicand a.a3 a.a1 d).eval
                parameter) : ℤ) : ℝ) := by
    exact_mod_cast hcount
  rw [hcountReal]
  exact
    connectingScaledThreeSquareRootFiberProductPointCount_error_le
      hchar hA1 hA2 hA3 hmoving hxi heta hpair
      hd hdegree homegaInv

/-- Removing the zero parameter costs at most `8`, and removing the
third-root-zero unit locus costs at most `16d`.  Thus the good unit
three-root cover has the explicit error
`768 d sqrt(|K|) + 8 + 16d`. -/
theorem connectingScaledGoodUnitThreeRootPowerCover_card_error_le
    (hchar : ringChar K ≠ 2)
    {a : Coefficients K} {xi eta omegaInv : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hpair : IsConnectingIncidencePair a xi eta)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0)
    (homegaInv : omegaInv ≠ 0) :
    let f := incidencePulledRadicand a xi d
    let g := incidencePulledRadicand a eta d
    let h :=
      C omegaInv * centeredNormPulledRadicand a.a3 a.a1 d
    |((Nat.card (GoodUnitThreeRootPowerCover f g h) : ℕ) : ℝ) -
        (Fintype.card K : ℝ)| ≤
      768 * d * Real.sqrt (Fintype.card K : ℝ) +
        8 + 16 * d := by
  dsimp only
  let f := incidencePulledRadicand a xi d
  let g := incidencePulledRadicand a eta d
  let h :=
    C omegaInv * centeredNormPulledRadicand a.a3 a.a1 d
  have hbridge :=
    natCard_goodUnitThreeRootPowerCover_eq_pointCount_sub_bad
      f g h
  have hbridgeReal :
      ((Nat.card (GoodUnitThreeRootPowerCover f g h) : ℕ) : ℝ) =
        ((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
        (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ) -
        (Nat.card (ThirdRootZeroUnitPowerCover f g h) : ℝ) := by
    exact_mod_cast hbridge
  have herrorRewrite :
      ((Nat.card (GoodUnitThreeRootPowerCover f g h) : ℕ) : ℝ) -
          (Fintype.card K : ℝ) =
        (((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
            (Fintype.card K : ℝ)) -
          (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ) -
          (Nat.card (ThirdRootZeroUnitPowerCover f g h) : ℝ) := by
    rw [hbridgeReal]
    ring
  have haffine :
      abs (((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
        (Fintype.card K : ℝ)) ≤
          768 * d * Real.sqrt (Fintype.card K : ℝ) := by
    exact
      connectingScaledThreeSquareRootFiberProductPointCount_error_le
        hchar hA1 hA2 hA3 hmoving hxi heta hpair
        hd hdegree homegaInv
  have hzeroNat :
      Nat.card (ThreeSquareRootFiber f g h 0) ≤ 8 :=
    natCard_threeSquareRootFiber_le_eight f g h 0
  have hzero :
      (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ) ≤ 8 := by
    exact_mod_cast hzeroNat
  have hbadNat :
      Nat.card (ThirdRootZeroUnitPowerCover f g h) ≤ 16 * d := by
    exact connectingScaledThirdRootZeroUnitPowerCover_card_le
      a xi eta homegaInv hd
  have hbad :
      (Nat.card (ThirdRootZeroUnitPowerCover f g h) : ℝ) ≤
        16 * d := by
    exact_mod_cast hbadNat
  rw [herrorRewrite]
  calc
    |(((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
          (Fintype.card K : ℝ)) -
        (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ) -
        (Nat.card (ThirdRootZeroUnitPowerCover f g h) : ℝ)| ≤
      |(((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
          (Fintype.card K : ℝ))| +
        |(Nat.card (ThreeSquareRootFiber f g h 0) : ℝ)| +
        |(Nat.card
          (ThirdRootZeroUnitPowerCover f g h) : ℝ)| := by
      have hfirst :=
        abs_sub
          ((((threeSquareRootFiberProductPointCount
            (fun parameter : K => f.eval parameter)
            (fun parameter : K => g.eval parameter)
            (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
            (Fintype.card K : ℝ)) -
            (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ))
          (Nat.card
            (ThirdRootZeroUnitPowerCover f g h) : ℝ)
      have hsecond :=
        abs_sub
          (((threeSquareRootFiberProductPointCount
            (fun parameter : K => f.eval parameter)
            (fun parameter : K => g.eval parameter)
            (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
            (Fintype.card K : ℝ))
          (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ)
      linarith
    _ =
      |(((threeSquareRootFiberProductPointCount
          (fun parameter : K => f.eval parameter)
          (fun parameter : K => g.eval parameter)
          (fun parameter : K => h.eval parameter) : ℤ) : ℝ) -
          (Fintype.card K : ℝ))| +
        (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ) +
        (Nat.card (ThirdRootZeroUnitPowerCover f g h) : ℝ) := by
      rw [abs_of_nonneg
          (show 0 ≤
            (Nat.card (ThreeSquareRootFiber f g h 0) : ℝ) by
            positivity),
        abs_of_nonneg
          (show 0 ≤
            (Nat.card
              (ThirdRootZeroUnitPowerCover f g h) : ℝ) by
            positivity)]
    _ ≤
      768 * d * Real.sqrt (Fintype.card K : ℝ) +
        8 + 16 * d :=
      add_le_add (add_le_add haffine hzero) hbad

end FiniteField

end

end GenMarkoff.General.Cage
