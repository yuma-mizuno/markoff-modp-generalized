import GenMarkoff.Symmetric.Cage.PowerCover
import GenMarkoff.Symmetric.Cage.PlaneModels

/-!
# Comparing the pulled incidence cover with its affine plane models

The plane models retain the power parameter `t`, while
`IncidencePulledRootPair` requires `t ≠ 0`.  On the diagonal the plane model
also forgets the choice between the two equal radicand roots.  This file
isolates those losses and bounds them by roots of explicit univariate
polynomials.
-/

namespace GenMarkoff.Symmetric.Cage

open Polynomial

noncomputable section

/-- A finite-field polynomial has at most its degree many distinct roots. -/
private theorem natCard_eval_eq_zero_le_natDegree
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (hf : f ≠ 0) :
    Nat.card {x : K // f.eval x = 0} ≤ f.natDegree := by
  classical
  let rootEmbedding : {x : K // f.eval x = 0} ↪ f.roots.toFinset :=
    { toFun := fun x => ⟨x, by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
        exact x.2⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : f.roots.toFinset => (z : K)) h }
  letI : Fintype {x : K // f.eval x = 0} := Fintype.ofFinite _
  calc
    Nat.card {x : K // f.eval x = 0} ≤ f.roots.toFinset.card := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
        Fintype.card_le_of_injective rootEmbedding rootEmbedding.injective
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f

/-- The pulled incidence radicand has degree at most `4d`. -/
theorem incidencePulledRadicand_natDegree_le
    (K : Type*) [Field K] (c xi : K) (d : Nat) :
    (incidencePulledRadicand c xi d).natDegree ≤ 4 * d := by
  unfold incidencePulledRadicand
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact natDegree_C_mul_X_pow_le _ _
        · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · exact (natDegree_C _).le.trans (Nat.zero_le _)

/-- A scalar in a finite field has at most two square roots. -/
private theorem natCard_sq_eq_le_two
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] (a : K) :
    Nat.card {x : K // x ^ 2 = a} ≤ 2 := by
  let f : K[X] := X ^ 2 - C a
  have hf : f ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun q : K[X] => q.coeff 2) hzero
    simp [f] at hcoeff
  let e : {x : K // x ^ 2 = a} ≃ {x : K // f.eval x = 0} :=
    Equiv.subtypeEquiv (Equiv.refl K) (by
      intro x
      simp [f, sub_eq_zero])
  calc
    Nat.card {x : K // x ^ 2 = a} =
        Nat.card {x : K // f.eval x = 0} := Nat.card_congr e
    _ ≤ f.natDegree := natCard_eval_eq_zero_le_natDegree f hf
    _ = 2 := by simp [f]

/-- Rational points of the diagonal incidence plane model. -/
abbrev IncidenceDiagonalPlanePoint
    (p : Nat) [Fact p.Prime] (c xi : ZMod p) (d : Nat) :=
  ↥(BGS.External.affinePlaneCurveZeros (ZMod p)
    (incidenceDiagonalPlanePolynomial c xi d))

/-- A diagonal plane point together with the sign used to recover the
second root. -/
abbrev IncidenceDiagonalTaggedPlanePoint
    (p : Nat) [Fact p.Prime] (c xi : ZMod p) (d : Nat) :=
  IncidenceDiagonalPlanePoint p c xi d × Bool

/-- The tagged points which recover a unique pulled pair.  At a zero root
the two signs coincide, so only `false` is retained. -/
def IsGoodIncidenceDiagonalTaggedPoint
    {p : Nat} [Fact p.Prime] {c xi : ZMod p} {d : Nat}
    (z : IncidenceDiagonalTaggedPlanePoint p c xi d) : Prop :=
  z.1.1.2 ≠ 0 ∧ (z.1.1.1 ≠ 0 ∨ z.2 = false)

/-- Away from the explicit exceptional set, a signed diagonal plane point
is exactly a pulled pair of roots. -/
def goodIncidenceDiagonalTaggedPointEquivPulled
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c xi : ZMod p) (d : Nat) :
    {z : IncidenceDiagonalTaggedPlanePoint p c xi d //
      IsGoodIncidenceDiagonalTaggedPoint z} ≃
      IncidencePulledRootPair p c xi xi d where
  toFun z := by
    let parameter : (ZMod p)ˣ := Units.mk0 z.1.1.1.2 z.2.1
    let root := z.1.1.1.1
    refine
      { parameter := parameter
        firstRoot := root
        secondRoot := if z.1.2 then -root else root
        firstEquation := ?_
        secondEquation := ?_ }
    · exact
        (eval_incidenceDiagonalPlanePolynomial_eq_zero_iff
          c xi d root z.1.1.1.2).mp
          (BGS.External.mem_affinePlaneCurveZeros_iff.mp z.1.1.2)
    · have hfirst :
          root ^ 2 =
            (incidencePulledRadicand c xi d).eval z.1.1.1.2 :=
        (eval_incidenceDiagonalPlanePolynomial_eq_zero_iff
          c xi d root z.1.1.1.2).mp
          (BGS.External.mem_affinePlaneCurveZeros_iff.mp z.1.1.2)
      split <;> simpa [parameter, root] using hfirst
  invFun z := by
    have hsquares :
        z.secondRoot = z.firstRoot ∨
          z.secondRoot = -z.firstRoot := by
      rw [← sq_eq_sq_iff_eq_or_eq_neg]
      exact z.secondEquation.trans z.firstEquation.symm
    let tag : Bool :=
      if z.secondRoot = z.firstRoot then false else true
    have htag :
        z.secondRoot =
          if tag then -z.firstRoot else z.firstRoot := by
      dsimp [tag]
      split
      · simp_all
      · simp_all
    refine ⟨(⟨(z.firstRoot, (z.parameter : ZMod p)), ?_⟩, tag), ?_⟩
    · apply BGS.External.mem_affinePlaneCurveZeros_iff.mpr
      exact
        (eval_incidenceDiagonalPlanePolynomial_eq_zero_iff
          c xi d z.firstRoot (z.parameter : ZMod p)).mpr
          z.firstEquation
    · refine ⟨z.parameter.ne_zero, ?_⟩
      by_cases hroot : z.firstRoot = 0
      · right
        have hsecond : z.secondRoot = 0 := by
          rcases hsquares with h | h <;> simp_all
        simp [tag, hroot, hsecond]
      · exact Or.inl hroot
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext <;> rfl
    · cases htag : z.1.2
      · simp [htag]
      · have hroot : z.1.1.1.1 ≠ 0 := by
          rcases z.2.2 with hroot | hfalse
          · exact hroot
          · simp [htag] at hfalse
        have hneg : -z.1.1.1.1 ≠ z.1.1.1.1 := by
          intro h
          have htwo : (2 : ZMod p) ≠ 0 :=
            BGS.Markoff.two_ne_zero_zmod
              (lt_of_le_of_ne
                (Fact.out : p.Prime).two_le (Ne.symm hpTwo))
          have hzero : z.1.1.1.1 + z.1.1.1.1 = 0 :=
            neg_eq_iff_add_eq_zero.mp h
          have hzero' : (2 : ZMod p) * z.1.1.1.1 = 0 := by
            simpa [two_mul] using hzero
          exact hroot ((mul_eq_zero.mp hzero').resolve_left htwo)
        simp [htag, hneg]
  right_inv z := by
    apply IncidencePulledRootPair.ext
    · apply Units.ext
      rfl
    · rfl
    · dsimp
      split
      · symm
        assumption
      · rename_i hne
        rcases
            (sq_eq_sq_iff_eq_or_eq_neg.mp
              (z.secondEquation.trans z.firstEquation.symm)) with
          h | h
        · exact (hne h).elim
        · exact h.symm

/-- Bad signed diagonal points inject into either the two signs above
`t = 0`, or a root of the pulled radicand with the duplicated sign. -/
def badIncidenceDiagonalTaggedPointEmbedding
    (p : Nat) [Fact p.Prime] (c xi : ZMod p)
    {d : Nat} (hd : 0 < d) :
    {z : IncidenceDiagonalTaggedPlanePoint p c xi d //
      ¬ IsGoodIncidenceDiagonalTaggedPoint z} ↪
      ({root : ZMod p //
          root ^ 2 = incidenceLeadingCoefficient xi} × Bool) ⊕
        {parameter : ZMod p //
          (incidencePulledRadicand c xi d).eval parameter = 0} :=
  { toFun := fun z => by
      by_cases hparameter : z.1.1.1.2 = 0
      · exact Sum.inl ⟨⟨z.1.1.1.1, by
            have heq :=
              (eval_incidenceDiagonalPlanePolynomial_eq_zero_iff
                c xi d z.1.1.1.1 z.1.1.1.2).mp
                (BGS.External.mem_affinePlaneCurveZeros_iff.mp z.1.1.2)
            simpa [hparameter,
              eval_incidencePulledRadicand_zero c xi hd] using heq⟩,
          z.1.2⟩
      · exact Sum.inr ⟨z.1.1.1.2, by
          have hbad := z.2
          have hroot : z.1.1.1.1 = 0 := by
            by_contra hroot
            exact hbad ⟨hparameter, Or.inl hroot⟩
          have heq :=
            (eval_incidenceDiagonalPlanePolynomial_eq_zero_iff
              c xi d z.1.1.1.1 z.1.1.1.2).mp
              (BGS.External.mem_affinePlaneCurveZeros_iff.mp z.1.1.2)
          simpa [hroot] using heq.symm⟩
    inj' := by
      intro x y hxy
      by_cases hx : x.1.1.1.2 = 0
      · by_cases hy : y.1.1.1.2 = 0
        · simp only [hx, hy] at hxy
          have hpayload := Sum.inl.inj hxy
          apply Subtype.ext
          apply Prod.ext
          · apply Subtype.ext
            apply Prod.ext
            · exact congrArg (fun q => q.1.1) hpayload
            · exact hx.trans hy.symm
          · exact congrArg
              (fun q :
                ({root : ZMod p //
                    root ^ 2 = incidenceLeadingCoefficient xi} × Bool) =>
                  q.2)
              hpayload
        · simp [hx, hy] at hxy
      · by_cases hy : y.1.1.1.2 = 0
        · simp [hx, hy] at hxy
        · simp only [hx, hy] at hxy
          have hpayload := Sum.inr.inj hxy
          have hparameter : x.1.1.1.2 = y.1.1.1.2 :=
            congrArg Subtype.val hpayload
          have hxroot : x.1.1.1.1 = 0 := by
            by_contra hroot
            exact x.2 ⟨hx, Or.inl hroot⟩
          have hyroot : y.1.1.1.1 = 0 := by
            by_contra hroot
            exact y.2 ⟨hy, Or.inl hroot⟩
          have hxtag : x.1.2 = true := by
            cases htag : x.1.2
            · exact (x.2 ⟨hx, Or.inr htag⟩).elim
            · rfl
          have hytag : y.1.2 = true := by
            cases htag : y.1.2
            · exact (y.2 ⟨hy, Or.inr htag⟩).elim
            · rfl
          apply Subtype.ext
          apply Prod.ext
          · apply Subtype.ext
            exact Prod.ext (hxroot.trans hyroot.symm) hparameter
          · exact hxtag.trans hytag.symm }

/-- The diagonal exceptional set has size at most `4d + 4`. -/
theorem natCard_badIncidenceDiagonalTaggedPoint_le
    (p : Nat) [Fact p.Prime] (c xi : ZMod p)
    {d : Nat} (hd : 0 < d)
    (hregular : OrderedTraceCandidateRegular c c c xi) :
    Nat.card
        {z : IncidenceDiagonalTaggedPlanePoint p c xi d //
          ¬ IsGoodIncidenceDiagonalTaggedPoint z} ≤
      4 * d + 4 := by
  have hLeading : incidenceLeadingCoefficient xi ≠ 0 := by
    simpa only [incidenceLeadingCoefficient,
      eval_orderedTraceDiscriminantPolynomial] using hregular.1
  have hradicand : incidencePulledRadicand c xi d ≠ 0 := by
    intro hzero
    have hcoeff :=
      congrArg
        (fun q : (ZMod p)[X] => q.coeff (4 * d)) hzero
    rw [incidencePulledRadicand_coeff_four_mul c xi hd,
      coeff_zero] at hcoeff
    exact hLeading hcoeff
  have hrootBound :
      Nat.card
          {root : ZMod p //
            root ^ 2 = incidenceLeadingCoefficient xi} ≤ 2 :=
    natCard_sq_eq_le_two _
  have hradicandBound :
      Nat.card
          {parameter : ZMod p //
            (incidencePulledRadicand c xi d).eval parameter = 0} ≤
        4 * d :=
    (natCard_eval_eq_zero_le_natDegree _ hradicand).trans
      (incidencePulledRadicand_natDegree_le (ZMod p) c xi d)
  have hinjective :=
    Nat.card_le_card_of_injective
      (badIncidenceDiagonalTaggedPointEmbedding p c xi hd).toFun
      (badIncidenceDiagonalTaggedPointEmbedding p c xi hd).injective
  rw [Nat.card_sum, Nat.card_prod] at hinjective
  have hbool : Nat.card Bool = 2 := by simp
  rw [hbool] at hinjective
  omega

/-- Exact bookkeeping identity behind the diagonal comparison. -/
theorem two_mul_incidenceDiagonalPlanePoint_card_eq_pulled_add_bad
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c xi : ZMod p) (d : Nat) :
    2 *
        (BGS.External.affinePlaneCurveZeros (ZMod p)
          (incidenceDiagonalPlanePolynomial c xi d)).card =
      Nat.card (IncidencePulledRootPair p c xi xi d) +
        Nat.card
          {z : IncidenceDiagonalTaggedPlanePoint p c xi d //
            ¬ IsGoodIncidenceDiagonalTaggedPoint z} := by
  classical
  have hgood :
      Nat.card
          {z : IncidenceDiagonalTaggedPlanePoint p c xi d //
            IsGoodIncidenceDiagonalTaggedPoint z} =
        Nat.card (IncidencePulledRootPair p c xi xi d) :=
    Nat.card_congr
      (goodIncidenceDiagonalTaggedPointEquivPulled
        p hpTwo c xi d)
  have hplane :
      Nat.card (IncidenceDiagonalPlanePoint p c xi d) =
        (BGS.External.affinePlaneCurveZeros (ZMod p)
          (incidenceDiagonalPlanePolynomial c xi d)).card := by
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_coe
        (BGS.External.affinePlaneCurveZeros (ZMod p)
          (incidenceDiagonalPlanePolynomial c xi d))
  have hbool : Nat.card Bool = 2 := by simp
  calc
    2 *
          (BGS.External.affinePlaneCurveZeros (ZMod p)
            (incidenceDiagonalPlanePolynomial c xi d)).card =
        Nat.card (IncidenceDiagonalTaggedPlanePoint p c xi d) := by
          rw [Nat.card_prod, hplane, hbool]
          omega
    _ =
        Nat.card
          ({z : IncidenceDiagonalTaggedPlanePoint p c xi d //
              IsGoodIncidenceDiagonalTaggedPoint z} ⊕
            {z : IncidenceDiagonalTaggedPlanePoint p c xi d //
              ¬ IsGoodIncidenceDiagonalTaggedPoint z}) :=
      (Nat.card_congr
        (Equiv.sumCompl
          (fun z : IncidenceDiagonalTaggedPlanePoint p c xi d =>
            IsGoodIncidenceDiagonalTaggedPoint z))).symm
    _ =
        Nat.card
            {z : IncidenceDiagonalTaggedPlanePoint p c xi d //
              IsGoodIncidenceDiagonalTaggedPoint z} +
          Nat.card
            {z : IncidenceDiagonalTaggedPlanePoint p c xi d //
              ¬ IsGoodIncidenceDiagonalTaggedPoint z} :=
      Nat.card_sum
    _ =
        Nat.card (IncidencePulledRootPair p c xi xi d) +
          Nat.card
            {z : IncidenceDiagonalTaggedPlanePoint p c xi d //
              ¬ IsGoodIncidenceDiagonalTaggedPoint z} := by
      rw [hgood]

/-- The pulled diagonal cover differs from twice its plane-model count by
at most `4d + 4`. -/
theorem incidencePulledRootPair_diagonal_card_comparison
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c xi : ZMod p) {d : Nat} (hd : 0 < d)
    (hregular : OrderedTraceCandidateRegular c c c xi) :
    |(Nat.card (IncidencePulledRootPair p c xi xi d) : Int) -
        2 *
          (BGS.External.affinePlaneCurveZeros (ZMod p)
            (incidenceDiagonalPlanePolynomial c xi d)).card| ≤
      4 * d + 4 := by
  have hexact :=
    two_mul_incidenceDiagonalPlanePoint_card_eq_pulled_add_bad
      p hpTwo c xi d
  have hbad :=
    natCard_badIncidenceDiagonalTaggedPoint_le
      p c xi hd hregular
  let bad :=
    {z : IncidenceDiagonalTaggedPlanePoint p c xi d //
      ¬ IsGoodIncidenceDiagonalTaggedPoint z}
  have hid :
      (Nat.card (IncidencePulledRootPair p c xi xi d) : Int) -
          2 *
            (BGS.External.affinePlaneCurveZeros (ZMod p)
              (incidenceDiagonalPlanePolynomial c xi d)).card =
        -(Nat.card bad : Int) := by
    change
      2 *
          (BGS.External.affinePlaneCurveZeros (ZMod p)
            (incidenceDiagonalPlanePolynomial c xi d)).card =
        Nat.card (IncidencePulledRootPair p c xi xi d) +
          Nat.card bad at hexact
    exact_mod_cast
      (by omega :
        (Nat.card (IncidencePulledRootPair p c xi xi d) : Int) -
            2 *
              (BGS.External.affinePlaneCurveZeros (ZMod p)
                (incidenceDiagonalPlanePolynomial c xi d)).card =
          -(Nat.card bad : Int))
  rw [hid, abs_neg, abs_of_nonneg (Int.natCast_nonneg _)]
  exact_mod_cast hbad

/-- Rational points of the off-diagonal primitive-element plane model. -/
abbrev IncidenceOffDiagonalPlanePoint
    (p : Nat) [Fact p.Prime] (c xi eta : ZMod p) (d : Nat) :=
  ↥(BGS.External.affinePlaneCurveZeros (ZMod p)
    (incidenceOffDiagonalPlanePolynomial c xi eta d))

def IsGoodIncidenceOffDiagonalPlanePoint
    {p : Nat} [Fact p.Prime] {c xi eta : ZMod p} {d : Nat}
    (z : IncidenceOffDiagonalPlanePoint p c xi eta d) : Prop :=
  z.1.1 ≠ 0 ∧ z.1.2 ≠ 0

def IsGoodIncidenceOffDiagonalPulledPair
    {p : Nat} [Fact p.Prime] {c xi eta : ZMod p} {d : Nat}
    (z : IncidencePulledRootPair p c xi eta d) : Prop :=
  z.firstRoot + z.secondRoot ≠ 0

/-- A good pulled root pair maps to the primitive sum-root plane point. -/
def goodIncidenceOffDiagonalPulledToPlane
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c xi eta : ZMod p) (d : Nat) :
    {z : IncidencePulledRootPair p c xi eta d //
      IsGoodIncidenceOffDiagonalPulledPair z} →
      {z : IncidenceOffDiagonalPlanePoint p c xi eta d //
        IsGoodIncidenceOffDiagonalPlanePoint z} := fun z => by
  let sumRoot := z.1.firstRoot + z.1.secondRoot
  refine ⟨⟨(sumRoot, (z.1.parameter : ZMod p)), ?_⟩,
    z.2, z.1.parameter.ne_zero⟩
  apply BGS.External.mem_affinePlaneCurveZeros_iff.mpr
  apply
    (eval_incidenceOffDiagonalPlanePolynomial_eq_zero_iff_exists_rootPair
      (BGS.Markoff.two_ne_zero_zmod
        (lt_of_le_of_ne
          (Fact.out : p.Prime).two_le (Ne.symm hpTwo)))
      c xi eta d z.2).mpr
  exact ⟨z.1.firstRoot, z.1.secondRoot, z.1.firstEquation,
    z.1.secondEquation, rfl⟩

theorem goodIncidenceOffDiagonalPulledToPlane_bijective
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c xi eta : ZMod p) (d : Nat) :
    Function.Bijective
      (goodIncidenceOffDiagonalPulledToPlane
        p hpTwo c xi eta d) := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    BGS.Markoff.two_ne_zero_zmod
      (lt_of_le_of_ne
        (Fact.out : p.Prime).two_le (Ne.symm hpTwo))
  constructor
  · intro x y hxy
    have hsum :
        x.1.firstRoot + x.1.secondRoot =
          y.1.firstRoot + y.1.secondRoot :=
      congrArg (fun z => z.1.1.1) hxy
    have hparameter : x.1.parameter = y.1.parameter := by
      apply Units.ext
      exact congrArg (fun z => z.1.1.2) hxy
    have hfirstSq :
        x.1.firstRoot ^ 2 = y.1.firstRoot ^ 2 := by
      rw [x.1.firstEquation, y.1.firstEquation, hparameter]
    have hsecondSq :
        x.1.secondRoot ^ 2 = y.1.secondRoot ^ 2 := by
      rw [x.1.secondEquation, y.1.secondEquation, hparameter]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hfirstSq with
      hfirst | hfirst
    · apply Subtype.ext
      apply IncidencePulledRootPair.ext hparameter hfirst
      linear_combination hsum - hfirst
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsecondSq with
        hsecond | hsecond
      · have hfirstZero : x.1.firstRoot = 0 := by
          have : (2 : ZMod p) * x.1.firstRoot = 0 := by
            rw [two_mul]
            linear_combination hsum - hsecond + hfirst
          exact (mul_eq_zero.mp this).resolve_left h2
        apply Subtype.ext
        apply IncidencePulledRootPair.ext hparameter
        · have hyfirstZero : y.1.firstRoot = 0 := by
            linear_combination hfirst - hfirstZero
          simp [hfirstZero, hyfirstZero]
        · exact hsecond
      · have hsumZero :
            x.1.firstRoot + x.1.secondRoot = 0 := by
          have :
              (2 : ZMod p) *
                  (x.1.firstRoot + x.1.secondRoot) = 0 := by
            rw [two_mul]
            linear_combination hsum + hfirst + hsecond
          exact (mul_eq_zero.mp this).resolve_left h2
        exact (x.2 hsumZero).elim
  · intro z
    have hexists :=
      (eval_incidenceOffDiagonalPlanePolynomial_eq_zero_iff_exists_rootPair
        h2 c xi eta d z.2.1).mp
        (BGS.External.mem_affinePlaneCurveZeros_iff.mp z.1.2)
    rcases hexists with
      ⟨firstRoot, secondRoot, hfirst, hsecond, hsum⟩
    let parameter : (ZMod p)ˣ :=
      Units.mk0 z.1.1.2 z.2.2
    let pulled : IncidencePulledRootPair p c xi eta d :=
      { parameter := parameter
        firstRoot := firstRoot
        secondRoot := secondRoot
        firstEquation := by simpa [parameter] using hfirst
        secondEquation := by simpa [parameter] using hsecond }
    have hpulledGood :
        IsGoodIncidenceOffDiagonalPulledPair pulled := by
      change firstRoot + secondRoot ≠ 0
      rw [hsum]
      exact z.2.1
    refine ⟨⟨pulled, hpulledGood⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact hsum
    · rfl

def goodIncidenceOffDiagonalPulledEquivPlane
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c xi eta : ZMod p) (d : Nat) :
    {z : IncidencePulledRootPair p c xi eta d //
      IsGoodIncidenceOffDiagonalPulledPair z} ≃
      {z : IncidenceOffDiagonalPlanePoint p c xi eta d //
        IsGoodIncidenceOffDiagonalPlanePoint z} :=
  Equiv.ofBijective _
    (goodIncidenceOffDiagonalPulledToPlane_bijective
      p hpTwo c xi eta d)

/-- The difference of two pulled radicands has degree at most `4d`. -/
theorem incidencePulledRadicand_sub_natDegree_le
    {K : Type*} [Field K] (c xi eta : K) (d : Nat) :
    (incidencePulledRadicand c xi d -
        incidencePulledRadicand c eta d).natDegree ≤ 4 * d :=
  (natDegree_sub_le _ _).trans
    (max_le
      (incidencePulledRadicand_natDegree_le K c xi d)
      (incidencePulledRadicand_natDegree_le K c eta d))

/-- Coprimality and nonunitness ensure that two admissible pulled
radicands are not identical. -/
theorem incidencePulledRadicand_sub_ne_zero
    {K : Type*} [Field K] {c xi eta : K}
    (hc : c ^ 2 ≠ 4)
    (hxi : OrderedTraceCandidateRegular c c c xi)
    (heta : OrderedTraceCandidateRegular c c c eta)
    (hpair : IsHasseWeilReadyIncidencePair c xi eta)
    {d : Nat} (hd : 0 < d) :
    incidencePulledRadicand c xi d -
        incidencePulledRadicand c eta d ≠ 0 := by
  intro hzero
  have heq :
      incidencePulledRadicand c xi d =
        incidencePulledRadicand c eta d :=
    sub_eq_zero.mp hzero
  have hcoprime :=
    incidencePulledRadicand_isCoprime
      hc hxi heta hpair hd
  rw [heq] at hcoprime
  have hunit :
      IsUnit (incidencePulledRadicand c eta d) :=
    isCoprime_self.mp hcoprime
  exact incidencePulledRadicand_not_isUnit heta hd hunit

/-- Bad pulled pairs inject into a root of the radicand difference together
with one of at most two square roots. -/
def badIncidenceOffDiagonalPulledEmbedding
    (p : Nat) [Fact p.Prime] (c xi eta : ZMod p) (d : Nat) :
    {z : IncidencePulledRootPair p c xi eta d //
      ¬ IsGoodIncidenceOffDiagonalPulledPair z} ↪
      (Σ parameter :
          {t : ZMod p //
            (incidencePulledRadicand c xi d -
              incidencePulledRadicand c eta d).eval t = 0},
        {root : ZMod p //
          root ^ 2 =
            (incidencePulledRadicand c xi d).eval parameter.1}) :=
  { toFun := fun z => by
      have hsum : z.1.firstRoot + z.1.secondRoot = 0 :=
        not_ne_iff.mp z.2
      have hsecond :
          z.1.secondRoot = -z.1.firstRoot := by
        linear_combination hsum
      have hevals :
          (incidencePulledRadicand c xi d).eval
              (z.1.parameter : ZMod p) =
            (incidencePulledRadicand c eta d).eval
              (z.1.parameter : ZMod p) := by
        rw [← z.1.firstEquation, ← z.1.secondEquation, hsecond]
        ring
      exact
        ⟨⟨(z.1.parameter : ZMod p), by
            simp only [eval_sub, hevals, sub_self]⟩,
          ⟨z.1.firstRoot, z.1.firstEquation⟩⟩
    inj' := by
      intro x y hxy
      have hparameter : x.1.parameter = y.1.parameter := by
        apply Units.ext
        exact congrArg (fun z => (z.1.1 : ZMod p)) hxy
      have hfirst : x.1.firstRoot = y.1.firstRoot :=
        congrArg (fun z => z.2.1) hxy
      have hxsum :
          x.1.firstRoot + x.1.secondRoot = 0 :=
        not_ne_iff.mp x.2
      have hysum :
          y.1.firstRoot + y.1.secondRoot = 0 :=
        not_ne_iff.mp y.2
      apply Subtype.ext
      apply IncidencePulledRootPair.ext hparameter hfirst
      linear_combination hxsum - hysum - hfirst }

/-- The bad pulled-pair locus has size at most `8d`. -/
theorem badIncidenceOffDiagonalPulled_card_le
    (p : Nat) [Fact p.Prime] (c xi eta : ZMod p)
    {d : Nat} (hd : 0 < d)
    (hc : c ^ 2 ≠ 4)
    (hxi : OrderedTraceCandidateRegular c c c xi)
    (heta : OrderedTraceCandidateRegular c c c eta)
    (hpair : IsHasseWeilReadyIncidencePair c xi eta) :
    Nat.card
        {z : IncidencePulledRootPair p c xi eta d //
          ¬ IsGoodIncidenceOffDiagonalPulledPair z} ≤
      8 * d := by
  let difference :=
    incidencePulledRadicand c xi d -
      incidencePulledRadicand c eta d
  let base := {t : ZMod p // difference.eval t = 0}
  let fiber : base → Type := fun t =>
    {root : ZMod p //
      root ^ 2 =
        (incidencePulledRadicand c xi d).eval t.1}
  have hinj :=
    Nat.card_le_card_of_injective
      (badIncidenceOffDiagonalPulledEmbedding
        p c xi eta d).toFun
      (badIncidenceOffDiagonalPulledEmbedding
        p c xi eta d).injective
  change Nat.card _ ≤ Nat.card (Σ t : base, fiber t) at hinj
  rw [Nat.card_sigma] at hinj
  have hfiber : ∀ t : base, Nat.card (fiber t) ≤ 2 :=
    fun t => natCard_sq_eq_le_two _
  have hsum :
      ∑ t : base, Nat.card (fiber t) ≤
        ∑ _t : base, 2 :=
    Finset.sum_le_sum fun t _ => hfiber t
  have hbase : Nat.card base ≤ 4 * d := by
    exact
      (natCard_eval_eq_zero_le_natDegree difference
        (by
          exact incidencePulledRadicand_sub_ne_zero
            hc hxi heta hpair hd)).trans
        (incidencePulledRadicand_sub_natDegree_le
          c xi eta d)
  have hsum' :
      ∑ t : base, Nat.card (fiber t) ≤
        Nat.card base * 2 := by
    simpa using hsum
  omega

/-- The off-diagonal primitive quartic specialized to parameter zero. -/
def incidenceOffDiagonalZeroParameterPolynomial
    {K : Type*} [Field K]
    (c xi eta : K) (d : Nat) : K[X] :=
  (X ^ 2 -
      C ((incidencePulledRadicand c xi d).eval 0 +
        (incidencePulledRadicand c eta d).eval 0)) ^ 2 -
    C (4 *
      (incidencePulledRadicand c xi d).eval 0 *
      (incidencePulledRadicand c eta d).eval 0)

theorem eval_incidenceOffDiagonalZeroParameterPolynomial
    {K : Type*} [Field K]
    (c xi eta sumRoot : K) (d : Nat) :
    (incidenceOffDiagonalZeroParameterPolynomial
        c xi eta d).eval sumRoot =
      MvPolynomial.eval ![sumRoot, 0]
        (incidenceOffDiagonalPlanePolynomial c xi eta d) := by
  rw [eval_incidenceOffDiagonalPlanePolynomial]
  simp [incidenceOffDiagonalZeroParameterPolynomial]

theorem incidenceOffDiagonalZeroParameterPolynomial_natDegree_le
    {K : Type*} [Field K]
    (c xi eta : K) (d : Nat) :
    (incidenceOffDiagonalZeroParameterPolynomial
        c xi eta d).natDegree ≤ 4 := by
  unfold incidenceOffDiagonalZeroParameterPolynomial
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_pow_le).trans (by
      have hinside :
          (X ^ 2 -
              C ((incidencePulledRadicand c xi d).eval 0 +
                (incidencePulledRadicand c eta d).eval 0) :
            K[X]).natDegree ≤ 2 :=
        (natDegree_sub_le _ _).trans
          (max_le
            (natDegree_X_pow_le 2)
            ((natDegree_C _).le.trans (by omega)))
      omega)
  · exact (natDegree_C _).le.trans (by omega)

theorem incidenceOffDiagonalZeroParameterPolynomial_ne_zero
    {K : Type*} [Field K]
    (c xi eta : K) (d : Nat) :
    incidenceOffDiagonalZeroParameterPolynomial
        c xi eta d ≠ 0 := by
  have hquadratic :
      IsMonicOfDegree
        (X ^ 2 -
            C ((incidencePulledRadicand c xi d).eval 0 +
              (incidencePulledRadicand c eta d).eval 0) :
          K[X]) 2 :=
    (isMonicOfDegree_X_pow K 2).sub (by simp)
  have hmonic :
      (incidenceOffDiagonalZeroParameterPolynomial
        c xi eta d).Monic := by
    unfold incidenceOffDiagonalZeroParameterPolynomial
    exact ((hquadratic.pow 2).sub (by
      have hpos : 0 < 2 * 2 := by norm_num
      simpa only [natDegree_C] using hpos)).monic
  exact hmonic.ne_zero

/-- Bad primitive-plane points lie either above `t = 0`, or at a root of
the pulled-radicand difference. -/
def badIncidenceOffDiagonalPlaneEmbedding
    (p : Nat) [Fact p.Prime]
    (c xi eta : ZMod p) (d : Nat) :
    {z : IncidenceOffDiagonalPlanePoint p c xi eta d //
      ¬ IsGoodIncidenceOffDiagonalPlanePoint z} ↪
      {sumRoot : ZMod p //
        (incidenceOffDiagonalZeroParameterPolynomial
          c xi eta d).eval sumRoot = 0} ⊕
      {parameter : ZMod p //
        (incidencePulledRadicand c xi d -
          incidencePulledRadicand c eta d).eval parameter = 0} :=
  { toFun := fun z => by
      by_cases hparameter : z.1.1.2 = 0
      · exact Sum.inl ⟨z.1.1.1, by
          rw [eval_incidenceOffDiagonalZeroParameterPolynomial]
          simpa [hparameter] using
            (BGS.External.mem_affinePlaneCurveZeros_iff.mp z.1.2)⟩
      · have hsumRoot : z.1.1.1 = 0 := by
          by_contra hsum
          exact z.2 ⟨hsum, hparameter⟩
        have hplane :=
          BGS.External.mem_affinePlaneCurveZeros_iff.mp z.1.2
        have hquartic :
            ((incidencePulledRadicand c xi d).eval z.1.1.2 -
              (incidencePulledRadicand c eta d).eval z.1.1.2) ^ 2 =
              0 := by
          rw [eval_incidenceOffDiagonalPlanePolynomial] at hplane
          rw [hsumRoot] at hplane
          linear_combination hplane
        have hevals :
            (incidencePulledRadicand c xi d).eval z.1.1.2 =
              (incidencePulledRadicand c eta d).eval z.1.1.2 :=
          sub_eq_zero.mp
            (mul_self_eq_zero.mp (by
              simpa [pow_two] using hquartic))
        exact Sum.inr ⟨z.1.1.2, by
          simp only [eval_sub, hevals, sub_self]⟩
    inj' := by
      intro x y hxy
      by_cases hx : x.1.1.2 = 0
      · by_cases hy : y.1.1.2 = 0
        · simp only [hx, hy] at hxy
          have hpayload := Sum.inl.inj hxy
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext
            (congrArg Subtype.val hpayload) (hx.trans hy.symm)
        · simp [hx, hy] at hxy
      · by_cases hy : y.1.1.2 = 0
        · simp [hx, hy] at hxy
        · simp only [hx, hy] at hxy
          have hpayload := Sum.inr.inj hxy
          have hparameter : x.1.1.2 = y.1.1.2 :=
            congrArg Subtype.val hpayload
          have hxsum : x.1.1.1 = 0 := by
            by_contra hsum
            exact x.2 ⟨hsum, hx⟩
          have hysum : y.1.1.1 = 0 := by
            by_contra hsum
            exact y.2 ⟨hsum, hy⟩
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext (hxsum.trans hysum.symm) hparameter }

/-- The bad primitive-plane locus has size at most `4d + 4`. -/
theorem badIncidenceOffDiagonalPlane_card_le
    (p : Nat) [Fact p.Prime] (c xi eta : ZMod p)
    {d : Nat} (hd : 0 < d)
    (hc : c ^ 2 ≠ 4)
    (hxi : OrderedTraceCandidateRegular c c c xi)
    (heta : OrderedTraceCandidateRegular c c c eta)
    (hpair : IsHasseWeilReadyIncidencePair c xi eta) :
    Nat.card
        {z : IncidenceOffDiagonalPlanePoint p c xi eta d //
          ¬ IsGoodIncidenceOffDiagonalPlanePoint z} ≤
      4 * d + 4 := by
  have hinj :=
    Nat.card_le_card_of_injective
      (badIncidenceOffDiagonalPlaneEmbedding
        p c xi eta d).toFun
      (badIncidenceOffDiagonalPlaneEmbedding
        p c xi eta d).injective
  rw [Nat.card_sum] at hinj
  have hzeroParameter :
      Nat.card
          {sumRoot : ZMod p //
            (incidenceOffDiagonalZeroParameterPolynomial
              c xi eta d).eval sumRoot = 0} ≤ 4 :=
    (natCard_eval_eq_zero_le_natDegree _
      (incidenceOffDiagonalZeroParameterPolynomial_ne_zero
        c xi eta d)).trans
      (incidenceOffDiagonalZeroParameterPolynomial_natDegree_le
        c xi eta d)
  have hdifference :
      Nat.card
          {parameter : ZMod p //
            (incidencePulledRadicand c xi d -
              incidencePulledRadicand c eta d).eval parameter = 0} ≤
        4 * d :=
    (natCard_eval_eq_zero_le_natDegree _
      (incidencePulledRadicand_sub_ne_zero
        hc hxi heta hpair hd)).trans
      (incidencePulledRadicand_sub_natDegree_le
        c xi eta d)
  omega

/-- The pulled off-diagonal cover differs from its primitive plane model by
at most `12d + 4`. -/
theorem incidencePulledRootPair_offDiagonal_card_comparison
    (p : Nat) [Fact p.Prime] (hpTwo : p ≠ 2)
    (c xi eta : ZMod p) {d : Nat} (hd : 0 < d)
    (hc : c ^ 2 ≠ 4)
    (hxi : OrderedTraceCandidateRegular c c c xi)
    (heta : OrderedTraceCandidateRegular c c c eta)
    (hpair : IsHasseWeilReadyIncidencePair c xi eta) :
    |(Nat.card (IncidencePulledRootPair p c xi eta d) : Int) -
        (BGS.External.affinePlaneCurveZeros (ZMod p)
          (incidenceOffDiagonalPlanePolynomial c xi eta d)).card| ≤
      12 * d + 4 := by
  classical
  letI : Finite (IncidencePulledRootPair p c xi eta d) :=
    Finite.of_injective
      (fun z => (z.parameter, z.firstRoot, z.secondRoot)) (by
        intro x y h
        apply IncidencePulledRootPair.ext
        · exact congrArg Prod.fst h
        · exact congrArg (fun q => q.2.1) h
        · exact congrArg (fun q => q.2.2) h)
  let goodPulled :=
    {z : IncidencePulledRootPair p c xi eta d //
      IsGoodIncidenceOffDiagonalPulledPair z}
  let badPulled :=
    {z : IncidencePulledRootPair p c xi eta d //
      ¬ IsGoodIncidenceOffDiagonalPulledPair z}
  let goodPlane :=
    {z : IncidenceOffDiagonalPlanePoint p c xi eta d //
      IsGoodIncidenceOffDiagonalPlanePoint z}
  let badPlane :=
    {z : IncidenceOffDiagonalPlanePoint p c xi eta d //
      ¬ IsGoodIncidenceOffDiagonalPlanePoint z}
  have hsplitPulled :
      Nat.card (IncidencePulledRootPair p c xi eta d) =
        Nat.card goodPulled + Nat.card badPulled := by
    calc
      Nat.card (IncidencePulledRootPair p c xi eta d) =
          Nat.card (goodPulled ⊕ badPulled) :=
        (Nat.card_congr
          (Equiv.sumCompl
            (fun z : IncidencePulledRootPair p c xi eta d =>
              IsGoodIncidenceOffDiagonalPulledPair z))).symm
      _ = Nat.card goodPulled + Nat.card badPulled :=
        Nat.card_sum
  have hplaneCard :
      Nat.card (IncidenceOffDiagonalPlanePoint p c xi eta d) =
        (BGS.External.affinePlaneCurveZeros (ZMod p)
          (incidenceOffDiagonalPlanePolynomial c xi eta d)).card := by
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_coe
        (BGS.External.affinePlaneCurveZeros (ZMod p)
          (incidenceOffDiagonalPlanePolynomial c xi eta d))
  have hsplitPlane :
      (BGS.External.affinePlaneCurveZeros (ZMod p)
          (incidenceOffDiagonalPlanePolynomial c xi eta d)).card =
        Nat.card goodPlane + Nat.card badPlane := by
    calc
      _ = Nat.card
          (IncidenceOffDiagonalPlanePoint p c xi eta d) :=
        hplaneCard.symm
      _ = Nat.card (goodPlane ⊕ badPlane) :=
        (Nat.card_congr
          (Equiv.sumCompl
            (fun z :
                IncidenceOffDiagonalPlanePoint p c xi eta d =>
              IsGoodIncidenceOffDiagonalPlanePoint z))).symm
      _ = Nat.card goodPlane + Nat.card badPlane :=
        Nat.card_sum
  have hgood :
      Nat.card goodPulled = Nat.card goodPlane :=
    Nat.card_congr
      (goodIncidenceOffDiagonalPulledEquivPlane
        p hpTwo c xi eta d)
  have hbadPulled : Nat.card badPulled ≤ 8 * d :=
    badIncidenceOffDiagonalPulled_card_le
      p c xi eta hd hc hxi heta hpair
  have hbadPlane : Nat.card badPlane ≤ 4 * d + 4 :=
    badIncidenceOffDiagonalPlane_card_le
      p c xi eta hd hc hxi heta hpair
  have herror :
      |(Nat.card (IncidencePulledRootPair p c xi eta d) : Int) -
          (BGS.External.affinePlaneCurveZeros (ZMod p)
            (incidenceOffDiagonalPlanePolynomial
              c xi eta d)).card| ≤
        Nat.card badPulled + Nat.card badPlane := by
    rw [hsplitPulled, hsplitPlane, hgood]
    push_cast
    have habs :=
      abs_sub (Nat.card badPulled : Int)
        (Nat.card badPlane : Int)
    simpa using habs
  exact herror.trans
    (by
      exact_mod_cast
        (by omega :
          Nat.card badPulled + Nat.card badPlane ≤
            12 * d + 4))

end

end GenMarkoff.Symmetric.Cage
