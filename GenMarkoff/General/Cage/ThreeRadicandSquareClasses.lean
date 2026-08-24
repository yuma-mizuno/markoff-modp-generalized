import GenMarkoff.General.Cage.ConnectingPairwiseCoprime
import BGS.Markoff.Incidence.Geometry

/-!
# Seven square classes from three pairwise-disjoint radicands

The three-root counting identity uses one ordinary hyperelliptic plane for
each nonempty product of three radicands.  Pairwise coprimality and
squarefreeness make all seven products squarefree.  If the three individual
radicands are nonunits, all seven products are therefore nonsquares in the
rational function field.
-/

namespace GenMarkoff.General.Cage

open Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- Squarefreeness of every nonempty product of three pairwise-coprime
squarefree polynomials. -/
theorem sevenRadicandProducts_squarefree
    {f g h : K[X]}
    (hf : Squarefree f) (hg : Squarefree g) (hh : Squarefree h)
    (hfg : IsCoprime f g) (hfh : IsCoprime f h)
    (hgh : IsCoprime g h) :
    Squarefree f ∧
      Squarefree g ∧
      Squarefree h ∧
      Squarefree (f * g) ∧
      Squarefree (f * h) ∧
      Squarefree (g * h) ∧
      Squarefree (f * g * h) := by
  have hfgSquarefree :
      Squarefree (f * g) :=
    squarefree_mul_iff.mpr ⟨hfg.isRelPrime, hf, hg⟩
  have hfhSquarefree :
      Squarefree (f * h) :=
    squarefree_mul_iff.mpr ⟨hfh.isRelPrime, hf, hh⟩
  have hghSquarefree :
      Squarefree (g * h) :=
    squarefree_mul_iff.mpr ⟨hgh.isRelPrime, hg, hh⟩
  have hfg_h : IsCoprime (f * g) h :=
    hfh.mul_left hgh
  have htripleSquarefree :
      Squarefree (f * g * h) :=
    squarefree_mul_iff.mpr
      ⟨hfg_h.isRelPrime, hfgSquarefree, hh⟩
  exact
    ⟨hf, hg, hh, hfgSquarefree, hfhSquarefree, hghSquarefree,
      htripleSquarefree⟩

/-- Every nonempty product of three pairwise-coprime squarefree nonunits is
a nonsquare in the rational function field. -/
theorem sevenRadicandProducts_not_isSquare_ratFunc
    {f g h : K[X]}
    (hf : Squarefree f) (hg : Squarefree g) (hh : Squarefree h)
    (hfg : IsCoprime f g) (hfh : IsCoprime f h)
    (hgh : IsCoprime g h)
    (hfUnit : ¬ IsUnit f) (hgUnit : ¬ IsUnit g)
    (hhUnit : ¬ IsUnit h) :
    (¬ IsSquare (algebraMap K[X] (RatFunc K) f)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) g)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) h)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g))) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * h))) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (g * h))) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g * h))) := by
  obtain ⟨hfSq, hgSq, hhSq, hfgSq, hfhSq, hghSq, htripleSq⟩ :=
    sevenRadicandProducts_squarefree hf hg hh hfg hfh hgh
  refine
    ⟨BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hfSq hfUnit,
      BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hgSq hgUnit,
      BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hhSq hhUnit,
      BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hfgSq ?_,
      BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hfhSq ?_,
      BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        hghSq ?_,
      BGS.Markoff.not_isSquare_algebraMap_of_squarefree_not_isUnit
        htripleSq ?_⟩
  · intro hunit
    exact hfUnit (IsUnit.mul_iff.mp hunit).1
  · intro hunit
    exact hfUnit (IsUnit.mul_iff.mp hunit).1
  · intro hunit
    exact hgUnit (IsUnit.mul_iff.mp hunit).1
  · intro hunit
    exact hfUnit
      (IsUnit.mul_iff.mp (IsUnit.mul_iff.mp hunit).1).1

/-- The three unequal connecting-cage radicands have all seven nontrivial
rational-function square classes after replacing the centered pullback by
its reduced representative. -/
theorem connectingSevenRadicandProducts_not_isSquare_ratFunc
    (h2 : (2 : K) ≠ 0)
    {a : Coefficients K} {xi eta : K}
    (hA1 : a.a1 ^ 2 ≠ 4)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (hmoving : (a.a3, a.a1) ≠ (0, 0))
    (hxi :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hpair : IsConnectingIncidencePair a xi eta)
    {d : ℕ} (hd : 0 < d) (hdegree : (d : K) ≠ 0) :
    let f := incidencePulledRadicand a xi d
    let g := incidencePulledRadicand a eta d
    let h := centeredNormReducedPulledRadicand a.a3 a.a1 d
    (¬ IsSquare (algebraMap K[X] (RatFunc K) f)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) g)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) h)) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g))) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * h))) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (g * h))) ∧
      (¬ IsSquare (algebraMap K[X] (RatFunc K) (f * g * h))) := by
  dsimp only
  obtain ⟨hf, hg, hfgSquarefree⟩ :=
    incidencePulledRadicand_squarefree_and_product
      h2 hA2 hxi heta hpair hd hdegree
  have hh :
      Squarefree
        (centeredNormReducedPulledRadicand a.a3 a.a1 d) :=
    centeredNormReducedPulledRadicand_squarefree
      hA3 hA1 hmoving hd hdegree
  have hfg :
      IsCoprime (incidencePulledRadicand a xi d)
        (incidencePulledRadicand a eta d) :=
    incidencePulledRadicand_isCoprime hA2 hxi heta hpair hd
  obtain ⟨hfh, hgh⟩ :=
    connectingIncidencePair_coprime_centeredNormReducedPulledRadicand
      hxi heta hpair hd
  exact
    sevenRadicandProducts_not_isSquare_ratFunc
      hf hg hh hfg hfh hgh
      (incidencePulledRadicand_not_isUnit hxi hd)
      (incidencePulledRadicand_not_isUnit heta hd)
      (centeredNormReducedPulledRadicand_not_isUnit a.a3 a.a1 hd)

end

end GenMarkoff.General.Cage
