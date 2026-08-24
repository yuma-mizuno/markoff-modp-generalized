import GenMarkoff.General.Cage.IncidenceAlgebra

/-!
# Finite relays for the coefficient-ordered incidence obstruction

Fix the first coordinate as the outer coordinate.  A prospective relay label
is therefore regular in the single ordered frame

`(a.a1, a.a2, a.a3)`.

For either endpoint, at most two relay labels annihilate the unequal
pair-obstruction polynomial.  Consequently:

* five labels suffice if a diagonal step is admitted separately; and
* seven labels suffice for two genuinely off-diagonal,
  obstruction-regular incidence pairs.

## New considerations in the unequal-coefficient generalization

* Every endpoint and relay is required to be candidate regular in the same
  coefficient order `(a.a1, a.a2, a.a3)`.  No coordinate permutation is used
  to turn the second pair around; only the proved symmetry of
  `incidencePairObstruction` is used.
* Avoiding the two quadratic bad sets does not itself avoid a diagonal.
  The five-label statement therefore records a
  diagonal-or-obstruction-regular alternative.  To obtain two genuinely
  off-diagonal obstruction-regular pairs, the
  seven-label statement additionally deletes the two endpoint labels.
* Nonvanishing of the formal resultants needs the separately ordered
  condition `a.a2 ^ 2 ≠ 4`, because `a.a2` is the shared middle coefficient
  in this first-axis incidence model.

These are finite-label and resultant statements only.  No parity
connectivity or incidence point count is asserted.
-/

namespace GenMarkoff.General.Cage

open Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- A finite collection of labels, all candidate regular in the canonical
first-axis coefficient order. -/
def IsFirstAxisCandidateRegularLabelSet
    (a : Coefficients K) (labels : Finset K) : Prop :=
  ∀ t ∈ labels,
    OrderedTraceCandidateRegular a.a1 a.a2 a.a3 t

/-- The diagonal is handled independently of the off-diagonal
obstruction-regular condition. -/
def IsDiagonalOrOffDiagonalObstructionRegularIncidencePair
    (a : Coefficients K) (xi eta : K) : Prop :=
  xi = eta ∨ IsOffDiagonalObstructionRegularIncidencePair a xi eta

/-- Five canonical candidate-regular labels contain a relay around the two
quadratic obstruction sets.  A relay coinciding with an endpoint is retained
as an explicit diagonal case. -/
theorem exists_diagonalOrOffDiagonalObstructionRegular_firstAxis_relay
    (a : Coefficients K) (labels : Finset K)
    (hlabels : IsFirstAxisCandidateRegularLabelSet a labels)
    (xi eta : K)
    (hxi : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hcard : 4 < labels.card) :
    ∃ relay ∈ labels,
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 relay ∧
        IsDiagonalOrOffDiagonalObstructionRegularIncidencePair a xi relay ∧
          IsDiagonalOrOffDiagonalObstructionRegularIncidencePair
            a relay eta := by
  classical
  let badXi := incidencePairObstructionBadTraces a xi
  let badEta := incidencePairObstructionBadTraces a eta
  have hbadXi : badXi.card ≤ 2 := by
    simpa [badXi] using
      incidencePairObstructionBadTraces_card_le_two a xi
  have hbadEta : badEta.card ≤ 2 := by
    simpa [badEta] using
      incidencePairObstructionBadTraces_card_le_two a eta
  have hunion : (badXi ∪ badEta).card ≤ 4 := by
    calc
      (badXi ∪ badEta).card ≤ badXi.card + badEta.card :=
        Finset.card_union_le _ _
      _ ≤ 2 + 2 := Nat.add_le_add hbadXi hbadEta
      _ = 4 := by norm_num
  have hexists : ∃ relay ∈ labels, relay ∉ badXi ∪ badEta := by
    by_contra hnone
    have hsubset : labels ⊆ badXi ∪ badEta := by
      intro relay hrelay
      by_contra hrelayBad
      exact hnone ⟨relay, hrelay, hrelayBad⟩
    have hle := Finset.card_le_card hsubset
    omega
  obtain ⟨relay, hrelay, hrelayBad⟩ := hexists
  have hrelayRegular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 relay :=
    hlabels relay hrelay
  have hnotBadXi : relay ∉ badXi := by
    intro hmem
    exact hrelayBad (Finset.mem_union_left badEta hmem)
  have hnotBadEta : relay ∉ badEta := by
    intro hmem
    exact hrelayBad (Finset.mem_union_right badXi hmem)
  have hobsXi :
      incidencePairObstruction a xi relay ≠ 0 := by
    intro hzero
    exact hnotBadXi
      ((mem_incidencePairObstructionBadTraces_iff
        a xi relay hxi).2 hzero)
  have hobsEta :
      incidencePairObstruction a eta relay ≠ 0 := by
    intro hzero
    exact hnotBadEta
      ((mem_incidencePairObstructionBadTraces_iff
        a eta relay heta).2 hzero)
  have hobsRelayEta :
      incidencePairObstruction a relay eta ≠ 0 := by
    rw [incidencePairObstruction_comm]
    exact hobsEta
  refine ⟨relay, hrelay, hrelayRegular, ?_, ?_⟩
  · by_cases hEq : xi = relay
    · exact Or.inl hEq
    · exact Or.inr ⟨hEq, hobsXi⟩
  · by_cases hEq : relay = eta
    · exact Or.inl hEq
    · exact Or.inr ⟨hEq, hobsRelayEta⟩

/-- Seven canonical candidate-regular labels contain a relay distinct from
both endpoints and outside both quadratic obstruction sets.  Thus both
incidence pairs are genuinely off-diagonal and obstruction-regular, including
when the original endpoints themselves coincide. -/
theorem exists_offDiagonalObstructionRegular_firstAxis_relay
    (a : Coefficients K) (labels : Finset K)
    (hlabels : IsFirstAxisCandidateRegularLabelSet a labels)
    (xi eta : K)
    (hxi : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hcard : 6 < labels.card) :
    ∃ relay ∈ labels,
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 relay ∧
        IsOffDiagonalObstructionRegularIncidencePair a xi relay ∧
          IsOffDiagonalObstructionRegularIncidencePair a relay eta := by
  classical
  let badXi := incidencePairObstructionBadTraces a xi
  let badEta := incidencePairObstructionBadTraces a eta
  let endpoints : Finset K := {xi, eta}
  have hbadXi : badXi.card ≤ 2 := by
    simpa [badXi] using
      incidencePairObstructionBadTraces_card_le_two a xi
  have hbadEta : badEta.card ≤ 2 := by
    simpa [badEta] using
      incidencePairObstructionBadTraces_card_le_two a eta
  have hbadUnion : (badXi ∪ badEta).card ≤ 4 := by
    calc
      (badXi ∪ badEta).card ≤ badXi.card + badEta.card :=
        Finset.card_union_le _ _
      _ ≤ 2 + 2 := Nat.add_le_add hbadXi hbadEta
      _ = 4 := by norm_num
  have hendpoints : endpoints.card ≤ 2 := by
    simpa [endpoints] using
      (Finset.card_le_two (a := xi) (b := eta))
  have hforbidden :
      ((badXi ∪ badEta) ∪ endpoints).card ≤ 6 := by
    calc
      ((badXi ∪ badEta) ∪ endpoints).card ≤
          (badXi ∪ badEta).card + endpoints.card :=
        Finset.card_union_le _ _
      _ ≤ 4 + 2 := Nat.add_le_add hbadUnion hendpoints
      _ = 6 := by norm_num
  have hexists :
      ∃ relay ∈ labels,
        relay ∉ (badXi ∪ badEta) ∪ endpoints := by
    by_contra hnone
    have hsubset :
        labels ⊆ (badXi ∪ badEta) ∪ endpoints := by
      intro relay hrelay
      by_contra hrelayForbidden
      exact hnone ⟨relay, hrelay, hrelayForbidden⟩
    have hle := Finset.card_le_card hsubset
    omega
  obtain ⟨relay, hrelay, hrelayForbidden⟩ := hexists
  have hnotBadUnion : relay ∉ badXi ∪ badEta := by
    intro hmem
    exact hrelayForbidden
      (Finset.mem_union_left endpoints hmem)
  have hnotBadXi : relay ∉ badXi := by
    intro hmem
    exact hnotBadUnion (Finset.mem_union_left badEta hmem)
  have hnotBadEta : relay ∉ badEta := by
    intro hmem
    exact hnotBadUnion (Finset.mem_union_right badXi hmem)
  have hnotEndpoints : relay ∉ endpoints := by
    intro hmem
    exact hrelayForbidden
      (Finset.mem_union_right (badXi ∪ badEta) hmem)
  have hrelayNeXi : relay ≠ xi := by
    intro hEq
    apply hnotEndpoints
    simp [endpoints, hEq]
  have hrelayNeEta : relay ≠ eta := by
    intro hEq
    apply hnotEndpoints
    simp [endpoints, hEq]
  have hobsXi :
      incidencePairObstruction a xi relay ≠ 0 := by
    intro hzero
    exact hnotBadXi
      ((mem_incidencePairObstructionBadTraces_iff
        a xi relay hxi).2 hzero)
  have hobsEta :
      incidencePairObstruction a eta relay ≠ 0 := by
    intro hzero
    exact hnotBadEta
      ((mem_incidencePairObstructionBadTraces_iff
        a eta relay heta).2 hzero)
  have hobsRelayEta :
      incidencePairObstruction a relay eta ≠ 0 := by
    rw [incidencePairObstruction_comm]
    exact hobsEta
  exact
    ⟨relay, hrelay, hlabels relay hrelay,
      ⟨hrelayNeXi.symm, hobsXi⟩,
      ⟨hrelayNeEta, hobsRelayEta⟩⟩

/-- Resultant-ready form of the seven-label relay.  The extra hypothesis is
the ordered middle-coefficient condition specific to this incidence chart. -/
theorem exists_nonzero_incidencePairResultant_firstAxis_relay
    (a : Coefficients K) (labels : Finset K)
    (hlabels : IsFirstAxisCandidateRegularLabelSet a labels)
    (hA2 : a.a2 ^ 2 ≠ 4)
    (xi eta : K)
    (hxi : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi)
    (heta : OrderedTraceCandidateRegular a.a1 a.a2 a.a3 eta)
    (hcard : 6 < labels.card) :
    ∃ relay ∈ labels,
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 relay ∧
        IsOffDiagonalObstructionRegularIncidencePair a xi relay ∧
          IsOffDiagonalObstructionRegularIncidencePair a relay eta ∧
            incidencePairResultant a xi relay ≠ 0 ∧
              incidencePairResultant a relay eta ≠ 0 := by
  obtain ⟨relay, hrelay, hrelayRegular, hxiRelay, hrelayEta⟩ :=
    exists_offDiagonalObstructionRegular_firstAxis_relay
      a labels hlabels xi eta hxi heta hcard
  exact
    ⟨relay, hrelay, hrelayRegular, hxiRelay, hrelayEta,
      hxiRelay.resultant_ne_zero hA2,
      hrelayEta.resultant_ne_zero hA2⟩

end

end GenMarkoff.General.Cage
