module

public import GenMarkoff.General.MiddleGame.ActualDiagonalization
public import GenMarkoff.General.MiddleGame.ActualMoveWiring
public import GenMarkoff.General.MiddleGame.ActualParameters
public import GenMarkoff.ShiftedTrace.MiddleGame.ShiftedCorvajaZannier
public import GenMarkoff.ShiftedTrace.MiddleGame.ActualOrderEscape
public import GenMarkoff.General.MiddleGame.RotationEigenvalueOrder
public import GenMarkoff.ShiftedTrace.MiddleGame.WeightedShiftedCorvajaZannier
public import BGS.Markoff.MiddleGame.OrderEscape

@[expose] public section

/-!
# Candidate regularity under field maps and parabolic rotation orders

Two facts used when passing between `ZMod p` and its quadratic extension and
when bounding actual rotation orders:

* `OrderedTraceCandidateRegular` is preserved by injective field
  homomorphisms (`orderedTraceCandidateRegular_map`) and reflected by field
  homomorphisms (`orderedTraceCandidateRegular_of_map`);
* for an odd prime `p`, both parabolic traces `t = ±2` in `ZMod p` have actual
  rotation linear order `p` (`rotationLinearOrder_eq_prime_of_parabolicTrace`).
-/

namespace GenMarkoff.General.MiddleGame

open BGS.Markoff
open GenMarkoff.ShiftedTrace.MiddleGame

noncomputable section

/-- Candidate regularity is preserved by an injective field homomorphism. -/
theorem orderedTraceCandidateRegular_map
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (hf : Function.Injective f)
    {A B C t : K} (h : OrderedTraceCandidateRegular A B C t) :
    OrderedTraceCandidateRegular (f A) (f B) (f C) (f t) := by
  rcases h with ⟨hD, htA, hcenter, hweight, hminus, hplus⟩
  simp only [eval_orderedTraceDiscriminantPolynomial] at hD ⊢
  simp only [eval_orderedTraceCenteredNormPolynomial] at hcenter ⊢
  simp only [eval_orderedTraceWeightDifferencePolynomial] at hweight ⊢
  simp only [eval_orderedTraceEvenMinusPolynomial] at hminus ⊢
  simp only [eval_orderedTraceEvenPlusPolynomial] at hplus ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hD
  · simpa using (map_ne_zero_iff f hf).mpr htA
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hcenter
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hweight
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hminus
  · simpa [map_ofNat] using (map_ne_zero_iff f hf).mpr hplus

/-- Candidate regularity is reflected by a field homomorphism. -/
theorem orderedTraceCandidateRegular_of_map
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) {A B C t : K}
    (h :
      OrderedTraceCandidateRegular (f A) (f B) (f C) (f t)) :
    OrderedTraceCandidateRegular A B C t := by
  rcases h with ⟨hD, htA, hcenter, hweight, hminus, hplus⟩
  simp only [eval_orderedTraceDiscriminantPolynomial] at hD ⊢
  simp only [eval_orderedTraceCenteredNormPolynomial] at hcenter ⊢
  simp only [eval_orderedTraceWeightDifferencePolynomial] at hweight ⊢
  simp only [eval_orderedTraceEvenMinusPolynomial] at hminus ⊢
  simp only [eval_orderedTraceEvenPlusPolynomial] at hplus ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    apply hD
    simpa [map_ofNat] using congrArg f hzero
  · intro hzero
    apply htA
    simpa using congrArg f hzero
  · intro hzero
    apply hcenter
    simpa [map_ofNat] using congrArg f hzero
  · intro hzero
    apply hweight
    simpa [map_ofNat] using congrArg f hzero
  · intro hzero
    apply hminus
    simpa [map_ofNat] using congrArg f hzero
  · intro hzero
    apply hplus
    simpa [map_ofNat] using congrArg f hzero

/-- For odd `p`, both parabolic traces `t = ±2` have actual rotation linear
order `p`.  Their `BGS.Markoff.rotationOrder` values are `p` and `2p`; dividing
by `gcd (·) 2` gives `p` in both cases. -/
theorem rotationLinearOrder_eq_prime_of_parabolicTrace
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (t : ZMod p) (hparabolic : t ^ 2 = 4) :
    rotationLinearOrder t = p := by
  rcases (normalizedTrace_sq_eq_four_iff_parabolic p t).mp hparabolic with
    ht | ht
  · rw [ht, Opening.rotationLinearOrder_eq_bgsRotationOrder_div_gcd,
      rotationOrder_two]
    have hcoprime : Nat.Coprime p 2 :=
      ((Fact.out : p.Prime).odd_of_ne_two hpTwo).coprime_two_right
    rw [hcoprime.gcd_eq_one]
    simp
  · rw [ht, Opening.rotationLinearOrder_eq_bgsRotationOrder_div_gcd,
      rotationOrder_neg_two p hpTwo]
    simp

end

end GenMarkoff.General.MiddleGame
