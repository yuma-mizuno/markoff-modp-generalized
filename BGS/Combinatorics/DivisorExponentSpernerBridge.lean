import BGS.Combinatorics.DivisorExponentCoefficient

/-!
# The divisor-antichain central-coefficient bound

This is the semantic bridge missing from a purely executable factorization
payload: the recomputed central coefficient really bounds every antichain in
the represented divisor exponent lattice.
-/

namespace BGS.NumberTheory

open BGS.Combinatorics

theorem divisorExponentAntichain_card_le_centralDivisorRankCoefficient
    (factors : List PrimePowerFactor)
    (antichain : Finset (DivisorExponentBox factors))
    (hantichain :
      IsAntichain (· ≤ ·) (antichain : Set (DivisorExponentBox factors))) :
    antichain.card ≤ centralDivisorRankCoefficient factors := by
  letI := divisorExponentBoxFintype factors
  letI := divisorExponentBoxPartialOrder factors
  have hcentral :=
    (divisorExponentBoxDecomposition factors).antichain_card_le_central_rank
      antichain hantichain
  rw [divisorExponentTotal_eq_primePowerTotalExponent] at hcentral
  rw [centralDivisorRankCoefficient_eq_layer_card]
  exact hcentral

end BGS.NumberTheory
