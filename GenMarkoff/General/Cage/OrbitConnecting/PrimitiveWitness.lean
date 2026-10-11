module

public import GenMarkoff.General.Cage.Connecting.PrimitiveWitness
public import GenMarkoff.General.Cage.OrbitConnecting.ThreeRootEstimate

@[expose] public section

/-!
# Exact-order orbit-connecting witness pairs

The one-sided Möbius inversion of `BGS.NumberTheory.OneSidedPrimitiveWitness`
turns the orbit-connecting three-root estimate into a count of pairs `(w, q)`
of a good orbit-connecting witness `w` and a unit `q` of exact order `p - 1`
with `w.middle = splitTorusTrace q`
(`orbitConnectingGoodThreeRootExactOrderSolutions`).

This file bounds the number of such pairs over a fixed middle trace: there
are at most eight witnesses (two signs for each of three square roots) and at
most two split-torus parameters, hence at most sixteen pairs.  The finite
sieves in `GenMarkoff.General.Cage.OrbitConnecting.PairPrimitiveWitness` use
this bound to remove finitely many middle traces at a cost of sixteen pairs
each.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff Polynomial
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

/-- The finite set of pairs `(w, q)` of a good orbit-connecting witness and a
unit `q` of order `Nat.card (ZMod p)ˣ` with
`w.1.middle = splitTorusTrace q`. -/
noncomputable abbrev orbitConnectingGoodThreeRootExactOrderSolutions
    (p : ℕ) [Fact p.Prime]
    (alpha gamma k omegaInv centerB centerC : ZMod p) :=
  BGS.rightTraceExactOrderSolutions
    (fun w :
      OrbitConnectingGoodThreeRootWitness
        alpha gamma k omegaInv centerB centerC => w.1.middle)
    (splitTorusTrace : (ZMod p)ˣ → ZMod p)
    (Nat.card (ZMod p)ˣ)

/-- For one fixed middle trace, the three square-root choices give at most
eight good orbit-connecting witnesses. -/
theorem natCard_orbitConnectingGoodThreeRootWitness_fixed_middle_le_eight
    (p : ℕ) [Fact p.Prime]
    (alpha gamma k omegaInv centerB centerC t : ZMod p) :
    Nat.card
        {w :
            OrbitConnectingGoodThreeRootWitness
              alpha gamma k omegaInv centerB centerC //
          w.1.middle = t} ≤ 8 := by
  let f : (ZMod p)[X] :=
    C (orbitComponentRadicand alpha k (t - gamma))
  let g : (ZMod p)[X] :=
    C (orbitOppositeComponentRadicand alpha k (t - gamma))
  let h : (ZMod p)[X] :=
    C (omegaInv * centeredNorm centerB centerC t)
  let target := ThreeSquareRootFiber f g h 0
  let embedding :
      {w :
          OrbitConnectingGoodThreeRootWitness
            alpha gamma k omegaInv centerB centerC //
        w.1.middle = t} ↪ target :=
    { toFun := fun w =>
        { firstRoot := w.1.1.plusRoot
          secondRoot := w.1.1.minusRoot
          thirdRoot := w.1.1.thirdRoot
          firstEquation := by
            simpa [f] using
              w.1.1.plusEquation.trans
                (congrArg
                  (fun s =>
                    orbitComponentRadicand alpha k (s - gamma))
                  w.2)
          secondEquation := by
            simpa [g] using
              w.1.1.minusEquation.trans
                (congrArg
                  (fun s =>
                    orbitOppositeComponentRadicand alpha k (s - gamma))
                  w.2)
          thirdEquation := by
            simpa [h] using
              w.1.1.thirdEquation.trans
                (congrArg
                  (fun s =>
                    omegaInv * centeredNorm centerB centerC s)
                  w.2) }
      inj' := by
        intro w z hwz
        apply Subtype.ext
        apply Subtype.ext
        exact OrbitConnectingThreeRootWitness.ext
          (w.2.trans z.2.symm)
          (congrArg (fun q : target => q.firstRoot) hwz)
          (congrArg (fun q : target => q.secondRoot) hwz)
          (congrArg (fun q : target => q.thirdRoot) hwz) }
  exact
    (Nat.card_le_card_of_injective
      embedding.toFun embedding.injective).trans
      (natCard_threeSquareRootFiber_le_eight f g h 0)

/-- A fixed middle trace supports at most sixteen exact-order
orbit-connecting pairs. -/
theorem
    orbitConnectingGoodThreeRootExactOrderSolutions_fixed_middle_card_le_sixteen
    (p : ℕ) [Fact p.Prime]
    (alpha gamma k omegaInv centerB centerC t : ZMod p) :
    ((orbitConnectingGoodThreeRootExactOrderSolutions
        p alpha gamma k omegaInv centerB centerC).filter fun z =>
          z.1.1.middle = t).card ≤ 16 := by
  classical
  let primitive :=
    orbitConnectingGoodThreeRootExactOrderSolutions
      p alpha gamma k omegaInv centerB centerC
  let source := ↥(primitive.filter fun z => z.1.1.middle = t)
  let target :=
    {w :
        OrbitConnectingGoodThreeRootWitness
          alpha gamma k omegaInv centerB centerC //
      w.1.middle = t} ×
    {q : (ZMod p)ˣ // splitTorusTrace q = t}
  let embedding : source ↪ target :=
    { toFun := fun z =>
        (⟨z.1.1, (Finset.mem_filter.mp z.2).2⟩,
          ⟨z.1.2, by
            have hz :=
              (BGS.mem_rightTraceExactOrderSolutions_iff
                (fun w :
                  OrbitConnectingGoodThreeRootWitness
                    alpha gamma k omegaInv centerB centerC =>
                      w.1.middle)
                (splitTorusTrace : (ZMod p)ˣ → ZMod p)
                (Nat.card (ZMod p)ˣ) z.1).mp
                (Finset.mem_filter.mp z.2).1
            exact hz.1.symm.trans (Finset.mem_filter.mp z.2).2⟩)
      inj' := by
        intro z w hzw
        apply Subtype.ext
        exact Prod.ext
          (congrArg (fun q : target =>
            (q.1.1 :
              OrbitConnectingGoodThreeRootWitness
                alpha gamma k omegaInv centerB centerC)) hzw)
          (congrArg (fun q : target => (q.2.1 : (ZMod p)ˣ)) hzw) }
  have hcard :=
    Nat.card_le_card_of_injective embedding.toFun embedding.injective
  -- `source` and `target` are local names for a `Finset` subtype and a
  -- product type; state `hcard` in these terms so that
  -- `Nat.card_eq_fintype_card`, `Fintype.card_coe` and `Nat.card_prod`
  -- rewrite it.
  change Nat.card source ≤ Nat.card target at hcard
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_prod] at hcard
  have hwitness :=
    natCard_orbitConnectingGoodThreeRootWitness_fixed_middle_le_eight
      p alpha gamma k omegaInv centerB centerC t
  have hunit := natCard_splitTorusTrace_fiber_le_two p t
  exact hcard.trans <|
    (Nat.mul_le_mul hwitness hunit).trans (by norm_num)

end

end GenMarkoff.General.Cage
