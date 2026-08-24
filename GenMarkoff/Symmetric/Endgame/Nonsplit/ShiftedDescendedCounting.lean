import GenMarkoff.Symmetric.Endgame.Nonsplit.ShiftedDescendedIrreducibility

/-!
# Counting the shifted descended nonsplit curve

The Cayley chart omits exactly the identity of the norm-one torus.  This file
identifies the affine zero count with the nonidentity torus count and bounds
the omitted identity fiber by `2e`.
-/

namespace GenMarkoff.Symmetric.Endgame.Nonsplit

open Polynomial
open BGS.Markoff

noncomputable section

variable (p : ℕ) [Fact p.Prime]

private abbrev F := ZMod p
private abbrev E := quadraticFiniteField p

noncomputable local instance : DecidableEq (quadraticNormOneTorus p) :=
  Classical.decEq _

def shiftedSeededNonsplitDescendedSolutions
    (s : (E p)ˣ) (gamma : F p) (d e : ℕ) :
    Finset (F p × (F p)ˣ) := by
  classical
  exact Finset.univ.filter fun z =>
    MvPolynomial.eval ![z.1, (z.2 : F p)]
      (shiftedSeededNonsplitDescendedPolynomial p s gamma d e) = 0

@[simp]
theorem mem_shiftedSeededNonsplitDescendedSolutions_iff
    (s : (E p)ˣ) (gamma : F p) (d e : ℕ)
    (z : F p × (F p)ˣ) :
    z ∈ shiftedSeededNonsplitDescendedSolutions p s gamma d e ↔
      MvPolynomial.eval ![z.1, (z.2 : F p)]
        (shiftedSeededNonsplitDescendedPolynomial p s gamma d e) = 0 := by
  classical
  simp [shiftedSeededNonsplitDescendedSolutions]

def shiftedSeededNonsplitNonidentitySolutions
    (k : (F p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : F p) (d e : ℕ) :
    Finset ({w : quadraticNormOneTorus p // w ≠ 1} × (F p)ˣ) := by
  classical
  exact Finset.univ.filter fun z =>
    ShiftedSeededNonsplitTraceCoverEquation
      p k s gamma d e z.1.1 z.2

@[simp]
theorem mem_shiftedSeededNonsplitNonidentitySolutions_iff
    (k : (F p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : F p) (d e : ℕ)
    (z : {w : quadraticNormOneTorus p // w ≠ 1} × (F p)ˣ) :
    z ∈ shiftedSeededNonsplitNonidentitySolutions p k s gamma d e ↔
      ShiftedSeededNonsplitTraceCoverEquation
        p k s gamma d e z.1.1 z.2 := by
  classical
  simp [shiftedSeededNonsplitNonidentitySolutions]

theorem shiftedSeededNonsplitDescendedSolutions_card_eq_nonidentity_card
    (k : (F p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : F p) (d e : ℕ) :
    (shiftedSeededNonsplitDescendedSolutions p s.1 gamma d e).card =
      (shiftedSeededNonsplitNonidentitySolutions
        p k s gamma d e).card := by
  classical
  apply Finset.card_bij'
      (fun z _ => ((quadraticCayleyParameterEquiv p z.1), z.2))
      (fun z _ => ((quadraticCayleyParameterEquiv p).symm z.1, z.2))
  · intro z hz
    rw [mem_shiftedSeededNonsplitNonidentitySolutions_iff]
    change ShiftedSeededNonsplitTraceCoverEquation
      p k s gamma d e (quadraticCayleyPoint p z.1) z.2
    rw [←
      eval_shiftedSeededNonsplitDescendedPolynomial_eq_zero_iff
        p k s gamma d e z.1 z.2]
    exact
      (mem_shiftedSeededNonsplitDescendedSolutions_iff
        p s.1 gamma d e z).mp hz
  · intro z hz
    apply Prod.ext
    · exact (quadraticCayleyParameterEquiv p).symm_apply_apply z.1
    · rfl
  · intro z hz
    apply Prod.ext
    · exact (quadraticCayleyParameterEquiv p).apply_symm_apply z.1
    · rfl
  · intro z hz
    rw [mem_shiftedSeededNonsplitDescendedSolutions_iff]
    rw [eval_shiftedSeededNonsplitDescendedPolynomial_eq_zero_iff]
    have hzEquation :=
      (mem_shiftedSeededNonsplitNonidentitySolutions_iff
        p k s gamma d e z).mp hz
    have hpoint := congrArg Subtype.val
      ((quadraticCayleyParameterEquiv p).apply_symm_apply z.1)
    change
      quadraticCayleyPoint p ((quadraticCayleyParameterEquiv p).symm z.1) =
        z.1.1 at hpoint
    rw [hpoint]
    exact hzEquation

theorem eval_shiftedSeededNonsplitDescendedPolynomial_zero_second_ne_zero
    (s : (E p)ˣ) (gamma : F p) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e) (z : F p) :
    MvPolynomial.eval ![z, (0 : F p)]
      (shiftedSeededNonsplitDescendedPolynomial p s gamma d e) ≠ 0 := by
  rw [eval_shiftedSeededNonsplitDescendedPolynomial]
  have he0 : e ≠ 0 := Nat.ne_of_gt he
  have htwoe0 : 2 * e ≠ 0 := by omega
  rw [zero_pow he0, zero_pow htwoe0]
  simp only [mul_zero, zero_add, mul_one, zero_sub, neg_ne_zero]
  exact
    pow_ne_zero d (quadraticCayleyNormPolynomial_eval_ne_zero p z)

private theorem affineShiftedDescendedZero_second_ne_zero
    (s : (E p)ˣ) (gamma : F p) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e) (z : F p × F p)
    (hz : z ∈ BGS.External.affinePlaneCurveZeros (F p)
      (shiftedSeededNonsplitDescendedPolynomial p s gamma d e)) :
    z.2 ≠ 0 := by
  intro hzero
  have hzEval := (BGS.External.mem_affinePlaneCurveZeros_iff).mp hz
  rw [hzero] at hzEval
  exact
    eval_shiftedSeededNonsplitDescendedPolynomial_zero_second_ne_zero
      p s gamma d e hd he z.1 hzEval

theorem affinePlaneCurveZeros_shiftedSeededNonsplitDescendedPolynomial_card_eq
    (s : (E p)ˣ) (gamma : F p) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e) :
    (BGS.External.affinePlaneCurveZeros (F p)
      (shiftedSeededNonsplitDescendedPolynomial p s gamma d e)).card =
      (shiftedSeededNonsplitDescendedSolutions p s gamma d e).card := by
  classical
  apply Finset.card_bij'
      (fun z hz => (z.1, Units.mk0 z.2
        (affineShiftedDescendedZero_second_ne_zero
          p s gamma d e hd he z hz)))
      (fun z _ => (z.1, (z.2 : F p)))
  · intro z hz
    rw [mem_shiftedSeededNonsplitDescendedSolutions_iff]
    exact (BGS.External.mem_affinePlaneCurveZeros_iff).mp hz
  · intro z hz
    apply Prod.ext <;> rfl
  · intro z hz
    apply Prod.ext
    · rfl
    · apply Units.ext
      rfl
  · intro z hz
    rw [BGS.External.mem_affinePlaneCurveZeros_iff]
    exact
      (mem_shiftedSeededNonsplitDescendedSolutions_iff
        p s gamma d e z).mp hz

def shiftedSeededNonsplitTraceCurveSolutions
    (k : (F p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : F p) (d e : ℕ) :
    Finset (quadraticNormOneTorus p × (F p)ˣ) := by
  classical
  exact Finset.univ.filter fun z =>
    ShiftedSeededNonsplitTraceCoverEquation
      p k s gamma d e z.1 z.2

@[simp]
theorem mem_shiftedSeededNonsplitTraceCurveSolutions_iff
    (k : (F p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : F p) (d e : ℕ)
    (z : quadraticNormOneTorus p × (F p)ˣ) :
    z ∈ shiftedSeededNonsplitTraceCurveSolutions p k s gamma d e ↔
      ShiftedSeededNonsplitTraceCoverEquation
        p k s gamma d e z.1 z.2 := by
  classical
  simp [shiftedSeededNonsplitTraceCurveSolutions]

def shiftedSeededNonsplitIdentityBoundarySolutions
    (k : (F p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : F p) (d e : ℕ) : Finset (F p)ˣ := by
  classical
  exact Finset.univ.filter fun u =>
    ShiftedSeededNonsplitTraceCoverEquation
      p k s gamma d e 1 u

@[simp]
theorem mem_shiftedSeededNonsplitIdentityBoundarySolutions_iff
    (k : (F p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : F p) (d e : ℕ) (u : (F p)ˣ) :
    u ∈ shiftedSeededNonsplitIdentityBoundarySolutions
      p k s gamma d e ↔
      ShiftedSeededNonsplitTraceCoverEquation
        p k s gamma d e 1 u := by
  classical
  simp [shiftedSeededNonsplitIdentityBoundarySolutions]

private theorem shiftedNonidentityFilter_card_eq
    (k : (F p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : F p) (d e : ℕ) :
    ((shiftedSeededNonsplitTraceCurveSolutions
      p k s gamma d e).filter fun z => z.1 ≠ 1).card =
      (shiftedSeededNonsplitNonidentitySolutions
        p k s gamma d e).card := by
  classical
  apply Finset.card_bij'
      (fun z hz => (⟨z.1, (Finset.mem_filter.mp hz).2⟩, z.2))
      (fun z _ => (z.1.1, z.2))
  · intro z hz
    apply Prod.ext <;> rfl
  · intro z hz
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  · intro z hz
    rw [mem_shiftedSeededNonsplitNonidentitySolutions_iff]
    exact
      (mem_shiftedSeededNonsplitTraceCurveSolutions_iff
        p k s gamma d e z).mp (Finset.mem_filter.mp hz).1
  · intro z hz
    rw [Finset.mem_filter]
    exact ⟨
      (mem_shiftedSeededNonsplitTraceCurveSolutions_iff
        p k s gamma d e _).mpr
          ((mem_shiftedSeededNonsplitNonidentitySolutions_iff
            p k s gamma d e z).mp hz),
      z.1.2⟩

private theorem shiftedIdentityFilter_card_eq
    (k : (F p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : F p) (d e : ℕ) :
    ((shiftedSeededNonsplitTraceCurveSolutions
      p k s gamma d e).filter fun z => ¬ z.1 ≠ 1).card =
      (shiftedSeededNonsplitIdentityBoundarySolutions
        p k s gamma d e).card := by
  classical
  apply Finset.card_bij'
      (fun z _ => z.2)
      (fun u _ => (1, u))
  · intro z hz
    apply Prod.ext
    · exact (not_ne_iff.mp (Finset.mem_filter.mp hz).2).symm
    · rfl
  · intro u hu
    rfl
  · intro z hz
    rw [mem_shiftedSeededNonsplitIdentityBoundarySolutions_iff]
    have hzMem := Finset.mem_filter.mp hz
    have hone : z.1 = 1 := not_ne_iff.mp hzMem.2
    simpa [hone] using
      (mem_shiftedSeededNonsplitTraceCurveSolutions_iff
        p k s gamma d e z).mp hzMem.1
  · intro u hu
    rw [Finset.mem_filter]
    exact ⟨
      (mem_shiftedSeededNonsplitTraceCurveSolutions_iff
        p k s gamma d e _).mpr
          ((mem_shiftedSeededNonsplitIdentityBoundarySolutions_iff
            p k s gamma d e u).mp hu),
      by simp⟩

theorem shiftedSeededNonsplitTraceCurveSolutions_card_eq_descended_add_boundary
    (k : (F p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : F p) (d e : ℕ) :
    (shiftedSeededNonsplitTraceCurveSolutions
      p k s gamma d e).card =
      (shiftedSeededNonsplitDescendedSolutions
        p s.1 gamma d e).card +
      (shiftedSeededNonsplitIdentityBoundarySolutions
        p k s gamma d e).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := shiftedSeededNonsplitTraceCurveSolutions
      p k s gamma d e) (fun z => z.1 ≠ 1)
  rw [shiftedNonidentityFilter_card_eq p k s gamma d e,
    ← shiftedSeededNonsplitDescendedSolutions_card_eq_nonidentity_card
      p k s gamma d e,
    shiftedIdentityFilter_card_eq p k s gamma d e] at hsplit
  exact hsplit.symm

def shiftedSeededNonsplitIdentityBoundaryPolynomial
    (s : E p) (gamma : F p) (e : ℕ) : Polynomial (F p) :=
  X ^ (2 * e) -
    C (Algebra.trace (F p) (E p) s + gamma) * X ^ e + 1

theorem shiftedSeededNonsplitIdentityBoundaryEquation_iff
    (k : (F p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : F p) (d e : ℕ) (u : (F p)ˣ) :
    ShiftedSeededNonsplitTraceCoverEquation
      p k s gamma d e 1 u ↔
      (shiftedSeededNonsplitIdentityBoundaryPolynomial
        p (s.1 : E p) gamma e).eval (u : F p) = 0 := by
  unfold ShiftedSeededNonsplitTraceCoverEquation
    shiftedSeededNonsplitIdentityBoundaryPolynomial
  simp only [one_pow, Subgroup.coe_one, Units.val_one, mul_one,
    splitTorusTrace, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_one]
  rw [Nat.mul_comm 2 e, pow_mul]
  constructor
  · intro h
    field_simp [Units.ne_zero u] at h
    linear_combination -h
  · intro h
    field_simp [Units.ne_zero u]
    linear_combination -h

theorem shiftedSeededNonsplitIdentityBoundaryPolynomial_ne_zero
    (s : E p) (gamma : F p) (e : ℕ) (he : 0 < e) :
    shiftedSeededNonsplitIdentityBoundaryPolynomial p s gamma e ≠ 0 := by
  intro hzero
  have hcoeff :=
    congrArg (fun P : Polynomial (F p) => P.coeff 0) hzero
  have he0 : e ≠ 0 := Nat.ne_of_gt he
  have h0e : 0 ≠ e := he0.symm
  have htwoe0 : 2 * e ≠ 0 := by omega
  have h0twoe : 0 ≠ 2 * e := htwoe0.symm
  simp [shiftedSeededNonsplitIdentityBoundaryPolynomial,
    he0, h0e, htwoe0, h0twoe] at hcoeff

theorem shiftedSeededNonsplitIdentityBoundaryPolynomial_natDegree_le
    (s : E p) (gamma : F p) (e : ℕ) :
    (shiftedSeededNonsplitIdentityBoundaryPolynomial
      p s gamma e).natDegree ≤ 2 * e := by
  unfold shiftedSeededNonsplitIdentityBoundaryPolynomial
  refine (Polynomial.natDegree_add_le _ _).trans
    (max_le ?_ (by simp))
  refine (Polynomial.natDegree_sub_le _ _).trans
    (max_le (by simp) ?_)
  exact Polynomial.natDegree_mul_le.trans (by simp; omega)

theorem shiftedSeededNonsplitIdentityBoundarySolutions_card_le
    (k : (F p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : F p) (d e : ℕ) (he : 0 < e) :
    (shiftedSeededNonsplitIdentityBoundarySolutions
      p k s gamma d e).card ≤ 2 * e := by
  classical
  let P :=
    shiftedSeededNonsplitIdentityBoundaryPolynomial
      p (s.1 : E p) gamma e
  have hP : P ≠ 0 :=
    shiftedSeededNonsplitIdentityBoundaryPolynomial_ne_zero
      p _ gamma e he
  have hmaps : Set.MapsTo (fun u : (F p)ˣ => (u : F p))
      ↑(shiftedSeededNonsplitIdentityBoundarySolutions
        p k s gamma d e) P.roots.toFinset := by
    intro u hu
    change (u : F p) ∈ P.roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact
      (shiftedSeededNonsplitIdentityBoundaryEquation_iff
        p k s gamma d e u).mp
        ((mem_shiftedSeededNonsplitIdentityBoundarySolutions_iff
          p k s gamma d e u).mp hu)
  have hinj : Set.InjOn (fun u : (F p)ˣ => (u : F p))
      ↑(shiftedSeededNonsplitIdentityBoundarySolutions
        p k s gamma d e) := by
    intro u hu v hv huv
    exact Units.ext huv
  calc
    _ ≤ P.roots.toFinset.card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ 2 * e :=
      shiftedSeededNonsplitIdentityBoundaryPolynomial_natDegree_le
        p _ gamma e

/-- Exact comparison between the full shifted torus count and the affine
descended count, with the omitted identity fiber displayed separately. -/
theorem shiftedSeededNonsplitTraceCurveSolutions_card_eq_affine_add_boundary
    (k : (F p)ˣ) (s : ↥(quadraticNormFiber p k))
    (gamma : F p) (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    (shiftedSeededNonsplitTraceCurveSolutions
      p k s gamma d e).card =
      (BGS.External.affinePlaneCurveZeros (F p)
        (shiftedSeededNonsplitDescendedPolynomial
          p s.1 gamma d e)).card +
      (shiftedSeededNonsplitIdentityBoundarySolutions
        p k s gamma d e).card := by
  rw [
    shiftedSeededNonsplitTraceCurveSolutions_card_eq_descended_add_boundary]
  rw [←
    affinePlaneCurveZeros_shiftedSeededNonsplitDescendedPolynomial_card_eq
      p s.1 gamma d e hd he]

end

end GenMarkoff.Symmetric.Endgame.Nonsplit
