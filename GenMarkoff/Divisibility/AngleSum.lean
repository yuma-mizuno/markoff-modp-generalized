import Mathlib

/-!
# The abstract three-angle summation argument

This is the coefficient-independent finite-sum core of Martin's orbit-
divisibility proof.  It deliberately knows nothing about Markoff surfaces.
The geometric work is exactly the construction of the three weights and their
pairing identities.
-/

namespace GenMarkoff

universe u v

/-- Let a finite set be invariant under three permutations.  If three weights
sum pointwise to `s`, and the `i`-th weight pairs to `s` across the `i`-th
permutation, then `s * |C| = 0` in the coefficient ring.

No division by two is used in this summation argument. -/
theorem multiplier_mul_card_cast_eq_zero_of_three_angle_system
    {X : Type u} {F : Type v} [CommRing F]
    (sigma1 sigma2 sigma3 : Equiv.Perm X)
    (delta1 delta2 delta3 : X → F) (s : F)
    (C : Finset X)
    (hC1 : ∀ x, sigma1 x ∈ C ↔ x ∈ C)
    (hC2 : ∀ x, sigma2 x ∈ C ↔ x ∈ C)
    (hC3 : ∀ x, sigma3 x ∈ C ↔ x ∈ C)
    (htotal : ∀ x, delta1 x + delta2 x + delta3 x = s)
    (hpair1 : ∀ x, delta1 x + delta1 (sigma1 x) = s)
    (hpair2 : ∀ x, delta2 x + delta2 (sigma2 x) = s)
    (hpair3 : ∀ x, delta3 x + delta3 (sigma3 x) = s) :
    s * (C.card : F) = 0 := by
  classical
  have hreindex1 :
      (∑ x : C, delta1 (sigma1 x.1)) = ∑ x : C, delta1 x.1 := by
    simpa [Equiv.Perm.subtypePerm_apply] using
      (Equiv.sum_comp (sigma1.subtypePerm hC1) (fun x : C ↦ delta1 x.1))
  have hreindex2 :
      (∑ x : C, delta2 (sigma2 x.1)) = ∑ x : C, delta2 x.1 := by
    simpa [Equiv.Perm.subtypePerm_apply] using
      (Equiv.sum_comp (sigma2.subtypePerm hC2) (fun x : C ↦ delta2 x.1))
  have hreindex3 :
      (∑ x : C, delta3 (sigma3 x.1)) = ∑ x : C, delta3 x.1 := by
    simpa [Equiv.Perm.subtypePerm_apply] using
      (Equiv.sum_comp (sigma3.subtypePerm hC3) (fun x : C ↦ delta3 x.1))
  have hsum1 :
      (2 : F) * (∑ x : C, delta1 x.1) = s * (C.card : F) := by
    calc
      (2 : F) * (∑ x : C, delta1 x.1) =
          (∑ x : C, delta1 x.1) + ∑ x : C, delta1 x.1 := by ring
      _ = (∑ x : C, delta1 x.1) + ∑ x : C, delta1 (sigma1 x.1) := by
        rw [hreindex1]
      _ = ∑ x : C, (delta1 x.1 + delta1 (sigma1 x.1)) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ _x : C, s := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact hpair1 x.1
      _ = s * (C.card : F) := by simp [mul_comm]
  have hsum2 :
      (2 : F) * (∑ x : C, delta2 x.1) = s * (C.card : F) := by
    calc
      (2 : F) * (∑ x : C, delta2 x.1) =
          (∑ x : C, delta2 x.1) + ∑ x : C, delta2 x.1 := by ring
      _ = (∑ x : C, delta2 x.1) + ∑ x : C, delta2 (sigma2 x.1) := by
        rw [hreindex2]
      _ = ∑ x : C, (delta2 x.1 + delta2 (sigma2 x.1)) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ _x : C, s := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact hpair2 x.1
      _ = s * (C.card : F) := by simp [mul_comm]
  have hsum3 :
      (2 : F) * (∑ x : C, delta3 x.1) = s * (C.card : F) := by
    calc
      (2 : F) * (∑ x : C, delta3 x.1) =
          (∑ x : C, delta3 x.1) + ∑ x : C, delta3 x.1 := by ring
      _ = (∑ x : C, delta3 x.1) + ∑ x : C, delta3 (sigma3 x.1) := by
        rw [hreindex3]
      _ = ∑ x : C, (delta3 x.1 + delta3 (sigma3 x.1)) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ _x : C, s := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact hpair3 x.1
      _ = s * (C.card : F) := by simp [mul_comm]
  have htotalSum :
      (∑ x : C, delta1 x.1) + (∑ x : C, delta2 x.1) +
          (∑ x : C, delta3 x.1) = s * (C.card : F) := by
    calc
      (∑ x : C, delta1 x.1) + (∑ x : C, delta2 x.1) +
            (∑ x : C, delta3 x.1) =
          ∑ x : C, (delta1 x.1 + delta2 x.1 + delta3 x.1) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = ∑ _x : C, s := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact htotal x.1
      _ = s * (C.card : F) := by simp [mul_comm]
  linear_combination 2 * htotalSum - hsum1 - hsum2 - hsum3

/-- The corrected algebraic factorization for the zero-coordinate cycle sum
in arXiv:2509.02187v3.  The published display has the wrong second factor. -/
theorem geometric_cycle_pair_sum_factor
    {F : Type u} [CommSemiring F] (q d0 d1 : F) (N : ℕ) :
    (∑ k ∈ Finset.range N, (q ^ k * d1 + q ^ (k + 1) * d0)) =
      (∑ k ∈ Finset.range N, q ^ k) * (d1 + q * d0) := by
  calc
    (∑ k ∈ Finset.range N, (q ^ k * d1 + q ^ (k + 1) * d0)) =
        ∑ k ∈ Finset.range N, q ^ k * (d1 + q * d0) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [pow_succ]
      ring
    _ = (∑ k ∈ Finset.range N, q ^ k) * (d1 + q * d0) := by
      rw [Finset.sum_mul]

/-- If `q` is a nontrivial `N`-th root of unity, the corrected cycle sum
vanishes. -/
theorem geometric_cycle_pair_sum_eq_zero
    {F : Type u} [Field F] {q : F} {N : ℕ}
    (hq : q ≠ 1) (hpow : q ^ N = 1) (d0 d1 : F) :
    (∑ k ∈ Finset.range N, (q ^ k * d1 + q ^ (k + 1) * d0)) = 0 := by
  rw [geometric_cycle_pair_sum_factor]
  have hgeom : (∑ k ∈ Finset.range N, q ^ k) = 0 := by
    rw [geom_sum_eq hq, hpow]
    simp
  rw [hgeom, zero_mul]

end GenMarkoff
