import GenMarkoff.General.MiddleGame.ToricEscape
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Associated

/-!
# Order in a translate of a subgroup of a finite cyclic group

This file supplies the finite cyclic-group input isolated by
`ToricEscape`.  The main result is stronger than the required lower bound:
if `H` is a subgroup of a finite cyclic group and `z` is arbitrary, then
the translate `z * H` contains an element whose order is divisible by
`Nat.card H`.

The elementary number-theoretic point is worth recording.  If `d ∣ n`, one
can choose `k` such that

`gcd n (a + d*k) ∣ d`.

After dividing `a` and `d` by their gcd, a suitable `k` is the product of
the prime divisors of the remaining modulus which do not divide the
remaining initial exponent.  For every relevant prime this product chooses
automatically between residue `0` and a nonzero residue, so no analytic
prime-in-progressions result is needed.

For a cyclic generator `g`, every subgroup is `zpowers (g ^ d)`.  The
finite-order relation also puts `g ^ gcd(orderOf g, d)` in that subgroup.
The exponent lemma then produces the required element of the translated
subgroup.
-/

namespace GenMarkoff.General.MiddleGame

open scoped BigOperators

noncomputable section

/-- Product of the prime factors of `L` which do not divide `a`.  This is
the elementary simultaneous residue choice used below. -/
def coprimeShiftMultiplier (L a : ℕ) : ℕ :=
  ∏ p ∈ L.primeFactors.filter (fun p => ¬ p ∣ a), p

/-- If `a` and the step `d` are coprime, a concrete shift of `a` by a
multiple of `d` is coprime to any prescribed nonzero modulus. -/
theorem coprime_add_mul_coprimeShiftMultiplier
    (L a d : ℕ) (hL : L ≠ 0) (had : a.Coprime d) :
    (a + d * coprimeShiftMultiplier L a).Coprime L := by
  by_contra hcop
  obtain ⟨p, hp, hpSum, hpL⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hcop
  by_cases hpa : p ∣ a
  · have hpd : ¬ p ∣ d :=
      hp.coprime_iff_not_dvd.mp (had.coprime_dvd_left hpa)
    have hpk : ¬ p ∣ coprimeShiftMultiplier L a := by
      apply (Nat.prime_iff.mp hp).not_dvd_finsetProd
      intro r hr
      simp only [Finset.mem_filter] at hr
      have hrPrime : r.Prime :=
        (Nat.mem_primeFactors.mp hr.1).1
      intro hpr
      have hprEq : p = r :=
        (Nat.prime_dvd_prime_iff_eq hp hrPrime).mp hpr
      subst r
      exact hr.2 hpa
    have hpdk : ¬ p ∣ d * coprimeShiftMultiplier L a := by
      intro hpMul
      rcases (hp.dvd_mul.mp hpMul) with h | h
      · exact hpd h
      · exact hpk h
    exact hpdk ((Nat.dvd_add_iff_right hpa).mpr hpSum)
  · have hpMem :
        p ∈ L.primeFactors.filter (fun r => ¬ r ∣ a) :=
      Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨hp, hpL, hL⟩, hpa⟩
    have hpk : p ∣ coprimeShiftMultiplier L a :=
      Finset.dvd_prod_of_mem (fun r => r) hpMem
    have hpdk : p ∣ d * coprimeShiftMultiplier L a :=
      dvd_mul_of_dvd_right hpk d
    exact hpa ((Nat.dvd_add_iff_left hpdk).mpr hpSum)

/-- Exponent form of the translated-cyclic-subgroup lemma. -/
theorem exists_gcd_add_mul_dvd_of_dvd
    (n a d : ℕ) (hn : 0 < n) (hd : d ∣ n) :
    ∃ k : ℕ, Nat.gcd n (a + d * k) ∣ d := by
  let c := Nat.gcd a d
  let A := a / c
  let D := d / c
  let N := n / c
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  have hcPos : 0 < c :=
    Nat.gcd_pos_of_pos_right a hdPos
  have hca : c * A = a :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left a d)
  have hcd : c * D = d :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right a d)
  have hcnDvd : c ∣ n :=
    (Nat.gcd_dvd_right a d).trans hd
  have hcn : c * N = n :=
    Nat.mul_div_cancel' hcnDvd
  have hAD : A.Coprime D :=
    Nat.coprime_div_gcd_div_gcd hcPos
  have hDN : D ∣ N := by
    apply (Nat.dvd_div_iff_mul_dvd hcnDvd).mpr
    simpa only [hcd] using hd
  have hNPos : 0 < N :=
    Nat.div_pos (Nat.le_of_dvd hn hcnDvd) hcPos
  have hDPos : 0 < D :=
    Nat.div_pos
      (Nat.le_of_dvd hdPos (Nat.gcd_dvd_right a d)) hcPos
  let L := N / D
  have hLPos : 0 < L :=
    Nat.div_pos (Nat.le_of_dvd hNPos hDN) hDPos
  let k := coprimeShiftMultiplier L A
  have hcop : (A + D * k).Coprime L :=
    coprime_add_mul_coprimeShiftMultiplier
      L A D hLPos.ne' hAD
  have hgD : Nat.gcd N (A + D * k) ∣ D := by
    have hgCop : (Nat.gcd N (A + D * k)).Coprime L :=
      hcop.coprime_dvd_left
        (Nat.gcd_dvd_right N (A + D * k))
    apply (hgCop.dvd_mul_right).mp
    rw [show D * L = N from Nat.mul_div_cancel' hDN]
    exact Nat.gcd_dvd_left N (A + D * k)
  refine ⟨k, ?_⟩
  have hnEq : n = c * N := hcn.symm
  have hsum : a + d * k = c * (A + D * k) := by
    rw [← hca, ← hcd]
    ring
  rw [hnEq, hsum, Nat.gcd_mul_left]
  simpa only [hcd] using Nat.mul_dvd_mul_left c hgD

/-- The gcd of the order and an exponent generates an element of the same
finite cyclic subgroup as that exponent. -/
theorem pow_gcd_orderOf_mem_zpowers_pow
    {G : Type*} [Group G] [Finite G] (g : G) (d : ℕ) :
    g ^ Nat.gcd (orderOf g) d ∈ Subgroup.zpowers (g ^ d) := by
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨Nat.gcdB (orderOf g) d, ?_⟩
  simp only [← zpow_natCast]
  rw [← zpow_mul]
  have hbez :=
    congrArg (fun e : ℤ => g ^ e)
      (Nat.gcd_eq_gcd_ab (orderOf g) d)
  simpa only [zpow_add, zpow_mul, zpow_natCast,
    pow_orderOf_eq_one, one_zpow, one_mul] using hbez.symm

/-- Division reverses a nested divisor relation in the form needed for
orders of powers. -/
theorem div_dvd_div_of_dvd_of_dvd
    {g d n : ℕ} (hg : g ∣ d) (hd : d ∣ n) (hn : 0 < n) :
    n / d ∣ n / g := by
  obtain ⟨r, rfl⟩ := hg
  obtain ⟨s, rfl⟩ := hd
  have hgPos : 0 < g := by
    exact Nat.pos_of_dvd_of_pos
      (dvd_mul_right g (r * s))
      (by simpa [Nat.mul_assoc] using hn)
  have hgrPos : 0 < g * r :=
    Nat.pos_of_dvd_of_pos (dvd_mul_right (g * r) s) hn
  rw [Nat.mul_div_cancel_left s hgrPos]
  rw [Nat.mul_assoc, Nat.mul_div_cancel_left (r * s) hgPos]
  exact dvd_mul_left s r

/-- Strong translated-subgroup theorem: in a finite cyclic ambient group,
every translate of every subgroup contains an element whose order is
divisible by the subgroup cardinality. -/
theorem exists_subgroup_card_dvd_orderOf_mul_of_isCyclic
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (H : Subgroup G) (z : G) :
    ∃ w : H, Nat.card H ∣ orderOf (z * (w : G)) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hHle : H ≤ Subgroup.zpowers g := by
    intro x _
    exact hg x
  obtain ⟨d, hHd⟩ :=
    (Subgroup.le_zpowers_iff g H).mp hHle
  subst H
  have hzPowers : z ∈ Submonoid.powers g :=
    mem_powers_iff_mem_zpowers.mpr (hg z)
  obtain ⟨a, ha⟩ :=
    (Submonoid.mem_powers_iff z g).mp hzPowers
  let n := orderOf g
  let D := Nat.gcd n d
  have hn : 0 < n :=
    orderOf_pos g
  obtain ⟨k, hk⟩ :=
    exists_gcd_add_mul_dvd_of_dvd
      n a D hn (Nat.gcd_dvd_left n d)
  have hDmem :
      g ^ D ∈ Subgroup.zpowers (g ^ d) :=
    pow_gcd_orderOf_mem_zpowers_pow g d
  let w : Subgroup.zpowers (g ^ d) :=
    ⟨g ^ (D * k), by
      rw [pow_mul]
      exact Subgroup.pow_mem _ hDmem k⟩
  refine ⟨w, ?_⟩
  have hzw :
      z * (w : G) = g ^ (a + D * k) := by
    rw [← ha]
    exact (pow_add g a (D * k)).symm
  have hdiv :
      n / D ∣ n / Nat.gcd n (a + D * k) :=
    div_dvd_div_of_dvd_of_dvd
      hk (Nat.gcd_dvd_left n d) hn
  rw [Nat.card_zpowers, orderOf_pow, hzw, orderOf_pow]
  exact hdiv

/-- The previously isolated lower-bound proposition follows from the
strong divisibility theorem. -/
theorem translatedSubgroupHasLargeOrder_of_isCyclic
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (H : Subgroup G) (z : G) :
    TranslatedSubgroupHasLargeOrder H z := by
  obtain ⟨w, hw⟩ :=
    exists_subgroup_card_dvd_orderOf_mul_of_isCyclic H z
  exact ⟨w, Nat.le_of_dvd (orderOf_pos (z * (w : G))) hw⟩

/-- For one directed toric trace, the order preserved without a second
toric direction is the order of `(q ^ 2) ^ 2`, exactly the factor-two
parity-loss scale. -/
theorem exists_firstToric_direction_squareGeneratorOrder_dvd
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (q z : G) :
    ∃ h : Subgroup.zpowers (q ^ 2),
      orderOf ((q ^ 2) ^ 2) ∣ orderOf ((z * (h : G)) ^ 2) := by
  obtain ⟨w, hw⟩ :=
    exists_subgroup_card_dvd_orderOf_mul_of_isCyclic
      (Subgroup.zpowers ((q ^ 2) ^ 2)) (z ^ 2)
  obtain ⟨h, hsq⟩ :=
    firstToric_squareCoset_covered q z w
  refine ⟨h, ?_⟩
  simpa only [Nat.card_zpowers, hsq] using hw

/-- If both adjacent directed traces are toric, parity completion recovers
the full current actual order, and that order divides one of the two new
squared-eigenvalue orders. -/
theorem exists_toric_direction_generatorOrder_dvd
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (q z : G) :
    ∃ h : Subgroup.zpowers (q ^ 2),
      orderOf (q ^ 2) ∣ orderOf ((z * (h : G)) ^ 2) ∨
        orderOf (q ^ 2) ∣ orderOf ((q * z * (h : G)) ^ 2) := by
  obtain ⟨w, hw⟩ :=
    exists_subgroup_card_dvd_orderOf_mul_of_isCyclic
      (Subgroup.zpowers (q ^ 2)) (z ^ 2)
  obtain ⟨h, hfirst | hsecond⟩ :=
    toric_squareCoset_covered_by_two_directions q z w
  · refine ⟨h, Or.inl ?_⟩
    simpa only [Nat.card_zpowers, hfirst] using hw
  · refine ⟨h, Or.inr ?_⟩
    simpa only [Nat.card_zpowers, hsecond] using hw

end

end GenMarkoff.General.MiddleGame
