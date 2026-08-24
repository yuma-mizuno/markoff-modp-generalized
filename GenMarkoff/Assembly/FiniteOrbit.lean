import GenMarkoff.Core.Action

/-!
# Finite-orbit assembly

This file isolates the finite group-action argument used at the end of the
Bourgain--Gamburd--Sarnak strategy.  It is independent of the generalized
Markoff equation: a single orbit whose complement has fewer than `p` points
is the whole space as soon as every nonempty orbit has cardinality divisible
by `p`.
-/

namespace GenMarkoff.FiniteOrbit

universe u v

/-- The cardinality of the complement of the orbit of `x`. -/
noncomputable def complementCard
    (G : Type u) {X : Type v} [Group G] [MulAction G X] (x : X) : ℕ :=
  (Set.univ \ MulAction.orbit G x).ncard

/-- A finite group action is transitive if one orbit has complement smaller
than `p` and every orbit cardinality is divisible by `p`. -/
theorem transitive_of_complementCard_lt_and_orbitCard_dvd
    {G : Type u} {X : Type v} [Group G] [MulAction G X] [Finite X]
    (p : ℕ) (x : X)
    (hsmall : complementCard G x < p)
    (hdiv : ∀ y : X, p ∣ (MulAction.orbit G y).ncard) :
    ∀ a b : X, ∃ g : G, g • a = b := by
  classical
  have hxAll : ∀ y : X, y ∈ MulAction.orbit G x := by
    intro y
    by_contra hy
    have horbitSubset :
        MulAction.orbit G y ⊆ Set.univ \ MulAction.orbit G x := by
      intro z hz
      refine ⟨Set.mem_univ z, ?_⟩
      intro hzx
      apply hy
      have hzy : MulAction.orbit G z = MulAction.orbit G y :=
        MulAction.orbit_eq_iff.mpr hz
      have hzx' : MulAction.orbit G z = MulAction.orbit G x :=
        MulAction.orbit_eq_iff.mpr hzx
      exact MulAction.orbit_eq_iff.mp (hzy.symm.trans hzx')
    have horbitPos : 0 < (MulAction.orbit G y).ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨y, MulAction.mem_orbit_self y⟩
    have hpLeOrbit : p ≤ (MulAction.orbit G y).ncard :=
      Nat.le_of_dvd horbitPos (hdiv y)
    have horbitLeComplement :
        (MulAction.orbit G y).ncard ≤ complementCard G x := by
      rw [complementCard]
      exact Set.ncard_le_ncard horbitSubset
    omega
  intro a b
  obtain ⟨ga, hga⟩ := MulAction.mem_orbit_iff.mp (hxAll a)
  obtain ⟨gb, hgb⟩ := MulAction.mem_orbit_iff.mp (hxAll b)
  refine ⟨gb * ga⁻¹, ?_⟩
  calc
    (gb * ga⁻¹) • a = gb • (ga⁻¹ • a) := mul_smul _ _ _
    _ = gb • x := by rw [← hga, inv_smul_smul]
    _ = b := hgb

end GenMarkoff.FiniteOrbit
