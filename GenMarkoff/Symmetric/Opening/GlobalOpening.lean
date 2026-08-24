import GenMarkoff.Symmetric.OneStepParabolic
import GenMarkoff.Symmetric.Opening.CenteredEscape
import GenMarkoff.Symmetric.Opening.ReturnExponentBound

/-!
# The global opening dichotomy for the symmetric one-step action

This file connects the two local opening mechanisms.  A parabolic coordinate
contains a full prime-length one-step cycle in the punctured one-step orbit.
Away from the parabolic locus, an affine-centered coordinate can be escaped
by two transverse one-step moves, after which the cyclotomic return-exponent
bound applies.
-/

namespace GenMarkoff.Symmetric.Opening

open BGS.Markoff

section PuncturedCycles

variable (p : ℕ)

/-- The first one-step cycle, retaining the proofs that all its points lie on
the punctured symmetric surface. -/
noncomputable def puncturedOneStep1Cycle
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    Finset (PuncturedSolutionSurface (coefficients c)) := by
  classical
  exact (Finset.range N).image fun n =>
    ((⟨oneStep1SurfacePerm c, oneStep1SurfacePerm_mem_OneStepGroup c⟩ :
      OneStepGroup c) ^ n) • x

/-- The second one-step cycle on the punctured symmetric surface. -/
noncomputable def puncturedOneStep2Cycle
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    Finset (PuncturedSolutionSurface (coefficients c)) := by
  classical
  exact (Finset.range N).image fun n =>
    ((⟨oneStep2SurfacePerm c, oneStep2SurfacePerm_mem_OneStepGroup c⟩ :
      OneStepGroup c) ^ n) • x

/-- The third one-step cycle on the punctured symmetric surface. -/
noncomputable def puncturedOneStep3Cycle
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    Finset (PuncturedSolutionSurface (coefficients c)) := by
  classical
  exact (Finset.range N).image fun n =>
    ((⟨oneStep3SurfacePerm c, oneStep3SurfacePerm_mem_OneStepGroup c⟩ :
      OneStepGroup c) ^ n) • x

/-- Forgetting the surface proofs identifies the punctured first-axis cycle
with the point-valued cycle. -/
theorem puncturedOneStep1Cycle_image_point
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    (puncturedOneStep1Cycle p c x N).image (fun y => y.1.1) =
      oneStep1Cycle p c x.1.1 N := by
  classical
  rw [puncturedOneStep1Cycle, oneStep1Cycle, Finset.image_image]
  apply Finset.image_congr
  intro n _hn
  change (((oneStep1SurfacePerm c) ^ n) x.1).1 =
    ((oneStep1 c)^[n]) x.1.1
  rw [Equiv.Perm.coe_pow]
  exact coe_iterate_oneStep1SurfacePerm c n x.1

/-- Forgetting the surface proofs identifies the punctured second-axis cycle
with the point-valued cycle. -/
theorem puncturedOneStep2Cycle_image_point
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    (puncturedOneStep2Cycle p c x N).image (fun y => y.1.1) =
      oneStep2Cycle p c x.1.1 N := by
  classical
  rw [puncturedOneStep2Cycle, oneStep2Cycle, Finset.image_image]
  apply Finset.image_congr
  intro n _hn
  change (((oneStep2SurfacePerm c) ^ n) x.1).1 =
    ((oneStep2 c)^[n]) x.1.1
  rw [Equiv.Perm.coe_pow]
  exact coe_iterate_oneStep2SurfacePerm c n x.1

/-- Forgetting the surface proofs identifies the punctured third-axis cycle
with the point-valued cycle. -/
theorem puncturedOneStep3Cycle_image_point
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    (puncturedOneStep3Cycle p c x N).image (fun y => y.1.1) =
      oneStep3Cycle p c x.1.1 N := by
  classical
  rw [puncturedOneStep3Cycle, oneStep3Cycle, Finset.image_image]
  apply Finset.image_congr
  intro n _hn
  change (((oneStep3SurfacePerm c) ^ n) x.1).1 =
    ((oneStep3 c)^[n]) x.1.1
  rw [Equiv.Perm.coe_pow]
  exact coe_iterate_oneStep3SurfacePerm c n x.1

/-- Every point of the punctured first-axis cycle belongs to the full
punctured one-step orbit. -/
theorem puncturedOneStep1Cycle_subset_puncturedOneStepOrbit
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    (puncturedOneStep1Cycle p c x N :
      Set (PuncturedSolutionSurface (coefficients c))) ⊆
      puncturedOneStepOrbit x := by
  classical
  intro y hy
  rw [Finset.mem_coe, puncturedOneStep1Cycle, Finset.mem_image] at hy
  obtain ⟨n, _hn, rfl⟩ := hy
  apply MulAction.mem_orbit_iff.mpr
  exact ⟨
    (⟨oneStep1SurfacePerm c, oneStep1SurfacePerm_mem_OneStepGroup c⟩ :
      OneStepGroup c) ^ n,
    rfl⟩

/-- Every point of the punctured second-axis cycle belongs to the full
punctured one-step orbit. -/
theorem puncturedOneStep2Cycle_subset_puncturedOneStepOrbit
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    (puncturedOneStep2Cycle p c x N :
      Set (PuncturedSolutionSurface (coefficients c))) ⊆
      puncturedOneStepOrbit x := by
  classical
  intro y hy
  rw [Finset.mem_coe, puncturedOneStep2Cycle, Finset.mem_image] at hy
  obtain ⟨n, _hn, rfl⟩ := hy
  apply MulAction.mem_orbit_iff.mpr
  exact ⟨
    (⟨oneStep2SurfacePerm c, oneStep2SurfacePerm_mem_OneStepGroup c⟩ :
      OneStepGroup c) ^ n,
    rfl⟩

/-- Every point of the punctured third-axis cycle belongs to the full
punctured one-step orbit. -/
theorem puncturedOneStep3Cycle_subset_puncturedOneStepOrbit
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    (puncturedOneStep3Cycle p c x N :
      Set (PuncturedSolutionSurface (coefficients c))) ⊆
      puncturedOneStepOrbit x := by
  classical
  intro y hy
  rw [Finset.mem_coe, puncturedOneStep3Cycle, Finset.mem_image] at hy
  obtain ⟨n, _hn, rfl⟩ := hy
  apply MulAction.mem_orbit_iff.mpr
  exact ⟨
    (⟨oneStep3SurfacePerm c, oneStep3SurfacePerm_mem_OneStepGroup c⟩ :
      OneStepGroup c) ^ n,
    rfl⟩

private theorem puncturedPoint_forget_injective
    (c : ZMod p) :
    Function.Injective
      (fun y : PuncturedSolutionSurface (coefficients c) => y.1.1) := by
  intro y z h
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- The proof-retaining and point-valued first-axis cycles have the same
cardinality. -/
theorem puncturedOneStep1Cycle_card
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    (puncturedOneStep1Cycle p c x N).card =
      (oneStep1Cycle p c x.1.1 N).card := by
  rw [← puncturedOneStep1Cycle_image_point p c x N]
  exact (Finset.card_image_of_injective _
    (puncturedPoint_forget_injective p c)).symm

/-- The proof-retaining and point-valued second-axis cycles have the same
cardinality. -/
theorem puncturedOneStep2Cycle_card
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    (puncturedOneStep2Cycle p c x N).card =
      (oneStep2Cycle p c x.1.1 N).card := by
  rw [← puncturedOneStep2Cycle_image_point p c x N]
  exact (Finset.card_image_of_injective _
    (puncturedPoint_forget_injective p c)).symm

/-- The proof-retaining and point-valued third-axis cycles have the same
cardinality. -/
theorem puncturedOneStep3Cycle_card
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    (puncturedOneStep3Cycle p c x N).card =
      (oneStep3Cycle p c x.1.1 N).card := by
  rw [← puncturedOneStep3Cycle_image_point p c x N]
  exact (Finset.card_image_of_injective _
    (puncturedPoint_forget_injective p c)).symm

section PrimeFieldBounds

variable [Fact p.Prime]

/-- A first-axis point cycle injects into the full punctured one-step orbit. -/
theorem oneStep1Cycle_card_le_puncturedOneStepOrbit_ncard
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    (oneStep1Cycle p c x.1.1 N).card ≤
      (puncturedOneStepOrbit x).ncard := by
  rw [← puncturedOneStep1Cycle_card p c x N,
    ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard
    (puncturedOneStep1Cycle_subset_puncturedOneStepOrbit p c x N)

/-- A second-axis point cycle injects into the full punctured one-step orbit. -/
theorem oneStep2Cycle_card_le_puncturedOneStepOrbit_ncard
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    (oneStep2Cycle p c x.1.1 N).card ≤
      (puncturedOneStepOrbit x).ncard := by
  rw [← puncturedOneStep2Cycle_card p c x N,
    ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard
    (puncturedOneStep2Cycle_subset_puncturedOneStepOrbit p c x N)

/-- A third-axis point cycle injects into the full punctured one-step orbit. -/
theorem oneStep3Cycle_card_le_puncturedOneStepOrbit_ncard
    (c : ZMod p)
    (x : PuncturedSolutionSurface (coefficients c)) (N : ℕ) :
    (oneStep3Cycle p c x.1.1 N).card ≤
      (puncturedOneStepOrbit x).ncard := by
  rw [← puncturedOneStep3Cycle_card p c x N,
    ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard
    (puncturedOneStep3Cycle_subset_puncturedOneStepOrbit p c x N)

end PrimeFieldBounds

end PuncturedCycles

section Parabolic

variable (p : ℕ) [Fact p.Prime]

private theorem eq_two_or_eq_neg_two_of_sq_eq_four
    (t : ZMod p) (h : t ^ 2 = 4) :
    t = 2 ∨ t = -2 := by
  apply (sq_eq_sq_iff_eq_or_eq_neg).mp
  calc
    t ^ 2 = 4 := h
    _ = (2 : ZMod p) ^ 2 := by norm_num

/-- A parabolic coordinate supplies at least `p` distinct points in the
punctured one-step orbit.  At trace `2` the corresponding one-step cycle has
length `p`; at trace `-2` it has length `2p`. -/
theorem prime_le_puncturedOneStepOrbit_ncard_of_hasParabolicTrace
    (hpTwo : p ≠ 2) (c : ZMod p) (hc : c ^ 2 ≠ 4)
    (x : PuncturedSolutionSurface (coefficients c))
    (hparabolic : HasParabolicTrace c x.1.1) :
    p ≤ (puncturedOneStepOrbit x).ncard := by
  rcases hparabolic with haxisOne | haxisTwo | haxisThree
  · rcases eq_two_or_eq_neg_two_of_sq_eq_four p
      (trace c x.1.1.x1) haxisOne with htrace | htrace
    · calc
        p = (oneStep1Cycle p c x.1.1 p).card :=
          (oneStep1Cycle_card_of_trace_eq_two
            p hpTwo c x.1.1 hc htrace x.1.2).symm
        _ ≤ (puncturedOneStepOrbit x).ncard :=
          oneStep1Cycle_card_le_puncturedOneStepOrbit_ncard p c x p
    · have hlong :
          2 * p ≤ (puncturedOneStepOrbit x).ncard := by
        calc
          2 * p = (oneStep1Cycle p c x.1.1 (2 * p)).card :=
            (oneStep1Cycle_card_of_trace_eq_neg_two
              p hpTwo c x.1.1 hc htrace x.1.2).symm
          _ ≤ (puncturedOneStepOrbit x).ncard :=
            oneStep1Cycle_card_le_puncturedOneStepOrbit_ncard
              p c x (2 * p)
      omega
  · rcases eq_two_or_eq_neg_two_of_sq_eq_four p
      (trace c x.1.1.x2) haxisTwo with htrace | htrace
    · calc
        p = (oneStep2Cycle p c x.1.1 p).card :=
          (oneStep2Cycle_card_of_trace_eq_two
            p hpTwo c x.1.1 hc htrace x.1.2).symm
        _ ≤ (puncturedOneStepOrbit x).ncard :=
          oneStep2Cycle_card_le_puncturedOneStepOrbit_ncard p c x p
    · have hlong :
          2 * p ≤ (puncturedOneStepOrbit x).ncard := by
        calc
          2 * p = (oneStep2Cycle p c x.1.1 (2 * p)).card :=
            (oneStep2Cycle_card_of_trace_eq_neg_two
              p hpTwo c x.1.1 hc htrace x.1.2).symm
          _ ≤ (puncturedOneStepOrbit x).ncard :=
            oneStep2Cycle_card_le_puncturedOneStepOrbit_ncard
              p c x (2 * p)
      omega
  · rcases eq_two_or_eq_neg_two_of_sq_eq_four p
      (trace c x.1.1.x3) haxisThree with htrace | htrace
    · calc
        p = (oneStep3Cycle p c x.1.1 p).card :=
          (oneStep3Cycle_card_of_trace_eq_two
            p hpTwo c x.1.1 hc htrace x.1.2).symm
        _ ≤ (puncturedOneStepOrbit x).ncard :=
          oneStep3Cycle_card_le_puncturedOneStepOrbit_ncard p c x p
    · have hlong :
          2 * p ≤ (puncturedOneStepOrbit x).ncard := by
        calc
          2 * p = (oneStep3Cycle p c x.1.1 (2 * p)).card :=
            (oneStep3Cycle_card_of_trace_eq_neg_two
              p hpTwo c x.1.1 hc htrace x.1.2).symm
          _ ≤ (puncturedOneStepOrbit x).ncard :=
            oneStep3Cycle_card_le_puncturedOneStepOrbit_ncard
              p c x (2 * p)
      omega

end Parabolic

section ResidueTransport

/-- Coordinatewise injectivity of `mapPair`. -/
theorem mapPair_injective
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (hf : Function.Injective f) :
    Function.Injective (mapPair f) := by
  intro v w h
  apply Prod.ext
  · apply hf
    exact congrArg Prod.fst h
  · apply hf
    exact congrArg Prod.snd h

/-- Centering a moving pair at its affine fiber center commutes with a field
homomorphism. -/
theorem mapPair_centerCoordinates_fiberCenter
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (c u t : K) (v : K × K) :
    mapPair f (centerCoordinates (fiberCenter c u t) v) =
      centerCoordinates (fiberCenter (f c) (f u) (f t))
        (mapPair f v) := by
  ext <;>
    simp [mapPair, centerCoordinates, fiberCenter, map_ofNat]

private theorem trace_sq_ne_four_in_openingResidueClosure
    (c : ℤ) (p : ℕ) [Fact p.Prime] (x : Point (ZMod p)) (i : Fin 3)
    (h : (match i with
      | 0 => trace (c : ZMod p) x.x1
      | 1 => trace (c : ZMod p) x.x2
      | 2 => trace (c : ZMod p) x.x3) ^ 2 ≠ 4) :
    (match i with
      | 0 => trace (c : OpeningResidueClosure p)
          (openingResiduePoint p x).x1
      | 1 => trace (c : OpeningResidueClosure p)
          (openingResiduePoint p x).x2
      | 2 => trace (c : OpeningResidueClosure p)
          (openingResiduePoint p x).x3) ^ 2 ≠ 4 := by
  let f := algebraMap (ZMod p) (OpeningResidueClosure p)
  intro hzero
  apply h
  apply f.injective
  fin_cases i <;>
    simpa [f, openingResiduePoint, mapPoint, map_trace, map_intCast,
      map_ofNat] using hzero

/-- Prime-field nonparabolicity and noncentering are exactly the pointwise
hypotheses needed by the cyclotomic opening theorem after transport to the
fixed residue closure. -/
theorem modulus_le_integerArchimedeanBound_pow_oneStepOrbit_ncard_cube_of_noParabolicTrace_allAxesNoncentered
    (c : ℤ) (hs : 3 * (1 + c) ≠ 0) (hc : c ^ 2 ≠ 4)
    (p : ℕ) [Fact p.Prime]
    (x : PuncturedSolutionSurface (coefficients (c : ZMod p)))
    (hfinite : (puncturedOneStepOrbit x).Finite)
    (hmultiplier : multiplier (c : ZMod p) ≠ 0)
    (hparabolic : ¬ HasParabolicTrace (c : ZMod p) x.1.1)
    (hnoncentered : AllAxesNoncentered (c : ZMod p) x.1.1) :
    p ≤ integerArchimedeanBound c ^
      (puncturedOneStepOrbit x).ncard ^ 3 := by
  let f := algebraMap (ZMod p) (OpeningResidueClosure p)
  have hsResidue : multiplier (c : OpeningResidueClosure p) ≠ 0 := by
    have hmapped := (map_ne_zero_iff f f.injective).mpr hmultiplier
    simpa [f, multiplier, map_ofNat, map_intCast] using hmapped
  have ht1Base : trace (c : ZMod p) x.1.1.x1 ^ 2 ≠ 4 :=
    fun h => hparabolic (Or.inl h)
  have ht2Base : trace (c : ZMod p) x.1.1.x2 ^ 2 ≠ 4 :=
    fun h => hparabolic (Or.inr (Or.inl h))
  have ht3Base : trace (c : ZMod p) x.1.1.x3 ^ 2 ≠ 4 :=
    fun h => hparabolic (Or.inr (Or.inr h))
  have ht1 :=
    trace_sq_ne_four_in_openingResidueClosure c p x.1.1 0 ht1Base
  have ht2 :=
    trace_sq_ne_four_in_openingResidueClosure c p x.1.1 1 ht2Base
  have ht3 :=
    trace_sq_ne_four_in_openingResidueClosure c p x.1.1 2 ht3Base
  have hv1 : centerCoordinates
      (fiberCenter (c : OpeningResidueClosure p)
        (openingResiduePoint p x.1.1).x1
        (trace (c : OpeningResidueClosure p)
          (openingResiduePoint p x.1.1).x1))
      (movingCoordinates1 (openingResiduePoint p x.1.1)) ≠ (0, 0) := by
    intro hzero
    apply hnoncentered.1
    apply mapPair_injective f f.injective
    rw [mapPair_centerCoordinates_fiberCenter]
    simpa [f, openingResiduePoint, mapPoint, mapPair, map_trace, map_intCast,
      map_ofNat, movingCoordinates1] using hzero
  have hv2 : centerCoordinates
      (fiberCenter (c : OpeningResidueClosure p)
        (openingResiduePoint p x.1.1).x2
        (trace (c : OpeningResidueClosure p)
          (openingResiduePoint p x.1.1).x2))
      (movingCoordinates2 (openingResiduePoint p x.1.1)) ≠ (0, 0) := by
    intro hzero
    apply hnoncentered.2.1
    apply mapPair_injective f f.injective
    rw [mapPair_centerCoordinates_fiberCenter]
    simpa [f, openingResiduePoint, mapPoint, mapPair, map_trace, map_intCast,
      map_ofNat, movingCoordinates2] using hzero
  have hv3 : centerCoordinates
      (fiberCenter (c : OpeningResidueClosure p)
        (openingResiduePoint p x.1.1).x3
        (trace (c : OpeningResidueClosure p)
          (openingResiduePoint p x.1.1).x3))
      (movingCoordinates3 (openingResiduePoint p x.1.1)) ≠ (0, 0) := by
    intro hzero
    apply hnoncentered.2.2
    apply mapPair_injective f f.injective
    rw [mapPair_centerCoordinates_fiberCenter]
    simpa [f, openingResiduePoint, mapPoint, mapPair, map_trace, map_intCast,
      map_ofNat, movingCoordinates3] using hzero
  obtain ⟨_, _, _, _, _, _,
      _, _, _,
      _, _, _,
      _, _, _,
      _, _, _,
      _, _, _,
      _, _, _,
      _, hbound⟩ :=
    exists_return_eigenvalues_with_oneStepOrbit_bounds
      c hs hc p x hfinite hsResidue ht1 ht2 ht3 hv1 hv2 hv3
  exact hbound

end ResidueTransport

section GlobalDichotomy

/-- For every punctured point on a nondegenerate symmetric surface over a
prime field, either a parabolic cycle already gives `p` points in the
one-step orbit, or the cyclotomic opening bound holds.  If the starting point
is affine-centered on one axis, the theorem uses the explicit two-step
transverse escape before applying one of the two alternatives. -/
theorem prime_le_oneStepOrbit_ncard_or_modulus_le_integerArchimedeanBound_pow_oneStepOrbit_ncard_cube
    (c : ℤ) (hs : 3 * (1 + c) ≠ 0) (hc : c ^ 2 ≠ 4)
    (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (x : PuncturedSolutionSurface (coefficients (c : ZMod p)))
    (hfinite : (puncturedOneStepOrbit x).Finite)
    (hmultiplier : multiplier (c : ZMod p) ≠ 0)
    (hcResidue : (c : ZMod p) ^ 2 ≠ 4) :
    p ≤ (puncturedOneStepOrbit x).ncard ∨
      p ≤ integerArchimedeanBound c ^
        (puncturedOneStepOrbit x).ncard ^ 3 := by
  have hpTwo : p ≠ 2 := by omega
  have hxOrigin : x.1.1 ≠ (origin : Point (ZMod p)) := by
    intro hzero
    apply x.2
    apply Subtype.ext
    exact hzero
  by_cases hxParabolic : HasParabolicTrace (c : ZMod p) x.1.1
  · exact Or.inl
      (prime_le_puncturedOneStepOrbit_ncard_of_hasParabolicTrace
        p hpTwo (c : ZMod p) hcResidue x hxParabolic)
  have ht1 : trace (c : ZMod p) x.1.1.x1 ^ 2 ≠ 4 :=
    fun h => hxParabolic (Or.inl h)
  have ht2 : trace (c : ZMod p) x.1.1.x2 ^ 2 ≠ 4 :=
    fun h => hxParabolic (Or.inr (Or.inl h))
  have ht3 : trace (c : ZMod p) x.1.1.x3 ^ 2 ≠ 4 :=
    fun h => hxParabolic (Or.inr (Or.inr h))
  by_cases hcenter1 :
      centerCoordinates
        (fiberCenter (c : ZMod p) x.1.1.x1
          (trace (c : ZMod p) x.1.1.x1))
        (movingCoordinates1 x.1.1) = (0, 0)
  · let g2 : OneStepGroup (c : ZMod p) :=
      ⟨oneStep2SurfacePerm (c : ZMod p),
        oneStep2SurfacePerm_mem_OneStepGroup (c : ZMod p)⟩
    let y : PuncturedSolutionSurface (coefficients (c : ZMod p)) :=
      (g2 ^ 2) • x
    have hyPoint :
        y.1.1 = oneStep2 (c : ZMod p)
          (oneStep2 (c : ZMod p) x.1.1) := by
      change (((oneStep2SurfacePerm (c : ZMod p)) ^ 2) x.1).1 =
        oneStep2 (c : ZMod p) (oneStep2 (c : ZMod p) x.1.1)
      rw [Equiv.Perm.coe_pow]
      simpa [Function.iterate_succ_apply'] using
        coe_iterate_oneStep2SurfacePerm (c : ZMod p) 2 x.1
    have hyOrbit : puncturedOneStepOrbit y = puncturedOneStepOrbit x := by
      apply MulAction.orbit_eq_iff.mpr
      apply MulAction.mem_orbit_iff.mpr
      exact ⟨g2 ^ 2, rfl⟩
    have hescape :=
      two_oneStep2_of_axisOne_centered_hasParabolicTrace_or_allAxesNoncentered_zmod
        p hp (c : ZMod p) x.1.1 hmultiplier hcResidue x.1.2
          hxOrigin ht1 hcenter1
    have hescapeY :
        HasParabolicTrace (c : ZMod p) y.1.1 ∨
          AllAxesNoncentered (c : ZMod p) y.1.1 := by
      rw [hyPoint]
      exact hescape
    by_cases hyParabolic : HasParabolicTrace (c : ZMod p) y.1.1
    · have hlarge :=
        prime_le_puncturedOneStepOrbit_ncard_of_hasParabolicTrace
          p hpTwo (c : ZMod p) hcResidue y hyParabolic
      left
      simpa only [hyOrbit] using hlarge
    · have hyNoncentered : AllAxesNoncentered (c : ZMod p) y.1.1 :=
        hescapeY.resolve_left hyParabolic
      have hyFinite : (puncturedOneStepOrbit y).Finite := by
        rw [hyOrbit]
        exact hfinite
      have hbound :=
        modulus_le_integerArchimedeanBound_pow_oneStepOrbit_ncard_cube_of_noParabolicTrace_allAxesNoncentered
          c hs hc p y hyFinite hmultiplier hyParabolic hyNoncentered
      right
      simpa only [hyOrbit] using hbound
  by_cases hcenter2 :
      centerCoordinates
        (fiberCenter (c : ZMod p) x.1.1.x2
          (trace (c : ZMod p) x.1.1.x2))
        (movingCoordinates2 x.1.1) = (0, 0)
  · let g3 : OneStepGroup (c : ZMod p) :=
      ⟨oneStep3SurfacePerm (c : ZMod p),
        oneStep3SurfacePerm_mem_OneStepGroup (c : ZMod p)⟩
    let y : PuncturedSolutionSurface (coefficients (c : ZMod p)) :=
      (g3 ^ 2) • x
    have hyPoint :
        y.1.1 = oneStep3 (c : ZMod p)
          (oneStep3 (c : ZMod p) x.1.1) := by
      change (((oneStep3SurfacePerm (c : ZMod p)) ^ 2) x.1).1 =
        oneStep3 (c : ZMod p) (oneStep3 (c : ZMod p) x.1.1)
      rw [Equiv.Perm.coe_pow]
      simpa [Function.iterate_succ_apply'] using
        coe_iterate_oneStep3SurfacePerm (c : ZMod p) 2 x.1
    have hyOrbit : puncturedOneStepOrbit y = puncturedOneStepOrbit x := by
      apply MulAction.orbit_eq_iff.mpr
      apply MulAction.mem_orbit_iff.mpr
      exact ⟨g3 ^ 2, rfl⟩
    have hescape :=
      two_oneStep3_of_axisTwo_centered_hasParabolicTrace_or_allAxesNoncentered_zmod
        p hp (c : ZMod p) x.1.1 hmultiplier hcResidue x.1.2
          hxOrigin ht2 hcenter2
    have hescapeY :
        HasParabolicTrace (c : ZMod p) y.1.1 ∨
          AllAxesNoncentered (c : ZMod p) y.1.1 := by
      rw [hyPoint]
      exact hescape
    by_cases hyParabolic : HasParabolicTrace (c : ZMod p) y.1.1
    · have hlarge :=
        prime_le_puncturedOneStepOrbit_ncard_of_hasParabolicTrace
          p hpTwo (c : ZMod p) hcResidue y hyParabolic
      left
      simpa only [hyOrbit] using hlarge
    · have hyNoncentered : AllAxesNoncentered (c : ZMod p) y.1.1 :=
        hescapeY.resolve_left hyParabolic
      have hyFinite : (puncturedOneStepOrbit y).Finite := by
        rw [hyOrbit]
        exact hfinite
      have hbound :=
        modulus_le_integerArchimedeanBound_pow_oneStepOrbit_ncard_cube_of_noParabolicTrace_allAxesNoncentered
          c hs hc p y hyFinite hmultiplier hyParabolic hyNoncentered
      right
      simpa only [hyOrbit] using hbound
  by_cases hcenter3 :
      centerCoordinates
        (fiberCenter (c : ZMod p) x.1.1.x3
          (trace (c : ZMod p) x.1.1.x3))
        (movingCoordinates3 x.1.1) = (0, 0)
  · let g1 : OneStepGroup (c : ZMod p) :=
      ⟨oneStep1SurfacePerm (c : ZMod p),
        oneStep1SurfacePerm_mem_OneStepGroup (c : ZMod p)⟩
    let y : PuncturedSolutionSurface (coefficients (c : ZMod p)) :=
      (g1 ^ 2) • x
    have hyPoint :
        y.1.1 = oneStep1 (c : ZMod p)
          (oneStep1 (c : ZMod p) x.1.1) := by
      change (((oneStep1SurfacePerm (c : ZMod p)) ^ 2) x.1).1 =
        oneStep1 (c : ZMod p) (oneStep1 (c : ZMod p) x.1.1)
      rw [Equiv.Perm.coe_pow]
      simpa [Function.iterate_succ_apply'] using
        coe_iterate_oneStep1SurfacePerm (c : ZMod p) 2 x.1
    have hyOrbit : puncturedOneStepOrbit y = puncturedOneStepOrbit x := by
      apply MulAction.orbit_eq_iff.mpr
      apply MulAction.mem_orbit_iff.mpr
      exact ⟨g1 ^ 2, rfl⟩
    have hescape :=
      two_oneStep1_of_axisThree_centered_hasParabolicTrace_or_allAxesNoncentered_zmod
        p hp (c : ZMod p) x.1.1 hmultiplier hcResidue x.1.2
          hxOrigin ht3 hcenter3
    have hescapeY :
        HasParabolicTrace (c : ZMod p) y.1.1 ∨
          AllAxesNoncentered (c : ZMod p) y.1.1 := by
      rw [hyPoint]
      exact hescape
    by_cases hyParabolic : HasParabolicTrace (c : ZMod p) y.1.1
    · have hlarge :=
        prime_le_puncturedOneStepOrbit_ncard_of_hasParabolicTrace
          p hpTwo (c : ZMod p) hcResidue y hyParabolic
      left
      simpa only [hyOrbit] using hlarge
    · have hyNoncentered : AllAxesNoncentered (c : ZMod p) y.1.1 :=
        hescapeY.resolve_left hyParabolic
      have hyFinite : (puncturedOneStepOrbit y).Finite := by
        rw [hyOrbit]
        exact hfinite
      have hbound :=
        modulus_le_integerArchimedeanBound_pow_oneStepOrbit_ncard_cube_of_noParabolicTrace_allAxesNoncentered
          c hs hc p y hyFinite hmultiplier hyParabolic hyNoncentered
      right
      simpa only [hyOrbit] using hbound
  · right
    exact
      modulus_le_integerArchimedeanBound_pow_oneStepOrbit_ncard_cube_of_noParabolicTrace_allAxesNoncentered
        c hs hc p x hfinite hmultiplier hxParabolic
          ⟨hcenter1, hcenter2, hcenter3⟩

end GlobalDichotomy

end GenMarkoff.Symmetric.Opening
