import GenMarkoff.General.Assembly.CenteredLocus
import GenMarkoff.General.Assembly.RotationComponent
import GenMarkoff.General.Assembly.Startup
import GenMarkoff.General.Assembly.RegularMiddleIteration
import GenMarkoff.General.Arithmetic.ExplicitCutoff
import GenMarkoff.General.MiddleGame.RotationEigenvalueOrder
import GenMarkoff.General.ParabolicRouting
import GenMarkoff.Symmetric.Opening.PeriodicSemisimple

/-!
# Quantitative startup routing to an alternating regular state

This module turns a large first- or second-axis actual rotation order into a
candidate-regular alternating state of prescribed lower actual order, without
permuting the fixed coefficient triple.

## New considerations for unequal coefficients

* An actual heterogeneous rotation has the square of the common BGS
  half-step as its centered linear part.  Consequently, actual order below
  `bound` only puts the BGS trace in the concrete low-order set at cutoff
  `2 * bound`.
* Candidate regularity is controlled by the ordered safe polynomial, whose
  zero support contributes at most twenty points.  A fixed adjacent trace
  fiber contributes at most two points.
* For a nonparabolic noncentered point, the cardinality of the actual point
  cycle is exactly `rotationLinearOrder`; this needs a return-divisibility
  argument because the affine center depends on the ordered coefficient
  frame.
* A centered nonparabolic point is rotation-fixed.  The first two such loci
  contribute at most six points, which must be included in the startup error
  term before choosing which large-order axis to route along.
* At trace `2` or `-2`, the semisimple cycle argument is replaced by the
  corrected signed parabolic theorem giving exact point period `p`.

The final theorem deliberately keeps the semisimple routing margin, the
parabolic routing margin, and the startup `small-card + 6 < p` hypothesis
explicit.  Thus it records the precise remaining numerical interface needed
by an eventual asymptotic assembly theorem.
-/

namespace GenMarkoff.General.Assembly

open Filter
open BGS.Markoff
open GenMarkoff.General.Explicit
open GenMarkoff.General.MiddleGame

noncomputable section

theorem centerCoordinates_iterate_affineRotation
    {K : Type*} [Field K]
    (B C u t : K) (v : K × K) (hD : discriminant t ≠ 0)
    (n : ℕ) :
    centerCoordinates (fiberCenter B C u t)
        (((affineRotation B C u t)^[n]) v) =
      ((fun w ↦ linearStep t (linearStep t w))^[n])
        (centerCoordinates (fiberCenter B C u t) v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        centerCoordinates_affineRotation B C u t _ hD, ih]

theorem iterate_squaredLinearStep
    {K : Type*} [Field K] (t : K) (v : K × K) (n : ℕ) :
    ((fun w ↦ linearStep t (linearStep t w))^[n]) v =
      ((linearStep t)^[2 * n]) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      calc
        linearStep t (linearStep t (((linearStep t)^[2 * n]) v)) =
            ((linearStep t)^[2 + 2 * n]) v := by
              rw [Function.iterate_add_apply]
              rfl
        _ = ((linearStep t)^[2 * (n + 1)]) v := by
          congr 1
          omega

theorem mapPair_generalLinearStep
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : R) (v : R × R) :
    GenMarkoff.Symmetric.Opening.mapPair f (linearStep t v) =
      GenMarkoff.Symmetric.linearStep (f t)
        (GenMarkoff.Symmetric.Opening.mapPair f v) := by
  ext <;>
    simp [GenMarkoff.Symmetric.Opening.mapPair, linearStep,
      GenMarkoff.Symmetric.linearStep]

theorem mapPair_iterate_generalLinearStep
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : R) (v : R × R) (n : ℕ) :
    GenMarkoff.Symmetric.Opening.mapPair f
        (((linearStep t)^[n]) v) =
      ((GenMarkoff.Symmetric.linearStep (f t))^[n])
        (GenMarkoff.Symmetric.Opening.mapPair f v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [mapPair_generalLinearStep, ih]

theorem mapPair_ne_zero
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (hf : Function.Injective f) (v : R × R)
    (hv : v ≠ (0, 0)) :
    GenMarkoff.Symmetric.Opening.mapPair f v ≠ (0, 0) := by
  intro hzero
  apply hv
  apply Prod.ext
  · apply hf
    simpa [GenMarkoff.Symmetric.Opening.mapPair] using
      congrArg Prod.fst hzero
  · apply hf
    simpa [GenMarkoff.Symmetric.Opening.mapPair] using
      congrArg Prod.snd hzero

theorem some_eigenCoordinate_ne_zero
    {K : Type*} [Field K]
    (w : Kˣ) (hw : (w : K) ^ 2 ≠ 1) {v : K × K}
    (hv : v ≠ (0, 0)) :
    GenMarkoff.Symmetric.Opening.firstEigenCoordinate w v ≠ 0 ∨
      GenMarkoff.Symmetric.Opening.secondEigenCoordinate w v ≠ 0 := by
  by_contra h
  push Not at h
  rcases h with ⟨hfirst, hsecond⟩
  apply hv
  apply Prod.ext
  · have hsum :=
      GenMarkoff.Symmetric.Opening.first_add_secondEigenCoordinate
        w hw v
    simpa [hfirst, hsecond] using hsum.symm
  · have hsum :=
      GenMarkoff.Symmetric.Opening.first_mul_add_second_mul_invEigenCoordinate
        w hw v
    simpa [hfirst, hsecond] using hsum.symm

theorem rotationLinearOrder_dvd_of_affineRotation_return
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (B C u t : ZMod p) (v : ZMod p × ZMod p)
    (hD : discriminant t ≠ 0)
    (hnoncentered :
      centerCoordinates (fiberCenter B C u t) v ≠ (0, 0))
    (d : ℕ)
    (hreturn : ((affineRotation B C u t)^[d]) v = v) :
    rotationLinearOrder t ∣ d := by
  let centered := centerCoordinates (fiberCenter B C u t) v
  have hcenteredReturn :
      ((linearStep t)^[2 * d]) centered = centered := by
    rw [← iterate_squaredLinearStep t centered d]
    rw [← centerCoordinates_iterate_affineRotation
      B C u t v hD d]
    exact congrArg (centerCoordinates (fiberCenter B C u t)) hreturn
  let f : ZMod p →+* quadraticFiniteField p :=
    algebraMap (ZMod p) (quadraticFiniteField p)
  let centeredE := GenMarkoff.Symmetric.Opening.mapPair f centered
  have hcenteredENe : centeredE ≠ (0, 0) :=
    mapPair_ne_zero f f.injective centered hnoncentered
  have hcenteredEReturn :
      ((GenMarkoff.Symmetric.linearStep (f t))^[2 * d]) centeredE =
        centeredE := by
    have hmap := congrArg
      (GenMarkoff.Symmetric.Opening.mapPair f) hcenteredReturn
    simpa [centeredE] using
      (mapPair_iterate_generalLinearStep
        f t centered (2 * d)).symm.trans hmap
  have heigen :
      ∃ q : (quadraticFiniteField p)ˣ,
        (q : quadraticFiniteField p) ^ 2 ≠ 1 ∧
          f t = splitTorusTrace q := by
    have hnonparabolic : t ^ 2 ≠ 4 := by
      simpa [discriminant] using sub_ne_zero.mp hD
    rcases exists_split_or_quadraticNormOneTrace
        p hpTwo t hnonparabolic with
      ⟨q, htrace, hq⟩ | ⟨q, htrace, hq⟩
    · let qE : (quadraticFiniteField p)ˣ :=
        Units.map f.toMonoidHom q
      refine ⟨qE, ?_, ?_⟩
      · intro hpower
        apply hq
        apply f.injective
        simpa [qE, map_pow, map_one] using hpower
      · change f t =
          (qE : quadraticFiniteField p) +
            (((qE⁻¹ : (quadraticFiniteField p)ˣ) :
              quadraticFiniteField p))
        have hmapped := congrArg f htrace
        have hqE :
            (qE : quadraticFiniteField p) = f (q : ZMod p) := by
          rfl
        have hqEInv :
            ((qE⁻¹ : (quadraticFiniteField p)ˣ) :
                quadraticFiniteField p) =
              (f (q : ZMod p))⁻¹ := by
          rw [Units.val_inv_eq_inv_val, hqE]
        rw [hqE, hqEInv]
        simpa only [splitTorusTrace, map_add,
          Units.val_inv_eq_inv_val, map_inv₀] using
          hmapped.symm
    · refine ⟨q.1, hq, ?_⟩
      rw [← htrace]
      exact algebraMap_quadraticNormOneTrace p q
  obtain ⟨q, hq, htrace⟩ := heigen
  have hqPow : (q ^ 2) ^ d = 1 := by
    rcases some_eigenCoordinate_ne_zero
        q hq hcenteredENe with hfirst | hsecond
    · have heq := congrArg
        (GenMarkoff.Symmetric.Opening.firstEigenCoordinate q)
        hcenteredEReturn
      rw [htrace,
        GenMarkoff.Symmetric.Opening.firstEigenCoordinate_iterate_linearStep
          q hq] at heq
      have hpow : (q : quadraticFiniteField p) ^ (2 * d) = 1 := by
        apply mul_left_cancel₀ hfirst
        simpa using heq
      have hpowUnits : q ^ (2 * d) = 1 := by
        apply Units.ext
        exact hpow
      simpa only [pow_mul] using hpowUnits
    · have heq := congrArg
        (GenMarkoff.Symmetric.Opening.secondEigenCoordinate q)
        hcenteredEReturn
      rw [htrace,
        GenMarkoff.Symmetric.Opening.secondEigenCoordinate_iterate_linearStep
          q hq] at heq
      have hpowInv :
          ((q⁻¹ : (quadraticFiniteField p)ˣ) :
            quadraticFiniteField p) ^ (2 * d) = 1 := by
        apply mul_left_cancel₀ hsecond
        simpa using heq
      have hpowInvUnits :
          (q⁻¹ : (quadraticFiniteField p)ˣ) ^ (2 * d) = 1 := by
        apply Units.ext
        exact hpowInv
      have hpowUnits : q ^ (2 * d) = 1 := by
        calc
          q ^ (2 * d) = q ^ (2 * d) * 1 := by simp
          _ = q ^ (2 * d) *
              (q⁻¹ : (quadraticFiniteField p)ˣ) ^ (2 * d) := by
            rw [hpowInvUnits]
          _ = (q * q⁻¹) ^ (2 * d) := by rw [mul_pow]
          _ = 1 := by simp
      simpa only [pow_mul] using hpowUnits
  have horder :
      orderOf (q ^ 2) = rotationLinearOrder t := by
    have hcard :=
      card_zpowers_sq_eq_rotationLinearOrder_of_discriminant_ne_zero
        p t q hD htrace
    rw [Nat.card_zpowers] at hcard
    exact hcard
  rw [← horder]
  exact orderOf_dvd_iff_pow_eq_one.mpr hqPow

private theorem iterate_eq_self_of_le
    {α : Type*} (f : α → α) (hf : Function.Injective f)
    (x : α) {n m : ℕ} (hnm : n ≤ m)
    (h : (f^[n]) x = (f^[m]) x) :
    (f^[m - n]) x = x := by
  apply (hf.iterate n)
  calc
    (f^[n]) ((f^[m - n]) x) =
        (f^[n + (m - n)]) x := by
          rw [Function.iterate_add_apply]
    _ = (f^[m]) x := by rw [Nat.add_sub_of_le hnm]
    _ = (f^[n]) x := h.symm

theorem rotationLinearOrder_dvd_of_rotation1_return
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (x : Point (ZMod p))
    (hD :
      discriminant (orderedTrace a.multiplier a.a1 x.x1) ≠ 0)
    (hnoncentered :
      centerCoordinates
          (fiberCenter a.a2 a.a3 x.x1
            (orderedTrace a.multiplier a.a1 x.x1))
          (movingCoordinates1 x) ≠
        (0, 0))
    (d : ℕ) (hreturn : ((rotation1 a)^[d]) x = x) :
    rotationLinearOrder
        (orderedTrace a.multiplier a.a1 x.x1) ∣ d := by
  apply rotationLinearOrder_dvd_of_affineRotation_return
    p hpTwo a.a2 a.a3 x.x1
      (orderedTrace a.multiplier a.a1 x.x1)
      (movingCoordinates1 x) hD hnoncentered d
  have hpair := congrArg movingCoordinates1 hreturn
  rw [movingCoordinates1_iterate_rotation1] at hpair
  exact hpair

theorem rotationLinearOrder_dvd_of_rotation2_return
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (x : Point (ZMod p))
    (hD :
      discriminant (orderedTrace a.multiplier a.a2 x.x2) ≠ 0)
    (hnoncentered :
      centerCoordinates
          (fiberCenter a.a3 a.a1 x.x2
            (orderedTrace a.multiplier a.a2 x.x2))
          (movingCoordinates2 x) ≠
        (0, 0))
    (d : ℕ) (hreturn : ((rotation2 a)^[d]) x = x) :
    rotationLinearOrder
        (orderedTrace a.multiplier a.a2 x.x2) ∣ d := by
  apply rotationLinearOrder_dvd_of_affineRotation_return
    p hpTwo a.a3 a.a1 x.x2
      (orderedTrace a.multiplier a.a2 x.x2)
      (movingCoordinates2 x) hD hnoncentered d
  have hpair := congrArg movingCoordinates2 hreturn
  rw [movingCoordinates2_iterate_rotation2] at hpair
  exact hpair

theorem rotation1Segment_card_eq_rotationLinearOrder
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (x : Point (ZMod p))
    (hD :
      discriminant (orderedTrace a.multiplier a.a1 x.x1) ≠ 0)
    (hnoncentered :
      centerCoordinates
          (fiberCenter a.a2 a.a3 x.x1
            (orderedTrace a.multiplier a.a1 x.x1))
          (movingCoordinates1 x) ≠
        (0, 0)) :
    (orbitSegment (rotation1 a)
      (rotationLinearOrder
        (orderedTrace a.multiplier a.a1 x.x1)) x).card =
      rotationLinearOrder
        (orderedTrace a.multiplier a.a1 x.x1) := by
  classical
  let M :=
    rotationLinearOrder (orderedTrace a.multiplier a.a1 x.x1)
  have hrotationInjective : Function.Injective (rotation1 a) := by
    intro y z hyz
    exact (rotation1Equiv (ZMod p) a).injective hyz
  have hinjective :
      Set.InjOn (fun n : ℕ ↦ ((rotation1 a)^[n]) x)
        (Finset.range M) := by
    intro n hn m hm heq
    have hnM : n < M := by simpa [M] using hn
    have hmM : m < M := by simpa [M] using hm
    rcases lt_trichotomy n m with hnm | hnm | hmn
    · let d := m - n
      have hdPos : 0 < d := Nat.sub_pos_of_lt hnm
      have hdM : d < M := (Nat.sub_le m n).trans_lt hmM
      have hreturn : ((rotation1 a)^[d]) x = x :=
        iterate_eq_self_of_le (rotation1 a)
          hrotationInjective x (Nat.le_of_lt hnm) heq
      have hMdiv : M ∣ d := by
        simpa [M] using
          rotationLinearOrder_dvd_of_rotation1_return
            p hpTwo a x hD hnoncentered d hreturn
      exact (Nat.not_dvd_of_pos_of_lt hdPos hdM hMdiv).elim
    · exact hnm
    · let d := n - m
      have hdPos : 0 < d := Nat.sub_pos_of_lt hmn
      have hdM : d < M := (Nat.sub_le n m).trans_lt hnM
      have hreturn : ((rotation1 a)^[d]) x = x :=
        iterate_eq_self_of_le (rotation1 a)
          hrotationInjective x (Nat.le_of_lt hmn) heq.symm
      have hMdiv : M ∣ d := by
        simpa [M] using
          rotationLinearOrder_dvd_of_rotation1_return
            p hpTwo a x hD hnoncentered d hreturn
      exact (Nat.not_dvd_of_pos_of_lt hdPos hdM hMdiv).elim
  rw [orbitSegment]
  calc
    ((Finset.range M).image fun n ↦ ((rotation1 a)^[n]) x).card =
        (Finset.range M).card := Finset.card_image_iff.mpr hinjective
    _ = M := Finset.card_range M

theorem rotation2Segment_card_eq_rotationLinearOrder
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p)) (x : Point (ZMod p))
    (hD :
      discriminant (orderedTrace a.multiplier a.a2 x.x2) ≠ 0)
    (hnoncentered :
      centerCoordinates
          (fiberCenter a.a3 a.a1 x.x2
            (orderedTrace a.multiplier a.a2 x.x2))
          (movingCoordinates2 x) ≠
        (0, 0)) :
    (orbitSegment (rotation2 a)
      (rotationLinearOrder
        (orderedTrace a.multiplier a.a2 x.x2)) x).card =
      rotationLinearOrder
        (orderedTrace a.multiplier a.a2 x.x2) := by
  classical
  let M :=
    rotationLinearOrder (orderedTrace a.multiplier a.a2 x.x2)
  have hrotationInjective : Function.Injective (rotation2 a) := by
    intro y z hyz
    exact (rotation2Equiv (ZMod p) a).injective hyz
  have hinjective :
      Set.InjOn (fun n : ℕ ↦ ((rotation2 a)^[n]) x)
        (Finset.range M) := by
    intro n hn m hm heq
    have hnM : n < M := by simpa [M] using hn
    have hmM : m < M := by simpa [M] using hm
    rcases lt_trichotomy n m with hnm | hnm | hmn
    · let d := m - n
      have hdPos : 0 < d := Nat.sub_pos_of_lt hnm
      have hdM : d < M := (Nat.sub_le m n).trans_lt hmM
      have hreturn : ((rotation2 a)^[d]) x = x :=
        iterate_eq_self_of_le (rotation2 a)
          hrotationInjective x (Nat.le_of_lt hnm) heq
      have hMdiv : M ∣ d := by
        simpa [M] using
          rotationLinearOrder_dvd_of_rotation2_return
            p hpTwo a x hD hnoncentered d hreturn
      exact (Nat.not_dvd_of_pos_of_lt hdPos hdM hMdiv).elim
    · exact hnm
    · let d := n - m
      have hdPos : 0 < d := Nat.sub_pos_of_lt hmn
      have hdM : d < M := (Nat.sub_le n m).trans_lt hnM
      have hreturn : ((rotation2 a)^[d]) x = x :=
        iterate_eq_self_of_le (rotation2 a)
          hrotationInjective x (Nat.le_of_lt hmn) heq.symm
      have hMdiv : M ∣ d := by
        simpa [M] using
          rotationLinearOrder_dvd_of_rotation2_return
            p hpTwo a x hD hnoncentered d hreturn
      exact (Nat.not_dvd_of_pos_of_lt hdPos hdM hMdiv).elim
  rw [orbitSegment]
  calc
    ((Finset.range M).image fun n ↦ ((rotation2 a)^[n]) x).card =
        (Finset.range M).card := Finset.card_image_iff.mpr hinjective
    _ = M := Finset.card_range M

/-- Abstract fixed-axis finite-family escape.  The factor `2` in the
low-order trace bound is essential in the general case: the actual rotation
is the square of the common BGS half-step. -/
theorem exists_orderedTraceCandidateRegular_rotationLinearOrder_ge_of_finite_family
    {T : Type*} [DecidableEq T]
    (p : ℕ) [Fact p.Prime]
    (hpTwo : p ≠ 2)
    (A B C : ZMod p) (S : Finset T)
    (traceValue : T → ZMod p) (bound : ℕ)
    (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4)
    (hfiber :
      ∀ t, (S.filter fun x => traceValue x = t).card ≤ 2)
    (hlarge :
      20 + 2 * (2 + 2 * (2 * bound) ^ 2) < S.card) :
    ∃ x ∈ S,
      OrderedTraceCandidateRegular A B C (traceValue x) ∧
        bound ≤ rotationLinearOrder (traceValue x) := by
  classical
  let lowTraceSet := concreteLowOrderTraceSet p (2 * bound)
  let low := S.filter fun x => traceValue x ∈ lowTraceSet
  let irregular := S.filter fun x =>
    Polynomial.eval (traceValue x)
      (orderedTraceSafePolynomial A B C) = 0
  have hlow :
      low.card ≤ 2 * (2 + 2 * (2 * bound) ^ 2) := by
    let cover := lowTraceSet.biUnion fun t =>
      S.filter fun x => traceValue x = t
    have hsubset : low ⊆ cover := by
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      change x ∈ lowTraceSet.biUnion (fun t =>
        S.filter fun y => traceValue y = t)
      rw [Finset.mem_biUnion]
      exact ⟨traceValue x, hx'.2,
        Finset.mem_filter.mpr ⟨hx'.1, rfl⟩⟩
    calc
      low.card ≤ cover.card := Finset.card_mono hsubset
      _ ≤ lowTraceSet.card * 2 := by
        apply Finset.card_biUnion_le_card_mul
        intro t _ht
        exact hfiber t
      _ ≤ (2 + 2 * (2 * bound) ^ 2) * 2 := by
        gcongr
        exact concreteLowOrderTraceSet_card_le p (2 * bound)
      _ = 2 * (2 + 2 * (2 * bound) ^ 2) := by omega
  have hirregular : irregular.card ≤ 20 := by
    exact card_orderedTraceSafePolynomial_zero_le_twenty
      A B C S traceValue
        (by
          have hpLe : 2 ≤ p := (Fact.out : p.Prime).two_le
          have hpLt : 2 < p := lt_of_le_of_ne hpLe hpTwo.symm
          exact two_ne_zero_zmod hpLt)
        hA hB hfiber
  have hunion : (irregular ∪ low).card < S.card := by
    calc
      (irregular ∪ low).card ≤ irregular.card + low.card :=
        Finset.card_union_le irregular low
      _ ≤ 20 + 2 * (2 + 2 * (2 * bound) ^ 2) :=
        Nat.add_le_add hirregular hlow
      _ < S.card := hlarge
  have hexists : ∃ x ∈ S, x ∉ irregular ∪ low := by
    by_contra hnone
    push Not at hnone
    have hsubset : S ⊆ irregular ∪ low := by
      intro x hx
      exact hnone x hx
    exact (Nat.not_le_of_lt hunion) (Finset.card_mono hsubset)
  obtain ⟨x, hxS, hxGood⟩ := hexists
  have hxIrregular : x ∉ irregular := fun hx =>
    hxGood (Finset.mem_union_left low hx)
  have hxLow : x ∉ low := fun hx =>
    hxGood (Finset.mem_union_right irregular hx)
  have hregular :
      OrderedTraceCandidateRegular A B C (traceValue x) := by
    rw [← orderedTraceSafePolynomial_eval_ne_zero_iff]
    intro hzero
    apply hxIrregular
    exact Finset.mem_filter.mpr ⟨hxS, hzero⟩
  have horder : bound ≤ rotationLinearOrder (traceValue x) := by
    by_contra hnot
    have hsmall : rotationLinearOrder (traceValue x) < bound :=
      Nat.lt_of_not_ge hnot
    apply hxLow
    apply Finset.mem_filter.mpr
    refine ⟨hxS, ?_⟩
    apply mem_concreteLowOrderTraceSet_of_rotationOrder_lt p hpTwo
    exact Opening.bgsRotationOrder_lt_two_mul_of_rotationLinearOrder_lt
      (traceValue x) bound hsmall
  exact ⟨x, hxS, hregular, horder⟩

/-- Divisor-sensitive fixed-axis escape.

Compared with
`exists_orderedTraceCandidateRegular_rotationLinearOrder_ge_of_finite_family`,
the low-order discard is linear in the requested actual order and in
`τ(p - 1) + τ(p + 1)`.  This refinement records the exact extra divisor
factor paid when regularity is obtained by changing the active axis. -/
theorem
    exists_orderedTraceCandidateRegular_rotationLinearOrder_ge_of_finite_family_divisor_sensitive
    {T : Type*} [DecidableEq T]
    (p : ℕ) [Fact p.Prime]
    (hpTwo : p ≠ 2)
    (A B C : ZMod p) (S : Finset T)
    (traceValue : T → ZMod p) (bound : ℕ)
    (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4)
    (hfiber :
      ∀ t, (S.filter fun x => traceValue x = t).card ≤ 2)
    (hlarge :
      20 + 2 * (2 + (2 * bound - 1) *
        ((p - 1).divisors.card + (p + 1).divisors.card)) < S.card) :
    ∃ x ∈ S,
      OrderedTraceCandidateRegular A B C (traceValue x) ∧
        bound ≤ rotationLinearOrder (traceValue x) := by
  classical
  let lowTraceSet := concreteLowOrderTraceSet p (2 * bound)
  let low := S.filter fun x => traceValue x ∈ lowTraceSet
  let irregular := S.filter fun x =>
    Polynomial.eval (traceValue x)
      (orderedTraceSafePolynomial A B C) = 0
  have hlow :
      low.card ≤ 2 * (2 + (2 * bound - 1) *
        ((p - 1).divisors.card + (p + 1).divisors.card)) := by
    let cover := lowTraceSet.biUnion fun t =>
      S.filter fun x => traceValue x = t
    have hsubset : low ⊆ cover := by
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      change x ∈ lowTraceSet.biUnion (fun t =>
        S.filter fun y => traceValue y = t)
      rw [Finset.mem_biUnion]
      exact ⟨traceValue x, hx'.2,
        Finset.mem_filter.mpr ⟨hx'.1, rfl⟩⟩
    calc
      low.card ≤ cover.card := Finset.card_mono hsubset
      _ ≤ lowTraceSet.card * 2 := by
        apply Finset.card_biUnion_le_card_mul
        intro t _ht
        exact hfiber t
      _ ≤ (2 + (2 * bound - 1) *
          ((p - 1).divisors.card + (p + 1).divisors.card)) * 2 := by
        gcongr
        exact concreteLowOrderTraceSet_card_le_divisor_sensitive (2 * bound)
      _ = 2 * (2 + (2 * bound - 1) *
          ((p - 1).divisors.card + (p + 1).divisors.card)) := by omega
  have hirregular : irregular.card ≤ 20 := by
    exact card_orderedTraceSafePolynomial_zero_le_twenty
      A B C S traceValue
        (by
          have hpLe : 2 ≤ p := (Fact.out : p.Prime).two_le
          have hpLt : 2 < p := lt_of_le_of_ne hpLe hpTwo.symm
          exact two_ne_zero_zmod hpLt)
        hA hB hfiber
  have hunion : (irregular ∪ low).card < S.card := by
    calc
      (irregular ∪ low).card ≤ irregular.card + low.card :=
        Finset.card_union_le irregular low
      _ ≤ 20 + 2 * (2 + (2 * bound - 1) *
          ((p - 1).divisors.card + (p + 1).divisors.card)) :=
        Nat.add_le_add hirregular hlow
      _ < S.card := hlarge
  have hexists : ∃ x ∈ S, x ∉ irregular ∪ low := by
    by_contra hnone
    push Not at hnone
    have hsubset : S ⊆ irregular ∪ low := by
      intro x hx
      exact hnone x hx
    exact (Nat.not_le_of_lt hunion) (Finset.card_mono hsubset)
  obtain ⟨x, hxS, hxGood⟩ := hexists
  have hxIrregular : x ∉ irregular := fun hx =>
    hxGood (Finset.mem_union_left low hx)
  have hxLow : x ∉ low := fun hx =>
    hxGood (Finset.mem_union_right irregular hx)
  have hregular :
      OrderedTraceCandidateRegular A B C (traceValue x) := by
    rw [← orderedTraceSafePolynomial_eval_ne_zero_iff]
    intro hzero
    apply hxIrregular
    exact Finset.mem_filter.mpr ⟨hxS, hzero⟩
  have horder : bound ≤ rotationLinearOrder (traceValue x) := by
    by_contra hnot
    have hsmall : rotationLinearOrder (traceValue x) < bound :=
      Nat.lt_of_not_ge hnot
    apply hxLow
    apply Finset.mem_filter.mpr
    refine ⟨hxS, ?_⟩
    apply mem_concreteLowOrderTraceSet_of_rotationOrder_lt p hpTwo
    exact Opening.bgsRotationOrder_lt_two_mul_of_rotationLinearOrder_lt
      (traceValue x) bound hsmall
  exact ⟨x, hxS, hregular, horder⟩

/-- Fixed-first-coordinate specialization in the reverse outgoing frame.
No permutation of either coordinates or coefficients is used. -/
theorem exists_axisTwo_reverseRegular_rotationLinearOrder_ge_of_fixed_axisOne_family
    (p : ℕ) [Fact p.Prime]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (S : Finset (Point (ZMod p))) (u : ZMod p) (bound : ℕ)
    (hmultiplier : a.multiplier ≠ 0)
    (hA2 : a.a2 ^ 2 ≠ 4) (hA1 : a.a1 ^ 2 ≠ 4)
    (hsolution : ∀ y ∈ S, IsSolution a y)
    (hfixed : ∀ y ∈ S, y.x1 = u)
    (hlarge :
      20 + 2 * (2 + 2 * (2 * bound) ^ 2) < S.card) :
    ∃ y ∈ S,
      OrderedTraceCandidateRegular a.a2 a.a1 a.a3
          (coordinateTrace2 a y) ∧
        bound ≤ rotationLinearOrder (coordinateTrace2 a y) := by
  classical
  refine
    exists_orderedTraceCandidateRegular_rotationLinearOrder_ge_of_finite_family
      p hpTwo a.a2 a.a1 a.a3 S (coordinateTrace2 a) bound
        hA2 hA1 ?_ hlarge
  intro t
  apply card_le_two_of_solution_fixed_x1_trace2 a
    (S.filter fun y => coordinateTrace2 a y = t) u t hmultiplier
  · intro y hy
    exact hsolution y (Finset.mem_filter.mp hy).1
  · intro y hy
    exact hfixed y (Finset.mem_filter.mp hy).1
  · intro y hy
    exact (Finset.mem_filter.mp hy).2

/-- Fixed-second-coordinate specialization in the forward outgoing frame.
The trace equation is inverted to use the existing quadratic fixed-first
fiber count; this is an algebraic relabelling inside the proof, not a surface
symmetry. -/
theorem exists_axisOne_forwardRegular_rotationLinearOrder_ge_of_fixed_axisTwo_family
    (p : ℕ) [Fact p.Prime]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (S : Finset (Point (ZMod p))) (u : ZMod p) (bound : ℕ)
    (hmultiplier : a.multiplier ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (hsolution : ∀ y ∈ S, IsSolution a y)
    (hfixed : ∀ y ∈ S, y.x2 = u)
    (hlarge :
      20 + 2 * (2 + 2 * (2 * bound) ^ 2) < S.card) :
    ∃ y ∈ S,
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3
          (coordinateTrace1 a y) ∧
        bound ≤ rotationLinearOrder (coordinateTrace1 a y) := by
  classical
  refine
    exists_orderedTraceCandidateRegular_rotationLinearOrder_ge_of_finite_family
      p hpTwo a.a1 a.a2 a.a3 S (coordinateTrace1 a) bound
        hA1 hA2 ?_ hlarge
  intro t
  apply card_le_two_of_solution_fixed_x1_trace2 a
    (S.filter fun y => coordinateTrace1 a y = t)
    ((t + a.a1) / a.multiplier)
    (a.multiplier * u - a.a2) hmultiplier
  · intro y hy
    exact hsolution y (Finset.mem_filter.mp hy).1
  · intro y hy
    apply (eq_div_iff hmultiplier).2
    have ht := (Finset.mem_filter.mp hy).2
    rw [coordinateTrace1] at ht
    linear_combination ht
  · intro y hy
    rw [coordinateTrace2, hfixed y (Finset.mem_filter.mp hy).1]

private theorem coe_iterate_rotation1SurfacePerm
    {R : Type*} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) (n : ℕ) :
    ((((rotation1SurfacePerm a)^[n]) x :
      SolutionSurface a) : Point R) =
        ((rotation1 a)^[n]) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        coe_rotation1SurfacePerm, ih]

private theorem coe_iterate_rotation2SurfacePerm
    {R : Type*} [CommRing R] (a : Coefficients R)
    (x : SolutionSurface a) (n : ℕ) :
    ((((rotation2SurfacePerm a)^[n]) x :
      SolutionSurface a) : Point R) =
        ((rotation2 a)^[n]) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        coe_rotation2SurfacePerm, ih]

private theorem sameRotationComponent_of_iterate_rotation1
    {R : Type*} [CommRing R] (a : Coefficients R)
    (x y : SolutionSurface a) (n : ℕ)
    (hxy : ((rotation1 a)^[n]) x.1 = y.1) :
    SameRotationComponent x y := by
  obtain ⟨g, hg⟩ :=
    sameRotationComponent_iterate_rotationSurfacePermAt
      a .first x n
  refine ⟨g, hg.trans ?_⟩
  apply Subtype.ext
  simpa [rotationSurfacePermAt] using
    (coe_iterate_rotation1SurfacePerm a x n).trans hxy

private theorem sameRotationComponent_of_iterate_rotation2
    {R : Type*} [CommRing R] (a : Coefficients R)
    (x y : SolutionSurface a) (n : ℕ)
    (hxy : ((rotation2 a)^[n]) x.1 = y.1) :
    SameRotationComponent x y := by
  obtain ⟨g, hg⟩ :=
    sameRotationComponent_iterate_rotationSurfacePermAt
      a .second x n
  refine ⟨g, hg.trans ?_⟩
  apply Subtype.ext
  simpa [rotationSurfacePermAt] using
    (coe_iterate_rotation2SurfacePerm a x n).trans hxy

/-- A nonparabolic noncentered first-axis cycle supplies a regular reverse
alternating state with prescribed lower actual order. -/
theorem exists_sameRotationComponent_secondFirst_regularState_of_large_axisOne_cycle
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (hA2 : a.a2 ^ 2 ≠ 4) (hA1 : a.a1 ^ 2 ≠ 4)
    (x : SolutionSurface a) (bound : ℕ)
    (hD : discriminant (coordinateTrace1 a x.1) ≠ 0)
    (hnoncentered :
      centerCoordinates
          (fiberCenter a.a2 a.a3 x.1.x1 (coordinateTrace1 a x.1))
          (movingCoordinates1 x.1) ≠ (0, 0))
    (hlarge :
      20 + 2 * (2 + 2 * (2 * bound) ^ 2) <
        rotationLinearOrder (coordinateTrace1 a x.1)) :
    ∃ state : AlternatingRegularState a,
      state.direction = .secondFirst ∧
        SameRotationComponent x state.point ∧
        bound ≤ alternatingActualOrder state := by
  classical
  let M := rotationLinearOrder (coordinateTrace1 a x.1)
  let S := orbitSegment (rotation1 a) M x.1
  have hcard : S.card = M := by
    simpa [S, M, coordinateTrace1, orderedTrace, discriminant] using
      rotation1Segment_card_eq_rotationLinearOrder
        p hpTwo a x.1
          (by
            simpa [coordinateTrace1, orderedTrace, discriminant] using hD)
          (by simpa [coordinateTrace1, orderedTrace] using hnoncentered)
  obtain ⟨y, hyS, hyRegular, hyOrder⟩ :=
    exists_axisTwo_reverseRegular_rotationLinearOrder_ge_of_fixed_axisOne_family
      p hpTwo a S x.1.x1 bound hmultiplier hA2 hA1
        (by
          intro z hz
          change z ∈ orbitSegment (rotation1 a) M x.1 at hz
          rw [orbitSegment, Finset.mem_image] at hz
          obtain ⟨n, _hn, rfl⟩ := hz
          exact isSolution_iterate_rotation1 a x.1 x.2 n)
        (by
          intro z hz
          change z ∈ orbitSegment (rotation1 a) M x.1 at hz
          rw [orbitSegment, Finset.mem_image] at hz
          obtain ⟨n, _hn, rfl⟩ := hz
          exact iterate_rotation1_firstCoordinate a x.1 n)
        (by simpa [hcard, M] using hlarge)
  change y ∈ orbitSegment (rotation1 a) M x.1 at hyS
  rw [orbitSegment, Finset.mem_image] at hyS
  obtain ⟨n, _hn, rfl⟩ := hyS
  let yPoint : Point (ZMod p) := ((rotation1 a)^[n]) x.1
  have hySolution : IsSolution a yPoint :=
    isSolution_iterate_rotation1 a x.1 x.2 n
  let ySurface : SolutionSurface a := ⟨yPoint, hySolution⟩
  let state : AlternatingRegularState a :=
    ⟨.secondFirst, ySurface, by
      simpa [alternatingTraceRegular, ySurface, yPoint, traceAt,
        coordinateTrace2, coefficientAt, coordinateAt, orderedTrace] using
        hyRegular⟩
  refine ⟨state, rfl, ?_, ?_⟩
  · exact sameRotationComponent_of_iterate_rotation1
      a x ySurface n rfl
  · simpa [state, alternatingActualOrder,
      AlternatingDirectedAxis.fixed, rotationLinearOrderAt, traceAt,
      coordinateTrace2, coefficientAt, coordinateAt, orderedTrace,
      ySurface, yPoint] using hyOrder

/-- A nonparabolic noncentered second-axis cycle supplies a regular forward
alternating state with prescribed lower actual order. -/
theorem exists_sameRotationComponent_firstSecond_regularState_of_large_axisTwo_cycle
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (x : SolutionSurface a) (bound : ℕ)
    (hD : discriminant (coordinateTrace2 a x.1) ≠ 0)
    (hnoncentered :
      centerCoordinates
          (fiberCenter a.a3 a.a1 x.1.x2 (coordinateTrace2 a x.1))
          (movingCoordinates2 x.1) ≠ (0, 0))
    (hlarge :
      20 + 2 * (2 + 2 * (2 * bound) ^ 2) <
        rotationLinearOrder (coordinateTrace2 a x.1)) :
    ∃ state : AlternatingRegularState a,
      state.direction = .firstSecond ∧
        SameRotationComponent x state.point ∧
        bound ≤ alternatingActualOrder state := by
  classical
  let M := rotationLinearOrder (coordinateTrace2 a x.1)
  let S := orbitSegment (rotation2 a) M x.1
  have hcard : S.card = M := by
    simpa [S, M, coordinateTrace2, orderedTrace, discriminant] using
      rotation2Segment_card_eq_rotationLinearOrder
        p hpTwo a x.1
          (by
            simpa [coordinateTrace2, orderedTrace, discriminant] using hD)
          (by simpa [coordinateTrace2, orderedTrace] using hnoncentered)
  obtain ⟨y, hyS, hyRegular, hyOrder⟩ :=
    exists_axisOne_forwardRegular_rotationLinearOrder_ge_of_fixed_axisTwo_family
      p hpTwo a S x.1.x2 bound hmultiplier hA1 hA2
        (by
          intro z hz
          change z ∈ orbitSegment (rotation2 a) M x.1 at hz
          rw [orbitSegment, Finset.mem_image] at hz
          obtain ⟨n, _hn, rfl⟩ := hz
          exact isSolution_iterate_rotation2 a x.1 x.2 n)
        (by
          intro z hz
          change z ∈ orbitSegment (rotation2 a) M x.1 at hz
          rw [orbitSegment, Finset.mem_image] at hz
          obtain ⟨n, _hn, rfl⟩ := hz
          exact iterate_rotation2_secondCoordinate a x.1 n)
        (by simpa [hcard, M] using hlarge)
  change y ∈ orbitSegment (rotation2 a) M x.1 at hyS
  rw [orbitSegment, Finset.mem_image] at hyS
  obtain ⟨n, _hn, rfl⟩ := hyS
  let yPoint : Point (ZMod p) := ((rotation2 a)^[n]) x.1
  have hySolution : IsSolution a yPoint :=
    isSolution_iterate_rotation2 a x.1 x.2 n
  let ySurface : SolutionSurface a := ⟨yPoint, hySolution⟩
  let state : AlternatingRegularState a :=
    ⟨.firstSecond, ySurface, by
      simpa [alternatingTraceRegular, ySurface, yPoint, traceAt,
        coordinateTrace1, coefficientAt, coordinateAt, orderedTrace] using
        hyRegular⟩
  refine ⟨state, rfl, ?_, ?_⟩
  · exact sameRotationComponent_of_iterate_rotation2
      a x ySurface n rfl
  · simpa [state, alternatingActualOrder,
      AlternatingDirectedAxis.fixed, rotationLinearOrderAt, traceAt,
      coordinateTrace1, coefficientAt, coordinateAt, orderedTrace,
      ySurface, yPoint] using hyOrder

/-- Any first-axis point cycle of exact length `p` routes quantitatively to
the reverse alternating frame.  This is the interface used by both signed
parabolic cases. -/
theorem exists_sameRotationComponent_secondFirst_regularState_of_axisOne_period_prime
    (p : ℕ) [Fact p.Prime]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (hA2 : a.a2 ^ 2 ≠ 4) (hA1 : a.a1 ^ 2 ≠ 4)
    (x : SolutionSurface a) (bound : ℕ)
    (hperiod : Function.minimalPeriod (rotation1 a) x.1 = p)
    (hlarge :
      20 + 2 * (2 + 2 * (2 * bound) ^ 2) < p) :
    ∃ state : AlternatingRegularState a,
      state.direction = .secondFirst ∧
        SameRotationComponent x state.point ∧
        bound ≤ alternatingActualOrder state := by
  classical
  let S := orbitSegment (rotation1 a) p x.1
  have hcard : S.card = p :=
    orbitSegment_card_of_minimalPeriod_eq (rotation1 a) p x.1 hperiod
  obtain ⟨y, hyS, hyRegular, hyOrder⟩ :=
    exists_axisTwo_reverseRegular_rotationLinearOrder_ge_of_fixed_axisOne_family
      p hpTwo a S x.1.x1 bound hmultiplier hA2 hA1
        (by
          intro z hz
          change z ∈ orbitSegment (rotation1 a) p x.1 at hz
          rw [orbitSegment, Finset.mem_image] at hz
          obtain ⟨n, _hn, rfl⟩ := hz
          exact isSolution_iterate_rotation1 a x.1 x.2 n)
        (by
          intro z hz
          change z ∈ orbitSegment (rotation1 a) p x.1 at hz
          rw [orbitSegment, Finset.mem_image] at hz
          obtain ⟨n, _hn, rfl⟩ := hz
          exact iterate_rotation1_firstCoordinate a x.1 n)
        (by simpa [hcard] using hlarge)
  change y ∈ orbitSegment (rotation1 a) p x.1 at hyS
  rw [orbitSegment, Finset.mem_image] at hyS
  obtain ⟨n, _hn, rfl⟩ := hyS
  let yPoint : Point (ZMod p) := ((rotation1 a)^[n]) x.1
  have hySolution : IsSolution a yPoint :=
    isSolution_iterate_rotation1 a x.1 x.2 n
  let ySurface : SolutionSurface a := ⟨yPoint, hySolution⟩
  let state : AlternatingRegularState a :=
    ⟨.secondFirst, ySurface, by
      simpa [alternatingTraceRegular, ySurface, yPoint, traceAt,
        coordinateTrace2, coefficientAt, coordinateAt, orderedTrace] using
        hyRegular⟩
  refine ⟨state, rfl, ?_, ?_⟩
  · exact sameRotationComponent_of_iterate_rotation1
      a x ySurface n rfl
  · simpa [state, alternatingActualOrder,
      AlternatingDirectedAxis.fixed, rotationLinearOrderAt, traceAt,
      coordinateTrace2, coefficientAt, coordinateAt, orderedTrace,
      ySurface, yPoint] using hyOrder

/-- Any second-axis point cycle of exact length `p` routes quantitatively to
the forward alternating frame. -/
theorem exists_sameRotationComponent_firstSecond_regularState_of_axisTwo_period_prime
    (p : ℕ) [Fact p.Prime]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (x : SolutionSurface a) (bound : ℕ)
    (hperiod : Function.minimalPeriod (rotation2 a) x.1 = p)
    (hlarge :
      20 + 2 * (2 + 2 * (2 * bound) ^ 2) < p) :
    ∃ state : AlternatingRegularState a,
      state.direction = .firstSecond ∧
        SameRotationComponent x state.point ∧
        bound ≤ alternatingActualOrder state := by
  classical
  let S := orbitSegment (rotation2 a) p x.1
  have hcard : S.card = p :=
    orbitSegment_card_of_minimalPeriod_eq (rotation2 a) p x.1 hperiod
  obtain ⟨y, hyS, hyRegular, hyOrder⟩ :=
    exists_axisOne_forwardRegular_rotationLinearOrder_ge_of_fixed_axisTwo_family
      p hpTwo a S x.1.x2 bound hmultiplier hA1 hA2
        (by
          intro z hz
          change z ∈ orbitSegment (rotation2 a) p x.1 at hz
          rw [orbitSegment, Finset.mem_image] at hz
          obtain ⟨n, _hn, rfl⟩ := hz
          exact isSolution_iterate_rotation2 a x.1 x.2 n)
        (by
          intro z hz
          change z ∈ orbitSegment (rotation2 a) p x.1 at hz
          rw [orbitSegment, Finset.mem_image] at hz
          obtain ⟨n, _hn, rfl⟩ := hz
          exact iterate_rotation2_secondCoordinate a x.1 n)
        (by simpa [hcard] using hlarge)
  change y ∈ orbitSegment (rotation2 a) p x.1 at hyS
  rw [orbitSegment, Finset.mem_image] at hyS
  obtain ⟨n, _hn, rfl⟩ := hyS
  let yPoint : Point (ZMod p) := ((rotation2 a)^[n]) x.1
  have hySolution : IsSolution a yPoint :=
    isSolution_iterate_rotation2 a x.1 x.2 n
  let ySurface : SolutionSurface a := ⟨yPoint, hySolution⟩
  let state : AlternatingRegularState a :=
    ⟨.firstSecond, ySurface, by
      simpa [alternatingTraceRegular, ySurface, yPoint, traceAt,
        coordinateTrace1, coefficientAt, coordinateAt, orderedTrace] using
        hyRegular⟩
  refine ⟨state, rfl, ?_, ?_⟩
  · exact sameRotationComponent_of_iterate_rotation2
      a x ySurface n rfl
  · simpa [state, alternatingActualOrder,
      AlternatingDirectedAxis.fixed, rotationLinearOrderAt, traceAt,
      coordinateTrace1, coefficientAt, coordinateAt, orderedTrace,
      ySurface, yPoint] using hyOrder

private theorem eq_two_or_eq_neg_two_of_sq_eq_four
    (p : ℕ) [Fact p.Prime] (t : ZMod p) (h : t ^ 2 = 4) :
    t = 2 ∨ t = -2 := by
  apply (sq_eq_sq_iff_eq_or_eq_neg).mp
  calc
    t ^ 2 = 4 := h
    _ = (2 : ZMod p) ^ 2 := by norm_num

/-- Signed parabolic first-axis routing.  Exact period `p`, rather than the
linear-order formula, supplies the available point count. -/
theorem exists_sameRotationComponent_secondFirst_regularState_of_parabolic_axisOne
    (p : ℕ) [Fact p.Prime]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (x : SolutionSurface a) (bound : ℕ)
    (hparabolic : coordinateTrace1 a x.1 ^ 2 = 4)
    (hlarge :
      20 + 2 * (2 + 2 * (2 * bound) ^ 2) < p) :
    ∃ state : AlternatingRegularState a,
      state.direction = .secondFirst ∧
        SameRotationComponent x state.point ∧
        bound ≤ alternatingActualOrder state := by
  rcases eq_two_or_eq_neg_two_of_sq_eq_four
      p (coordinateTrace1 a x.1) hparabolic with htrace | htrace
  · apply
      exists_sameRotationComponent_secondFirst_regularState_of_axisOne_period_prime
        p hpTwo a hmultiplier hA2 hA1 x bound
    · apply minimalPeriod_rotation1_eq_prime_of_trace_eq_two
        p hpTwo a x.1 hA1 hA3
      · simpa [coordinateTrace1, orderedTrace] using htrace
      · exact x.2
    · exact hlarge
  · apply
      exists_sameRotationComponent_secondFirst_regularState_of_axisOne_period_prime
        p hpTwo a hmultiplier hA2 hA1 x bound
    · apply minimalPeriod_rotation1_eq_prime_of_trace_eq_neg_two
        p hpTwo a x.1 hA1 hA3
      · simpa [coordinateTrace1, orderedTrace] using htrace
      · exact x.2
    · exact hlarge

/-- Signed parabolic second-axis routing to the forward alternating frame. -/
theorem exists_sameRotationComponent_firstSecond_regularState_of_parabolic_axisTwo
    (p : ℕ) [Fact p.Prime]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (x : SolutionSurface a) (bound : ℕ)
    (hparabolic : coordinateTrace2 a x.1 ^ 2 = 4)
    (hlarge :
      20 + 2 * (2 + 2 * (2 * bound) ^ 2) < p) :
    ∃ state : AlternatingRegularState a,
      state.direction = .firstSecond ∧
        SameRotationComponent x state.point ∧
        bound ≤ alternatingActualOrder state := by
  rcases eq_two_or_eq_neg_two_of_sq_eq_four
      p (coordinateTrace2 a x.1) hparabolic with htrace | htrace
  · apply
      exists_sameRotationComponent_firstSecond_regularState_of_axisTwo_period_prime
        p hpTwo a hmultiplier hA1 hA2 x bound
    · apply minimalPeriod_rotation2_eq_prime_of_trace_eq_two
        p hpTwo a x.1 hA2 hA1
      · simpa [coordinateTrace2, orderedTrace] using htrace
      · exact x.2
    · exact hlarge
  · apply
      exists_sameRotationComponent_firstSecond_regularState_of_axisTwo_period_prime
        p hpTwo a hmultiplier hA1 hA2 x bound
    · apply minimalPeriod_rotation2_eq_prime_of_trace_eq_neg_two
        p hpTwo a x.1 hA2 hA1
      · simpa [coordinateTrace2, orderedTrace] using htrace
      · exact x.2
    · exact hlarge

private theorem eq_fiberCenter_of_centerCoordinates_eq_zero
    {K : Type*} [Field K] (m v : K × K)
    (hcentered : centerCoordinates m v = (0, 0)) :
    v = m := by
  apply Prod.ext
  · have h := congrArg Prod.fst hcentered
    simpa [centerCoordinates] using sub_eq_zero.mp h
  · have h := congrArg Prod.snd hcentered
    simpa [centerCoordinates] using sub_eq_zero.mp h

theorem rotation1_fixed_of_nonparabolic_centered
    {K : Type*} [Field K]
    (a : Coefficients K) (x : Point K)
    (hD : discriminant (coordinateTrace1 a x) ≠ 0)
    (hcentered :
      centerCoordinates
          (fiberCenter a.a2 a.a3 x.x1 (coordinateTrace1 a x))
          (movingCoordinates1 x) = (0, 0)) :
    rotation1 a x = x := by
  have hmoving :
      movingCoordinates1 x =
        fiberCenter a.a2 a.a3 x.x1 (coordinateTrace1 a x) :=
    eq_fiberCenter_of_centerCoordinates_eq_zero _ _ hcentered
  have hmovingFixed :
      movingCoordinates1 (rotation1 a x) = movingCoordinates1 x := by
    calc
      movingCoordinates1 (rotation1 a x) =
          affineRotation a.a2 a.a3 x.x1 (coordinateTrace1 a x)
            (movingCoordinates1 x) := by
              simpa [coordinateTrace1, orderedTrace] using
                movingCoordinates1_rotation1 a x
      _ = affineRotation a.a2 a.a3 x.x1 (coordinateTrace1 a x)
            (fiberCenter a.a2 a.a3 x.x1 (coordinateTrace1 a x)) := by
              rw [hmoving]
      _ = fiberCenter a.a2 a.a3 x.x1 (coordinateTrace1 a x) :=
        affineRotation_fiberCenter _ _ _ _ hD
      _ = movingCoordinates1 x := hmoving.symm
  apply Point.ext
  · rfl
  · exact congrArg Prod.fst hmovingFixed
  · exact congrArg Prod.snd hmovingFixed

theorem rotation2_fixed_of_nonparabolic_centered
    {K : Type*} [Field K]
    (a : Coefficients K) (x : Point K)
    (hD : discriminant (coordinateTrace2 a x) ≠ 0)
    (hcentered :
      centerCoordinates
          (fiberCenter a.a3 a.a1 x.x2 (coordinateTrace2 a x))
          (movingCoordinates2 x) = (0, 0)) :
    rotation2 a x = x := by
  have hmoving :
      movingCoordinates2 x =
        fiberCenter a.a3 a.a1 x.x2 (coordinateTrace2 a x) :=
    eq_fiberCenter_of_centerCoordinates_eq_zero _ _ hcentered
  have hmovingFixed :
      movingCoordinates2 (rotation2 a x) = movingCoordinates2 x := by
    calc
      movingCoordinates2 (rotation2 a x) =
          affineRotation a.a3 a.a1 x.x2 (coordinateTrace2 a x)
            (movingCoordinates2 x) := by
              simpa [coordinateTrace2, orderedTrace] using
                movingCoordinates2_rotation2 a x
      _ = affineRotation a.a3 a.a1 x.x2 (coordinateTrace2 a x)
            (fiberCenter a.a3 a.a1 x.x2 (coordinateTrace2 a x)) := by
              rw [hmoving]
      _ = fiberCenter a.a3 a.a1 x.x2 (coordinateTrace2 a x) :=
        affineRotation_fiberCenter _ _ _ _ hD
      _ = movingCoordinates2 x := hmoving.symm
  apply Point.ext
  · exact congrArg Prod.snd hmovingFixed
  · rfl
  · exact congrArg Prod.fst hmovingFixed

/-- The startup orbit can simultaneously avoid both small first/second
orders and the six-point union of nonparabolic centered loci. -/
theorem exists_mem_rotationOrbit_outside_firstTwoCentered_with_large_order_of_dvd
    (p : ℕ) [Fact p.Prime]
    (a : Coefficients (ZMod p)) (startupBound : ℕ)
    (hmultiplier : a.multiplier ≠ 0)
    (x : PuncturedSolutionSurface a)
    (hdiv : p ∣ (puncturedRotationOrbit x).ncard)
    (hsmallCentered :
      (pointsWithSmallFirstTwoRotationLinearOrders
          p a startupBound).card + 6 < p) :
    ∃ y : PuncturedSolutionSurface a,
      y ∈ puncturedRotationOrbit x ∧
        y.1.1 ∉ firstTwoAxesNonparabolicRotationFixedLocus p a ∧
        (startupBound ≤ rotationLinearOrder (coordinateTrace1 a y.1.1) ∨
          startupBound ≤ rotationLinearOrder (coordinateTrace2 a y.1.1)) := by
  classical
  let small :=
    pointsWithSmallFirstTwoRotationLinearOrders p a startupBound
  let centered :=
    firstTwoAxesNonparabolicRotationFixedLocus p a
  let bad := small ∪ centered
  have hbadCard : bad.card < p := by
    calc
      bad.card ≤ small.card + centered.card :=
        Finset.card_union_le _ _
      _ ≤ small.card + 6 := Nat.add_le_add_left
        (firstTwoAxesNonparabolicRotationFixedLocus_card_le_six
          p a hmultiplier) _
      _ < p := by simpa [small] using hsmallCentered
  have horbitPos : 0 < (puncturedRotationOrbit x).ncard := by
    apply (Set.ncard_pos (Set.toFinite (puncturedRotationOrbit x))).mpr
    exact ⟨x, MulAction.mem_orbit_self x⟩
  have hpLeOrbit : p ≤ (puncturedRotationOrbit x).ncard :=
    Nat.le_of_dvd horbitPos hdiv
  let orbitFinset : Finset (PuncturedSolutionSurface a) :=
    (Set.toFinite (puncturedRotationOrbit x)).toFinset
  let pointEmbedding : PuncturedSolutionSurface a ↪ Point (ZMod p) :=
    ⟨(fun y => y.1.1), by
      intro y z hyz
      exact Subtype.ext (Subtype.ext hyz)⟩
  have hexists : ∃ y ∈ orbitFinset, pointEmbedding y ∉ bad := by
    by_contra hnone
    push Not at hnone
    have hsubset : orbitFinset.map pointEmbedding ⊆ bad := by
      intro z hz
      rw [Finset.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact hnone y hy
    have hle :
        orbitFinset.card ≤ bad.card := by
      rw [← Finset.card_map (f := pointEmbedding)]
      exact Finset.card_le_card hsubset
    have horbitCard :
        orbitFinset.card = (puncturedRotationOrbit x).ncard := by
      simpa [orbitFinset] using
        (Set.ncard_eq_toFinset_card (puncturedRotationOrbit x)
          (Set.toFinite (puncturedRotationOrbit x))).symm
    rw [horbitCard] at hle
    omega
  obtain ⟨y, hyOrbitFinset, hyBad⟩ := hexists
  have hyOrbit : y ∈ puncturedRotationOrbit x := by
    simpa [orbitFinset] using hyOrbitFinset
  have hySmall : y.1.1 ∉ small := fun hy =>
    hyBad (Finset.mem_union_left centered hy)
  have hyCentered : y.1.1 ∉ centered := fun hy =>
    hyBad (Finset.mem_union_right small hy)
  have hyOrder :
      startupBound ≤ rotationLinearOrder (coordinateTrace1 a y.1.1) ∨
        startupBound ≤ rotationLinearOrder (coordinateTrace2 a y.1.1) := by
    by_contra hnone
    push Not at hnone
    apply hySmall
    apply mem_pointsWithSmallFirstTwoRotationLinearOrders_iff.mpr
    exact ⟨y.1.2, hnone.1, hnone.2⟩
  exact ⟨y, hyOrbit, by simpa [centered] using hyCentered, hyOrder⟩

/-- The additive six-point centered error is asymptotically harmless for the
same startup exponent `1 / 8`.  This is a genuinely new numerical margin
relative to the uncentered startup count. -/
theorem eventually_startupSmallOrderCountBound_add_six_lt_prime :
    ∀ᶠ p : ℕ in atTop,
      2 *
          (2 + 2 *
            (2 * Nat.ceil ((p : ℝ) ^ startupExponent)) ^ 2) ^ 2 +
        6 < p := by
  let θ : ℝ := 3 / 16
  have hExponentLt : startupExponent < θ := by
    norm_num [startupExponent, θ]
  have hThetaPos : 0 < θ := startupExponent_pos.trans hExponentLt
  have hThreeFourthsLtOne : (3 : ℝ) / 4 < 1 := by
    norm_num
  have hceilBuffered :
      ∀ᶠ p : ℕ in atTop,
        (((Nat.ceil ((p : ℝ) ^ startupExponent) + 1 : ℕ) : ℝ) ≤
          (p : ℝ) ^ θ) :=
    eventually_natCeil_rpow_add_one_le_rpow
      startupExponent_pos hExponentLt
  have hdominance :
      ∀ᶠ p : ℕ in atTop,
        (400 : ℝ) * (p : ℝ) ^ ((3 : ℝ) / 4) <
          (p : ℝ) ^ (1 : ℝ) :=
    eventually_const_mul_rpow_lt_rpow
      (C := (400 : ℝ)) (a := (3 : ℝ) / 4) (b := 1)
        hThreeFourthsLtOne
  filter_upwards [hceilBuffered, hdominance, eventually_ge_atTop 12] with
      p hceilBuffer hdominanceP hpTwelve
  let B : ℕ := Nat.ceil ((p : ℝ) ^ startupExponent)
  have hpRealOne : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (show 1 ≤ p by omega)
  have hpowOne : (1 : ℝ) ≤ (p : ℝ) ^ θ :=
    Real.one_le_rpow hpRealOne hThetaPos.le
  have hB : (B : ℝ) ≤ (p : ℝ) ^ θ := by
    calc
      (B : ℝ) ≤ ((B + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_add_right B 1)
      _ ≤ (p : ℝ) ^ θ := by
        simpa [B] using hceilBuffer
  have hBSq : (B : ℝ) ^ 2 ≤ ((p : ℝ) ^ θ) ^ 2 := by
    gcongr
  have hpowSqOne : (1 : ℝ) ≤ ((p : ℝ) ^ θ) ^ 2 := by
    nlinarith [sq_nonneg ((p : ℝ) ^ θ - 1)]
  have hinner :
      (2 : ℝ) + 2 * (2 * (B : ℝ)) ^ 2 ≤
        10 * ((p : ℝ) ^ θ) ^ 2 := by
    calc
      (2 : ℝ) + 2 * (2 * (B : ℝ)) ^ 2 =
          2 + 8 * (B : ℝ) ^ 2 := by ring
      _ ≤ 2 + 8 * ((p : ℝ) ^ θ) ^ 2 := by
        gcongr
      _ ≤ 2 * ((p : ℝ) ^ θ) ^ 2 +
          8 * ((p : ℝ) ^ θ) ^ 2 := by
        nlinarith
      _ = 10 * ((p : ℝ) ^ θ) ^ 2 := by ring
  have hcountReal :
      ((2 *
          (2 + 2 * (2 * B) ^ 2) ^ 2 : ℕ) : ℝ) ≤
        200 * (p : ℝ) ^ ((3 : ℝ) / 4) := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow]
    calc
      (2 : ℝ) *
          ((2 : ℝ) + 2 * (2 * (B : ℝ)) ^ 2) ^ 2 ≤
          2 * (10 * ((p : ℝ) ^ θ) ^ 2) ^ 2 := by
        gcongr
      _ = 200 * (((p : ℝ) ^ θ) ^ 4) := by ring
      _ = 200 * (p : ℝ) ^ (θ * (4 : ℕ)) := by
        rw [Real.rpow_mul_natCast (Nat.cast_nonneg p) θ 4]
      _ = 200 * (p : ℝ) ^ ((3 : ℝ) / 4) := by
        norm_num [θ]
  have hdoubleCountRealLt :
      (2 : ℝ) *
          ((2 *
            (2 + 2 * (2 * B) ^ 2) ^ 2 : ℕ) : ℝ) <
        (p : ℝ) := by
    calc
      (2 : ℝ) *
          ((2 *
            (2 + 2 * (2 * B) ^ 2) ^ 2 : ℕ) : ℝ) ≤
          2 * (200 * (p : ℝ) ^ ((3 : ℝ) / 4)) := by
        gcongr
      _ = 400 * (p : ℝ) ^ ((3 : ℝ) / 4) := by ring
      _ < (p : ℝ) ^ (1 : ℝ) := hdominanceP
      _ = (p : ℝ) := by rw [Real.rpow_one]
  have hdoubleCount :
      2 * (2 * (2 + 2 * (2 * B) ^ 2) ^ 2) < p := by
    exact_mod_cast hdoubleCountRealLt
  change 2 * (2 + 2 * (2 * B) ^ 2) ^ 2 + 6 < p
  omega

/-- A ceiling of a nonnegative prime power is at most twice that power once
the prime is at least one. -/
theorem natCeil_rpow_le_two_mul
    {p : ℕ} {theta : ℝ}
    (hpOne : 1 ≤ p) (htheta : 0 ≤ theta) :
    (Nat.ceil ((p : ℝ) ^ theta) : ℝ) ≤
      2 * (p : ℝ) ^ theta := by
  have hpRealOne : (1 : ℝ) ≤ p := by exact_mod_cast hpOne
  have hpowOne : (1 : ℝ) ≤ (p : ℝ) ^ theta :=
    Real.one_le_rpow hpRealOne htheta
  have hceil :
      (Nat.ceil ((p : ℝ) ^ theta) : ℝ) <
        (p : ℝ) ^ theta + 1 :=
    Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg p) theta)
  linarith

/-- Closed-cutoff form of the centered startup estimate. -/
theorem startupSmallOrderCountBound_add_six_lt_prime_of_analyticCutoff
    {p : ℕ} (hp : analyticCutoff ≤ p) :
    2 *
          (2 + 2 *
            (2 * Nat.ceil ((p : ℝ) ^ startupExponent)) ^ 2) ^ 2 +
        6 < p := by
  let B := Nat.ceil ((p : ℝ) ^ startupExponent)
  have hpOne : 1 ≤ p :=
    (analyticCutoff_gt_one.trans_le hp).le
  have hpRealOne : (1 : ℝ) ≤ p := by exact_mod_cast hpOne
  have hpRealStrict : (1 : ℝ) < p := by
    exact_mod_cast analyticCutoff_gt_one.trans_le hp
  have hpRealPos : (0 : ℝ) < p := zero_lt_one.trans hpRealStrict
  have hB :
      (B : ℝ) ≤ 2 * (p : ℝ) ^ startupExponent := by
    exact natCeil_rpow_le_two_mul hpOne
      (by norm_num [startupExponent])
  have hpowOne :
      (1 : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow hpRealOne (by norm_num)
  have hcount :
      (2 *
          (2 + 2 * (2 * B) ^ 2) ^ 2 + 6 : ℕ) ≤
        (3206 : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_pow]
    calc
      (2 : ℝ) *
            (2 + 2 * (2 * (B : ℝ)) ^ 2) ^ 2 + 6 ≤
          2 * (2 + 2 * (2 *
            (2 * (p : ℝ) ^ startupExponent)) ^ 2) ^ 2 + 6 := by
        gcongr
      _ = 2 * (2 + 32 *
          ((p : ℝ) ^ startupExponent) ^ 2) ^ 2 + 6 := by ring
      _ ≤ 2 * (34 *
          ((p : ℝ) ^ startupExponent) ^ 2) ^ 2 +
            6 * (p : ℝ) ^ (1 / 2 : ℝ) := by
        have hone :
            (1 : ℝ) ≤ ((p : ℝ) ^ startupExponent) ^ 2 := by
          have hrootOne :
              (1 : ℝ) ≤ (p : ℝ) ^ startupExponent :=
            Real.one_le_rpow hpRealOne
              (by
                norm_num [startupExponent] :
                  (0 : ℝ) ≤ startupExponent)
          nlinarith [sq_nonneg
            ((p : ℝ) ^ startupExponent - 1)]
        apply add_le_add
        · gcongr
          nlinarith
        · nlinarith
      _ = 2318 * (p : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)
          startupExponent 2]
        calc
          2 * (34 * (p : ℝ) ^ (startupExponent * 2)) ^ 2 +
                6 * (p : ℝ) ^ (1 / 2 : ℝ) =
              2312 * ((p : ℝ) ^
                (startupExponent * 2)) ^ 2 +
                6 * (p : ℝ) ^ (1 / 2 : ℝ) := by ring
          _ = 2318 * (p : ℝ) ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)
              (startupExponent * 2) 2]
            norm_num [startupExponent]
            ring
      _ ≤ 3206 * (p : ℝ) ^ (1 / 2 : ℝ) := by
        gcongr
        norm_num
  have hfixed :
      (3206 : ℝ) < (p : ℝ) ^ (1 / 256 : ℝ) :=
    small_fixed_lt_rpow_one_div_twoHundredFiftySix hp
      (by norm_num)
  have hdominance :
      (3206 : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ) < p := by
    calc
      (3206 : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ) <
          (p : ℝ) ^ (1 / 256 : ℝ) *
            (p : ℝ) ^ (1 / 2 : ℝ) :=
        mul_lt_mul_of_pos_right hfixed
          (Real.rpow_pos_of_pos hpRealPos _)
      _ = (p : ℝ) ^ (129 / 256 : ℝ) := by
        rw [← Real.rpow_add hpRealPos]
        congr 1
        norm_num
      _ < p := by
        have hexponent : (129 / 256 : ℝ) < 1 := by norm_num
        simpa only [Real.rpow_one] using
          Real.rpow_lt_rpow_of_exponent_lt
            hpRealStrict hexponent
  exact_mod_cast hcount.trans_lt hdominance

/-- Threshold form of the centered startup estimate. -/
theorem exists_threshold_startupSmallOrderCountBound_add_six_lt_prime :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p →
      2 *
          (2 + 2 *
            (2 * Nat.ceil ((p : ℝ) ^ startupExponent)) ^ 2) ^ 2 +
        6 < p :=
  ⟨analyticCutoff,
    fun _p hp =>
      startupSmallOrderCountBound_add_six_lt_prime_of_analyticCutoff hp⟩

/-- For a fixed integrally nondegenerate integral coefficient triple, every
punctured rotation orbit modulo every sufficiently large prime contains a
large first- or second-order point outside both nonparabolic centered loci.
This is the centered refinement of the original startup theorem. -/
theorem
    IntegrallyNondegenerate.exists_threshold_every_rotationOrbit_has_large_order_outside_firstTwoCentered
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a) :
    ∃ threshold : ℕ,
      ∀ (p : ℕ) (_hp : p.Prime), threshold ≤ p →
        letI : Fact p.Prime := ⟨_hp⟩
        ∀ x : PuncturedSolutionSurface (modCoefficients a p),
          ∃ y : PuncturedSolutionSurface (modCoefficients a p),
            y ∈ puncturedRotationOrbit x ∧
              y.1.1 ∉
                firstTwoAxesNonparabolicRotationFixedLocus
                  p (modCoefficients a p) ∧
              (Nat.ceil ((p : ℝ) ^ startupExponent) ≤
                  rotationLinearOrder
                    (coordinateTrace1 (modCoefficients a p) y.1.1) ∨
                Nat.ceil ((p : ℝ) ^ startupExponent) ≤
                  rotationLinearOrder
                    (coordinateTrace2 (modCoefficients a p) y.1.1)) := by
  obtain ⟨divisibilityThreshold, hdivisibility⟩ :=
    ha.eventually_rotationOrbitDivisibility
  obtain ⟨countThreshold, hcount⟩ :=
    exists_threshold_startupSmallOrderCountBound_add_six_lt_prime
  refine
    ⟨max (max divisibilityThreshold (genericAdmissibilityCutoff a))
        (max countThreshold 5), ?_⟩
  intro p hp hpLarge x
  letI : Fact p.Prime := ⟨hp⟩
  have hpDivisibility : divisibilityThreshold ≤ p :=
    (Nat.le_max_left divisibilityThreshold
      (genericAdmissibilityCutoff a)).trans <|
        (Nat.le_max_left
          (max divisibilityThreshold (genericAdmissibilityCutoff a))
          (max countThreshold 5)).trans hpLarge
  have hpGeneric : genericAdmissibilityCutoff a ≤ p :=
    (Nat.le_max_right divisibilityThreshold
      (genericAdmissibilityCutoff a)).trans <|
        (Nat.le_max_left
          (max divisibilityThreshold (genericAdmissibilityCutoff a))
          (max countThreshold 5)).trans hpLarge
  have hpCount : countThreshold ≤ p :=
    (Nat.le_max_left countThreshold 5).trans <|
      (Nat.le_max_right
        (max divisibilityThreshold (genericAdmissibilityCutoff a))
        (max countThreshold 5)).trans hpLarge
  have hpFive : 5 ≤ p :=
    (Nat.le_max_right countThreshold 5).trans <|
      (Nat.le_max_right
        (max divisibilityThreshold (genericAdmissibilityCutoff a))
        (max countThreshold 5)).trans hpLarge
  have hpTwo : p ≠ 2 := by omega
  have hgeneric : GenericAdmissible (modCoefficients a p) :=
    ha.genericAdmissibleAt_of_cutoff_le hpGeneric
  let startupBound : ℕ :=
    Nat.ceil ((p : ℝ) ^ startupExponent)
  have hsmallCentered :
      (pointsWithSmallFirstTwoRotationLinearOrders
          p (modCoefficients a p) startupBound).card + 6 < p := by
    calc
      (pointsWithSmallFirstTwoRotationLinearOrders
          p (modCoefficients a p) startupBound).card + 6 ≤
          2 * (2 + 2 * (2 * startupBound) ^ 2) ^ 2 + 6 := by
        gcongr
        exact pointsWithSmallFirstTwoRotationLinearOrders_card_le
          p hpTwo (modCoefficients a p) hgeneric.1 startupBound
      _ < p := by
        simpa [startupBound] using hcount p hpCount
  have hdiv :
      p ∣ (puncturedRotationOrbit x).ncard :=
    hdivisibility p hp hpDivisibility x
  simpa [startupBound] using
    (exists_mem_rotationOrbit_outside_firstTwoCentered_with_large_order_of_dvd
      p (modCoefficients a p) startupBound hgeneric.1
        x hdiv hsmallCentered)

/-- Conditional startup-to-regular-state route.  The two numerical margins
are kept separate: a nonparabolic cycle is counted by its actual linear
order, while a signed parabolic cycle is counted by its exact point period
`p`. -/
theorem exists_sameRotationComponent_alternatingRegularState_of_startup
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)]
    (hpTwo : p ≠ 2)
    (a : Coefficients (ZMod p))
    (hmultiplier : a.multiplier ≠ 0)
    (hA1 : a.a1 ^ 2 ≠ 4) (hA2 : a.a2 ^ 2 ≠ 4)
    (hA3 : a.a3 ^ 2 ≠ 4)
    (x : PuncturedSolutionSurface a)
    (startupBound bound : ℕ)
    (hdiv : p ∣ (puncturedRotationOrbit x).ncard)
    (hsmallCentered :
      (pointsWithSmallFirstTwoRotationLinearOrders
          p a startupBound).card + 6 < p)
    (hlargeSemisimple :
      20 + 2 * (2 + 2 * (2 * bound) ^ 2) < startupBound)
    (hlargeParabolic :
      20 + 2 * (2 + 2 * (2 * bound) ^ 2) < p) :
    ∃ state : AlternatingRegularState a,
      SameRotationComponent x.1 state.point ∧
        bound ≤ alternatingActualOrder state := by
  obtain ⟨y, hyOrbit, hyNotCentered, hyOrder⟩ :=
    exists_mem_rotationOrbit_outside_firstTwoCentered_with_large_order_of_dvd
      p a startupBound hmultiplier x hdiv hsmallCentered
  have hxy : SameRotationComponent x.1 y.1 :=
    (mem_puncturedRotationOrbit_iff_sameRotationComponent x y).mp hyOrbit
  rcases hyOrder with hyFirst | hySecond
  · by_cases hparabolic : coordinateTrace1 a y.1.1 ^ 2 = 4
    · obtain ⟨state, _hdirection, hystate, hstateOrder⟩ :=
        exists_sameRotationComponent_secondFirst_regularState_of_parabolic_axisOne
          p hpTwo a hmultiplier hA1 hA2 hA3 y bound
            hparabolic hlargeParabolic
      exact ⟨state, sameRotationComponent_trans hxy hystate, hstateOrder⟩
    · have hD : discriminant (coordinateTrace1 a y.1.1) ≠ 0 := by
        simpa [discriminant] using sub_ne_zero.mpr hparabolic
      have hnoncentered :
          centerCoordinates
              (fiberCenter a.a2 a.a3 y.1.1.x1
                (coordinateTrace1 a y.1.1))
              (movingCoordinates1 y.1.1) ≠ (0, 0) := by
        intro hcentered
        apply hyNotCentered
        rw [firstTwoAxesNonparabolicRotationFixedLocus,
          Finset.mem_union]
        left
        apply (mem_axisOneNonparabolicRotationFixedLocus
          p a y.1.1).mpr
        refine ⟨y.1.2, ?_, ?_⟩
        · simpa [coordinateTrace1, orderedTrace] using hD
        · exact rotation1_fixed_of_nonparabolic_centered
            a y.1.1 hD hcentered
      obtain ⟨state, _hdirection, hystate, hstateOrder⟩ :=
        exists_sameRotationComponent_secondFirst_regularState_of_large_axisOne_cycle
          p hpTwo a hmultiplier hA2 hA1 y.1 bound
            hD hnoncentered (hlargeSemisimple.trans_le hyFirst)
      exact ⟨state, sameRotationComponent_trans hxy hystate, hstateOrder⟩
  · by_cases hparabolic : coordinateTrace2 a y.1.1 ^ 2 = 4
    · obtain ⟨state, _hdirection, hystate, hstateOrder⟩ :=
        exists_sameRotationComponent_firstSecond_regularState_of_parabolic_axisTwo
          p hpTwo a hmultiplier hA1 hA2 y bound
            hparabolic hlargeParabolic
      exact ⟨state, sameRotationComponent_trans hxy hystate, hstateOrder⟩
    · have hD : discriminant (coordinateTrace2 a y.1.1) ≠ 0 := by
        simpa [discriminant] using sub_ne_zero.mpr hparabolic
      have hnoncentered :
          centerCoordinates
              (fiberCenter a.a3 a.a1 y.1.1.x2
                (coordinateTrace2 a y.1.1))
              (movingCoordinates2 y.1.1) ≠ (0, 0) := by
        intro hcentered
        apply hyNotCentered
        rw [firstTwoAxesNonparabolicRotationFixedLocus,
          Finset.mem_union]
        right
        apply (mem_axisTwoNonparabolicRotationFixedLocus
          p a y.1.1).mpr
        refine ⟨y.1.2, ?_, ?_⟩
        · simpa [coordinateTrace2, orderedTrace] using hD
        · exact rotation2_fixed_of_nonparabolic_centered
            a y.1.1 hD hcentered
      obtain ⟨state, _hdirection, hystate, hstateOrder⟩ :=
        exists_sameRotationComponent_firstSecond_regularState_of_large_axisTwo_cycle
          p hpTwo a hmultiplier hA1 hA2 y.1 bound
            hD hnoncentered (hlargeSemisimple.trans_le hySecond)
      exact ⟨state, sameRotationComponent_trans hxy hystate, hstateOrder⟩

/-- Eventual fixed-integral-coefficient startup endpoint.  Divisibility,
generic admissibility, the quartic small-order count, and the additive
six-point centered error are discharged uniformly.  Only the two explicit
cycle-routing inequalities remain for the caller's prescribed lower order
`bound`. -/
theorem
    IntegrallyNondegenerate.exists_threshold_every_rotationOrbit_has_alternatingRegularState
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a) :
    ∃ threshold : ℕ,
      ∀ (p : ℕ) (hp : p.Prime), threshold ≤ p →
        letI : Fact p.Prime := ⟨hp⟩
        ∀ (x : PuncturedSolutionSurface (modCoefficients a p))
          (bound : ℕ),
          20 + 2 * (2 + 2 * (2 * bound) ^ 2) <
              Nat.ceil ((p : ℝ) ^ startupExponent) →
            20 + 2 * (2 + 2 * (2 * bound) ^ 2) < p →
              ∃ state : AlternatingRegularState (modCoefficients a p),
                SameRotationComponent x.1 state.point ∧
                  bound ≤ alternatingActualOrder state := by
  obtain ⟨divisibilityThreshold, hdivisibility⟩ :=
    ha.eventually_rotationOrbitDivisibility
  obtain ⟨countThreshold, hcount⟩ :=
    exists_threshold_startupSmallOrderCountBound_add_six_lt_prime
  refine
    ⟨max (max divisibilityThreshold (genericAdmissibilityCutoff a))
        (max countThreshold 5), ?_⟩
  intro p hp hpLarge x bound hlargeSemisimple hlargeParabolic
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (quadraticFiniteField p) := Fintype.ofFinite _
  have hpDivisibility : divisibilityThreshold ≤ p :=
    (Nat.le_max_left divisibilityThreshold
      (genericAdmissibilityCutoff a)).trans <|
        (Nat.le_max_left
          (max divisibilityThreshold (genericAdmissibilityCutoff a))
          (max countThreshold 5)).trans hpLarge
  have hpGeneric : genericAdmissibilityCutoff a ≤ p :=
    (Nat.le_max_right divisibilityThreshold
      (genericAdmissibilityCutoff a)).trans <|
        (Nat.le_max_left
          (max divisibilityThreshold (genericAdmissibilityCutoff a))
          (max countThreshold 5)).trans hpLarge
  have hpCount : countThreshold ≤ p :=
    (Nat.le_max_left countThreshold 5).trans <|
      (Nat.le_max_right
        (max divisibilityThreshold (genericAdmissibilityCutoff a))
        (max countThreshold 5)).trans hpLarge
  have hpFive : 5 ≤ p :=
    (Nat.le_max_right countThreshold 5).trans <|
      (Nat.le_max_right
        (max divisibilityThreshold (genericAdmissibilityCutoff a))
        (max countThreshold 5)).trans hpLarge
  have hpTwo : p ≠ 2 := by omega
  have hgeneric : GenericAdmissible (modCoefficients a p) :=
    ha.genericAdmissibleAt_of_cutoff_le hpGeneric
  let startupBound : ℕ :=
    Nat.ceil ((p : ℝ) ^ startupExponent)
  have hsmallCentered :
      (pointsWithSmallFirstTwoRotationLinearOrders
          p (modCoefficients a p) startupBound).card + 6 < p := by
    calc
      (pointsWithSmallFirstTwoRotationLinearOrders
          p (modCoefficients a p) startupBound).card + 6 ≤
          2 * (2 + 2 * (2 * startupBound) ^ 2) ^ 2 + 6 := by
        gcongr
        exact pointsWithSmallFirstTwoRotationLinearOrders_card_le
          p hpTwo (modCoefficients a p) hgeneric.1 startupBound
      _ < p := by
        simpa [startupBound] using hcount p hpCount
  have hdiv :
      p ∣ (puncturedRotationOrbit x).ncard :=
    hdivisibility p hp hpDivisibility x
  apply exists_sameRotationComponent_alternatingRegularState_of_startup
    p hpTwo (modCoefficients a p) hgeneric.1
      hgeneric.2.1 hgeneric.2.2.1 hgeneric.2.2.2
      x startupBound bound hdiv hsmallCentered
  · simpa [startupBound] using hlargeSemisimple
  · exact hlargeParabolic

/-- Pointwise startup route with every threshold exposed.  The analytic
cutoff controls the counting term, while `genericAdmissibilityCutoff a`
controls both good reduction and generalized Martin divisibility. -/
theorem
    IntegrallyNondegenerate.every_rotationOrbit_has_alternatingRegularState_of_explicitCutoffs
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a)
    (p : ℕ) (hp : p.Prime)
    (hpAnalytic : analyticCutoff ≤ p)
    (hpGeneric : genericAdmissibilityCutoff a ≤ p)
    (x : PuncturedSolutionSurface (modCoefficients a p))
    (bound : ℕ)
    (hlargeSemisimple :
      20 + 2 * (2 + 2 * (2 * bound) ^ 2) <
        Nat.ceil ((p : ℝ) ^ startupExponent))
    (hlargeParabolic :
      20 + 2 * (2 + 2 * (2 * bound) ^ 2) < p) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ state : AlternatingRegularState (modCoefficients a p),
      SameRotationComponent x.1 state.point ∧
        bound ≤ alternatingActualOrder state := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (quadraticFiniteField p) := Fintype.ofFinite _
  have hpFive : 5 ≤ p :=
    (five_le_analyticCutoff.trans hpAnalytic)
  have hpTwo : p ≠ 2 := by omega
  have hgeneric : GenericAdmissible (modCoefficients a p) :=
    ha.genericAdmissibleAt_of_cutoff_le hpGeneric
  let startupBound : ℕ :=
    Nat.ceil ((p : ℝ) ^ startupExponent)
  have hsmallCentered :
      (pointsWithSmallFirstTwoRotationLinearOrders
          p (modCoefficients a p) startupBound).card + 6 < p := by
    calc
      (pointsWithSmallFirstTwoRotationLinearOrders
          p (modCoefficients a p) startupBound).card + 6 ≤
          2 * (2 + 2 * (2 * startupBound) ^ 2) ^ 2 + 6 := by
        gcongr
        exact pointsWithSmallFirstTwoRotationLinearOrders_card_le
          p hpTwo (modCoefficients a p) hgeneric.1 startupBound
      _ < p := by
        simpa [startupBound] using
          startupSmallOrderCountBound_add_six_lt_prime_of_analyticCutoff
            hpAnalytic
  have hVieta : VietaOrbitDivisibilityAt a p hp := by
    apply generalizedMartinGenericDivisibility
    · exact hpFive
    · exact hgeneric
  have hRotation :
      RotationOrbitDivisibilityAt a p hp :=
    rotationOrbitDivisibility_of_vietaOrbitDivisibility
      p hp hpFive (modCoefficients a p) hVieta
  exact
    exists_sameRotationComponent_alternatingRegularState_of_startup
      p hpTwo (modCoefficients a p) hgeneric.1
        hgeneric.2.1 hgeneric.2.2.1 hgeneric.2.2.2
        x startupBound bound (hRotation x) hsmallCentered
        (by simpa [startupBound] using hlargeSemisimple)
        hlargeParabolic

end

end GenMarkoff.General.Assembly
