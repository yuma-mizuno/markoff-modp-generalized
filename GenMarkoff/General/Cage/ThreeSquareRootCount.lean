import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Counting three simultaneous square roots

The connecting-cage argument asks for a parameter at which three radicands
simultaneously have square roots.  Instead of introducing an auxiliary
degree-eight primitive-element equation, one can expand the three root
counts using the quadratic character.  The result involves only the seven
nonempty products of the three radicands.

The identities in this file include vanishing radicands.  This is important:
the number of square roots of zero is one, and the quadratic character is
zero there.
-/

namespace GenMarkoff.General.Cage

open Finset

/-- The integer-valued number of square roots of a scalar in a finite
field. -/
def squareRootCount
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (a : F) : ℤ :=
  #{x : F | x ^ 2 = a}.toFinset

/-- Over a finite field of odd characteristic, the square-root count is one
plus the quadratic character. -/
theorem squareRootCount_eq_quadraticChar_add_one
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (a : F) :
    squareRootCount a = quadraticChar F a + 1 :=
  quadraticChar_card_sqrts hF a

/-- Pointwise two-square-root identity.  As in the three-root identity
below, vanishing radicands are included exactly. -/
theorem two_squareRootCount_identity
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (a b : F) :
    squareRootCount a * squareRootCount b =
      squareRootCount a + squareRootCount b +
        squareRootCount (a * b) - 2 := by
  simp only [squareRootCount_eq_quadraticChar_add_one hF, map_mul]
  ring

/-- Pointwise three-square-root identity.  No nonvanishing hypothesis on
`a`, `b`, or `c` is needed. -/
theorem three_squareRootCount_identity
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (a b c : F) :
    squareRootCount a * squareRootCount b * squareRootCount c =
      squareRootCount a + squareRootCount b + squareRootCount c +
        squareRootCount (a * b) + squareRootCount (a * c) +
        squareRootCount (b * c) + squareRootCount (a * b * c) - 6 := by
  simp only [squareRootCount_eq_quadraticChar_add_one hF, map_mul]
  ring

/-- The total number of square roots over the values of a function, counted
as an integer.  For a polynomial radicand, this is the affine point count of
the corresponding hyperelliptic plane model. -/
def squareRootCoverPointCount
    {ι F : Type*} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
    (f : ι → F) : ℤ :=
  ∑ x, squareRootCount (f x)

/-- The total number of pairs of square roots over a common parameter. -/
def twoSquareRootFiberProductPointCount
    {ι F : Type*} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
    (f g : ι → F) : ℤ :=
  ∑ x, squareRootCount (f x) * squareRootCount (g x)

/-- Global two-square-root identity.  It expresses the fiber-product count
through the three nonempty products of the two radicands. -/
theorem twoSquareRootFiberProductPointCount_eq_three_covers
    {ι F : Type*} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (f g : ι → F) :
    twoSquareRootFiberProductPointCount f g =
      squareRootCoverPointCount f +
        squareRootCoverPointCount g +
        squareRootCoverPointCount (fun x => f x * g x) -
        2 * Fintype.card ι := by
  classical
  simp only [twoSquareRootFiberProductPointCount,
    squareRootCoverPointCount]
  simp_rw [two_squareRootCount_identity hF]
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_univ,
    nsmul_eq_mul]
  ring

/-- The total number of triples of square roots over a common parameter,
counted as an integer. -/
def threeSquareRootFiberProductPointCount
    {ι F : Type*} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
    (f g h : ι → F) : ℤ :=
  ∑ x, squareRootCount (f x) * squareRootCount (g x) *
    squareRootCount (h x)

/-- Global three-square-root identity.  It rewrites a three-cover fiber
product count as the sum of the seven ordinary double-cover counts, with the
constant correction `6 * |ι|`. -/
theorem threeSquareRootFiberProductPointCount_eq_seven_covers
    {ι F : Type*} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (f g h : ι → F) :
    threeSquareRootFiberProductPointCount f g h =
      squareRootCoverPointCount f +
        squareRootCoverPointCount g +
        squareRootCoverPointCount h +
        squareRootCoverPointCount (fun x => f x * g x) +
        squareRootCoverPointCount (fun x => f x * h x) +
        squareRootCoverPointCount (fun x => g x * h x) +
        squareRootCoverPointCount (fun x => f x * g x * h x) -
        6 * Fintype.card ι := by
  classical
  simp only [threeSquareRootFiberProductPointCount,
    squareRootCoverPointCount]
  simp_rw [three_squareRootCount_identity hF]
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_univ,
    nsmul_eq_mul]
  ring

end GenMarkoff.General.Cage
