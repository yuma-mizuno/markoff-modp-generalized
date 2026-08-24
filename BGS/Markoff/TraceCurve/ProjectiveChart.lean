/-!
# Standard charts of the biprojective trace curve
-/

namespace BGS.Markoff

/-- The four standard affine charts of the biprojective trace curve. -/
inductive WeightedSplitTraceProjectiveChart where
  /-- The original affine chart. -/
  | affine
  /-- The chart obtained by inverting the first projective coordinate. -/
  | invertFirst
  /-- The chart obtained by inverting the second projective coordinate. -/
  | invertSecond
  /-- The chart obtained by inverting both projective coordinates. -/
  | invertBoth
  deriving DecidableEq

/-- Backwards-compatible name used by earlier Blueprint snapshots. -/
abbrev WeightedSplitTraceNormalizationChart := WeightedSplitTraceProjectiveChart

universe u

/-- Universe-lifted chart index used by Mathlib's gluing category. -/
abbrev WeightedSplitTraceProjectiveChartIndex :=
  ULift.{u} WeightedSplitTraceProjectiveChart

end BGS.Markoff
