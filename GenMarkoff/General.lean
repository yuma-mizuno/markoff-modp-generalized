import GenMarkoff.General.Assembly.RotationComponent
import GenMarkoff.General.Assembly.RegularMiddleIteration
import GenMarkoff.General.Assembly.RegularMiddleThreshold
import GenMarkoff.General.Assembly.RegularNonsplitEndgame
import GenMarkoff.General.Assembly.RegularSplitEndgame
import GenMarkoff.General.Assembly.DirectedRegularOrderGrowth
import GenMarkoff.General.Assembly.CenteredLocus
import GenMarkoff.General.Assembly.Startup
import GenMarkoff.General.Assembly.StartupRegularRouting
import GenMarkoff.General.Assembly.StartupRegularThreshold
import GenMarkoff.General.Assembly.UnifiedRegularEndgame
import GenMarkoff.General.Assembly.ParityCageBoundary
import GenMarkoff.General.Assembly.ConnectingCageBoundary
import GenMarkoff.General.Assembly.ReductionSurjectivity
import GenMarkoff.General.Assembly.StrongApproximation
import GenMarkoff.General.Assembly.ExplicitStrongApproximation
import GenMarkoff.General.Assembly.VietaParityCollapse
import GenMarkoff.General.Assembly.VietaRotationEquivalence
import GenMarkoff.General.Axis
import GenMarkoff.General.Cage.FirstAxisTorusVieta
import GenMarkoff.General.Cage.FirstAxisTorusVietaParity
import GenMarkoff.General.Cage.ConnectingQuartic
import GenMarkoff.General.Cage.ConnectingFiber
import GenMarkoff.General.Cage.ConnectingAxisDispatch
import GenMarkoff.General.Cage.ConnectingIncidenceAlgebra
import GenMarkoff.General.Cage.ConnectingPulledRadicands
import GenMarkoff.General.Cage.CenteredReducedPulledRadicand
import GenMarkoff.General.Cage.ConnectingPairwiseCoprime
import GenMarkoff.General.Cage.DirectedConnectingFiber
import GenMarkoff.General.Cage.IncidenceAlgebra
import GenMarkoff.General.Cage.PairRelay
import GenMarkoff.General.Cage.ThreeSquareRootCount
import GenMarkoff.General.Cage.ThreeRadicandSquareClasses
import GenMarkoff.General.Cage.ConnectingGeometricSquareClasses
import GenMarkoff.General.Cage.HyperellipticPlane
import GenMarkoff.General.Cage.ConnectingSevenPlaneEstimates
import GenMarkoff.General.Cage.ThreeRootPowerCover
import GenMarkoff.General.Cage.ConnectingThreeRootEstimate
import GenMarkoff.General.Cage.ConnectingGoodPowerCover
import GenMarkoff.General.Cage.OrbitCosetBiquadratic
import GenMarkoff.General.Endgame.ActualSplitRotation
import GenMarkoff.General.Endgame.Nonsplit.ActualRotation
import GenMarkoff.General.Endgame.Nonsplit.RegularPrimitiveCount
import GenMarkoff.General.Endgame.RegularPrimitiveCount
import GenMarkoff.General.FixedPoints
import GenMarkoff.General.MiddleGame.ActualCorvajaZannier
import GenMarkoff.General.MiddleGame.ActualDiagonalization
import GenMarkoff.General.MiddleGame.ActualMoveWiring
import GenMarkoff.General.MiddleGame.ActualOrderEscape
import GenMarkoff.General.MiddleGame.ActualOrderGrowth
import GenMarkoff.General.MiddleGame.CyclicCosetOrder
import GenMarkoff.General.MiddleGame.DirectedOrderGrowth
import GenMarkoff.General.MiddleGame.DirectedStrictOrderGrowth
import GenMarkoff.General.MiddleGame.ParityClosedOrderEscape
import GenMarkoff.General.MiddleGame.RotationEigenvalueOrder
import GenMarkoff.General.MiddleGame.ToricEscape
import GenMarkoff.General.Opening.RotationBridge
import GenMarkoff.General.Parabolic
import GenMarkoff.General.ParabolicRouting
import GenMarkoff.General.ParabolicSurface
import GenMarkoff.General.TraceSurface

/-!
# Fixed general-coefficient strong approximation

This umbrella imports the completed eventual strong-approximation theorem for
every fixed integrally nondegenerate integral coefficient triple.  The proof
first reaches canonical primitive split endpoints by actual rotations, makes
them cage-ready, and then connects them in the full Vieta group.  Square and
nonsquare centered-norm endpoints are handled by separate orbit-preserving
normalization counts before a directed three-root relay joins the resulting
primitive connecting fibers.
The resulting full-Vieta cage is transferred to the rotation group at large
generic primes and then to surjectivity of integral reduction.

The public endpoints are
`eventualVietaStrongApproximationStatement`,
`eventualStrongApproximationStatement`, and
`IntegrallyNondegenerate.eventuallyReductionSurjective`.
The explicit counterparts use
`explicitStrongApproximationCutoff a` and prove fixed-prime Vieta
transitivity, rotation transitivity, and reduction surjectivity whenever
`explicitStrongApproximationCutoff a ≤ p`.
The downstream corollaries
`generalizedGiantOrbitStatement` and
`IntegrallyNondegenerate.eventuallyCanonicalFirstAxisPrimitiveSplitCage`
record, respectively, the formal giant-orbit proposition and the eventual
canonical parity-cage predicate.

The all-zero triple is handled by an explicit bridge to the classical BGS
formalization.  Otherwise a nonzero coefficient is moved to the first
position only by simultaneously cycling coefficients and coordinates; no
coordinate permutation is asserted to preserve a fixed unequal-coefficient
surface.

This eventual fixed-integral theorem remains distinct from the
puncture-corrected all-generic-primes version of the source conjecture and
from the optional direct parity-aware rotation-cage route documented in the
Blueprint.
-/
