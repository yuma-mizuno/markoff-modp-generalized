import Solution

/-!
# Submission axiom audit

The Comparator-facing theorem is the only public result submitted for
comparison. Its proof may use exactly the three axioms permitted by
`comparator.json`.
-/

/--
info: 'Challenge.generalizedMarkoff_reduction_surjective_of_large_prime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.generalizedMarkoff_reduction_surjective_of_large_prime
