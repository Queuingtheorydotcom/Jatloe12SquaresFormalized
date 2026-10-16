# C977: the ending must retain the other central owners

This is a source and mathematical dependency map. It does not claim a
new exclusion or a new Lean replay. The original square model and owner
order are those of `Completion/Cases/C977/AuxiliaryVectors.lean`.

## What the five-square counterexample rules out

The parent's exact rational audit
`evidence/positive-central-five-square-countermodel.json` passed all ten
pair separations, containment, common side, exact original marker and
auxiliary signatures, the original singleton seeds, central crosspoints
and the paired corner point. It includes actual C977 owners

    O=0, L=1, E=4, A=5, W=8.

A misses both `(2,2)` and `(1,2)`. E is the genuine northwest paired
corner, not a substitute point. Therefore adding E to the local O/L/A/W
claim cannot prove either compulsory point. The failure is mathematical,
not a missing certificate or tactic.

The seven absent actual owners are 2, 3, 6, 7, 9, 10 and 11. A valid
ending needs at least some of their complete-square coupling. No single
one has yet been proved unable to extend this witness; that must not be
inferred just because the whole case is the intended target.

## Exact original owner map

All points below are strict owned points. “Either” is the finite-domain
disjunction visible in `pruningDomain4`, not an independent choice of
saved pose. Coordinates are from the original F/G tables.

| Owner | Mask / position | Uniform original points beyond its marker(s) | Remaining ownership information |
|---|---|---|---|
| 0 | 1, bottom singleton O | `(1.12,1)`, `(1.74,1)`, `(1.87,.76)` | Exact auxiliary `{2,12}`; canonical missing corner |
| 1 | 2, left singleton L | `(1,1.12)`, `(1,1.74)`, `(.76,1.87)` | Exact auxiliary `{0,10}`; owns corner in the residual |
| 2 | 12, southeast paired corner | `(3,1)` | Auxiliary empty or `{18}` = `(3,1.6)` |
| 3 | 48, northeast paired corner | `(3,3)` | Auxiliary empty |
| 4 | 192, northwest paired corner E | `(1,3)` | Auxiliary empty or `{3}` = `(1.6,3)` |
| 5 | 256, southwest central A | `(2,1.74)`, `(1.74,2)`; geometric crosspoints `(2,1.5)`, `(1.5,2)` | May additionally own `(2,2.26)` and/or `(2.26,2)` |
| 6 | 512, southeast central B | `(3,1.74)` | Owns at least one of `(2.26,2)` or `(3,1.6)`; may also own `(2,2.26)` |
| 7 | 2048, northwest central C | `(1.74,3)` | Owns at least one of `(1.6,3)` or `(2,2.26)`; may also own `(2.26,2)` |
| 8 | 4096, left wall W | `(1,2.26)`, `(1,2.4)` | May additionally own `(1.6,3)` |
| 9 | 8192, bottom wall D | `(2.4,1)`, `(2.26,1)` | May additionally own `(3,1.6)` |
| 10 | 16384, right wall R | `(3,2.26)`, `(3,2.4)` | May additionally own `(2.26,2)` |
| 11 | 32768, top wall T | `(2.4,3)`, `(2.26,3)` | May additionally own `(2,2.26)` |

The southeast and northwest central markers are `(2.35,1.65)` and
`(1.65,2.35)`. Marker `(2.35,2.35)` is globally unused: every actual square
misses it. This absence is stronger than merely assigning it to a foreign
owner and is already available as `unused_marker_ten`.

## Genuine source reductions already available

* `C977CentralReach.central_points` supplies both A crosspoints from the
  actual bottom/left singleton segments. It applies before any sign split.
* `C977WallCenters` and `C977OppositeWallCenters` keep only the all-upper
  wall branch, with the stronger strict `2.1` center cuts. These are
  individual original-square consequences; they are not a whole ending.
* `C977OppositeWallExtras.simultaneous_extras_impossible` excludes R owning
  `(2.26,2)` simultaneously with T owning `(2,2.26)`. Their actual centers
  would lie in the same `.7` by `.7` square, contradicting separation.
* `C977CentralWingReach.right_wing_point` says B owning `(2,2.26)` forces
  B `(3,1.5)`, hence `(3,1.6)`, using actual A's strict segment.
* `C977CentralWingReach.top_wing_point` says C owning `(2.26,2)` forces
  C `(1.5,3)`, hence `(1.6,3)`, by the corresponding actual-square transform.

The last two implications and the incompatible wall extras reduce the
source cover to 50 vectors in `C977CentralWingReach.remainingVectors`.
That is a coverage theorem only. It has no terminal universal contradiction.

Also, if A owns either optional inner point, convexity immediately gives
the center: use `(2,1.74)` with `(2,2.26)`, or `(1.74,2)` with `(2.26,2)`.
Thus any attempt to study A missing center can safely retain the exact
two-point auxiliary assignment `{4,13}`. This does not force either inner
point to be owned elsewhere; the finite domains must still be respected.

## The missing global interactions

The most useful remaining network has three actual central owners, not
one local corner owner with a proposed compulsory point.

1. **A–C–T:** C owns the northwest central marker and `(1.74,3)`; T owns
   `(2,3.086)`, `(2.26,3)`, `(2.4,3)`. Actual A/C and C/T separation must
   be coupled. The local counterexample omits both C and T, so its free
   vertical space above A cannot be treated as available in the packing.
   E/C, W/C and the actual northeast corner/T constraints must not be
   discarded if an isolated three-square version remains feasible.
2. **A–B–R:** the corresponding rightward path uses B's southeast marker
   and `(3,1.74)`, then R's marker and `(3,2.26)`, `(3,2.4)`. Retain B/D,
   B/southeast-corner and R/northeast-corner separation as needed. This is
   the transpose of the geometric path, not a license to independently
   transpose the already normalized packing.
3. **B–C–R–T:** mutual B/C separation and the two globally missing-marker
   constraints couple the optional inner ownerships. The existing
   incompatible-extra theorem is one complete consequence of this region;
   the converse (“one of the extras must occur”) is not proved and should
   not be inserted as an assumption.
4. **Perimeter closure:** E–C–T–northeast corner and O–D–southeast corner
   connect the two central paths to real container support. This is where
   a shared support-chain inequality could finish a cycle rather than
   demand that one local square contain a false compulsory point.

Priority is a joint implication across these paths, preserving both
candidate SAT axes until a genuine closed cycle eliminates them. The
counterexample has no power to identify a unique next blocking owner.
Claiming, for example, that C alone or the opposite corner alone excludes
it would require a new mathematical argument.

## Why the old chain helper is not an ending yet

`C977DisjointChain.openSquare_chain_cut_of_disjoint` is a valid generic
support telescoping theorem, but requires near-axis frames, a common
height strip of width at most `.43`, directed center gaps and adjacent
actual disjointness. Only the last premise is automatic in a packing.
Current point/center bounds do not provide the first three uniformly over
the 50 vectors. The historical near-axis certificates cannot be assumed
as the original entrance. Reusing the helper is sensible only after a
new joint geometric argument establishes those hypotheses, or after a
more general continuous support-cycle theorem replaces them.

No further local O/L/A/W/E center proof should be pursued. Valid scalar
and face reductions can be reused as constraints inside the larger cycle;
their conclusion must not be strengthened to the refuted local statement.

## New uniform outer-wing reduction (source only)

`Compact/Geometry/CentralOuterWing.lean` now gives the following all-angle
implication, using only side greater than one:

* strict `P=(1.65,2.35)`, `D=(2,2.26)`, `W=(1.74,3)`;
* missing `T=(2.35,2.35)` and the genuinely foreign `Z=(1.5,2)`;
* conclusion: strict `F=(1.6,3)`.

In a nonnegative face frame, F can escape only through lower U or upper V,
while T can escape only through upper U or lower V. The equal-axis
combinations contradict side greater than one, using coefficient vectors
`(.75,-.65)` and `(.65,.75)`. The two lower faces contradict P's U-band
and D's V-band. In the remaining two upper faces, Z must be inside: its U
width is at most `.85c+.35s ≤ 1`, its V width is at most `c-.1s ≤ 1`,
and W supplies the other strict bands. No new angular grid is involved.

`Compact/Bridge/C977OuterWings.lean` binds that lemma to the original
packing and the already sourced southwest crosspoints. The pruned
original domains then force, uniformly,

    18 ∈ owner6's auxiliary set; 3 ∈ owner7's auxiliary set.

The second conclusion follows from the first geometric statement; the
first uses its coordinate transpose. The genuine paired corners and wall
owners consequently cannot own either of these foreign points. The new
`canonical_remaining_cover` filters the prior 50-vector cover by these two
forced memberships without dropping any geometric assumption. It does
not assert a new vector count or a whole exclusion. Both files await the
single whole-source Lean replay.

## Positive-bottom missing-center sector (source only)

`C977PositiveBottomWest.frame_west` now binds a complete continuous
O/L/A argument to the actual packing. If O and A have nonnegative
canonical frames, O misses the southwest corner and A misses the center,
then A strictly owns `(1,2)`. L's canonical sign is selected internally.
The genuine foreign point `(1,1.6)` comes from L's original auxiliary
ownership; the argument does not use the unavailable `(1,2.88)` premise.

For positive L, all four remaining support-selector combinations are
discharged. `PositiveLeftOwnV` handles both outgoing axes after incoming
separation on L's V face. Its central-axis comparison uses
`PositiveCentralCrossMargin`; its own-axis comparison uses actual central
vertices and two exact continuous endpoint bounds in
`PositiveLeftOwnVBounds` and `PositiveLeftOwnVEndpoint`.
`PositiveCentralPositiveLeft` handles the other incoming face.
`PositiveCentralNegativeLeft` handles strictly negative L.

Combining the original west-point adapter with the genuine-marker wall
cycle gives `C977PositiveBottomWest.frame_negative_wall_excludes`: the
whole original O-positive/A-positive/W-negative orientation sector is
excluded, including both signs of L. This is not a whole C977 exclusion.
The new source and its mathematical identities were independently read;
Lean replay remains deferred to the assembled final proof.
