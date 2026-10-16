# C977: symbolic reduction from sixteen wall branches to four

## Result and validation boundary

New source is in `Compact/Geometry/WallCenterBarrier.lean` and
`Compact/Bridge/C977WallCenters.lean`. It has not yet been replayed by Lean.
The algebra below is a direct symbolic derivation, not a numerical search.

For every original normalized packing of the C977 family, the new adapter
proves the left wall owner's center has y > 2 and the bottom wall owner's
center has x > 2. Consequently the first two wall Booleans are false. This
excludes twelve of the sixteen wall branches uniformly over all 57 actual
ownership vectors, leaving exactly four branches and 228 contexts. It does
not exclude an entire vector or the whole case.

The new `canonical_four_wall_context_cover` preserves the whole packing
(and only its previously proved transpose alternative), strengthened missing
corner, canonical corner bounds, every exact auxiliary ownership set, and
both remaining opposite-wall decisions. The final conditional interface is
`excludes_case_of_four_wall_contexts`; its four-by-57 contradictions remain
unsupplied.

## Actual original-owner premises

The owner order and labels are those proved in C977/AuxiliaryVectors.lean.
The argument does not identify square labels by assumed historical index.

| Owner | Required points | Missing point from exact auxiliary set | Foreign singleton anchor |
|---|---|---|---|
| slot8, code4096 | (.914,2), (1,2.4) | (1.74,2), auxiliary13 | (.76,1.87), owned by slot1/code2 |
| slot9, code8192 | (2,.914), (2.4,1) | (2,1.74), auxiliary4 | (1.87,.76), owned by slot0/code1 |

The first required point is its original marker. The second follows from
`pruned_auxiliary_domain_actual`: slot8 is in `[{1,11},{1,3,11}]`, so owns11
and excludes13; slot9 is in `[{6,15},{6,15,18}]`, so owns6 and excludes4.
The foreign anchors follow from the existing singleton-forcing theorems and
original packing disjointness. Thus there is no dependence on choosing one
of the 57 complete vectors or one of the wall branches.

The bottom conclusion is the coordinate transpose of the left conclusion.
Face reindexing in the geometric lemma preserves both actual center
coordinates, and covers axis directions as well as tilted squares.

## Symbolic center bound

Write a > 1 for the actual side, c,s >= 0 with c²+s²=1 for a positive
face frame, and U,V for the lower face coordinates. Left containment gives

    c U - s(V+a) >= 0.

Let P=(.914,2), Q=(1,2.4) be strictly inside, while W=(.76,1.87) and
D=(1.74,2) are outside. The same face elimination used in WallForcedPoint
leaves these alternatives:

    D: U+a <= 1.74 c+2s, or V >= -1.74s+2c;
    W: U >= .76c+1.87s, or V >= -.76s+1.87c.

The discarded faces are ruled out by strict membership of P and Q, so zero
normal components are retained. If W takes its lower-U alternative, D must
take its lower-V alternative: the other combination would give

    a <= .98c+.13s <= 1,

contradicting a>1. For Y=s(U+a/2)+c(V+a/2), the two lower faces then give

    Y > 2 - .13s² - .98cs + (c+s)/2 > 2.

For the last inequality use c+s >= 1+.8cs, s²<=1, and cs<=1/2. In fact its
margin is at least .08.

If W takes its lower-V alternative, multiply the wall inequality by s and
use the exact identity

    cY = s[cU-s(V+a)] + V + (a/2)(1+s²+cs).

Hence

    c(Y-2) > (1+s²+cs)/2 - .76s - .13c
             = (s-.76)²/2 + .2112 + cs/2 - .13c
             >= .0812 > 0.

Since c>=0, this implies Y>2 even at the possible c=0 endpoint (which would
itself be contradictory). No angle subdivisions, transcendental estimates,
SAT assumptions, or finite pose data enter this deduction.

## Comparison with the new shared template

The exact four-square templates do not immediately eliminate a remaining
C977 vector. For the southwest central owner (code256), the two inward
auxiliary points (2,1.74) and (1.74,2) are forced. Rotating CentralCross by
180 degrees therefore forces either (2,1.5) or (1.5,2), given the already
available foreign points. This is useful propagation, not an exclusion.

The adjacent central owner needed as the B square of the four-square
endgame would also need both wall-row anchors. In C977 those points belong
to the intervening wall owner instead: (2.4,1),(2.26,1) belong to code8192,
and (1,2.4),(1,2.26) belong to code4096. Substituting that wall owner for B
would lose the required central marker. The current template cannot be
applied by relabeling these distinct actual owners.

The existing exact-hull audit found no initial compulsory-hull crossing in
any of the 57 vectors. OwnerSegmentCrossing formalizes such a contradiction
if new propagation supplies one; its availability alone does not establish
an intersection. No new whole-vector exclusion is claimed here.
