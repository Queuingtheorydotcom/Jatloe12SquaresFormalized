# C981: reusable consequences and the remaining joint interaction

Source and mathematical review, 10 October 2026. No Lean invocation,
numerical search, certificate generation, or archive extraction was run.
The consequences below are hand deductions from the existing checked
geometry interfaces; their C981 bindings have not been separately replayed.
No additional complete representative is claimed.

## An actual entrance consequence survives the missing-barrier problem

Use the original owner order in `Completion/Cases/C981/Ownership.lean:8`.
For any actual C981 vector with auxiliary bits 5 and 13 in owner 7, and
bit 11 in owner 8, the already checked `FourSquareAAll.point` implies

```
owner 7 contains (2, 5/2) and (2, 12/5).
```

Apply horizontal reflection to A=owner7, B=owner6, R=owner8. Their marker
points supply A=(1.65,2.35), B=(2.35,2.35), R=(.914,2) in the original
frame. The auxiliary points supply A=(2,2.26),(1.74,2) and R=(1,2.4).
The low point (.76,1.87) is strictly owned by the **actual singleton
owner1, mask2**, so it is outside R by packing disjointness. A's two
missing marker points follow from ExactMarkers. Thus every premise of
`Compact/Geometry/FourSquareAAll.lean:12` is available. Reflection fixes
the resulting x=2 points. `FourSquareAForced.row_point` supplies the second
point by interpolation.

This applies, for example, to the still-open V0 and V2 entrances, not merely
to already closed vectors. Their literals are `VectorData.lean:13,15`.
The implication is expressed by the three ownership-bit conditions above;
no new exhaustive applicability count was computed.

For V2, owner10 also owns (3,2.4). Therefore owners8,7,10 occupy all three
grid slots on y=2.4. `FourSquareBCorner.no_long_section` immediately proves
that owner6 has **no** long section on this row. This removes the radius-safe
branch using original premises, without an incoming pose cover. Its signed
corner branches still require a contradiction; no long-section premise
for owner6 has been manufactured.

## A second all-orientation consequence uses two symmetric cuts

A generic consequence of `FourSquareAForced.positive_shallow_point` and
`axis_point` is the following. A square of side greater than one containing
the closed triangle

```
(2,2.26), (2.26,2), (2.35,2.35)
```

and excluding the five points

```
(1.65,1.65), (2.35,1.65), (1.65,2.35), (3,2.4), (2.4,3)
```

contains (2,2.5) **or** (2.5,2). Choose a nonnegative frame. If s<=c,
use the shallow theorem, handling s=0 with `axis_point`. Otherwise swap
coordinates and use it there. The compulsory triangle and missing-point
set are invariant under that swap. This covers equality and both axes.
It needs no wall, upper side cap, or foreign square.

In horizontally reflected V2, owner5 is the lower central square C,
with compulsory triangle (2,1.74),(1.74,2),(1.65,1.65). Its exact marker
and auxiliary exclusions provide all five rotated missing points. A
180-degree rotation of the consequence gives

```
C contains (2,1.5) or (1.5,2),
and hence C contains (2,1.6) or (1.6,2).
```

These are two genuine geometric branches, not a case split on numerical
angle cells. They may replace a propagation prefix. Neither branch has
yet been proved to contradict the rest of the packing.

The subsequently supplied `WallLowerBarrier` / `FourSquareHighRight`
variant improves V0: its reflected owner10 owns the lower points
(1,1.74),(1,1.6), rather than V2's upper points, and excludes (1,2.26).
After a 180-degree rotation these provide the alternative R barrier
(3,1.74). Consequently the improved AAll route can select the vertical
conclusion for C: (2,1.5), hence (2,1.6). In V0 the three bottom-row slots
(1,1.6),(2,1.6),(3,1.6) are then occupied, as well as two slots on the upper
row. A fourth long section on the lower row, or seven squares meeting these
two cuts in long sections, has not been derived. This does not close V0.

## Exact obstruction to a tempting two-square completion

The missing low barrier for the reflected left-wall square L cannot be
recovered merely by adding C and its **exact local ownership exclusions**.
Nor do those data force L to contain one of the negative-B endgame points
M=(1.3,2.4), N=(1,2.68).

Here is an exact two-square witness in that reflected frame. All displayed
terminating decimals denote exact rationals. Both squares have side 1.001
and normal (c,s)=(.8,.6). Write U=.8x+.6y, V=-.6x+.8y.

| Square | Open U interval | Open V interval |
|---|---|---|
| L | (1.39806,2.39906) | (.86308,1.86408) |
| C | (1.845,2.846) | (-.141,.86) |

They have disjoint interiors because C's upper V face .86 is strictly below
L's lower V face .86308. Both are inside [0,4]^2: their coordinate ranges
are respectively [0,1.4014] x [1.5293,2.9307] and
[.96,2.3614] x [.9942,2.3956].

Substitution in the original marker and auxiliary tables gives exactly the
reflected V2 local sets: L owns only its wall marker (.914,2) and auxiliary
points (1,2.26),(1,2.4); C owns only its central marker (1.65,1.65) and
auxiliary points (2,1.74),(1.74,2). For the auxiliary index convention, these
are the horizontal reflections of owner10's {9,19} and owner5's {4,16}.
Both masks are single central/wall markers, so their seed queries add no
corner-singleton or two-marker wall extras.

Nevertheless L contains W=(.76,1.87), since (U(W),V(W))=(1.73,1.04).
It excludes M and N because U(M)=2.48 and U(N)=2.408, both exceeding
2.39906. Thus even the weaker conclusion `L.Inside M or L.Inside N` is
false for this complete two-owner local input. The witness is not a
twelve-square packing and does not refute C981.

L also excludes the alternative barrier W'=(1,1.74), since V(W')=.792,
and excludes D=(1.74,2), since U(D)=2.592. It does contain the newly forced
(1,2.5), with U=2.3 and V=1.4. Thus the new wall-point lemma is consistent
with this witness, while substituting W' for W in the stronger B/L endgame
would leave the same obstruction. The kernel worker confirmed that its
new complete-template variant changes only R's barrier and retains L's
original missing W premise.

## The precise outstanding mathematics

V2 now has an original-entrance route to A's two forced points, a failed
B section, B's signed corner alternatives, and C's two-point alternative.
The unproved step is a **joint** interaction involving B with C and L
(possibly also A's full shape or the adjacent corner/bottom owners).
It cannot be replaced by a theorem about C and L alone with the same local
ownership data, as the witness above demonstrates. The existing four-square
terminal needs L's missing W, which the original C981 entrance does not give.

SectionCapacity is useful after a fourth long section or extra occupied
slot is proved; the current original points do not supply one. WallChain
still requires a common height band and appropriate directed separating
axes. ThreeSquareOriginal still requires its two follower sections and
small-angle/center hypotheses. Those are mathematical implications to
prove from these entrances, not missing literal certificate fields.

For the archived 55 open contexts, the residual route labels describe how
the proposed traces proceed; they are not 55 instances of any currently
proved common terminal. V75's recorded numerical trace is a separate
mechanical certification task. Neither that recorded trace nor the two
new consequences above establishes a source-size bound for all55 contexts.
