# C1092 and the shared right-pair families: mathematical handoff

Frozen for the requested progress push and handoff, 11 October2026.
This worker ran no Lean compiler, numerical search, solver, generator or
network operation during the investigation below. All new source mentioned
here remains source-only unless the parent supplies a later replay receipt.

## Original C1092 obligation

The unchanged entrance is a `S12.NormalizedPacking p` with

```lean
codedMarkerFamily p =
  {3,12,48,192,256,512,1024,2048,4096,8192,16384,32768}
```

All twelve actual congruent squares have common side `1<a≤1001/1000`, lie
in `[0,4]²`, and have pairwise disjoint open interiors. The ordered owners
in `Compact/Bridge/C1092WallCycle.lean` are:

| Indices | Actual marker masks | Meaning |
|---|---|---|
|0,1,2,3|3,12,48,192|SW,SE,NE,NW corner pairs|
|4,5,6,7|256,512,1024,2048|SW,SE,NE,NW central singletons|
|8,9,10,11|4096,8192,16384,32768|left,bottom,right,top wall singletons|

`owners` uses actual `ownerIndex`, and `owners_disjoint` proves that
different displayed names are different physical packing squares. It is
not legitimate to replace an owner by an arbitrary square carrying only
some of its positive points.

## Existing exact reduction to four sectors

`Compact/Bridge/C1092WallSymmetry.lean` proves genuine whole-packing D4
transport, including the physical squares, original markers, central and
corner names, wall center cuts, and all48 forced wall points. Its Boolean
classification concerns only16 center-sign patterns, not an angle grid.

A true bit means the tangent center coordinate is at most2; false means
it is at least2. The bit order is left,bottom,right,top, with corresponding
original center coordinates y,x,y,x. Equality is retained in either
closed branch. The four canonical branches are:

| Field | Branch bits | Index |
|---|---|---|
|`windmill`|`[true,false,false,true]`|0|
|`oneExceptional`|`[true,true,true,false]`|1|
|`adjacentPair`|`[true,false,true,false]`|2|
|`oppositePair`|`[true,true,false,false]`|3|

Each field of `C1092WallSymmetry.FourBranchEndings` has the exact type

```lean
∀ p : NormalizedPacking,
  codedMarkerFamily p = C1092WallCycle.family →
  C1092WallCycle.WallContext p (canonicalBranch k) → False
```

All four fields are still genuine mathematical gaps. Supplying them gives
`excludes_original`. `Compact/Cases/C1092Compact.lean` identifies original
retained row576 with case1092 and exposes `excludes_case (work : Pending)`.
That conditional theorem is not an unconditional exclusion.

## What the wall context really provides

For the left lower branch the wall square strictly contains twelve points
`(targetX i,targetY i)` from `C1092WallPolynomial`; `x` ranges from`.914`
to1 and the two ordinates at x=1 are1.606 and1.894. The upper branch is the
reflection `y↦4-y`. Other walls use the explicitly proved `pointMap`.

`C1092WallCycle.local_wall_segment` supplies the entire strict segment
at local x=1 with `1.606≤y≤1.894`, including both endpoints, or its actual
reflection. All central owners avoid every point of these wall segments.
For the finite target list the stronger closed-membership exclusion is
also supplied: a point strictly inside a foreign wall cannot belong to a
central square's closure.

The actual corner pairs strictly contain(1,1),(3,1),(3,3),(1,3).
`CornerInwardPoint` additionally derives the corresponding closed points
at distance a from both neighboring container walls, using full corner
containment and both original markers. Its use must preserve that physical
corner; a single fixed corner point is weaker.

The uniform wall calculation is in:

- `Compact/Geometry/C1092WallPolynomial.lean`: complete real-parameter
  support calculation for all12 target systems, without angle subdivisions.
- `Compact/Geometry/C1092WallCenterRegion.lean` and
  `C1092WallCenterCover.lean`: original geometric entrances, including the
  center-X≥1 branch that cannot be dropped.
- `Compact/Geometry/C1092WallPhysical.lean`: the arbitrary-orientation
  physical theorem `original_wall_point`, then
  `singleton_wall_point_cover` with both closed center-sign branches.

## Existing geometric obstruction, and its scope

`Compact/Geometry/ReentrantCorridor.lean` proves that an open square in the
first quadrant cannot fit in the union of two strips both narrower than
its side. It constructs a closed point northeast of(side,side), then an
interior point beyond the narrower strip widths.

`C1092WindmillGap.no_wall` applies that continuous result to four prescribed
axis-parallel blockers. It excludes every orientation and translation of
the missing wall square for those blockers. Those blocker positions have
not been derived from arbitrary original C1092 squares.

The exact eight-square windmill model in
`C1092WallRelaxation.lean` and `audit/C1092-WALL-CYCLE.md` retains the four
central squares, all four physical corner squares, all original marker
codes, and avoidance of all48 selected wall targets. It omits the four
physical wall squares. It demonstrates why a point-only relaxation is
insufficient for the windmill sector, not a counterexample to C1092.

`audit/C1092-WINDMILL-AXIS-CENTRALS.md` gives a continuous support argument
for the additional sector where all four central squares and the SW
corner square are axis parallel. Those five angle assumptions are not
original hypotheses and have not been established for the whole sector.

## Current opposite-pair investigation

The newly assigned target was `BranchEnding 3`. Here both occupied wall
segments next to SW point toward SW:

```
x=1, 1.606≤y≤1.894;  y=1, 1.606≤x≤1.894.
```

NE has their half-turn images. All four wall squares remain actual
physical squares with the stated center cuts. This pattern may admit a
shorter coupled central-square argument than the windmill, but no such
whole argument has been completed.

An individual SW-center theorem from these point barriers is false, even
when exact original marker exclusions are retained. A manually checked
rational one-square relaxation is:

```
a=1001/1000, c=4/5, s=3/5,
loU=1799/1000, loV=-163/1000.
```

Its upper U face is14/5, exactly the projection of(2,2), so its open
interior misses the center. It strictly owns only original marker8,
the southwest central marker. It is contained in the container; its
coordinate extrema are `.9364,2.3378` in x and `.949,2.3504` in y.
All lower left-wall targets miss below U, all upper left-wall targets
miss above V, and every bottom-wall target misses below V. Right/top
targets miss above U. The four corner points are outside too. This is a
single-square relaxation, not a countermodel to a sector containing the
other eleven squares. No automated verification was run for this new
example; the displayed band comparisons were checked by hand.

Therefore do not assert either central square owns(2,2) from finite wall
targets alone. The actual adjacent wall's support and center-sign cut, or
the other central/corner squares, must participate in the proof.

One unfinished analytic route is to first force the inward elbow points
`(2,1.74),(1.74,2)` of the SW owner. There is a useful hand-derived face
elimination, but not a complete lemma yet. Choose a positive canonical
central frame `c≥s≥0`, let M=(1.65,1.65), D=(2,1.74), and suppose D is
excluded below V. Then `loV≥1.74c−2s`. The foreign NW marker forces
`hiU≤1.65c+2.35s`: its V displacement from D is`.61c+.35s<1`, so it cannot
escape above V, while M gives its other lower bands. The genuine left-wall
point P=(1,1.606) is then strictly inside the central square:

- Its lower U gap is at least `a−.65c−.744s>0`, since
  `.65²+.744²=.976036<1`.
- Its upper U follows from M.
- D below V and strict M imply `.35s>.09c`, hence
  `V(P)−V(M)=.65s−.044c>0`.
- Its upper V gap follows from `V(P)−V(D)=s−.134c<1<a`.

This eliminates one outside face of D. Its upper-U/upper-V faces and the
corresponding sign/transpose transport still need proof before an inward
elbow theorem can be claimed. Even that theorem must then be composed
with actual walls to close the entire opposite-pair sector. Investigation
was frozen here for the user-requested push and handoff.

## Practical next work

1. Start from the exact `BranchEnding 3` interface, not historical pinwheel
   angle bounds or ownership assignments.
2. Retain the physical bottom/left wall squares and their center cuts while
   completing the central face argument. The one-square example above is
   a useful immediate check against over-strong point-only claims.
3. If inward elbows are obtained, check existing all-angle wall/central
   support lemmas against the actual segment height2.394, rather than
   silently replacing it by2.4. The difference matters at strict bounds.
4. Exhaust both squares' separating axes and both directions. A selected
   axis is a conclusion to prove, not a new original hypothesis.
5. Only register a field when the whole original-packing branch is closed.
   All current C1092 endings remain open and require the deferred Lean
   replay once source is assembled.

## Shared cases48,573,574 checkpoint

`Compact/Bridge/C48RightBarOwnership.lean` is new source from this worker.
It derives18 common original auxiliary points for all three families from
the real F3/G2 budgets and checked specifications. C574 retains F cardinality
one or two and uses genuine wall-pair seed segments for its merged bottom
owner8196; it does not misuse the F-upper-one specification70.

The parent-run exact diagnostic `evidence/right-bar-broad-domains.json`
has8/8/10 assignments and39/41/49 search nodes, respectively. Ordinary
finite Lean checks in the new entrance are uncompiled. The whole continuous
ending remains open; see `audit/C48-C573-C574-SYMBOLIC.md`.

Two invalid reuse routes are explicitly excluded: C84's reflected ending
needs a bottom marker absent from the SW owner256, and the four-square
template's A-missing-SE premise is false for the merged right owner1536.
No source uses either shortcut. An optional NW-F5 branch matches the
ordinary-right-wall outer-top elbow geometry currently being investigated
for C981 rows34/41; that route was not yet a whole theorem at this freeze.
