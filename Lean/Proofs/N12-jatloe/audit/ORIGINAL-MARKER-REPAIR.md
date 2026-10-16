# Genuine-marker corner cycle and the remaining global problem

11 October 2026. This checkpoint describes mathematical source progress,
not Lean acceptance. Compilation remains deferred until the whole source
is assembled. The original target and packing assumptions are unchanged.

## The correction

The northwest corner in C696 and C977 is a paired owner. It supplies
`(1,3)` and the marker `(.914,3)`, but not the singleton seed `(1,2.88)`.
Earlier cycle and missing-west-point order lemmas using that seed remain
valid conditional statements; they cannot serve as original-case endings.
An axis square `(0,1.001) × (2.999,4)` already refutes the proposed
paired-corner-only seed implication.

The replacement keeps the actual squares O, L and W. Write the positive
bottom frame as `(c,s)`, the negative wall frame as `(d,-t)`, and use the
actual common side `a>1`. The genuine faces are

    O.hiU ≤ 2c + .914s,
    W.hiU ≤ 1.65d − 2.35t,
    W.hiV ≤ .914t + 3d.

The actual missing corner and bottom wall also give

    1 + s/c − 2s − .914s²/c < O.hiV.

The wall faces imply `t<.6` and `d>.8`. These replace the unavailable
sharper top face and its associated tighter angle range.

## Completed continuous support cycle

`Compact.Geometry.CornerWallMarkerCycle.impossible` now covers both
canonical signs of L and every surviving O/L and L/W separating axis.
Its explicit `Data.order` is `s≤t`. It retains actual strict points,
L's strict `(1,1)` corner, complete contained congruent squares, and
their actual pairwise disjointness. This is a sector theorem, not an
unconditional C696 or C977 exclusion.

The main reductions are short algebraic arguments over whole angle arcs:

* Positive L uses shared support bounds and unit-normal dot products for
  the mixed and transverse separators. Both longitudinal separators use
  the two genuine W faces together.
* If negative L separates backward on its own U axis, its actual strict
  corner forces `c<.914` and `r>.6`. Thus a whole smaller-tilt range is
  impossible before further splitting. The two remaining scalar margins
  have positive rational remainders.
* The final negative-L mixed selector is monotone in L's angle. Put
  `Q=l+d`, `R=r+t`, `x=Q-R`. Its finite-difference numerator is bounded
  below by

      H = (Q²−R²)/2 − 3QR/4 + 7R/4 − 13Q/20
        = 7x²/40 + (2−x)/50 + 3(4−Q²−R²)/8
          + (x+11/10)(R−7/5+7x/10).

  All four terms are nonnegative: canonical normals give `0≤x≤2`,
  their dot product gives `Q²+R²≤4`, and each normal obeys `7l+3r≥7`.
  The equal-angle endpoint is the previously proved disk margin plus
  `43t/500`. This uses no angular mesh or numerical optimization.

The scalar and geometric bindings received independent hand reviews.
Every changed Lean source still requires the final compiler replay.

## Original-packing entrances and exact obstructions

For owned `A.Inside 1 2`,
`Compact.Bridge.C977PositiveCornerOrder.frame_angle_order_of_west`
already derives the required strict O/W angle order using genuine
original markers. `Compact.Bridge.C977OwnedWestCorner.frame_excludes`
now binds the complete signed cycle to this original C977 sector. It
chooses L's canonical frame internally and supplies every marker, seed,
side, containment, disjointness and angle-range premise. An independent
source and premise review passed; Lean replay is still pending. This is
one complete original orientation/incidence sector, not the whole case.

For missing `A.Inside 1 2`, the old O/A/W-only order implication cannot
be repaired by merely replacing its top cap. The exact witness in
`evidence/positive-bottom-order-triple-countermodel.json` has all three
actual signatures and pair separations but positive O tilt and zero W
tilt. The actual left square is essential.

`Compact.Geometry.PositiveCentralEscapeLeft` begins that repair. The
original O/A support and northwest cap force `O.c>.9`. The actual L
corner and O's bottom containment then rule out the negative L-U
separator. `Compact.Geometry.PositiveCentralNegativeLeft.west` now
completes that negative-L route: A's actual upper-left vertex is northwest
of L's strict corner, eliminating one L/A axis. The remaining two support
bounds contradict L's container wall on the entire canonical negative arc.
It forces the west point without using W at all.

`Compact.Bridge.C977NegativeLeftWest.frame_excludes` supplies all those
premises from the original family and composes the result with the
genuine-marker cycle. Thus positive O, negative L and negative W are
excluded when A misses the center, without a west-point assumption.
The full source and original-premise bindings received independent hand
reviews. This addition is after the source census below. The positive-L
missing-west-point route is still being completed; no all-sign order
theorem or whole C977 exclusion is asserted.

The positive-L repair now has two more continuous pieces. After O/L
separation on O's V axis, `PositiveCentralPositiveLeft` excludes both
remaining L/A axes. Its own-axis argument retains A's actual upper-left
vertex and uses a disk bound over all L angles. Its central-axis argument
reduces three relative-angle ranges to the normals 0, O and A by exact
unit-circle chords. Independent hand review passed; source is uncompiled.

For separation on L's V axis, `PositiveCentralCrossMargin` supplies a
short global two-angle comparison. Put `k=457/500` and

    F(p,q,l,r)=1-2r-kqr/p+r/p+pl+qr+max(ql-pr,0).

For canonical unit normals it proves

    F(p,q,l,r) >= F(l,r,l,r) = 2-2r+r(1-kr)/l,
    r F(p,q,l,r) >= 2l(l+r-1).

For q<=r the scaled difference factors as

    p l (p+l) (F-F_diagonal)
      = (pr-lq) [r(k-r)(p+l)-l(r-q)(p-r)].

The bracket is at least `r(p+l)(k-(1+r)/2)>=0`, using
`l<=p`, `p<=1`, `0<=q<=r<=5/7`. For q>=r the other bracket
is the explicitly nonnegative sum

    (p+l)[p(l-q)+r(p+q-k)] + p(q-r)(p-r).

The diagonal margin, multiplied by `l(1+l)`, is
`(1-l)r^2(1-r)+(43/500)r^3(1+l)`. Thus the two-angle minimum
needs no differentiation, fine angle split or numerical certificate.
The remaining L-V geometric transfer is now assembled in
`PositiveLeftOwnV`; `PositiveCentralPositiveLeftWest.west` covers all four
positive-L selectors. `C977PositiveBottomWest.frame_excludes` chooses the
actual L and W frames internally and closes both signs of each. Its
`frame_residual` now leaves only strictly negative O, strictly positive A,
and an actual L-owned corner under the original missing-corner and
missing-center assumptions. Whole C977 remains open.

The same complete positive-bottom exclusion is transported to the original
C696 family by `C696PositiveBottomWest.frame_excludes`. The central frame
is chosen internally using the earlier negative-central theorem. The only
orientation input is the actual positive canonical bottom frame; the wall
and left-square signs are both handled internally. These connected sector
results still do not discharge either original whole case.

The stronger witness in
`evidence/positive-central-five-square-countermodel.json` includes the
whole O/L/A/W configuration and actual paired northwest corner. It has
negative O, positive A, all ten pair separations and original signatures,
but A misses both `(1,2)` and `(2,2)`. Therefore the complete proof must
retain more of the original twelve-square packing. It is not a
counterexample to the original theorem.

Both countermodels were checked with exact rational arithmetic in
sub-second bounded jobs, with cleanup receipts. They are diagnostic
mathematical checks, not Lean acceptance or full packings.

## Coupling to the other original squares

Two new unconditional consequences retain the previously omitted owners:

* `Compact.Bridge.C977OuterWings.owned` forces original owner 6 to own
  `(3,1.6)` and owner 7 to own `(1.6,3)`. The shared four-face argument
  uses the actual southwest central crosspoint. It covers all angles
  without a container bound. Its remaining-vector cover retains every
  original packing; it is not a terminal contradiction.
* `Compact.Bridge.C696GlobalSections` uses the four occupied grid cuts
  at coordinates `1.74` and `2.26`. Three actual owners occupy each cut.
  Section capacity yields simultaneous exact radius cuts on both central
  owners and all four wall owners. No saved pose, missing-corner root or
  orientation bound is an input.

`C977PositiveWallOwnedWest.frame_excludes` now closes the entire
positive-W/owned-A-west sector, independently of O's sign. It binds
the actual northwest paired corner's point `(.8,3)` and both V-face
bounds for positive W, with `0<W.s<.172`. The true northeast vertex of
W then lies in `.98<x<1`, `3<y<3.02`, strictly inside the triangle of
genuine E points `(.8,3)`, `(1,3)`, `(1,3.086)`. A closed W vertex
strictly inside E contradicts the original disjoint open interiors.
The full generic proof and original adapter received an independent
hand review; final Lean acceptance remains pending.

`C696BoundaryChain.actual` now retains both five-owner boundary chains,
all exhaustive directed support alternatives, and the true central
barriers from A6 and A7. Their telescoping contradiction remains open.

For C981, `FullAuxWallLowerCorner.opposite_v_impossible` removes the
entire negative-C V-axis sector, including the near-diagonal range. It
retains the quadratic cosine deficit in A's actual lower face. The
remaining coupled cycle and positive-C selectors are not closed, and
this does not discharge row4 or change the whole-vector count.

`FullAuxWallLeftMargins` now replaces the proposed three-angle search
in the negative-C sector with two uniform product certificates. The
first gives a spare coefficient `149lr/4000` after the needed face
margin. The second uses the arc inequality `12l+5r>=12` and the
compensated estimate `C J>=67r/240`; retaining this cosine factor avoids
an invalid loss of `C^2`. The resulting margins support the actual
left-wall angle-order argument. They alone do not close its later
coupled B/L/T cycle.

The next global arguments must close actual support cycles through these
owners. Replacing them by independent center boxes or isolated foreign
points has already lost necessary information in several checked relaxations.

## Remaining assembly contract

`Compact.Assembly.SourceAssembly.Pending` still contains **34 original
whole-case obligations**. Its known registry has **83 whole-case source
entries**. C981 still has **49 whole-vector obligations**, and C1092 has
four whole-packing sectors. No result above changes those counts.

The preferred source manifest retains the new arguments and their
dependencies, including valid conditional lemmas. The measured source
checkpoint is **320,565 lines in 4,205 project modules plus three drafts**.
The bounded source-only census passed with no unexpected missing import,
1.922 seconds elapsed, less than 32 MiB peak resident memory and no
remaining child process. Its receipt is
`.verification/continuous-sector-source-census-20261011.json`.
Two missing historical helpers remain explicitly confined to retained
draft dependencies. The active C696 section theorem derives disjointness
directly and does not import those helpers. Source written after the
checkpoint is not included in this number. This remains separate evidence;
current simplifications do not yet establish a final sub-million-line
bound or a completion ETA.
