# Positive bottom / positive left entrance

This is source-only mathematical work. No Lean compiler, numerical solver,
search, generator, or finite angle check was run for these additions.

The actual bottom square is `O=(p,q)`, the actual left singleton is
`L=(l,r)`, and the southwest central square is `A=(C,S)`, with positive
canonical unit normals. The original O/A support and foreign northwest
marker give `q≤S`, `p>9/10`, `C>81/100`, and `S<3/5` when A misses `(1,2)`.
The proof retains L's full square supports and actual left container wall.

`PositiveCentralPositiveLeft.left_alternatives` removes both transverse
L/A axes using the original L near/far seeds and A's marker and crosspoints.
It leaves exactly L-U and A-U forward separation. This uses no saved pose
enclosure and no auxiliary point asserted to belong to A.

For O-V incoming separation, both surviving outgoing choices are now closed:

* `PositiveCentralPositiveLeft.own_axis_impossible` uses A's actual upper-left
  vertex. Its coordinates satisfy
  `x<1−g(C,S)−S(1−p)` and `y≤2−S(1−C)`, where
  `g(c,s)=(1−c)(1−s)/c`. The defect is monotone on the required central arc.
  After reducing A to O, one disk estimate covers every canonical L angle.
  The estimate uses `δ=1−p≤1/10` and `k=2/7`; its remainder is at least
  `δ²(1−9δ)≥0`. The strict side length remains in the geometry.
* `PositiveCentralPositiveLeft.central_axis_impossible` eliminates L's
  translation from its actual full supports and left wall. The scalar
  coefficient is handled by `PositiveCentralPositiveLeftArc.central_axis_margin`.
  Three continuous relative-angle ranges reduce to L equal to the horizontal,
  O, or A normal. The range above A is monotone, so it requires no additional
  endpoint. The middle range uses the exact unit-circle chord identity
  `(S−q)²l²−((S−r)p+(r−q)C)²
   =(r−q)(S−r)((p−C)²+(S−q)²)`.

The O/L separator on L-V is supplied by `PositiveLeftOwnV`. Its two outgoing
choices use the genuine bottom-marker coefficient 457/500 and L's actual
corner and container wall. `PositiveLeftOwnVEndpoint.endpoint_left` supplies
the A=L endpoint: the exact increment is nonnegative when `p≥457/500`; in
the remaining range `9/10≤p≤457/500`, its inner factor is at least 59/10000.
The A=O endpoint and the continuous interpolation are in
`PositiveLeftOwnVBounds`.

`PositiveCentralPositiveLeftWest.west` now combines all four selector pairs.
It uses only side>1, with no side upper bound. The separately proved negative-L
result retains the actual side≤1001/1000 premise. The O-V scalar/geometry
chains, the own-V endpoints and geometry, and the original adapter received
independent hand reviews by other agents. This is not a Lean replay.

`C977PositiveBottomWest.frame_west` chooses the actual L1 canonical frame
internally and derives A5(1,2) for both L signs. The original foreign point
A5 missing (1,1.6) comes from owner1's actual auxiliary index 10. All markers,
central crosspoints, side bounds and disjointness are original consequences.

`C977PositiveBottomWest.frame_excludes` additionally chooses actual W8's
canonical frame. Nonnegative W uses the original paired-corner theorem
`C977PositiveWallOwnedWest.frame_excludes`; negative W uses the genuine-marker
cycle through `C977OwnedWestCorner.frame_excludes`. The frame replacement
changes only owner8's coordinates and preserves its physical square.
There is no remaining L sign, W sign, W angle order, or assumed Awest point
at this combined interface.

The precise original residual is now recorded in
`C977PositiveBottomWest.frame_residual`. For any canonical frames of O0 and
A5, if original O0 misses (1,1) and A5 misses (2,2), then O0.s<0, A5.s>0, and
the actual L1 owns (1,1). A nonpositive A frame was already closed by
`C977CornerReach`. This proves a whole orientation sector, not the whole C977
family. No whole-family pending count was changed.

The original context does not assume A5 misses (2,2).
`C977Residual.canonical_remaining_cover` therefore retains two alternatives:
the actual A5 owns (2,2), or A5 misses it and has a canonical negative O0,
positive A5, actual L1(1,1), and exact A5 auxiliary signature {4,13}.
The signature reduction applies only to this second branch. All original
missing-corner strengthening, canonical bounds, wall half-spaces and the
surviving full auxiliary vector remain in the cover.
`C977Residual.excludes_case_of_two_endings` explicitly requires a contradiction
for each alternative. Neither contradiction is supplied by this reduction.

The unavailable `(1,2.88)` wall exclusion is not used in these new chains.
The two-square O/A or three-square O/A/W shortcuts remain invalid; the
verified countermodel for the latter does not include the actual L used here.

## Actual right and top support continuation

`CentralRightCornerSupport.lower_support` uses an actual right square R
with positive canonical frame, side at least one, full right container
wall, strict marker (3.086,2), and missing genuine corner (3,3). In every
positive canonical direction (c,s), it proves
`lower R c s ≤ 2(c+s)+1`. No restriction on the angle difference or side
upper bound is used. Both upper-U and upper-V escapes of the corner are
covered; the right wall and marker remove its lower-face escapes.

The upper-V case uses the continuous scalar
`F=1−2c−s+s(1−t)/d+cd+st+max(ct−sd,0)≥0`.
Its minimum occurs at equal normals and is at least
`(1−d)^2+(1−d)t(1−t)/d`. The upper-U case either has a larger version of
the same margin or a direct lower bound 157/1000. The full support and
the nonnegative correction for side greater than one remain in the proof.

`negative_lower_support` closes the other canonical wall sign using only
its genuine marker and full right wall `d(u+a)+t(v+a)≤4`. Its scalar is
`1−Pc−Qs≥0`, with `P=2−d−t≤d` and
`Q=t(d+t−.914)/d≤t`, followed by the unit-normal dot-product bound.
The corner exclusion is not needed in this sign. Thus
`canonical_lower_support` includes both signed wall sectors.

`signed_direction_support` also covers negative canonical test directions.
It reflects only the right square across y=2, retains the marker, and uses
the actual lower corner exclusion (3,1). The exact transport is
`lower (pullY R) c (-s)=lower R c s-4s`.

`C977RightCornerSupport` derives these exclusions from actual paired owners:
owner3 owns (3,3), owner2 owns (3,1), and owner4 owns (1,3). Its
`right_signed_support` and separately swapped `top_signed_support` therefore
cover both signs of the wall frame and both signs of the test direction.
Its `center_chain_signed_excludes` closes the actual center-owned A5/B6/R10
selector pair in which both separators use B6's U direction, without any
B6 or R10 sign restriction. It does not discard the other separating axes,
the other inner-point assignments, or the signed escape branch.
The complete C977 ending remains open. All new source remains uncompiled.

`CentralOpposedCornerChain.upper_sum` supplies an orientation-free bound for
the actual center square. For any two unit normals n,m and a point P inside
A, its upper supports relative to P obey
`h_A(n)+h_A(m) ≥ −A.side*(n·m)`. Each coordinate uses two nonnegative
endpoint margins for coefficients in [−1,1]. The resulting `impossible`
excludes the paired corner-cap chains
`upper A (c,−t)+a≤3c−t` and `upper A (−r,d)+a≤3d−r` when A owns (2,2)
and a>1. The remaining scalar is exactly
`2+cr+td−c−t−d−r=(1−c)(1−r)+(1−d)(1−t)≥0`.
The stated two chains are explicit premises; they have not been inferred
for every original A/B and A/C separator.

`CentralRightChain.lower_shift` handles the complete positive-frame B/R
selector once B's lower U face is beyond the center and B owns inner16.
Both transverse directions are removed by actual strict B/R points.
B's own U separator contradicts the complete right-wall support bound.
The shallower-wall mixed separator has margin
`K+.35(c+s)G≥1`; the steeper-wall mixed separator has
`K−.26sH≥d`, with exact identity
`c*(K−.26sH−d)=d*(1−c)+sH*(1−.26c)≥0`.
The only remaining conclusion is the genuine displacement
`R.loU>3R.c+2R.s`. The original binding is
`C977CenterRightChain.frame_shift`: it retains center ownership, B's
conditional inner16 ownership, positive B/R frames and the incoming A/B
separator on B's U axis. The E3/T coupled contradiction and other original
incoming/sign/inner-assignment modes remain separate obligations.

The negative right-wall sign is now fully excluded in this same conditional
central entrance. `CentralRightChain.negative_alternatives` retains both
the B-owned U axis and the R-owned V axis from the complete signed SAT
disjunction. The first contradicts the already proved signed wall support;
the second forces `R.loV>3t+2R.c`, where `R.s=-t<0`. The generalized
`steeper_direction_reach` is homogeneous in its test direction and applies
to `(t,R.c)` without a canonical-angle requirement on that direction.

`PairedCornerPositiveWall` removes the previously needed foreign lower
singleton from the positive-wall corner argument. For the actual outward
corner point, its upper-U escape and the full container wall would imply
`a(d+t)≤1−.2d²+dt≤d+t`, contradicting `a>1`. The remaining upper-V cap
forces the wall vertex into the actual paired corner triangle. Its
horizontal reflection closes the negative right-wall R-owned V selector.
The complete corner square remains in the final disjointness argument.

`C977CenterRightChain.corner_outward` supplies actual owner3(3.2,3) from
markers4/5, owner11's original aux7=(2.4,3), and owner10's aux19=(3,2.4),
via square-only reflection of `CornerBudgetReach.upper_left`.
`negative_frame_excludes` binds the negative-R contradiction to the actual
owners. `canonical_frame_shift` therefore covers both right-wall signs and
all B/R separating axes; it concludes a nonnegative R frame and the strict
lower-U displacement. Positive B, conditional Binner16, and the incoming
A/B separator on B's U axis are still explicit premises. No whole-family
pending count changed; all this source remains uncompiled.

The preferred center-owned reduction is now shorter and removes both
conditional inner-point premises. `CentralRightCornerAlternatives` keeps
the genuine corner alternatives for every signed canonical B frame:
`B.hiU≤3c+s` or `B.loV≥c−3s`. With `B.loU≥2(c+s)` from the incoming
B-owned axis, the second alternative forces actual B(3,2). The lower U
band follows from B's strict marker; the lower V band follows from the
original outer point B(3,1.74). Both upper bands follow from the complete
side `a>1≥c`. In the first alternative, the same width bound forces `s<0`.
Thus no inner16 ownership or B/R separating-axis enumeration is needed.

`C977CenterCornerAlternatives.all_frame_alternatives` binds that argument
to original owners. `negative_wall_point` independently forces R(3,2)
for every nonpositive canonical right-wall frame using the actual paired
northeast corner. Hence the B(3,2) outcome forces a positive-wall lower-U
escape; the other outcome retains B's negative-angle southeast cap.

`C977CenterOpposedChains.top_frame_alternatives` applies the same result
to the entire genuinely transposed C977 packing. Its owner permutation is
proved from transformed marker codes; the frame changes preserve every
physical square. `wall_escape` then excludes the simultaneous southeast
and northwest corner caps using `CentralOpposedCornerChain.impossible`.
It forces either the actual R lower-U escape or the actual T lower-V
escape, for all B/C/R/T signs and without inner auxiliary assumptions.
The incoming A/B and A/C separators on the neighboring B/C axes remain
explicit. The paired northeast endpoint ending and the other incoming
central axes remain genuine global obligations.

`CentralRightIncomingPositive` covers the other incoming axis when A's
canonical frame is nonnegative and B's is nonpositive. If B's upper U
face lies before (3,2), its complete lower support in A's direction is
at most the support value of (2,2), contradicting the actual A-owned
separator. The continuous scalar has component margins
`dx=1−c−.65t²−.35ct≤0` and
`dx+dy=−(c−t)(1−.65c+.35t)≤0`; the positive canonical test direction
weights these two margins by `C−S` and `S`.
Consequently the genuine B lower-V corner escape forces B(3,2) also
for this incoming axis. `C977CenterCornerAlternatives.positive_axis_alternatives`
binds the argument to the original packing and retains the alternative
southeast upper-U cap. That cap has not been passed to the opposed-corner
theorem, which requires the different B-owned incoming separator.

`CentralRightIncomingOrdered` extends that support comparison to every
signed canonical A/B frame with `As*Bc−Ac*Bs≥0`. Its cone endpoints are
B's own normal and the diagonal. Their exact margins are `c−1` and
`−(c+s)(1−.65c−.35s)`, so no angular subdivision is used.
`C977CenterCornerAlternatives.ordered_axis_alternatives` binds this to
the original A-owned separator and retains the negative-B southeast
cap or the positive-R shift. `top_ordered_axis_alternatives` supplies
the exact whole-packing diagonal transport.

`CentralCenterPairIncoming` and `C977CenterIncoming.frame_cover` now
give the full original incoming classification with no conditional
inner16 or inner5 premise. The actual signed A caps put B's marker
strictly in A's V strip, removing both A-owned transverse directions.
The right pair retains precisely A.U, B.U, or B.V with `3Bc<7Bs`.
The top pair retains the three exact diagonal counterparts. Every
original signed frame and all four SAT axes are accounted for before
these reductions.

`C977CenterIncomingCorner` couples this cover to the genuine northeast
ending. With positive E, the right shift is impossible, leaving the
real southeast cap, A-owned reversed angle order, or the steep B.V
axis. With negative E, its exact top counterpart holds. These are
explicit residuals, not a whole center-owned contradiction. In
particular, the cap-only generalized opposed-chain claim for A-owned
axes is false: the full actual paired corner squares remain necessary.
The B.V southeast upper-U face is itself impossible from B's actual
wall point; it must not be confused with an upper-U cap at the different
inward point (3,2). No pending count changed. All new source remains
uncompiled.

The positive-A transverse mode is now actually discharged by
`CentralPositiveTransverse.impossible`, with the real southeast-corner
exclusion retained. Its exact scalar margin is at least 1/28.
`C977CenterIncoming.positive_right_alternatives` therefore gives precisely
the A-owned or B-owned U separator for every original signed B frame.
`C977CenterIncomingCorner.positive_center_residual` has three outcomes:
negative B with its southeast cap; positive B steeper than A on A's U
axis; or a positive R shift with E and T both negatively oriented.

`CentralSteeperIncoming.central_cap` handles the reversed positive
A/B angle order when B misses (3,2). B's genuine southeast exclusion
forces its lower V face, and its inward upper-U escape gives the exact
excess `C(1-c)(1-s)+S(c(1-c)-s)`. Positive excess forces `S<.4`, while
the excess is at most `.09C`. The latter uses one unit-circle chord,
not sampled orientations.

`CentralSteeperNegativeBottom.small_bottom` retains all O/A SAT axes
with this enlarged A cap. The steep negative-O face has residual at
most either `.09t` or `(3593/9500)t-(93/475)c`; both are strictly below
the genuine bottom boundary on `t>.47` and `c+t>1.35`. The other actual
marker face forces `t<.2`. `C977SteeperNegativeBottom.frame_point` then
uses the existing original O/D9 ending to force B(3,2), and `frame_shift`
transfers it to the actual right wall. The nonpositive-O reversed-order
orientation is complete, without a side upper bound or inner ownership.

The preferred `C977CenterIncomingCorner.missing_corner_residual` keeps
the original O0 missing-corner root explicit. For positive A, the
reversed-order alternative now also requires positive O. The negative-B
cap and the remaining northeast escape are still retained until their
separate complete endings are supplied. Choosing A positive has not
silently reflected the original missing-corner owner. All modules are
source-only and remain uncompiled; no whole C977 exclusion is claimed.

The original root now supplies a stronger all-orientation bottom-wall
constraint. `C977BottomExtendedReach.point` uses O's genuine strengthened
point (1.82,1), A's actual crosspoint (2,1.5), and the full D9 wall to force
D9(2.6,1). Neither O's angle nor A's center incidence enters that reach.
Together with the original D9(2.4,1), this closes reversed positive B
incoming supports in `CentralSteeperBottomReach.impossible` and its
negative-central counterpart `negative_impossible`. The latter uses the
actual lower crosspoint, avoiding any transpose of the missing-O root.

The preferred original entrance is now
`C977SignedCentralCorner.frame_cap`: for every signed canonical A frame,
under the original O0 missing (1,1) and A5 owning (2,2), B6 has strictly
negative sine and `B.hiU≤3Bc+Bs`. The intrinsic R10(3,2) from
`C977WallMiddle` removes every right-wall displacement. For the remaining
B.V selector, its strict support below A(2,1.5) and genuine inward upper-U
cap force B(2.6,1), contradicting actual D9. The two-negative reversed
angle case is closed by `CentralNegativeIncoming.lower_bound`; its cone
endpoints are B's normal and the negative diagonal. The new generic
`CentralBottomTransverse` keeps the real wall point, side width, and
inward exclusion explicit throughout.

This is a complete signed-A cap reduction, not a whole C977 ending.
The full negative-B paired-corner/bottom continuation is still required.
Earlier residual APIs remain for provenance, but their angle and shifted
wall alternatives are now subsumed by this preferred entrance. No global
pending count was changed. All of this work remains source-only and
uncompiled.

`C977NegativeCentralFloor.frame_floor` further binds the actual lower
face `B.loV≥Bc+2.6t` for the remaining negative B, with no A-sign or
incoming-axis assumption. For A-owned incoming support, the positive
case uses `CentralNegativeBottomUpper`; the negative case uses the new
`CentralNegativeIncomingBottom`. Its two relative-angle cones have the
same parallel endpoint `.6c+.5t−1<0`. The other endpoints follow from
the unit-circle chord `c+t≥1+.7ct`, `t²≤.5`, and `ct≤.5`. When the
transverse coefficient is negative, the proof uses B's real strict
marker as the lower bound on its upper face. For the B-owned incoming
axis, A's actual lower crosspoint and `a>1` rule out the upper-U miss
directly. The remaining full D/B transverse coupling is still required;
this lower-face result is not a whole-family exclusion.

For a nonpositive canonical D9 frame, the genuine stronger O point
(1.96,.76) advances its actual horizontal reach to (2.86,1).
`C977NegativeCentralFarFloor.frame_bounds` then forces
`B.loV≥Bc+2.86t` and `t<.3`, for every signed A frame and both incoming
longitudinal axes. The negative-A case uses
`CentralNegativeFarIncoming`: in its hard relative-angle sector, the
actual lower face at 2.6 puts the relevant B vertex above y=1.5, so A's
true lower crosspoint forces horizontal incoming support. The existing
full negative-D proof then applies. Both actual D/B transverse axes are
retained; a point-only farther-reach claim would be insufficient.

`NegativeBottomTransverseChain.impossible` closes the remaining
O-on-D.V / D-on-B.V separator. Its two exact unit-circle expansions have
t coefficients `r−1−.13r²−.154dr` and
`r−.14−.99r²−.24dr`; the original far marker supplies the strict support.
Together with the other three selectors, the original adapter
`C977PositiveBottomNegativeWall.frame_excludes` excludes the entire
positive-O / nonpositive-D branch, with no A-sign assumption.
`wall_positive` records the corresponding actual orientation consequence.
These sources and their original point bindings have independent hand
reviews, but no Lean replay has run. The negative-O and remaining
positive-D continuations are still explicit obligations; no whole C977
claim or pending-count change follows from this branch alone.

The positive-D continuation is now assembled as well.
`PositiveBottomSupport.positive_projection` and
`PositiveBottomWallCentralAxis.impossible` retain both actual O/D
longitudinal axes and exclude the B-owned outgoing transverse axis.
For the remaining D-owned axis, `PositiveBottomWallNeighborAxis`
handles B-owned incoming support using A's actual lower crosspoint,
independently of A's orientation. Its normalized margin is
`d²A−d−drE+.914r²≤0`, with `A≤1`, `E≥.53`,
`d(1−d)≥.4r²`, and `r≤d`.

The A-owned incoming axis is covered by `CentralNegativePositiveBottom`
for positive A and `CentralNegativeSignedPositiveBottom` for negative A.
The latter uses exactly three support endpoints: horizontal, B's own U
axis, and the negative diagonal, with explicit unit identities on both
linear cones. It uses the original lower crosspoint rather than a
reflection of the missing-corner root. The original all-A adapter
`C977PositiveBottomWallClosure.bottom_excludes` therefore excludes every
nonnegative canonical O frame in the center-owned branch. Its positive-A
corollary derives that O sign through the earlier genuine entrance.
The generic identities and original owner/point bindings have independent
hand reviews. Lean remains unrun, and the negative-A/negative-O entrance
is still retained as the remaining whole-case obligation.

That final signed entrance is now also assembled in source. The true
foreign bottom marker splits negative O into a shallow face, already
excluded by the actual next-wall ending, or a steep face. For negative
D, `NegativeBottomCentralAxis` and `NegativeBottomOwnTransverse` close
the two O-owned transverse selectors; the previously reviewed full
support chain and short middle-square argument close the two D-owned
selectors. `C977NegativeBottomNegativeWall` binds all four to the original
owners. For positive D, `C977NegativeBottomPositiveWall` retains the O.V
and D.U incoming modes and the two outgoing axes, using the actual
bottom-wall marker and extended reach together with the sign-independent
central incoming contradiction.

The final `C977CenterClosure.excludes : ExcludesCase 977` chooses a
canonical frame separately for each actual square, preserving every
interior and the original missing-O root. It exhausts all O/D signs,
including zero, and consumes the unchanged `C977SignedEscapeClosure`
contract for both center alternatives. The final original bindings and
generic support identities have independent hand reviews. This is now
a complete source-level ending for the original case; it is **not a
Lean-verified theorem yet**, and no compiler or computational replay was
run by this worker. Registry and pending-count updates remain with root.
