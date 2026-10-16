# C696: transporting the positive-bottom west-point proof

This checkpoint contains original-packing implications, with no Lean run
or computation. It does not exclude the whole C696 family.

## Original corner entrance

`C696CornerReach.left_corner` proves that any positive canonical frame of
original southwest central owner6 which misses `(2,2)` forces original
left singleton owner1 to own `(1,1)`.

If owner1 missed its corner, `SouthwestCornerTranspose.point` would force
the central point. Its premises are precisely the original owner1
marker/near/far seeds, owner1's missing left-wall marker, owner0's original
horizontal segment, and the owner6 triangle plus the genuine new strict
point `(2,1.5)`. The proof retains actual disjointness and the full left
singleton containment. It does not assume a global packing reflection or
any bottom or wall orientation.

## West forcing for both left signs

`C696PositiveBottomWest.frame_west` chooses a canonical frame of original
owner1 and dispatches its two signs to
`PositiveCentralPositiveLeftWest.west` and
`PositiveCentralNegativeLeft.west`. Their entrances bind as follows:

| Generic object or premise | Original C696 source |
| --- | --- |
| Bottom O, left L, southwest central A | owners0,1,6 |
| O marker and singleton seeds | owner0 exact query points |
| O missing next bottom marker | owner0 exact query exclusion |
| L inner corner | `C696CornerReach.left_corner` |
| L near/far singleton seeds | owner1 exact query points |
| A original triangle | marker8, auxiliary4 and13 |
| A new crosspoints `(1.5,2)`, `(2,1.5)` | `C696CentralReach.central_points` |
| A missing northwest central marker | owner6 exact marker exclusion |
| A missing `(1,1.6)` | owner6 exact auxiliary exclusion |
| Common side, containment, pair disjointness | original normalized packing |
| A upper U cap | original missing center and strict triangle bands |

No C977-only auxiliary assignment, corner-wing ownership, wall point,
angle order, or saved enclosure is used. The negative-left theorem's
side upper bound is exactly the original normalized bound `a≤1.001`.

`C696PositiveBottomWest.west` also chooses the positive central frame
internally, using `C696NegativeCentral.positive_frame_of_missing_center`.
Its remaining premises are only an equivalent positive bottom frame and
the two original exclusions: owner0 misses `(1,1)`, owner6 misses `(2,2)`.
The conclusion is actual owner6 ownership of `(1,2)`.

## Complete positive-wall cell

`C696PositiveWallOwnedWest.frame_excludes`, independently authored and
reviewed, binds the genuine paired-corner triangle argument in all four
square-level charts. The chart roles are

```
wall      [8,9,10,11]
corner    [5,2,2,5]
central   [6,6,7,7]
singleton [1,0,4,3]
```

The coordinate maps are identity, swap, half-turn, and half-turn after
swap. Both paired owners have exact empty auxiliary assignment, providing
the two genuine exclusions for `CornerBudgetReach.upper_left`. The corner
marker/seed triangle and wall-square vertex are transported together;
there is no independent rearrangement of owners.

`C696PositiveBottomWest.positive_wall_excludes` combines the new west
forcing with chart0 of that result, closing the original southwest
positive-bottom / positive-wall cell. It assumes neither central nor
left-singleton orientation.

## Complete positive-bottom sector

`C696OwnedWestCorner.frame_excludes` now binds the other wall sign to the
completed genuine-marker cycle. Original owner8 supplies `(.914,2)`,
`(1,2.26)`, and `(1,2.4)`. Original owner1's far seed is foreign to it,
and its exact marker set excludes both `(.914,3)` and `(1.65,2.35)`.
The proved lower face and `NegativeWallMarkerCap` therefore supply both
true upper faces and the true wall range. `PositiveCentralWallAngleOrder`
uses the already-derived central ownership of `(1,2)` to supply the
bottom-to-wall angle order. No height2.88 premise is used. The actual
left singleton is canonicalized internally and all its selectors and
both signs are consumed by `CornerWallMarkerCycle.impossible`.

`C696PositiveBottomWest.frame_excludes` chooses the central and wall
frames internally, derives the central west point for both left signs,
and invokes the appropriate original wall-sign exclusion. Thus a
positive canonical bottom frame is impossible whenever original owner0
misses `(1,1)` and original owner6 misses `(2,2)`.

The public consequence `canonical_sine_negative` proves that every
canonical frame equivalent to that actual bottom square has strictly
negative sine. This includes elimination of the zero-angle endpoint.
The remaining negative-bottom sector and the complete original C696
family are not excluded by this checkpoint.
