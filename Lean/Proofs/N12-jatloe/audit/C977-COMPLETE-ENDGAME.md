# C977 complete continuous ending: source checkpoint

`Compact/Bridge/C977CenterClosure.lean` now exposes the unchanged original
contract `excludes : ExcludesCase 977`. The source has not been compiled.
This receipt records mathematical coverage, not successful Lean replay
and not completion of the unrestricted twelve-square theorem.

## Original coverage

The existing original root cover provides a bottom singleton O which
misses (1,1), retaining the actual entire packing and its owner map.
The complete missing-center argument
`C977SignedEscapeClosure.center_owned` forces the southwest central
owner A to contain (2,2). The new center ending chooses a canonical
representation of each actual square independently; this changes no
physical point, owner, or missing-corner premise. In particular it never
reflects a missing point of O into an unproved missing point of L.

The actual central incoming alternatives and the genuine right-wall
middle point force the southeast central square B into a negative
canonical frame `(c,-t)` with upper U face at most `3c-t`. Its original
marker, outward wing and the foreign right-wall middle point also give
upper V face at most `2c+3t`.

Write D for the actual bottom wall to O's right. The complete remaining
argument is a four-cell sign cover of the physical O and D squares:

| O sign | D sign | Complete original source consumer |
| --- | --- | --- |
| nonnegative | nonpositive | `C977PositiveBottomNegativeWall.frame_excludes` |
| nonnegative | nonnegative | `C977PositiveBottomWallClosure.frame_excludes` |
| nonpositive | nonpositive | `C977NegativeBottomNegativeWall.frame_excludes` |
| nonpositive | nonnegative | `C977NegativeBottomPositiveWall.frame_excludes` |

These consumers retain both central incoming axes and both signs of A.
Every endpoint with zero sine is included. The actual frames, sides,
strict points, closed container and full pair separations are supplied
by the original packing adapters.

## Why the bottom chain closes

All cells use actual O/D and D/B separating axes. There is no replacement
of either full square by a collection of independent point domains.
The exact point D(2.6,1) comes from O's original missing-corner reach and
A's genuine crosspoint. For a negative D, the actual paired corner
supplies D(2,1), and O's stronger far point supplies D(2.86,1). Full
central incoming and D/B geometry then force B's tilt below .3. Those
facts are not assumed numerical localization bounds.

For negative O, its actual next marker splits the argument into a
shallow upper-U escape, handled by the original next-wall contradiction,
or a steep upper-V escape. The negative-D case is the four-cell support
cycle detailed in `C977-NEGATIVE-BOTTOM-ENDGAME.md`.

For positive D, the wall-owned outgoing axis is incompatible with the
original central incoming supports, independently of O's orientation.
On the other outgoing axis, actual bottom containment and a full side
width give the contradiction. In the last negative-O selector, the
true singleton has upper V height greater than `p+1.8q`; the two relative
angle orders reduce to a uniform support-width bound and two exact
endpoint margins. The cone identity uses nonnegative coefficients and
keeps the zero relative-support boundary. It needs no angle grid.

The final whole-case theorem composes this center ending with the
already retained original missing-center ending and root cover. It does
not require choosing any of the historical full auxiliary ownership
vectors or replaying the 4413 research selectors in the ending.

## Validation boundary

The new mathematical lemmas and their original packing adapters have
been independently hand-reviewed during construction. Two independent
workers have also reviewed the final whole-case adapter and its full
original coverage, with no mathematical or premise gap found. Lean
elaboration, tactic success, complete import replay and final axiom
inspection remain outstanding. Other original case endings remain
separate obligations in the global assembly.
