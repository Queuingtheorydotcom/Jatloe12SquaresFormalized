# A symbolic extension covering eleven further proposed case applications

The new source replaces the right barrier of the checked four-square theorem
by an actual lower point excluded by a fifth owner. It introduces no angle
bins or numerical propagation data. All three new geometry modules await the
parent's Lean replay; the original-case adapters have separate ownership.

The eleven original case IDs are
`405,424,985,990,993,994,999,1063,1064,1069,1070`.
They belong to the 47 capacity shortcuts outside the earlier twelve-case
template group. The archive entrance comparison uses exact rational points
and all eight symmetries. Every template positive point is already present.
The old right barrier `(81/25,187/100)` is not a supplied compulsory point of
a foreign owner, whereas `(3,87/50)` is. The left barrier remains unchanged.

## The actual new implication

In a positive frame write the face coordinates as
`u(x,y)=cx+sy` and `v(x,y)=-sx+cy`, with `c>0`, `s>=0`, `c^2+s^2=1`.
Assume the original left wall, side `a>1`, closed points

- `P=(457/500,2)`;
- `Q=(1,12/5)`;

and missing interior points `W=(1,87/50)`, `D=(87/50,2)`.
Then `T=(1,5/2)` is strictly inside the actual square.

The P/Q bounds first make both lower T inequalities strict. D can fail
containment only at the upper u face or lower v face. W can fail only at a
lower face. For W's upper u inequality, `s>0` follows from Q directly; at
`s=0`, `c=1`, the wall and `a>1` make that inequality strict.

If W fails at its lower u face, D cannot fail at its upper u face:
their displacement `(37/50,13/50)` has norm strictly less than one, so those
two face failures would force `a<1`. D therefore fails at its lower v face.
The displacements `T-W=(0,19/25)` and `T-D=(-37/50,1/2)` also have norm less
than one. They give both strict upper T inequalities.

If W fails at its lower v face, that face already gives T's upper v bound.
Suppose T fails at its upper u face. Combining the left wall with these two
face inequalities gives

`a(c+s) <= 1 + (19/25)cs`.

But the unit arc gives `c+s >= 1+(4/5)cs`, and `a>1`, `cs>=0` make this
impossible. This completes the whole-angle argument, including axis and
contact endpoints.

Reflection gives the original right square's strict point `(3,5/2)` from
its missing point `(3,87/50)`. The new shared endgame derives A's strict
point `(2,5/2)` and then applies the existing positive/negative B arguments.
No new assumption replaces separation, containment, or equal side lengths.
In particular this is **not** permission to replace the left barrier in the
B/L endgame; that stronger proposed change has a counterexample.

## Exact application map

The transformation maps template coordinates to the recorded case: first
swap coordinates if indicated, then reflect the indicated coordinates about
2. Owner numbers are archive indices and must be translated to original
marker masks by the case adapters.

| Cases | Transformation | A,B,L,R owner indices | Lower foreign owner |
|---|---|---|---|
|405,424|identity|7,8,9,10|6|
|985,990,993,994|swap|6,5,9,11|7|
|999|identity|6,7,8,10|5|
|1063,1064,1069,1070|reflect x|7,6,10,8|4|

`evidence/four-square-lower-barrier-family.json` records each archive member
hash, its foreign owner's exact compulsory hull, its original capacity
conclusion, and the old pair-recipe length. These recipes are eliminated
only when the new whole original-case exclusions pass; they are not counted
as proved merely because the point patterns match.

## Source and remaining acceptance

- `Compact/Geometry/WallLowerBarrier.lean` proves the new wall implication.
- `Compact/Geometry/FourSquareHighRight.lean` proves the shared endgame from
  the actual higher R point.
- `Compact/Geometry/FourSquareLowerBarrier.lean` combines them at the original
  template premises, replacing only `rMissingLow` with `rMissingRow`.
- The symbolic worker owns `Compact/Bridge/FourSquareCaseVariant.lean` and
  the eleven original-case adapters. Their fifth owner supplies the missing
  point through original auxiliary ownership and physical disjointness.

Parent replay must accept the new geometry, the exact auxiliary-domain
forces, the original retained-row bindings, and all eleven exclusions.
Until then this is a complete source route, not eleven accepted theorems.

## Consequence for the whole-proof budget

The current source-only union before this extension was approximately
170,000 lines, dominated by C898's 150,465 case-specific lines. A uniform
mechanical conversion of the other six historical cases does not establish
the requested 300,000-line assembled bound. A new symbolic family is the
right scale of improvement: this extension needs a few shared lemmas and
small ownership adapters, replacing whole per-case propagation traces.

It still does not establish the full one-million-line bound. The remaining
baseline and eleven late-case obligations require either further proved
symbolic families or complete, counted compact certificate instances. The
uncounted supports, branches and entry coverage cannot be budgeted as zero.
