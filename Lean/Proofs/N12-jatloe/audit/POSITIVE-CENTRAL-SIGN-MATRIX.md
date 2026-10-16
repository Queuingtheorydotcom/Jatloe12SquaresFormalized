# Positive-central corner ending: historical matrix and premise audit

**Superseded status:** the matrix below records the earlier conditional
2.88-seed route. The genuine-marker replacement is now assembled for the
whole signed-L ordered cycle. Its original missing-west-point entrance
and the other global sign sectors remain open. See
[the current repair checkpoint](ORIGINAL-MARKER-REPAIR.md); do not use the
old cell counts below as the current mathematical status.

This is a source audit, not a Lean replay or a whole-case exclusion. No
compilation, numerical search, or certificate generation was run for it.
The source interfaces and the owning workers were checked on 2026-10-11.

## Scope before the matrix

The central square A has a canonical positive frame `(C,S)`, `0≤S≤C`,
and is assumed to miss `(2,2)`. Its actual strict points give the upper-U
escape `A.hiU≤2(C+S)`. The bottom singleton O misses `(1,1)`, and the left
singleton L owns `(1,1)`.

The two earlier complete geometric reductions remain separate:

* `SouthwestNegativeCorner.point` handles a negative canonical A, with
  either O sign and the genuine foreign L segment.
* `SouthwestCornerTranspose.point` handles positive A when L instead
  misses `(1,1)`, by applying that theorem to the reflected actual squares.

Neither statement handles the residual below: positive A and L owning
the corner. A zero canonical sine may be assigned to the positive branch;
the non-strict normal hypotheses of adjacent lemmas overlap at zero.

`Awest` means the actual strict ownership `A.Inside 1 2`. It is not
available universally: the exact three-square countermodel in
`evidence/positive-central-three-square-left-point-countermodel.json`
satisfies the original O/L/A signatures and misses both Awest and center.

## All sixteen signed/ownership cells

Here `+` means nonnegative canonical sine, and `−` negative canonical
sine. “Conditional complete” means a whole geometric contradiction has
source, but its listed extra premise is not established by the original
C696/C977 entrance. “Open” is mathematical, not just an absent wrapper.

| O | W | Awest | L positive | L negative |
|---|---|---|---|---|
| + | − | owned | Conditional complete: ordered cycle, top/tilt entrance missing | Same |
| + | − | missing | Conditional complete: escape order plus ordered cycle, top/tilt entrance missing | Same |
| − | + | missing | Conditional complete: `PositiveWallPositiveLeft.missing_left_impossible`, missing-top entrance missing | Open; `refactor_symbolic` owns remaining upper-U coupling |
| − | + | owned | Open | Open |
| + | + | owned | Open | Open |
| + | + | missing | Open | Open |
| − | − | owned | Open | Open |
| − | − | missing | Open | Open |

In particular, the original-packing positive-central ending is not
complete. There are eleven open cells even after granting the extra
top-seed premise, and the five conditional cells have an additional
original-entrance gap. No orientation normalization currently identifies
these cells while preserving the actual bottom/left corner ownership.

## What the completed conditional routes actually say

### Positive O, negative W

`CornerWallOrderedCycle.impossible` covers both L signs and every O/L and
L/W SAT direction. Its `Data` requires the actual contained congruent
O/L/W squares, original strict points including L's corner, and actual
O/L and L/W disjointness. Its additional scalar premises are:

    O.hiU ≤ 2c+s
    bottom(c,s) < O.hiV
    W.hiV ≤ t+2.88d
    s ≤ t ≤ .51,   .86 ≤ d

Here O is `(c,s)` and W is `(d,−t)`. The theorem explicitly assumes
`Normal O.c O.s`; it cannot be used for negative O.

For owned Awest, `PositiveCentralWallAngleOrder.angle_order` supplies
`O.s<t` using the genuine excluded marker `(.914,3)`. That order theorem
does not itself require the disputed `(1,2.88)` point. The sharper top
bound and `.51` tilt needed by the complete cycle still do.

For missing Awest, `PositiveCentralEscapeOrder.angle_order` supplies
`O.s<t`, but already requires `¬W.Inside 1 (72/25)`. Its proof uses
`NegativeWallTopSeed.upper_face`. The latter's lower-face/tilt route also
depends on that exclusion. The older `LeftWallNegativeFaces` theorem
uses only the actual upper marker and yields the weaker `t<.6`; this
does not supply the complete cycle's stronger `.51`/`.86` hypotheses.

### Negative O, positive W, missing Awest

`PositiveWallPositiveLeft.cuts` obtains the actual bottom support,
`0<t<.2`, O's upper-U cap, A's strict floor and northwest cap from the
actual O/A premises. No top-corner assumption is used for these cuts.

`PositiveWallEscapeFaces.faces` next requires the explicit exclusion
`¬W.Inside 1 (72/25)`. It separates W into an upper-U and an upper-V
escape. `PositiveWallUpperVImpossible.impossible` closes the upper-V
escape using actual A/W geometry without any L sign restriction.

`PositiveWallUpperUPositiveLeft.impossible` closes all O/L and L/W SAT
choices in the upper-U escape for positive L. The whole original-point
wrapper is `PositiveWallPositiveLeft.missing_left_impossible`.
The corresponding negative-L upper-U argument remains under development.
These lemmas do not cover owned Awest, positive O, or negative W.

### Genuine-marker upper-U reduction

The positive-L upper-U support cycle has now been generalized without
duplicating its proof. `PositiveWallUpperUPositiveLeft.impossible_relaxed`
requires only

    W.hiU ≤ d+2.914s.

The genuine upper marker's U escape `W.hiU≤.914d+3s` implies this bound
because `s≤d`. The previous explicit `2.88` theorem remains a small
compatibility wrapper. In the shared proof, the two critical scalar
remainders become `l(1−d)(1−s)+r*s²` and `(1−d)(d+s)`, both nonnegative;
strict common side greater than one supplies the strict contradiction.

`PositiveWallMarker.upper_faces` uses the genuine excluded marker
`(.914,3)`. `PositiveWallMarker.upper_v` combines it with the full
negative-bottom/positive-left cycle and leaves the actual bound

    W.hiV ≤ 3d−.914s.

Thus that entire marker upper-U escape has a source proof under genuine
original-point hypotheses. This does not close its matrix cell: the
marker upper-V escape is weaker than the old `2.88` upper-V bound and
still requires a new ending. The previous cell counts concern whole
contradictions, not these one-direction reductions.

## The top-seed premise is not part of these original families

Both C696 and C977 have a paired northwest corner owner with marker mask
192, namely markers 6 and 7. `source/S12/Seeds.lean` defines singleton
extras only when the exact marker set is a singleton. For a paired corner
it supplies the corner point `(1,3)`, not `(1,2.88)`. Its soundness theorem
cannot manufacture the singleton seed from the paired marker set.

The genuine upper marker `(.914,3)` is foreign to W. The stronger point
`(1,2.88)` is presently unbound. Previous notes calling it an “actual
upper singleton seed” for C696/C977 were incorrect.

A corner-only theorem forcing that point is itself false. For example,
the axis-aligned open square

    E = (0,1001/1000) × (2999/1000,4)

has side `1001/1000>1`, is contained, and strictly owns the paired markers
`(.914,3)`, `(1,3.086)` and their forced corner `(1,3)`, but misses
`(1,2.88)`. This observation uses direct rational comparisons, not a new
numerical run, and is not a twelve-square counterexample.

A valid repair must use actual E/W or wider packing coupling, or redo
the support cycle with genuinely available bounds. Merely replacing a
singleton record by a paired-corner record does not establish the premise.

## Exhaustiveness and next mathematical obligations

The old O/A and A/W two-axis reductions are valuable but do not close a
cell by themselves. The angle-order theorems have signed normal premises;
their names must not be treated as an all-angle result.

The next bridge must retain each of the following until independently
discharged:

1. A legitimate original-family replacement for the disputed top seed.
2. The negative-L upper-U escape with negative O and positive W.
3. Both Awest branches when O and W have the same canonical sign.
4. The owned-Awest branch for negative O and positive W.

All statements above preserve actual complete squares, strict owned
points, non-strict support contacts, common side, containment and the
required original disjointness. There are no proposed admissions or
unchecked finite-angle substitutes.
