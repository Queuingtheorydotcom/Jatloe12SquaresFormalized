# C981 outer-top vectors 34/41: mathematical handoff

Checkpoint: 2026-10-11. This is source and hand-mathematics work. No Lean
compiler, generator, solver, numerical search, or replay was run by this
worker for these files. The new reductions do **not** exclude either whole
vector 34 or 41. The parent owns registration and the authoritative case
counts.

## Frozen files and validation boundary

* `Compact/Geometry/OuterTopElbowFaces.lean`: exact shallow exclusion,
  four steep faces, and two outer arms. Source only.
* `Compact/Geometry/OuterTopElbowReach.lean`: row-34 narrowness and true
  top-wall reaches. The parent independently hand-reviewed these arguments.
* `Compact/Geometry/OuterTopElbowOpposite.lean`: exhaustive directed A/C
  SAT reduction, both canonical signs of C. An independent worker reviewed
  the mathematics. Source only; no kernel acceptance is claimed.
* `Compact/Geometry/OuterTopElbowCentralReach.lean`: positive-C angle,
  exact upper-U face, shifted point, and elimination of C's remaining own-V
  separator. The strengthened angle was hand-reviewed by the parent. The
  final `only_a_axis` addition was self-reviewed only at this checkpoint.
* `audit/C981-OUTER-TOP-ORDINARY-WALLS.md`: earlier detailed notes and the
  unverified five-square local candidate. Its candidate is not an original
  packing or a global counterexample.

The latest source-only review repaired two concrete transcription risks:
the forward A.V elimination needed upper-D/lower-A point bounds; the
`only_a_axis` polynomial identity has unit-normal multiplier
`3*D.c-(33/20)*D.s`. Support rewrites in the new central-reach file use
explicit ring conversion rather than assuming reordered products are
definitionally equal. All these files still require the final Lean replay.

Earlier whole-vector source progress, already handed to the parent, is
separate: `DiagonalWallCenter`/`C981DiagonalWallCenter` for diagonal-wall
vectors 5/6/42 and `DiagonalOuterElbow`/`C981DiagonalOuterElbows` for 35/60.
Their exact active names and registration are controlled by the parent.
Do not conflate those completed source arguments with unfinished 34/41.

## Actual chart and ownership

The chart is the original transform `⟨true,false,true⟩`, equivalently
`old=(new_y,4-new_x)`. Relevant original owner indices are:

| Role | Owner | Genuine chart data |
| --- | --- | --- |
| A | 5 | P=(2,2.26), F=(2.26,3), M=(2.35,2.35) |
| B | 6 | (1.65,2.35), (1,2.26), (1,2.4) |
| C | 7 | (1.65,1.65), (1.74,2), (2,1.74) |
| bottom wall | 8 | (2,.914), (1.6,1), (1.74,1) |
| R | 9 | (3.086,2), (3,2.26), (3,2.4) |
| T | 10 | (2,3.086), (1.6,3), (1.74,3) |
| L | 11 | (.914,2), (1,1.6), (1,1.74) |

Owner 2 supplies the true paired corner (3,3), and owner 3 supplies
(1,3). The C center (2,2) comes from the existing double-wall placement;
the two strict C crosspoints (1.5,2), (2,1.5) have existing genuine wall
proofs. A production original-vector wrapper still needs to call those
theorems and transport their facts; no anonymous extra points may be added.

Row 34 has A auxiliary pattern `{8,16}`, and A **does not** own
Q=(2.26,2). Row 41 has `{4,8,16}` and **does** own Q. Both have ordinary
R `{6,15}`; neither permits assigning (2.4,3) to R. C's absence of Q is
genuine in both rows, even when Q is not owned by A.

All square-side, container, orientation, and disjointness assumptions
remain those of the actual original packing. The side cap, if needed,
is 1001/1000. None of the reductions uses saved pose ancestry.

## Exact source APIs and mathematical gains

### OuterTopElbowFaces

`shallow_impossible` rules out a positive canonical A (`0≤s≤c`) using
P,F,M, missing center, missing NW marker, and exact missing (2.4,3).
It does not require the unavailable inward point Q.

`faces` in a positive frame returns:

```
c < s
2(c+s) ≤ Au
AhiU ≤ 2.4c+3s
AhiV ≤ 2.35c−1.65s
2.4c−3s ≤ Av
```

Besides P,F,M it uses actual missing center, NW marker, outer top/right
auxiliaries, and the genuine top-owner point (1.74,3).

`arms` gives strict A(2.35,2.65) and A(2.65,2.35).

### OuterTopElbowReach

`narrow` adds A's exact missing Q and proves `2c<s`. This is a **row-34**
entrance and must not be applied to row 41.

`points`, for `2c≤s`, uses the genuine R exclusion (3,2.5) to strengthen
the lower V face to `2.5c−3s≤Av` and prove strict A(2,2.5), A(2.18,3).
The genuine R(3,2.5) itself follows from the existing ordinary-wall reach
and R's own exact exclusions; it does not depend on A owning Q.

`top_basic` gives T(1.44,3) from P,F and the actual T marker/left point,
container, side and A/T disjointness. This is available in both rows.

`top_strong` gives T(1.4,3) from the two new A points. This is currently
bound only through the row-34 narrow entrance. Convexity then supplies
the entire strict T segment from x=1.4 to x=1.6 at height 3, including 1.5.

### OuterTopElbowOpposite

`alternatives` takes the actual same-side A/C disjointness, signed canonical
C, A near-vertical faces and P/M, C center/SW marker/bottom crosspoint.
It covers all eight directed SAT possibilities and returns only:

```
upper C (c,s) ≤ Au
or
ChiV ≤ lower A (-C.s,C.c).
```

`no_positive_u` is the closed-A-corner argument removing the extra C.U
axis when C is positive. Its proof retains the full A square.

### OuterTopElbowCentralReach

For positive canonical C=(C,S), `only_a_axis` removes the second selector
using the genuine A upper-U and NW-marker upper-V caps. In the relevant
closed-corner projection the center gap is `C*f+S*g`, where

```
f = 1−.65c²+.75cs−c−s < 0
g = .35−.75c²−.65cs+c−s ≤ 0.
```

The first bound uses `1−s≤c²` and the short vector (.35,.75); the second
uses `2c≤s` and `s≥7/8`. This is not a point-only replacement of SAT.

`angle` retains both input selectors and proves **5S<C**. On the
contrary sector use `(5S−C)(C−S)≥0`, hence `6CS≥1+4S²`; the two endpoint
short vectors are `(109/260,47/52)` and `(.65,.75)`. The C.V branch also
has a coarse independent strict bound. Both vectors have norm below 1.

`upper_u` uses C's exact missing Q and its center/bottom crosspoint to
prove `ChiU≤2.26C+2S`.

`point` then proves strict C(1.3,1.9), under the weaker `2S≤C`. Its U-width
estimate is `.96C+.1S<1`; its upper-V band comes from C(1.5,2). The parent
observed that (1.27,1.9) is also valid, but no separate helper was added
without a demonstrated need.

The actual A.U support retains a useful correlation. Write

```
alpha=cC+sS, gamma=sC−cS,
u=ChiU−2(C+S), v=ChiV−2(C−S), e=Au−2(c+s).
```

Then `alpha*u+gamma*v≤e`, with strict `v>S/2`, `e<.4c+s−1`, and `u>0`.
The current geometry file does not yet package this full formula as a
public theorem. The closed-corner proof is direct. Do not replace it by
the unavailable old bounds `u<.001` or `u<.1`.

## What remains genuinely open

* Neither row 34 nor row 41 has a whole original-packing exclusion.
* In row 34, positive C now leaves only A's incoming U separator; negative
  C retains two full-square selectors. Midpoint worker was assigned the
  complementary negative-C/B-sign continuation.
* This worker retained positive-C/positive-B. Actual B/L/T/corner coupling
  remains to be closed. An angle bound or isolated forced point is not the
  whole branch.
* Row 41 does not inherit `2c<s`, the improved A points, or T(1.4,3), since
  it owns Q. Its additional A point may allow a different shorter ending,
  but that argument is not present here.
* Production frame/original-owner adapters for these new reductions are
  not written. The intended final adapter must retain all original signs,
  ownership, side equality, container and pairwise-disjointness premises.

## Concrete next mathematical step

For positive C, its new cap and 5S<C also force the genuine bottom-V face
`C−1.6S≤CloV`: the U lower band of the foreign point (1.6,1) follows from
`.66C+S<1`; the other two bands follow from the center. This short bridge
has not yet been written in the new module.

Use the genuine strict T point (1.5,3), not an invented diagonal R point.
For positive B, the B-owned transverse separator makes the point's
upper-V escape impossible directly from C(1.5,2): it would require
`a<b≤1`. The C-owned transverse separator admits an elementary scalar
check. With positive relative angle `Ct−Sb≥0`, set

```
f=2−b−.74t²−.5bt,
g=.5−.5t²+.74bt−t.
```

The needed estimate is `C*f+S*g≤1`. A hand certificate was sent to the
parent: for `t≤.3`, `gb−ft=.5b−1.26t≥0`, so the existing arc lemma bounds
the expression by `bf+tg=2b−1`; for `t≥.3`, the ordinary defect bound
`1−b≤.6t²` gives `f≤.895`, `g≤.422`, and this rational vector has norm
below 1. For negative relative angle, the analogous coefficients

```
f=2−b−.65t²+.15bt ≥0,
g=−.15+.15t²+.65bt−t ≤0
```

reduce by angle ordering to the same endpoint `2b−1`. These are hand
derivations, not new checked/source theorems at this checkpoint. The parent
may be sourcing the scalar separately; coordinate before duplicating it.

Once these genuine strips are established, B's exact absence of T(1.5,3)
forces `BhiU≤1.5b+3t`; its actual corner/left-marker exclusions give
`BhiV≤3b−t` and `BloU≥.914b+2t`. Thus `1<.586b+t`. This may substantially
sharpen the full B/L/C support cycle. It does **not** by itself exclude
the remaining B-owned V separator: the actual C excess correlation or
the actual L square must still be retained.

## False shortcuts and counterexample constraints

1. R has no diagonal (2.4,3) in 34/41. The successful 35/60 diagonal-wall
   theorem cannot simply be instantiated here.
2. A lacks Q in 34 but owns it in 41. Never reuse the missing-Q narrow
   argument on 41.
3. C's new upper-U cap is `u≤.26C`, not the old tiny `u<.001` bound.
   Old C/B/L cycle theorems must not receive the latter without a new proof.
4. T owning a point at height 3 implies `T.loY<3` in an axis frame, not
   `T.loY≤3−a`. The latter informal shortcut was withdrawn; no source
   lemma uses it.
5. With top point x=1.4 and C(1.5,2), the B.V span is `b+.1t`, not
   `b−.1t`. The incorrect exploratory sign was explicitly withdrawn.
   The true x=1.5 midpoint gives the useful exact span b instead.
6. The local five-square A/C/R/T/E candidate in the earlier audit omits
   the actual NW B and left/bottom chains. It is unverified and does not
   refute either original vector. It only warns against prematurely
   claiming a five-square center lemma.

No new global theorem, acceptance claim, or registry change is made by
this handoff.
