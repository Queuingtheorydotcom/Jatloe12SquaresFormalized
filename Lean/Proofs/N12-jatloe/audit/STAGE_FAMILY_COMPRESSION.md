# Whole-family compression: exact mathematics and current boundary

The complete C898 Step04 family has seven blocked source contexts and all 64
original neighbor contexts. Its original 448 pairs use 3,584 separating-axis
checks. This note describes proposed replacements of that whole family;
neither the envelope audit nor point feasibility is a Lean acceptance result.

## Measured kernel bottleneck

The original cached numeric family passed in 39.120 s. Exact proof-free raw
context materialization reduced it to 33.571 s; the equivalent Boolean family
took 41.144 s. These measurements exclude the separately checked context data.
The Boolean version is not being adopted broadly. Removing repeated source
syntax and proof-bearing numeric types alone does not give the required
compilation improvement.

## Exact margins and envelopes

For a context C and actual integer axis n =(x,y), let bC(n) be its checked upper
bound on −n·center. Its strict bit means the actual value is strictly below
that bound. Let rC(n) be the radius of its exact inner reference square along
the integer direction. In the existing reference representation,

    rC(n) = radiusNumerator(reference,n) /
            (2 * reference.denominator * reference.sideDenominator).

The direction denominator does not appear: both terms here use the integer
linear form. Define mC(n)=bC(n)−rC(n). The old pair comparison is exactly

    mA(n) + mB(−n) ≤ 0,

with strict slack or a strict support bit on at least one side. Each actual
direction remains checked; fan lookup keys are only hints.

For a finite family, an upper envelope M bounds each member margin. Its strict
bit may be true only when every member attaining the maximum has a strict
support bound; nonattainers supply their own strict slack. Therefore checking
M_A + M_B≤0 with the same strict rule implies every represented pair inequality.

The scopes must retain the original eight axes. On a source-owned axis, only
sources with that axis are restricted, while every neighbor participates.
On a neighbor-owned axis, every source participates and only neighbors with
that axis are restricted. The exact Step04 audit found 28 source-axis and 256
neighbor-axis comparisons. It also found 3,812 unique context/direction
supports, 3,584 nontrivial envelope-member checks, 284 singleton identities,
3,300 maximum-selection comparisons and 568 strict-attainer checks. Thus 284
is not the total proof cost and does not justify a thirteen-fold speed claim.

The numeric proposal is `evidence/c898-step04-family-margins.json`, produced
by `scripts/audit_c898_family_margins.py`. The generic checked support-margin
and envelope bridges are owned by the shared-core worker. No broad replay has
been scheduled from these counts alone.

## A genuine geometric reduction: a common polygon

For each context, consider only the four normals of its own reference square.
A fixed point z lies strictly inside every such square for every admitted
center whenever

    n·z + mC(n) ≤ 0

for all four normals, with strict slack or the checked strict support bit.
The intersection of these halfplanes for all neighbor contexts is a robust
common polygon. Its closed polygon is only a search region; each selected
point must still satisfy the full strict rule on every boundary it touches.

If a source context contains a point z in that polygon for every admitted
source center, then it overlaps every original neighbor at z. Different source
contexts may use different points. To avoid repeating all neighbor checks,
form the convex hull of the chosen points. It is enough to check each hull
vertex in every neighbor and provide checked convex combinations expressing
the source points in that hull. Open squares contain all convex combinations
of their interior points, including segment endpoints.

A common segment would require 512 neighbor axis inequalities, 28 source
point inequalities and at most seven two-term convex combinations, together
with 284 original directional-support checks. It would replace the complete
448-pair family, retaining all original square/row/angle hypotheses. These are
conditional costs, not a claimed successful certificate.

The single common-point probe failed. The larger common-polygon audit also
failed: its neighbor intersection within the candidate search box was empty,
all 37 source-group candidates failed, and it produced no point certificate
(0.055 seconds). Both failures remain in their original evidence files.

The bounded partition audit passed in 1.64 seconds. It examined 63 contiguous
neighbor intervals and selected seven geometric groups covering 434 pairs,
plus the original fourteen pairs for neighbors zero and one. Every original
neighbor occurs exactly once. In this particular result each geometric group
has a single common point shared by all seven source contexts; no convex-hull
or convex-combination certificate is required.

The exact points and neighbor intervals are:

| Neighbor indices | Point, divided by 1000 |
| --- | --- |
| 2–3 | (2966,1977) |
| 4–7 | (2941,1973) |
| 8–15 | (3074,2012) |
| 16–31 | (3173,2045) |
| 32–47 | (3111,2023) |
| 48–55 | (3048,2000) |
| 56–63 | (3021,1991) |

The actual replacement source has 49 source-point checks and 62 neighbor-point
checks, each using four own-axis supports. This means 444 point inequalities
and 112 unchanged fallback axis checks, versus 3,584 original axis checks.
There are 276 unique own-axis supports; the first pilot deliberately checks
their cones at each point use, so it does not claim all cone computations have
already been shared. The old 49 one-term convex combinations are omitted.

`Step04CommonPoints.lean` contains these numerical obligations and
`Step04Geometric.lean` assembles the complete original transition through the
same plans, domains, strict complements and outward-relaxation links. These
generic common-point theorem and original-pose/plan bridges passed in 8.629,
1.172 and 1.167 seconds. The complete numerical replacement passed in 4.523
seconds, compared with 39.120 seconds for the old complete numerical family
(about 8.6 times faster in that matched numerical scope). Both figures exclude
shared-context setup. The final original transition assembly is still pending,
so this is not a claim about total project compilation time.

The next prepared audit, `scripts/audit_c898_all_common_points.py`, applies the
same exact one-point certificate to all thirteen C898 pair stages. It allows
rectangles in source and neighbor indices and at most 100 selected groups per
stage. Every unsuccessful group preserves explicit original fallback record
indices. It verifies all original Cartesian coverage, counts every point and
support check, and makes no new acceptance claim for the fallback arithmetic.
The thirteen-stage audit passed in 9.017 seconds. It covers all 25,843 original
pairs: 19,267 receive a geometric common point and 6,576 retain explicit original
axis obligations. It contains 3,825 point checks (15,300 inequalities), 4,648
stage-local unique own-axis supports, and 67,908 total scalar comparisons,
compared with 206,744 original pair-axis checks. Stage-local support counts can
overlap across stages and are not a global dictionary size. Each selected stage
partition contains between one and 53 groups, all below the 100-group limit.

`scripts/build_c898_common_pairs.py` prepares complete original stage source in
an isolated proposal. It shares raw contexts across stages, uses one generic
checked-rectangle constructor for point groups and one for unchanged fallback
groups, and checks exhaustive pair coverage using only small natural-number
ranges. It retains the better existing Step04 certificate and the accepted
terminal stage14. The initial isolated proposal was produced successfully;
named per-context equality bindings were then added to bound elaboration memory.
The proposal requires regeneration before activation. These
counts remain candidate proof obligations; they are not thirteen accepted Lean
transitions or a whole-project compilation bound.

The terminal stage14 has now passed as a complete original transition using a
single point `(10079/5000,2457/2500)`. Its 61 point checks and actual domain-cover
contradiction compiled together in 10.396 seconds with ordinary axioms. The
production `Step14` alias now imports this theorem; the old axis-based alias is
preserved as provenance. Together with the retained manual Step04 partition,
the assembled production proposal contains 6,583 fallback pairs and 3,817
point checks, or 67,932 scalar comparisons. These totals count the actually
selected source route, not the slightly different candidate partition audit.
The complete C898 endpoint remains pending replay.

The initial search box is only a candidate-generation bound; failure produces
no mathematical exclusion or completeness claim. A successful partition would
still needs original-model reference containment and kernel replay of every
numerical and coverage obligation. This particular single-point-per-group
replacement needs no convexity theorem.
