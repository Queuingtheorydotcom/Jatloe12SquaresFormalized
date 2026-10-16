# C898: backward dependencies and a genuine chord fusion

This audit concerns the current compact C898 source. A source implication,
an exact rational preparation check, and a Lean-accepted complete case remain
different validation stages. No compiler or computational search was run by
the author of this audit.

## What the final contradiction actually depends on

`Mixed.lean` uses these transitions, where `owner_stage` denotes a domain:

| Stage | Source | Required neighbor | Exit |
|---|---|---|---|
| 0 | 1_0 | 8_0 | 1_1 |
| 1 | 2_0 | 10_0 | 2_2 |
| 2 | 3_0 | 11_0 | 3_3 |
| 3 | 6_0 | 3_3 | 6_4 |
| 4 | 6_4 | 10_0 | 6_5 |
| 5 | 7_0 | 6_5 | 7_6 |
| 6 | 7_6 | 11_0 | 7_7 |
| 7 | 9_0 | 2_2 | 9_8 |
| 8 | 0_0 | 1_1 | 0_9 |
| 9 | 5_0 | 0_9, 7_7, 11_0 | 5_10 |
| 10 | 5_10 | 3_3, 6_5, 9_8 | 5_11 |
| 11 | 5_11 | 0_9 | 5_12 |
| 12 | 5_12 | 6_5 | 5_13 |
| 13 | 5_13 | 7_7 | 5_14 |
| 14 | 5_14 | 9_8 | empty |

Every stage lies on an actual backward dependency path. Owner4 is already
absent from the eleven-square replay; its omission is not a new saving.

The final stage has8 source poses and53 neighbor poses, hence424 pair scopes.
Stage13 begins with23 source poses and leaves8. Its15 closed source poses
still require proofs: filtering the trace to only surviving final identifiers
would silently discard required original coverage. The same restriction
applies to neighbor domains. Row-level dependency slicing can safely retain
only demanded supports, but no measured row-liveness result is claimed here.

## Uniform geometric simplification

Owner5 contains the two original bottom-central markers
`(33/20,33/20)` and `(47/20,33/20)`. With side `a≤1001/1000`, any orientation
satisfies `|c|+|s|≤3/2`. Closed-square support therefore gives

`6397/4000 ≤ centerX ≤ 9603/4000`.

Stage9 excludes the closed center interval

`[77541931/50000000 − r, 79616259/50000000 + r]`,

where `r≥0` is the already certified radius of the original source angle.
Its left alternative is impossible because
`77541931/50000000 < 6397/4000`. Consequently its entire geometric effect is

`79616259/50000000 + r < centerX`.

Stage10 excludes

`[252785619/100000000 − r, 25285449/10000000 + r]`.

Its right alternative is impossible because
`9603/4000 < 25285449/10000000`. Its geometric effect is

`centerX < 252785619/100000000 − r`.

The two window hypotheses involve only the six listed foreign domains.
Neither depends on the intermediate owner5 domain. Both cuts can therefore
be applied simultaneously to each original owner5 pose.

## Exact entrance and exit obligation

The replacement entrance is the original53-pose domain5_0, the six foreign
domain covers, all relevant containment/disjointness/side>1 assumptions,
the original side cap, and the two original owned markers. It preserves the
actual angle witness; it is not an angle sample or a center-only relaxation.

The exit remains the existing49-pose domain5_11. There is one target pose per
surviving angle. The omitted angles are **0,1,56,63**. Angle56 needs original
source inequalities for its contradiction; the strip width alone does not
justify all four omissions.

Each final target row must follow from the original source rows plus the two
strict cuts. `ChordFusedPlans.lean` requires a checked two-row affine support
for every non-aliased target row. Each omitted angle instead supplies a
checked implication `centerX≤leftHi+r`, contradicting the strict lower cut.
Thus empty cases are checked just as explicitly as surviving cases.

`scripts/build_c898_fused_chord.py --run` prepares exactly these53 roots and
copies the unchanged six neighbor-window proof tables. It is bounded to60s
and256KiB new output and must run under the parent's256MiB process guard.
It performs all exact checks before writing generated source. The generator
has run, and the full fused transition has passed the parent's bounded Lean
replay. The final emitted cache uses 419 distinct two-row supports over 53
original sources, 49 target poses and four checked empties. It separates
exact row/radius identities from arithmetic on small literal rows; direct
arithmetic over repeated global table lookups overflowed the checker stack.

Recorded accepted components are `ChordFusedCache` (1.749s), the isolated
first empty-plan check (1.077s), `ChordFusedData` (13.741s), all six neighbor
tables in `ChordFusedNeighbors` (11.562s), and the full `ChordFused` theorem
(3.097s). The final 53-to-49 transition is accepted with its original geometric
and six foreign-cover premises. These checks do not establish the remaining
initial covers or pair stages of the complete C898 exclusion.

The accepted direct implications let the new path bypass 105 branch plans,
101 chord relaxation links,101 raw chord-piece poses, and the52-pose
intermediate relaxed owner5 domain. The old data cannot be deleted globally
until remaining consumers and dictionary references are checked. These
savings do not remove any of the six foreign input covers.

## Stronger original-point route for C713

C713's historical chord window has upper endpoint
`33574687/20000000 = 1.67873435`. Actual foreign owners1,6,10 occupy the three
closed row points `(1,87/50)`, `(2,87/50)`, `(3,87/50)`. Sourceowner7 owns the
strict top-central marker `(33/20,47/20)`, which lies0.61 above that row.

`CentralBarHeight` forces `centerY>87/50+actualSectionRadius` directly from
these original assumptions. `OccupiedRowChord.above_window` transfers this
argument to the square supplied by the actual angle witness, then uses the
certified radius bound. It concludes `centerY>historicalHi+certifiedRadius`.
Thus this chord needs neither its lower branch nor any of its three
propagated neighbor-window cover certificates. Its final outgoing hull rows
still require a checked direct implication; the whole case is not concluded
by this geometric argument alone.

The same occupied-row premise is available in cases701,717,978,979, with
their corresponding actual foreign owners. Exact historical endpoints and
final outgoing rows must be checked before claiming the same replacement.
C973 lacks the common third compulsory point at `(3,87/50)`, so this
argument does not cover it unchanged.

### Arbitrary-orientation audit of the height bridge

The original square `q` need not have a positive or canonical frame.
`PoseLeaf.AngleWitness` supplies an actual square `r` with the same side and
center, the same strict interior, and frame `(normalC t,normalS t)` for an
actual parameter in the leaf's full interval. The bridge proceeds as follows:

1. Transfer the original **strict** top marker to `r` using the interior iff,
   then weaken its inequalities to closed membership. This avoids assuming
   that closed membership transfers automatically through an arbitrary iff.
2. Transfer side, cap, container, and source-versus-neighbor disjointness.
   Foreign squares and their closed occupied row points are unchanged.
3. Apply the original-square blocked-row height theorem to `r`.
4. Use the interval's checked radius bound at the actual parameter `t`.
   Nonnegative normal components justify the two absolute-value reductions
   in the formula for `sectionRadius r`.
5. Transport only the resulting center coordinate back using
   `centerY r=centerY q`.

No assertion that the two frame-dependent radius formulas are definitionally
equal is needed. Original C713 marker11 is strictly owned and supplies the
required strict top premise. The generic bridge does not prove ownership of
the three foreign row points: the whole-case adapter must bind those to the
actual original owners and prove distinctness. Finally, the adapter must
bind the old radius certificate to the exact checked `AngleSection.Radius`
used in the outgoing row. Reusing its numeric radius without that check
would leave a mathematical gap.

## Separate proposed whole-case replacement

`MixedFusedProposal.lean` replaces only the two chord calls with the fused
call and retains the other13 pair stages. `CompleteFusedProposal.lean`
derives the side cap from `NormalizedPacking.side_le` and the two strict
central points from `coded_exact` at the actual owner of mask768, using
markers8 and9. Its `family_impossible` and `ExcludesCase898` have the original
packing/family assumptions. Neither proposal changes the current production
assembly until complete replay succeeds.
