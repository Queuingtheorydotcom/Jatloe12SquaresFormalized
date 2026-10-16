# Mathematical compression beyond shared literal dictionaries

This is a source-level plan and a separately assembled pilot. It does not
claim a new accepted case or a completed global size bound.

## Measured obstruction and useful reuse

The complete authenticated accepted-seven source inventory contains 230,414
distinct rational rows, 42,393 distinct poses, 194,536 distinct tree syntax
nodes and 283,495 candidate pair declarations. Literal dictionaries plus
tree sharing alone do not meet the requested 300,000-line assembled target.
These are costs of one representation, not mathematical lower bounds.

The complete C898 support audit found 25,843 pair records, 1,063 distinct
input contexts, 10,071 globally distinct two-row bases and 10,072 context–basis
memberships; the largest context uses 30 bases. The old pair records repeat
413,488 basis occurrences. Evidence: `evidence/c898-support-fan-counts.json`.

## Shared directional fans: actual prepared implementation

A context is the exact set of its source rows, including its pruning block
when applicable. Each two-row basis bounds one linear direction whenever
its determinant-derived weights are nonnegative. Among valid bases the
generator chooses the smallest rational constant divided by the positive
determinant, preferring a strict bound at a tie. This choice is done with
exact integers/rationals, not floating point.

Only the finitely requested directions are needed. Order the reference
directions around the four quadrants; merge consecutive requests with the
same selected basis into intervals. A context then stores direction
breakpoints and row pairs. Bounded binary search retrieves the candidate.
Each original pair stores source pose, neighbor pose, block, source fan and
neighbor fan: five indices instead of the original three indices plus
eight four-row supports. Every original pair and all eight axes remain.

The new logical interface does **not** trust optimality, sorted breakpoints,
direction-to-key correctness, or generator completeness. The returned rows
must pass their actual membership tests, determinant signs, constant bound
and strictness for the unchanged `ReferenceAxis.target`. An arbitrary
default, missing interval or bad key cannot make the theorem weaker; it
can only make a finite check fail. No Cartesian search over basis pairs is
performed by Lean.

`Compact/Core/PairSupportFast.lean` proves the four Cramer coefficient
identities once by polynomial algebra. `FastCheck.toCheck` reconstructs the
original checker proposition. This removes repeated big-integer coefficient
equalities without adding an axiom or changing the target. The core still
checks signs and strictness, including strictness inherited from a positive
weight on a strict input row.

The independent source modules are:

- `Compact/Core/PairSupportFast.lean`
- `Compact/Core/SupportFan.lean`
- `Compact/Cases/C898/PairFan.lean`
- prepared generator `scripts/build_c898_pair_fan_pilot.py`

The generator requires `--run` and has a 120-second/192-MiB/8-MiB-output cap.
It preserves all 424 original Step14 records and their order, audits every
one of 3,392 axes, and emits `PairStep14FanPilot.lean` separately from active
sources. It also checks the bounded binary lookup itself. At the time this
note was written only Python syntax parsing had run; Lean replay and measured
pilot size/time remain the acceptance gate.

An additional arithmetic optimization remains available: current targets
multiply the direction by
`2 * a.denominator * a.sideDenominator * b.denominator * b.sideDenominator`.
This positive factor can be moved to the final constant comparison, leaving
Cramer weights at the unscaled integer direction. Its generic scaling proof
must be checked before use; the present pilot retains original target scaling.

## Eliminating initial subdivision history entirely

The current initial-region tree representation is not a necessary part of
the mathematical argument. `source/S12/PoseRegion.lean` provides exactly:

- `poseInputs`: outer-reference containment of each compulsory point, four
  container-wall bounds and a constant strict true row;
- `poseForbidden`: inner-reference containment of each forbidden point;
- `poseInputs_sound` and `poseForbidden_sound`: their connection to every
  actual original square, including its orientation and side assumptions.

Fix one angle enclosure with reference axes `(c,s)` and `(-s,c)`. Apply the
invertible coordinates `u = c*x+s*y`, `v = -s*x+c*y`. The compulsory-point
conditions become axis-aligned interval bounds. Each forbidden-point block
becomes an open axis-aligned square, all with the same inner-reference side.
The container contributes four oblique halfplanes. Thus admissible centers
are a convex polygon minus a union of congruent open rectangles, with exact
rational boundaries.

For C898, the old initial tree's many leaves are immediately relaxed into
one convex pose per owner and angle. A stronger compression target is to
prove each of those reduced pose inequalities **directly**, eliminating
both the old bisection tree and its raw initial leaves. For a desired row
`L`, prove that every point satisfying the initial conditions and the exact
logical negation of `L` lies in at least one forbidden open rectangle.
`poseForbidden_sound` then supplies the contradiction. The original reduced
pose and all later pruning/chord statements can stay unchanged.

### A sound finite cover checker

Vertex-only testing is insufficient: a union of rectangles may contain all
vertices of a polygon while leaving an interior gap. A correct checker can
instead sweep all distinct vertical rectangle boundaries in `(u,v)`:

1. Treat every boundary line and every open strip separately. The open
   forbidden rectangles do not cover their boundary automatically.
2. On an open strip the set of active forbidden rectangles is constant.
   Sort their vertical endpoints and merge their **open** intervals, retaining
   whether equal endpoints leave an uncovered point.
3. The violating polygon contributes a vertical interval whose endpoints
   are piecewise affine rational functions. Split additionally at its
   vertices and at intersections with horizontal rectangle boundaries.
4. Check that every resulting interval lies in the active rectangle union.
   A boundary-line check handles the equality cases excluded from open strips.
5. Carry strict/nonstrict endpoint inclusion explicitly. The negation of a
   strict target is closed; the negation of a nonstrict target is strict.

Alternatively, build the finite arrangement of polygon edges and rectangle
edges and check **all dimensions**: open 2-cells, open edges and vertices.
Either method is a theorem about continuous real centers, not a finite sample.

The rectangle lists, angle parameters and reduced target rows are the
mathematical input. Bisection histories and thousands of repeated Farkas
weight strings need not be stored. Sorted-event/intersection certificates
can be untrusted hints checked by determinant identities and ordering tests.
The finite arrangement now has an accepted exact soundness theorem in
`Compact/Core/PlanarVertex.lean`, and an accepted integer checker in
`Compact/Core/PlanarVertexCheck.lean`. The proof selects the closed arrangement
cell containing an arbitrary admissible real point, then moves to a feasible
intersection whose target value is no greater. This validates all nonstrict
linear target rows and constant-negative empty-region targets; it does not
use the unsound inference from coverage of a polygon's vertices to coverage
of its interior.

### Size and runtime gates

This route requires a bounded exact pilot before it can support a global
budget. Needed measurements are the number of forbidden points per owner,
the number of reduced target facets, and sweep events after deduplication.
Complexity must include all strict boundary checks and all seven cases.
An O(m²) arrangement may still be too large when repeated per target row;
reusing one arrangement per owner/angle and checking all reduced facets at
once is preferable. No extrapolation from one easy leaf is justified.

## Generate geometric rows from their actual parameters

Many literal rows are already determined by an angle enclosure, marker point,
face index and inner/outer reference choice. The existing `pointForms`,
`wallForms`, `poseInputs` and `poseForbidden` define those formulas exactly.
They should become shared derived data, rather than a second literal copy.
The row-recipe catalogue must distinguish these generated rows from genuinely
new pruning cuts; equality can be checked once per recipe and reused. Positive
scaling must preserve the ray sign and strict bit. Primitive normalization
alone has no measured global benefit yet; the new inventory run is pending.

The appropriate completion gate is an unconditional whole-case exclusion
with the original entry/coverage/strictness/terminal chain. Neither a smaller
table nor a passed finite pilot changes the status of remaining cases.

## Current cached-pair and full-domain status

The exact direct-cover audits passed every selected initial root of all
seven inherited exclusions: 6,848 owner-angle roots, including 312 roots
whose closed relaxations are empty. These are candidate arithmetic audits,
not full seven-case Lean acceptance. The generic checker and original-square
bridges have passed focused Lean replay; the coordinating worker is replaying
the actual root data. See `INITIAL-DOMAIN-COMPRESSION.md` and the two exact
audit JSON reports for the scope and original model.

For C898, the original 25,843 pair exclusions repeatedly recomputed the same
two-row support. Their exact candidate bases have 1,063 distinct row contexts
and 10,071 globally distinct bases. The terminal step alone has 424 pairs,
but these are exactly eight source contexts times all 53 neighbor contexts.
Its 3,392 axes can use 297 fan intervals, retaining every strict input bit.

The first fan implementation still unfolded the full shared dictionary
inside numeric checks. A four-pair/sixteen-pair batch could therefore exceed
the memory guard even though a complete single pair passed. The revised
`VertexSupport` construction checks a basis intersection `(X,Y)/D` once:
`D > 0` and both input-row affine expressions vanish at the point. For any
requested normal `(u,v)`, nonnegative Cramer weights then prove the exact
support row `(D*u,D*v,-u*X-v*Y)`, with strictness inherited from a positive
weight on a strict input. Pairing two such bounds requires one scalar integer
comparison against the unchanged separating-axis radius. No optimality of
the selected support vertex is trusted or required.

`VertexSupport`, `CachedSupportFan` and the original-model `CachedPairFan`
bridge passed focused Lean replay, with only the ordinary axioms `propext`,
`Classical.choice` and `Quot.sound`. `CachedSupportFan` adds one checked
input-membership and copied-row identity per basis. The numeric pair decision
then reads only the small cached values, not the global 26,026-row dictionary.
The authentic first context's seven basis checks passed in 2.229 seconds
(`propext` only), and the local literal data passed in 9.697 seconds.
All 61 contexts and 297 bases passed in 31.239 seconds. The complete 424-pair
numeric family plus the actual overlap theorem passed in 43.152 seconds.
The checks use opaque batches of at most eight pairs in the same module;
the generic composition proves every index is covered, including a partial
last batch. A single 53-neighbor decision had exceeded the memory guard.
The final original-domain composition subsequently passed in 15.280 seconds
after its coverage check was simplified. Thus the complete terminal
transition is accepted; the complete C898 exclusion and complete seven-case
migration remain separate pending gates.

`scripts/build_c898_cached_pair_pilot.py` preserves all 424 original pairs
and generates finite kernel checks connecting the eight sources and 53
neighbors to their complete original domains. All eight terminal pruning
blocks are empty, so this final transition can discard the old complement
plans and relaxation-link bookkeeping altogether. It still proves the same
original terminal transition, using actual open-square realizations.

`scripts/build_c898_cached_pairs.py` prepares the corresponding complete
thirteen-stage migration. `CachedPairPlans` separates checked geometric
overlap from plan assembly, removing per-overlap record indices while
retaining every source, every neighbor, every exact complement, each surviving
piece, orientation transfer and outward-relaxation link. The full generator
ran successfully in 1.823 seconds and assembled all 25,843 original pair
obligations, including reuse of the accepted 424-pair terminal transition.
The other twelve stages contain 25,419 pairs, 1,002 shared context routes and
6,533 cached bases. This is source assembly; the full chain is not accepted.
No complete-case status or global
300,000-line claim follows until the entire original entry-to-terminal chain
has passed replay and its actual source closure is measured.

The assembled retained-relaxation source removes the 1,121 obsolete
raw-initial-leaf links. Its exact remaining set contains 927 pair/chord
links and 7,086 support rules, eliminating 8,418 support rules. The new
chord-fusion route may remove another 101 links after its independent
original-model proof and data check pass; that prospective saving is not
included in the safe 927-link baseline. Dictionary trimming is complete,
so discarded incoming poses and rows no longer remain as active
dictionary literals. Public original pose and row IDs are preserved, and
every active selected literal value is exact.

The completed source-closure selector (`evidence/c898-active-dictionary.json`)
retains 10,851 of 26,026 rows and 2,196 of 3,317 poses. It removes all 1,121
obsolete raw poses and 15,175 unused rows. Its scope includes every original
pair plan, complete neighbor domain, surviving piece, all 927 retained links,
both original chord transitions, all 500 blocks and all 725 used complement
keys. Every retained pose's angle, row order, coefficient, denominator and
strict bit matches the authenticated original map. Future chord-fusion savings
are excluded. The prepared sparse proposal saves 1,042,405 literal bytes before
76,083 bytes of explicit original keys; it also removes the 1,121 dead pose
aliases. This is a measured source-data saving, not a compiled-time result.

`Compact/Core/SparseLiteral.lean` represents the retained dictionaries as
balanced transparent constructor trees with their original IDs. Its parsers
emit ordinary typed Lean terms; selected-row materialization only inspects
literal constructors. Missing IDs have explicit defaults, so these tables
must be activated together with the audited production closure: inactive
legacy overlays requiring discarded data are provenance, not usable proofs
over the sparse dictionary. Actual original-square entry, complement, support
and exit checks must all pass independently after activation. The proposed
files under `evidence/proposals/C898Sparse` were activated after the generic
helper passed in 4.036 seconds. The previous dense dictionaries are preserved
under `evidence/retired/C898DenseDictionaries`, with every before/after hash in
`evidence/c898-sparse-dictionary-activation.json`. Including the 725-key
complement table, the three active source files shrink from 32,816 lines and
2,123,861 bytes to 16,045 lines and 1,020,305 bytes. The four dictionary roots
passed replay in 5.071, 7.862, 0.936 and 1.441 seconds. Their complete downstream
replay is still pending; the historical coefficient/pose JSON is unchanged.

The terminal composition's metadata bottleneck was isolated and removed.
An inferred finite decision could enumerate the whole global pose-ID type
despite a small membership premise. Exact `List.finRange.map` identities now
provide source and neighbor coverage directly; all metadata completed in
3.382 seconds. Remaining finite list checkers explicitly choose
`List.decidableBAll`/`List.decidableBEx` over actual listed objects, including
pruning plans and retained-relaxation supports. The proposition types are
unchanged; only their finite decision procedures differ.

The complete Step04 numeric family (seven blocked sources and all 64 original
neighbors, 448 pairs) passed in 39.120 seconds. Its three context modules took
approximately 26 seconds separately. This is too slow to treat naive scaling
to all six other historical cases as an acceptable finished design.

`KernelMatrix` replaces repeated per-source composition proofs by one generic
row-major range theorem and a balanced proof tree. Every leaf still contains
at most eight ordinary-kernel acceptance checks. Its generic theorem and
nonempty/empty examples passed in 1.451 seconds using ordinary axioms. Across
the twelve new C898 stages, this needs 3,181 leaf facts instead of 3,336 padded
row chunks and removes 592 per-source composition proofs. It does not reduce
the actual mathematical pair obligations or claim to solve their arithmetic
cost by changing source formatting.

The proof-free raw numeric comparator preserves all 71 Step04 contexts by
ordinary exact equalities. Its data replay passed in 9.175 seconds, all 448
pairs in 33.571 seconds, and its transfer to the original semantic pair
predicate in 1.641 seconds. The roughly 14% numeric improvement is measured
but insufficient on its own. An equivalent Boolean checker and shared
directional-bound caches are being assessed separately before wider replay.
The all-stage producer's optional `--raw-numeric` and `--recipe-contexts`
modes are prepared, not yet executed. The latter uses the shared
`VertexFanTable` constructor to remove repeated context wrapper definitions;
it does not replace any geometric or finite-check premise.
