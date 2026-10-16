# Symbolic refactor of the n=12 propagation proof

Status: 10 October 2026. This is a mathematical design and a bounded source
audit, not a completed case exclusion. No certificate generation, optimization
search, Lean compilation or remote writes were run for this report. A later
authorized exact terminal probe is documented in `C696-TERMINAL.md`; it took
0.160 seconds and 23.5 MB, and identifies a single explicit polynomial target
that would replace the post54 root-one tail if proved from actual geometry.

## What must change

The dominant object in the current development is a **history of whole
continuous-domain approximations**. At each step it exports the source and
neighbor pose families, forbidden regions, cut trees, all retained leaves and
Farkas relaxations into another whole pose family. Soundness is proved for all
of that state even if the terminal contradiction needs only a handful of
support inequalities or strict point memberships.

The refactor should make the proof object a **derivation of those final
inequalities and memberships**, with explicit coverage at every genuine
geometric split. Most intermediate domain rows should never become Lean
declarations. Simply moving the same numerical history into a single array,
binary blob, long line, or procedural decoder does not meet the compilation
objective.

Existing useful mathematics should be retained: strict marker ownership,
whole-packing symmetries, border-point transfer, chord and strip arguments,
the exact strict/non-strict Farkas rules, and disjointness. In particular the
short border-transfer theorems are valuable; the giant ancestry supplying
their elementary bounds is the part to replace.

## Concrete new simplification: normalize a coupled center quantity

Write `B(p) = centerY (owners p 9)` and
`T(p) = centerY (owners p 11)` for C696 root zero. The already written original
half-turn proof gives a physical transformed packing `H(p)` with:

* the same case family and root-zero assumptions;
* `B(H(p)) = 4 - T(p)`;
* `T(H(p)) = 4 - B(p)`.

Therefore every root-zero counterexample has a representative satisfying

\[
                         B+T\le 4.
\]

**Proof.** If the inequality holds, keep the packing. Otherwise apply the
half-turn: the transformed sum is `8 - (B+T) < 4`. Equality is retained in the
first branch. This is a symmetry of the whole physical packing, not an
independent reflection of two local domains.

Now split at `B = 4/5`. In the high branch, `B > 4/5` and `B+T ≤ 4` immediately
give `T < 16/5`. Both branches keep the coupled inequality `B+T ≤ 4`.

This improves the previous source: `RootZeroSymmetry.lean` only gets the top
bound *after* a separate proof that the low-bottom branch is impossible. The
new normal form supplies a stronger, joint linear restriction before any
propagation or low-branch exclusion. It can therefore participate in a direct
Farkas contradiction; the old independent-owner state cannot express it.

Written source:

* `Compact/Geometry/C696Symmetry.lean` proves canonical existence, the strict
  middle bound, and reduction to the two canonical geometric obligations.
* `adapters/C696SymmetryOriginal.lean` instantiates the action using the
  original `NormalizedPacking`, `owners`, `CornerRoot`, and half-turn lemmas.
  It is outside the standalone compact core because the sparse checkout does
  not contain all its historical dependencies.

These sources were not compiled by this worker. Neither proves the low or
middle contradiction. There is no claim that all 515 prefix actions can
already be discarded. Applying the stronger joint constraint at the start
requires new terminal-support derivations; the old middle trace still has
its old ancestry.

The additional `Compact/Geometry/ChordRadius.lean` supplies an actual analytic
bound over the whole unit arc. It removes angle-specific chord certificates
for the last root-one follower once its coarse center bound is established.
The harder next follower reduces to `98X+49(C+S-2CS)-347 ≥ 0`; its precise
unproved ancestry is recorded in the terminal report.

## Replace repeated propagation by sparse inequality derivations

Let the actual normalized packing coordinates be `z`, including centers,
orientation parameters and the common side. An affine fact has the form
`f(z) ≥ 0`, together with a strictness bit when `f(z) > 0` is known.

For a single convex branch, if

\[
                  g=\sum_i\lambda_i f_i,\qquad \lambda_i\ge0,
\]

then the facts `f_i ≥ 0` imply `g ≥ 0`. If a positive coefficient multiplies
a strict premise, then `g > 0`. This is the existing Farkas semantics. The
change is to retain only facts requested by the terminal proof, recursively
retaining their nonzero supports, and to substitute through intervening
relaxations. Intermediate facts can be shared as acyclic nodes when direct
substitution would make coefficients or support sets grow.

For example, if `g = 2 f₁ + f₂` and `h = 3 g + 4 f₃`, the final certificate is
`h = 6 f₁ + 3 f₂ + 4 f₃`; neither a domain containing `g` nor any of its other
rows is part of the final certificate. Combining such derivations is exact
rational arithmetic. A global check must bind every root fact to actual
geometry; an index into an unverified terminal domain is not a root fact.

This is especially suitable for C696 border transfers. The final root-one
transfer only needs specific facts about owners 4, 10 and 2, plus strict hull
points. Its current certificate already isolates center boxes, angle bounds,
displacement bounds and follower chord bounds. Those are the backward proof
goals. Proving every row of every earlier domain is unnecessary.

At a genuine nonconvex split, both branches still need proof. An implication
valid on one angle interval cannot silently replace coverage of all angles.
Closed cut ties remain in the cover, and strictness must survive every
composition. Different branches may share a child only after checking its
actual premises, not merely by comparing a hash or displayed name.

### Close a propagation cycle simultaneously

Repeated bound-tightening often approximates a simultaneous linear solution.
Suppose scalar deficits `d_i` satisfy, from actual geometry,

\[
             d_i\ge\sum_j A_{ij}d_j+h_i,
             \qquad A_{ij}\ge0,\quad h_i\ge0.
\]

A nonnegative rational matrix `W` satisfying `W(I-A)=I` proves all `d_i ≥ 0`
by taking nonnegative linear combinations of these premises. The matrix
identity and coefficient signs are the finite certificate. They replace an
arbitrarily long relaxation history. Usually only the rows of `W` needed at
the terminal are necessary, and they may be sparse.

Here is a complete hand-worked example. From

\[
              3x-2y\ge1,\qquad 3y-2x\ge1,
\]

multiply the first inequality by `3/5`, the second by `2/5`, and add to get
`x ≥ 1`. Reversing the weights gives `y ≥ 1`. This replaces any number of
alternating lower-bound updates. If both right sides are `1+ε` with `ε>0`,
then their sum yields `x+y ≥ 2+2ε`, contradicting `x+y ≤ 2` in one step.

An equivalent qualitative criterion is a positive vector `w` and `ρ<1` with
`Aw≤ρw`. If some `d_i` were negative, choose a minimum `m=d_i/w_i<0`. Then
`d_i≥Σ A_ij d_j≥m(Aw)_i≥mρw_i>mw_i=d_i`, a contradiction. The reversed
inequality in the third step is essential because `m<0`.

**Unfinished application obligation:** no such grounded matrix or direct
dual certificate has yet been found for a full C696 or C976 residual branch.
A proposed target state being preserved by propagation is insufficient and
would make a circular proof. The premises above must hold for the actual
initial packing without already assuming the deficits are nonnegative.

## Eliminate the angle grid where analytic inequalities suffice

An oriented square with center `(X,Y)`, side `a` and half-angle parameter `t`
has

\[
 c=(1-t^2)/(1+t^2),\qquad s=2t/(1+t^2).
\]

For a fixed point `(p_x,p_y)`, strict membership is exactly four polynomial
inequalities after multiplication by the positive number `2(1+t²)`:

\[
 a(1+t^2)\mathbin\pm2((1-t^2)(p_x-X)+2t(p_y-Y))>0,
\]
\[
 a(1+t^2)\mathbin\pm2(-2t(p_x-X)+(1-t^2)(p_y-Y))>0.
\]

Thus many marker/face implications can be proved on an entire signed angle
interval by a single polynomial identity and nonnegativity facts. The
existing C696/C709 transfer lemmas already follow this analytic pattern;
retain those proofs instead of exporting their consequences for 64 or 128
individual angles again.

For two squares, the separating-axis theorem gives the four axis directions
of the pair. With common side `a`, the radius sum on the first square's axis
is `a/2 * (1 + |cos(β-α)| + |sin(β-α)|)`. Canonical orientations make the
relative cosine nonnegative; the remaining absolute-value sign can be
handled by the closed split between the two angle orders. After clearing
positive denominators, these are low-degree polynomial conditions. A
small, selected contact configuration can use them directly, rather than
pairing every source-angle bin with every neighbor-angle bin.

Do not enumerate eight separating-axis choices for every pair of twelve
squares. Use existing marker/face geometry to eliminate impossible axes
first, and split only on the surviving local alternatives. Otherwise the
polynomial reformulation simply moves the combinatorial explosion elsewhere.

For nonlinear remnants, a rational sum-of-squares identity is a possible
certificate mechanism. Every multiplier, denominator condition, sign and
polynomial identity must be checked in Lean. An optimizer's feasibility
report is not a proof. Credit Muhammad Maaz's SOS work at
<https://mmaaz.ca/writings/sostactic.html> if that route is used. No SOS
certificate was computed in this audit, and no claim is made that a useful
low-degree certificate exists for the remaining cases.

## Bounded source measurements: simple pruning is insufficient

The local saved C696 candidate traces were inspected without executing their
geometry. Object sizes below count each referenced domain/hull object once,
after gzip decompression; they are **candidate states, not proof certificates**.

| Trace | Actions | Unique candidate objects | Decoded object bytes |
|---|---:|---:|---:|
| Root one | 105 | 153 | 989,240 |
| Root-zero common prefix | 515 | 606 | 3,169,810 |
| Root-zero low tail | 48 | 93 | 412,675 |
| Root-zero right tail | 189 | 307 | 957,123 |
| Root-zero middle, 64-angle segment | 168 | 260 | 610,085 |
| Root-zero middle, 128-angle segment | 29 | 54 | 182,894 |

All 515 common-prefix steps change their state. All low/right/middle actions
also change it. The one unchanged state in root one is terminal border
action 104: it proves the contradiction and cannot be deleted as a no-op.
An owner-level backward scan of root one, conservatively treating walls as
reading all owners, only suggests removal of actions 98–102; it still needs
a formal projection of kernel updates. This is nowhere near the required
order-of-magnitude improvement.

Six generated root-one pair files and eleven generated root-zero prefix
files have empty support tables. Together these contain only 17,941 lines
and 1,074,364 bytes. Their representations change through pure relaxations
but they add no pair-overlap certificate. Even eliminating these entirely
would leave the dominant cost intact. Their downstream implications must
still be composed from earlier facts.

The small raw state corpus compared with the giant exported source shows
that explicit evidence and repeated conversions, rather than just stored
coordinates, dominate growth. It does **not** show that a small decoder will
compile quickly: computing the same huge proof inside Lean can be slower.

## Concrete completion skeleton and acceptance criteria

The compact development should expose these obligations in this order:

1. Original-packing normalization and marker/ownership coverage. Reuse the
   checked mathematics, including all boundary cases; compact their data
   independently of the geometric case work.
2. A physical symmetry normal form for each case, including the new C696
   joint-center inequality where applicable.
3. A small list of terminal requirements: point ownerships, support/chord
   inequalities or an empty branch. Keep the actual strictness and angle
   premises in their statements.
4. Backward sparse linear derivations for those requirements. Retain only
   genuine sign/ownership/angle splits and shared facts with sound ancestry.
5. A direct analytic or rational polynomial certificate for each unresolved
   nonlinear implication. An empty skeleton entry is an open mathematical
   obligation, never a successful certificate.
6. Complete coverage, case exclusions and final original theorem assembly.

Before exporting a complete large case, demonstrate an entire compact
exclusion on C709 or a complete C976 vector, including its original initial
coverage. A tiny checker unit test, a single transition or an assumed final
domain is not the required pilot. Record total proof data bytes, number of
nonzero certificate coefficients, coefficient bit lengths, full import
closure, peak memory and compile time, as well as source lines.

Under 300,000 lines of assembled material and under 1,000,000 eventually are
reasonable **admission budgets for the new build**, not established bounds
on a known complete proof. The current evidence does not justify confidence
that all cases will fit merely by using this architecture. The real gate is
a complete compact hard-case certificate and compression of the already
proved legacy exclusions; their historical dependency closure is itself
large. A failed pilot must trigger more symbolic mathematics, not another
million-line export or an unchecked computational shortcut.

## Sources inspected

All paths below are within the current source checkout
`LOCAL_PATH/n12-jatloe419`.

* `Completion/Cases/C696/RootOne.lean`, `RootZeroSymmetry.lean`,
  `CornerReduction.lean`, `SideSignPacking.lean`, `BorderTransfer.lean`,
  `NegativeBoxTransfer.lean`, `TransferFrame.lean`.
* `Completion/Cases/C696/RootOneStep000Data.lean`,
  `RootZeroPrefixN64Step151Data.lean`, `Border104Owner4Data.lean`, and the
  generated data-file families used for the small bounded measurements.
* `Completion/Cases/C976/CompactPruning.lean`, `CompactPair.lean`,
  `CompactSupport.lean`, `CompactTrace.lean`, `CompactGeometry.lean`,
  `Compact/BasisData.lean` and the pair exporter.
* `evidence/C696/root-one/trace.json`, the five `root-zero/trace-*.json`
  segments, and their already local compressed candidate-state objects.

The legacy source was not changed. The mathematical statements and geometric
semantics remain those of the original proof.

## New three-square shortcut: a stronger theorem, not another trace export

The subsequently discovered `s12-density-and-signs.zip` contains a written
three-square forced-point argument, five recorded applications, and exact
rational research checks. Its own documentation explicitly leaves Lean and
inherited prefix validity open. No script in that archive was executed for
this work; the small mathematical text was read directly from the ZIP.

The following new source is now assembled:

* `Compact/Geometry/ThreeSquareForcedPoint.lean` proves whole-angle analytic
  bounds, three automatic corner faces for each target-angle sign, uniform
  separating-direction exclusions, relative-support coefficient bounds, and
  the height consequence of a wall/chord-radius bound.
* `adapters/ThreeSquareOriginal.lean` proves `forced_point` for the original
  `OpenSquare` objects, by composing those new bounds with the existing C709
  endpoint and negative-transfer theorems. Its conclusion is actual strict
  `A.Inside 1 1`, not an ownership surrogate or a proposed checker result.

Both are newly written source without a fresh Lean replay by this worker.
The adapter remains outside the active core until its original geometry
dependency closure is recovered and checked. There is no new axiom,
admission, native computation, generated angle enumeration, or certificate.

### Exact strengthened statement

Let A, E and D be the original open squares, each of side greater than one.
Their side lengths need not be equal. Assume:

1. A and E have `c >= 35/37`, `|s| <= 12/37`.
2. `1 <= X_A <= 3/2`, `2 <= X_E <= 5/2`, and `X_E <= X_D`.
3. A and E have heights in `[1/2,1]`.
4. A and D are contained in the container; A/E and E/D have disjoint
   interiors.
5. The middle square E contains `(2,1)` in its closure.
6. E and D each have an actual strict horizontal section on `y=35/72`,
   whose length is at least that square's side.

Then `(1,1)` is strictly inside A.

This is stronger than the archive's stated theorem: **A needs no long
section**; D needs no angle bound beyond whatever establishes its section;
the centers' vertical differences may be as large as `1/2`; and no
three-section midpoint sorting or global `3a <= 4` deduction is needed.
The original common-side and radius hypotheses imply these premises, once
the existing radius-to-section theorem is available. The angle bridge is
proved directly for every rational half-angle `z` with `|z| <= 1/6`.

### Hand-worked proof and why it compresses the terminal

Write `u = c(1-X) + s(1-Y)` and `v = -s(1-X) + c(1-Y)` for the target's
two centered face coordinates at `(1,1)`. The target box gives
`0 <= X-1 <= 1/2`, `0 <= 1-Y <= 1/2`, and `c <= 1`.

If `s >= 0`, then `-1/2 <= u <= s/2 <= 6/37` and `v >= 0`.
Thus the side being greater than one leaves only the upper face as a
possible exclusion. If `s <= 0`, then `u <= 0` and
`-6/37 <= s/2 <= v <= c/2 <= 1/2`. Only the left face can exclude the point.
These are the new scalar lemmas `corner_nonnegative` and
`corner_nonpositive`, with the zero-angle case retained.

For positive sine, the existing C709 endpoint calculation applies at
`h=35/72`: `c+s-1 <= c*h` and `h*(1+c) <= c` follow uniformly from the
component bounds. Failure of upper-face containment creates an actual
target section with left endpoint before its center and right endpoint
strictly past `1 + side_A`. Every follower long section crosses its own
center abscissa. Disjointness and the ordered centers therefore force the
two followers after the target and in order. They add at least two more
units of length, so the last endpoint is greater than four. This contradicts
D's containment. This argument uses the real sections, not a motion or
rearrangement of squares.

For nonpositive sine, apply the existing C709 negative-transfer theorem.
It suffices to verify its SAT and relative-angle premises. For either A or
E, put `dx=X_E-X_A` and `dy=Y_E-Y_A`. Then

`|-s*dx+c*dy| <= (12/37)*(3/2)+1/2 = 73/74 < 1`,

and `c*dx+s*dy >= -6/37 > -1`. Thus perpendicular and backward
separating normals are impossible. The two forward alternatives are
handled by the original weak-contact separating-axis proof and closed
point support. For its relative coefficient
`k=(c*S-s*C)/C`, the component bounds give
`c*C+s*S >= (35/37)^2-(12/37)^2 > 0` and
`C*k <= 24/37 < C`, hence `k <= 1`. The target height is at most one,
which is stronger than the negative-transfer cap `3/2`.

There are only two mathematical branches, the target's sine sign. No
ordering of three angles or comparison of corner-angle polynomials occurs.

### Exact remaining original-premise obligations

The terminal theorem does **not** establish any of the five case entries:

| Representative | A,E,D | Coordinates | Candidate entry |
|---|---|---|---|
| canonical 696 | 0,9,2 | original | research8/slanted-chordpilot-0-strip.json |
| canonical 974 | 0,9,2 | original | research8/n9-network-r1-974-0-point-01.json |
| canonical 977 | 0,9,2 | original | research8/n9-network-977-0-point-01.json |
| mixed 696 | 0,9,2 | original | research16/missing696-1-chordstrips.json |
| missing-1 974 | 1,8,4 | transposed | research17/push974-0-clean-0-segments-seed.json |

For each entry, one must still prove original normalized-packing membership
in its continuous enclosures, retain every actual parent deduction needed
for those facts, establish the chosen signed frames, certify the two
followers' radius bounds, and derive E's **closed** point containment from
its compulsory hull. The missing-corner hypothesis must then exclude
A's **strict** ownership. Owner distinctness supplies the disjointness
premises, and the transpose must preserve the exact missing selector.
The archive's inherited symmetry transport of five representatives to eight
labels is not a newly checked coverage proof here.

The original C709 modules `PointTransfer`, `UpperEndpoint`, and `SignedFrame`
are available in the sparse legacy checkout, but their import closure is
not wholly restored in the refactor. In particular the original
`S12.SquareAxes` and `S12.LongChordGeometry` source gap is material. Do not
replace either by an assumed declaration. The adapter's local proof is
assembled; a complete original-model replay still awaits that closure.

The archive reports candidate entries twenty and nine saved parent links
earlier for mixed696 and missing-1 974. Those are ancestry-link counts, not
certified Lean operations removed. The strengthened theorem may permit
earlier entries still because it drops A's chord and D's angle requirements;
that is an actionable next scan, **not** a completed further shortening.

This removes a substantial terminal argument but does not by itself solve
the large prefix problem, the seven existing large exclusions, or the
forty baseline eliminations outside the other archive's 59-case shortcut.

### Subsequent replacement of the missing geometry closure

The missing-library limitation in the preceding subsection describes the
**first adapter draft**. It is now superseded by a new compact source route:

* `ThreeSquareSupport.lean` proves closed support bounds, the signed bottom
  wall bound, center crossing of every certified section longer than one,
  and weak interval ordering directly for the original `OpenSquare`.
* `ThreeSquareOriginal.lean` proves `forced_point_compact` using those facts,
  the compact `BorderEndpoint` calculation, and the independently recovered
  `Compact.Bridge.CongruentSAT`. It imports no legacy `SquareAxes`,
  `LongChordGeometry`, `ClosedPointSupport`, or C709 proof module.
* `ThreeSquareRadius.lean` proves `forced_point_of_radius`, which supplies
  all section hypotheses using the other worker's new global theorem
  `LongSectionGeometry.horizontal_long_section`.

Consequently there is now an assembled **complete terminal theorem at the
original radius interface**, with no assumed SAT or long-section theorem.
It retains the original normalized packing's equal sides and
`1<a<=1001/1000`. The side cap makes every square's horizontal half-width
less than one, so even an arbitrary open subinterval of length greater than
one crosses the center abscissa. This replaces the first draft's stronger
`length>=side` follower interface with `SectionCapacity.LongSection`.
The side cap is already a field of the original `NormalizedPacking`; no
stronger condition on actual packings was introduced.

The direct three-square source comprises four files and 619 lines before
the parent's validation repairs. Its shared support includes the new global
section and congruent-SAT modules, whose source sizes and validation are
tracked by their respective workers. The earlier optional adapter remains
as a comparison draft and must not be counted as an additional proved case.

This worker did not compile any of these files. Source was frozen and handed
to the parent for one serial dependency-ordered replay. All five case-entry
and global coverage obligations above remain open until separately
discharged. In particular, a checked terminal theorem is not a continuous
proof that the original C696 branch reaches its proposed entry enclosure.
