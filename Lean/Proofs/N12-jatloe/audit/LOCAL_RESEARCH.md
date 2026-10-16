# Earlier local mathematical simplifications — 10 October 2026

Read-only audit of three newly identified local archives. Archive titles and internal completion claims are treated as evidence to investigate, not as accepted mathematical or Lean results. No bundled program was executed and no nested archive was extracted. Selected text and source manifests were read directly through `zipfile`, staying below 10 MB of uncompressed content read.

## Archive inventory and trust boundary

| Archive | ZIP bytes | Files | Total uncompressed member bytes | Lean source |
|---|---:|---:|---:|---|
| `s12-earlier-case-shortcuts.zip` | 3,414,734 | 160 | 11,206,655 | None |
| `s12-proof-complete.zip` | 481,603,345 | 91 | 487,364,720 | None at top level or in the two nested manifests |
| `s12-density-and-signs.zip` | 1,600,317 | 58 | 35,901,180 | None |

The large complete-proof ZIP contains a 476,710,108-byte research snapshot and a 2,661,992-byte checking-source subset. Their manifest tables contain 30,028 and 1,197 files respectively: neither lists a `.lean` file, `SquareAxes`, or the original Lean certificate exporter. Therefore these archives **do not recover `S12/SquareAxes.lean` or any matching original Lean source/interface**. The large nested snapshot was not read/extracted. Its README warns that full expansion is about 12.2 GiB; it must remain archived under the local disk limit.

The complete package reports an exact computer-assisted proof of `s(12)=4`, with a final record saying no labelled subdivisions remain. It explicitly is **not a proof-assistant formalization**, and retains published Bentz covering and corrected singleton-forcing geometry as starting premises. Its final joins, source hashes and written lemmas do not replace Lean proofs or the unrestricted ancestry checks. This audit did not rerun those joins or leaf certificates.

## Main new simplification: 59 cases in the large baseline

The earlier-case supplement has a precise 59-row `case-index.json`. **None of its 59 case IDs occurs in the eighteen-case Lean frontier.** Thus it can replace 59 of the 99 cases removed by the historical 117-to-18 reduction; it does not directly replace any of the seven replayed exclusions or any remaining survivor.

Its replacement uses a shared capacity fact: a line of length four can contain long sections from at most three disjoint-interior squares of common side `a>1`. Consequently, seven distinct squares each forced to cross at least one of two cuts in a section of length at least `a` cannot fit. The proof needs only an incidence count, not a choice of the cut used by each square.

| Finish | Cases | Previous corner/wall records replaced |
|---|---:|---:|
| Four long sections on one cut | 52 | Part of 125 total |
| Seven owners each hitting at least one of two cuts | 7 | Part of 125 total |
| Total | 59 | 125 |

The two-cut cases are 405, 985, 990, 1063, 1064, 1069 and 1078. The finite source enclosures cover full angle intervals and center polygons; the final checker examines all changes of cut-incidence pattern at exact endpoints and intervening intervals. This is a continuous-coverage claim, not a finite-sample argument. It still needs formal enclosure/coverage proofs.

The 59 stored case-state JSON files total **2,784,173 bytes**, dramatically smaller than the old Lean reduction source. Their recorded changes during a single pair pass total **2,421 pair operations**, ranging from 35 to 44 per case. Those records are states and replay recipes, not complete Lean certificates; these small input sizes are promising but do not certify a final Lean-size bound.

The generic verification script always checks the final capacity certificates and reconstructs the shared template. Fresh reconstruction of each case's initial enclosure and pair pass is behind `--replay`; the default verification is therefore not automatically a fresh replay of all 59 cases. No replay was run by this audit.

### One five-step four-square theorem removes twelve individual case calculations

The supplement provides a shared local theorem on four squares A,B,L,R. Its stated premises are twelve required points (three per square), six excluded points, common side `1<a≤1001/1000`, box containment and disjoint interiors. It requires no complete original marker grouping, wall-sign choice, or other eight squares.

Its source recipe uses 32 full angle bins and five pair deductions:

1. Prune B against L.
2. Prune A against B.
3. Prune B against A.
4. Prune L against B.
5. Prune R against A.

All four then have long sections on `y=12/5`, contradicting capacity. Its hypotheses are supplied by original compulsory hulls/marker exclusions for cases **28, 537, 556, 565, 567, 569, 570, 575, 576, 1085, 1086, 1087**. These twelve are included in the 59; do not add them again. Three further template matches (78, 577, 585) have simpler original arguments and are explicitly left unchanged.

The template replay deliberately uses zero dummy auxiliary labels; it reconstructs only the stated positive/excluded point hypotheses. This makes it a good shared theorem boundary for the refactor. A valid Lean implementation still needs the initial all-angle enclosure theorem, five sound pruning steps, four long-section facts and the geometric capacity theorem.

### Precise limits for the seven existing case proofs

The broad screen includes all seven 701, 713, 717, 898, 973, 978 and 979. Their recorded one-pass capacity scores remain at or below the available capacity; none enters the 59 successful cases. It also fails to close 976, 1089, 1090 and 1091. Therefore this supplement does **not** solve the 2.12 GB seven-case closure problem identified in `LEGACY_COMPRESSION.md`. It solves a different major part of the baseline simplification problem.

## C709's unsplit point-transfer shortcut is already present in current source

The earlier-case archive's eight-point appendix gives an unsplit C709 exclusion at the original 117-case input. Its route uses the original unique F/G masks, initial enclosures, **36 changed pair operations and four point-ownership transfers**, stopping when owners 0 and 1 both contain `(1,1)` strictly. This matches the existing checkpoint C709 source route; it is useful mathematical provenance, not additional progress to count twice.

The two shared ingredients are a positive-angle endpoint obstruction (A itself need not have a full-length chord) and a negative-angle point-inheritance lemma. The latter only requires `Y_A≤3/2`, bounded half-angles and suitable separating-direction exclusions. The evidence explicitly keeps zero-angle and missing-point boundary cases. It avoids the older four corner-mask certificates, sharper wall polygons, later hull updates and chord pruning.

The same procedure forces four side midpoints in C696 without a contradiction. It does not close C696.

## Three-square terminal shortcut for C696, C974 and C977

`EARLIER_THREE_SQUARE_PROOF.md` in the density/sign supplement gives a substantial written simplification: three squares beside one wall can replace the older terminal six-square/two-wall argument and its later four-square angle comparison.

Its explicit local statement assumes common side `a>1`, disjoint interiors, containment in `[0,4]^2`, and for each of A,E,D the half-angle bound `|tan(theta/2)|≤1/6`. Set `h=35/72` and `R(theta)=(cos(theta)+|sin(theta)|−2cos(theta)|sin(theta)|)/2`. Assume:

- `1≤X_A≤3/2`, `2≤X_E≤5/2`, `3≤X_D≤7/2`;
- `Y_i−h≤R(theta_i)` for all three squares;
- `(2,1)` belongs to E (closed containment suffices).

Then `(1,1)` lies strictly inside A. The transpose is also available. The proof compacts the three horizontal sections for counting, without asserting any collision-free movement of the squares. The resulting endpoint bound cancels center coordinates against separating-axis and wall inequalities. No comparison between the three angles is assumed.

Its reported five applications are canonical 696, canonical 974, canonical 977, mixed 696, and missing-1 974. Existing symmetries make these five representatives cover the eight final labels. The mixed696 and missing-1 974 premises already hold respectively 20 and 9 saved ancestry links before their old terminal states. Those are link counts, not independent case counts.

This is meaningful mathematical shortening, but the ZIP explicitly reuses earlier prefix validity and symmetry coverage without rerunning them. The lemma's source-state premises must be derived from actual normalized packings. **It does not bypass the inherited prefixes or establish that the whole local C696 trace can be deleted.** Determining the earliest certified entry for the new lemma is a high-priority refactor task.

## Sign-only version and density experiments

`SIGN_LEMMA.md` removes the premise that the middle square contains `(2,1)` and gives a weaker but simpler consequence. If three squares have ordered long sections on `y=h`, `0<h≤1/2`, with `X_A≥1`, `Y_A≤1`, nonnegative angle for A and `cos(theta_A)≥h/(1−h)`, then A strictly contains `(1,1)`. Hence a missing corner forces A's angle negative under the same bounds.

The recorded applications remove some orientation/center components in two C709 states and one local C981 branch. Subsequent exact propagation did **not** close those branches. The full three-square scan's successful C981 matches merely recover ownership already present; successful old C709 experiments have unproved corner assumptions and cannot be adopted as exclusions. The 1092 inputs fail the required premises. No new whole-case closure is claimed.

Area and density searches also did not produce a usable exclusion: recorded forced-empty-area estimates remain below four; finite-profile density objectives do not exceed the required threshold. Their numerical failures do not prove that all stronger density arguments fail. These experiments should not consume the initial refactor budget ahead of the explicit capacity and three-square lemmas.

## Recommended changes to the refactor plan

1. Put the geometric long-section formula and one/two-cut incidence capacity theorem in the shared library. A purely combinatorial count is only the last step; prove that actual square intersections supply the claimed lengths.
2. Formalize the local four-square template once and discharge its twelve case applications by verified hull/point transport. Use the other 47 capacity certificates to replace their longer baseline routes.
3. Reuse current C709's source route while replacing its data-heavy pair certificates with the shared compact checker; the archive confirms its exact mathematical ancestry.
4. Formalize the three-square forced-point lemma and bridge each of its five applications to the earliest justified prefix. Avoid rebuilding the obsolete terminal six-square/angle-comparison tails if the new entry premises are established.
5. Continue independent compression of the seven verified exclusions and remaining 40 baseline eliminations. The new 59-case result is a valuable partial classification simplification, not a universal replacement.

No archive in this audit adds a compiled Lean theorem. The written lemmas, exact rational checker source and recorded applications provide concrete routes for the new formalization, with explicit remaining coverage and semantics obligations.
