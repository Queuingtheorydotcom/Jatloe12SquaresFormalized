# C981 rows 34/41: complementary signed-sector handoff

Checkpoint: 2026-10-11. Investigation is frozen for the requested publication
and handoff. This note records the complementary work assigned to the
midpoint worker. **There is no new whole negative-C exclusion, no whole
row-34/41 exclusion, and no new original-vector adapter from this worker.**
No Lean compiler, solver, numerical search, or generated certificate was run
for this checkpoint. All mathematical statements below distinguish retained
source from proposed continuation. The parent owns integration and the
authoritative remaining-case count.

Read this alongside `audit/HANDOFF-C981-POSITIVE.md` and
`audit/C981-OUTER-TOP-ORDINARY-WALLS.md`. The former records the kernel
worker's frozen positive-C reductions and their exact validation status.

## Frozen work and ownership

The substantive source currently available is:

* `Compact/Geometry/OuterTopElbowFaces.lean`;
* `Compact/Geometry/OuterTopElbowReach.lean`;
* `Compact/Geometry/OuterTopElbowOpposite.lean`;
* `Compact/Geometry/OuterTopElbowCentralReach.lean`.

These files belong to the kernel worker; this checkpoint does not edit
them. The midpoint worker independently hand-reviewed the complete signed
A/C SAT classification in `OuterTopElbowOpposite`, and the original
central-reach point and its earlier angle argument. The later strengthened
`5*S<C` angle and final `only_a_axis` addition have the separate review
status recorded in the positive handoff. Do not silently promote an earlier
review of an earlier version to a review of every final addition.

No complementary geometry module was started before the publication
freeze. The only new file produced by this final task is this handoff.
The kernel worker retained positive-C/positive-B; the complementary
assignment was negative C with both B signs, with positive-C/negative-B
as an alternative if it yielded a shorter complete sector. Neither
complementary branch was completed.

## Actual chart, owners, and hypotheses

The chart is `Transform` value `⟨true,false,true⟩`: original coordinates
are `(new_y,4-new_x)`. Names in the generic geometry may call C `D`.

| Role | Original owner | Genuine points in this chart |
| --- | --- | --- |
| A | 5 | (2,2.26), (2.26,3), (2.35,2.35) |
| B | 6 | (1.65,2.35), (1,2.26), (1,2.4) |
| C | 7 | (1.65,1.65), (1.74,2), (2,1.74) |
| bottom wall | 8 | (2,.914), (1.6,1), (1.74,1) |
| right wall R | 9 | (3.086,2), (3,2.26), (3,2.4) |
| top wall T | 10 | (2,3.086), (1.6,3), (1.74,3) |
| left wall L | 11 | (.914,2), (1,1.6), (1,1.74) |

Owner 2 supplies the paired corner (3,3); owner 3 supplies (1,3).
C's strict center (2,2) and crosspoints (1.5,2), (2,1.5) have existing
original-packing ancestry. A final adapter must actually invoke and
transport those results. They must not become anonymous additional
assumptions in a purported whole-vector theorem.

B genuinely excludes C's point (1.74,2) and center (2,2), the actual L
marker, the paired corner (1,3), and all derived T points. C genuinely
excludes the NW/SE/NE central markers, Q=(2.26,2), and the listed foreign
left/bottom-wall points. Preserve the full B/C/L and C/bottom-wall
disjointness whenever using these exclusions or a support cycle.

The square side is the original common side, strictly above 1. Real
container bounds, exact orientation normals, and actual pairwise
disjointness remain available. A side upper bound must be stated if used;
none may be inferred from a local drawing or a saved pose.

### Essential row distinction

Row 34 has A pattern `{8,16}` and A misses Q. Row 41 has A pattern
`{4,8,16}` and A owns Q. Both have ordinary R pattern `{6,15}`.
**Neither row supplies R with the diagonal point (2.4,3).**

The row-34 missing-Q argument gives `2*A.c<A.s`. With the genuine
R(3,2.5) it yields strict A(2,2.5), A(2.18,3), and then T(1.4,3).
Row 41 currently has only `A.c<A.s` and the common T(1.44,3) reach.
It does not inherit any result whose entrance needs `2*A.c≤A.s`.

## Exact negative-C source conclusion

Write A=(c,s), with c>0, s≥0 and `2*c≤s`, and let C be any signed
canonical frame with C.c>0 and `|C.s|≤C.c`. The public theorem
`OuterTopElbowOpposite.alternatives` takes:

* `1<A.side` and `A.side=C.side`;
* `AhiU≤2.4*c+3*s` and `2.5*c-3*s≤AloV`;
* A's strict points (2,2.26), (2.35,2.35);
* C's strict center, SW marker, and bottom crosspoint (2,1.5);
* actual A/C interior disjointness.

Its complete conclusion is exactly

```
upper C c s ≤ AloU
or
ChiV ≤ lower A (-C.s) C.c.
```

The theorem checks both square-owned SAT frames and both directions of
each axis. In particular, when C.s<0 the eliminated forward C.U mode
already conflicts with A(2,2.26) and C(2,2). Reverse directions are
removed using strict original markers. The surviving C.V separator is
not discarded for negative C.

This is the strongest frozen negative-C reduction from the present
assignment. It is applicable to the currently established near-vertical
row-34 entrance, not automatically to row 41. There is no source theorem
here forcing a negative-C angle bound, a new negative-C left reach, or
either B sign. The positive-only theorem `only_a_axis` cannot remove the
negative-C C.V alternative.

## Exact open obligation

For row 34, close the negative-C branch for both canonical signs of the
actual B owner, retaining both displayed A/C separators until each is
genuinely excluded. Use the actual B/L/bottom-wall squares and the actual
top/paired-corner exclusions. An isolated A/C angle or point implication
is not a full ending.

For row 41, first supply a valid replacement for the missing-Q narrowing
entrance, or directly exploit its additional strict A point Q. The
row-34 reduction cannot be installed as a row-41 ending by weakening its
hypotheses informally.

Neither branch has an original owner/frame wrapper at this checkpoint.
After a continuous geometric ending is found, its wrapper must still
derive all points/exclusions from the original catalogue row, choose
frames preserving each physical square, retain the original side and
container facts, and cover all signs. No pending row may be removed
before that complete original exclusion exists.

## Alternative positive-C/negative-B continuation

This was inspected briefly but not sourced. It may be shorter than the
negative-C cycle and should be coordinated with the positive worker.

The genuine positive-C APIs are:

* `OuterTopElbowCentralReach.angle`: `5*C.s<C.c` under its stated
  near-vertical A hypotheses and either A/C selector;
* `upper_u`: C's exact missing Q, center, and bottom crosspoint give
  `ChiU≤2.26*C.c+2*C.s`;
* `point`: under the weaker `2*C.s≤C.c`, side>1 and the actual two
  crosspoints, C strictly contains (1.3,1.9).

An unsourced but short proposed next bridge is the lower-V face forced
by C's actual missing bottom-wall point (1.6,1):

```
CloV ≥ C.c-1.6*C.s.
```

Its intended proof checks the other three strict bands: the upper-U cap
and side>1 give the lower-U band using `.66*C.c+C.s<1`, while the center
gives the two upper bands. This argument is positive-C only.

`FullAuxWallPositiveCNegativeB.impossible_of_transverse` is already a
source consumer for exactly that face. It requires positive canonical C,
negative canonical B, both sides>1, Ccenter, B's NW marker and (1,2.4),
B missing the true T point (1.6,3) and paired corner (1,3), and one of

```
ChiV ≤ lower B (-C.s) C.c
or
upper C (-B.s) B.c ≤ BloV.
```

Its original premises are relevant here, but a complete new B/C selector
reduction has not been written. The new C(1.3,1.9) is weaker in the
relevant direction than the old sharp left reach. For B=(b,-t), one
potential remaining mode is

```
BhiU ≤ lower C b (-t).
```

The direct point comparison eliminates it only when
`.35*b-.45*t≥0`. Thus steep negative B cannot simply be omitted.

A hand-derived support upper bound for this remaining mode, using C's
upper-U cap, side>1, and strict C(1.5,2), gives the necessary positive gap

```
b*(.35+.26*C.c^2-C.c-.5*C.s^2)
 + t*(.35+C.s-.76*C.c*C.s) > 0.
```

This is an exploratory reduction, not a new Lean API or a completed
scalar contradiction. The bound `5*C.s<C.c` alone was not shown to
contradict this expression uniformly. Do not assert that it closes
steep B. Possible next steps are to retain the actual A.U support
correlation, derive a stronger genuine C point, or use the full B/L/T
cycle. Any stronger angle bound must be proved, not inserted as a
numerical cutoff.

## Failed shortcuts and preservation rules

1. The successful diagonal-wall endings for other vectors use a point
   absent from these ordinary-wall rows. They are not drop-in endings.
2. The old `C981FullAuxNegative` route's C(1.1,2) or C(1.2,1.9) came from
   a different A clearance. Those points have not been derived here.
3. Positive-C `5*S<C`, its missing-Q upper-U face, shifted point, and
   `only_a_axis` cannot be applied to negative C by changing a sign in
   the notation. Reflection also changes the original ownership chart.
4. The cap-only C/B/L route does not receive the old tiny central excess
   bound for free. Here the genuine positive-C upper-U excess is bounded
   by `.26*C.c`, not `.001` or `.1`.
5. A local A/C/R/T/E placement was hand-proposed in the earlier audit.
   It omits B and the left/bottom cycle and has not been independently
   exact-verified. It is neither a full-packing counterexample nor proof
   of local feasibility. Its role is to warn against dropping real
   neighboring squares from a claimed ending.
6. Owning a point at y=3 does not give `loY≤3-side`; the withdrawn axis-T
   shortcut must not be revived. No retained source uses it.
7. The span from C(1.5,2) to T(1.4,3) on a positive B.V axis is
   `b+.1*t`, not `b-.1*t`. T(1.5,3) follows by strict convexity only after
   the actual T1.4 and T1.6 points are available.

## Resume and validation order

1. Read the two handoffs and the exact current source signatures.
2. Choose one complete signed branch; coordinate ownership before edits.
3. Preserve the original negative-C two-selector contract, or close the
   remaining positive-C/negative-B longitudinal selector with real
   geometry. Do not produce another claimed whole ending with an
   unproved local premise.
4. Bind the resulting theorem to original row data, separately respecting
   row 34 versus row 41.
5. Only after full assembly, perform the user-authorized Lean replay and
   axiom audit. This handoff itself does not authorize computation.

The publication freeze leaves the original theorem and residual count
unchanged by this complementary C981 work.
