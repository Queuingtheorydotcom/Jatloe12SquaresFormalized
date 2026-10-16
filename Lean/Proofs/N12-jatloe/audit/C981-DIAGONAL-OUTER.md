# Diagonal endpoint exclusion

Status: complete mathematical argument and uncompiled Lean source. No compiler,
solver, generator, search program, or network task was run for this result.
The whole C981 pending partition is owned by the root task and was not edited.

`Compact/Geometry/DiagonalOuterPoint.lean` proves `point` and `impossible`.
The sole size assumption is **side > 1**. Neither a side upper bound nor
container containment is used, including in the original-vector adapter.

Let an open square own A=(2.26,3), C=(3,2.26), and miss
D=(2,2.26), E=(2.26,2). Then it owns F=(2.4,3) or G=(3,2.4).

Choose a positive face frame, with U=cx+sy, V=-sx+cy,
c>0, s>=0, c²+s²=1. First take s<=c and suppose G is missing.

1. At D, upper U and both V bands follow from the strict A/C bands.
   Thus U(D)<=loU.
2. At G, lower U and both V bands follow from A/C. Thus
   loU+side<=U(G).
3. Subtracting gives side<=c+0.14s, and hence c+0.14s>1.
   If c<=3s, then
   (c+0.14s)²-1 = 0.28cs-0.9804s²
   <= -0.1404s² <=0, a contradiction. Therefore 3s<c.
4. F lies strictly inside all four bands: lower U and upper V follow
   from A, lower V follows from C, and upper U follows from C because
   U(C)-U(F)=0.6c-0.74s>0.

For c<s, exchange x and y and use E in place of D. This covers every
orientation and proves the disjunction. Missing both F and G is impossible.
The strict endpoints and side>1 handle contacts without a limiting argument.

`Compact/Bridge/C981DiagonalOuter.lean` exports:

- `Check`: owner 6 owns auxiliary 17 and 9 and misses 5,16,7,19.
- `excludes`: `Check v -> ExcludesVector v` using direct `AuxExact` facts.
- `coveredIds = [7,110]`.
- `covered_excluded`: complete original-vector exclusions for these two rows.

Both rows have owner-6 auxiliary set exactly `{9,17}` in the original
catalogue. Representative 116 also has that set, but is already covered by
the earlier midpoint proof, so it is omitted from this additional list.
Representative 7 is one of the original 55 residual entries; 110 was among
the earlier certificate-connected entries that still needed translation.

All finite catalogue membership proofs use ordinary `decide +kernel` source.
They and the geometry await the authorized final Lean replay. No admissions,
custom axioms, or native decision tactic were added.
