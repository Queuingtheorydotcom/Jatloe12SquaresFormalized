# C981 representatives 3 and 4: shared continuous source argument

Checkpoint: 11 October 2026. This is a **source completion and hand-review
record, not a Lean acceptance receipt**. Compilation remains deferred until
the entire proof source is assembled, as requested.

`Compact.Bridge.C981FullAuxNegative` supplies the original unrestricted
whole-vector exclusions for representatives 3 and 4. The shared `Check`
retains every actual point query and the original opposite-center entrance.
`Compact.Cases.C981Compact` consumes these and the other completed vectors,
leaving 42 whole-vector obligations. This does not close the entire C981 case. The global assembly
still has 84 whole-case source entries and 33 pending original cases.

## Mathematical simplification

The proof keeps the actual squares, their common side greater than one,
their container walls, and every relevant separating axis. Its chart is
`(x,y)=(4-oldY,oldX)`. In this chart A is the escaping northeast central
square, C the southwest center owner, B the northwest central square,
and L the original left-wall square. They are owners 5, 7, 6 and 11.

1. The original ownership and full right/top neighbors force A into a
   narrow positive canonical frame. Earlier continuous arguments exclude
   every nonpositive frame of C or B.
   Representative 3 uses the shorter genuine top segment from `(1.6,3)`
   to `(2.26,3)`. For steep A, set `z=c/(1+s)`. When `z` is at least
   `.26`, the endpoint `(2.26,3)` is inside A; otherwise the exact crossing
   `(2+z,3)` lies in both squares. The shallow entrance requires A's
   exact exclusion of `(2.4,3)`; it does not invent another owner of that
   point. All subsequent geometry is the same shared support cycle.
2. Retaining the **full right-wall square** gives the exact clearance
   `c*e + (2/5)*s² - (1-c)*(1-s) < 0`, where
   `e = A.loU - 2*(c+s) ≥ 0`. This improves the coarse position bound to
   `e < 1/1250`. The only maximization is the identity
   `2916/15625 - s²*(27-125*s) = (s-18/125)²*(125*s+9)`.
3. Both actual A/C separators preserve a projection bound on C's excess
   `u = C.hiU - 2*(C.cos+C.sin)`. The same exact clearance yields
   `50*C.sin < 11*C.cos` and `u < 1/1000`.
4. The actual C/B separators, B's foreign top/corner/left points, and
   C's genuine lower face give `1/20 < C.sin` and
   `3/10 < B.sin < 23/50`. These are inequalities on whole canonical
   arcs, not finite samples or assumed enclosures.
5. For a nonpositive L frame, all C/L axes force its absolute sine below
   `1/50`. All B/L axes then force `B.sin > 23/50`, a contradiction.
6. For a positive L frame, all B/L axes force `L.sin > 4/25`. Both
   surviving C/L axes are then impossible. C's axis uses an exact diagonal
   comparison. L's axis uses a diagonal comparison on the shallow arc and
   the affine cosine bound `l ≥ 5/4 - (77/100)*r` on the remaining arc.
   The resulting quadratic has two rational endpoints; its coefficients
   and endpoint bounds are proved algebraically.

The last step replaces an angle subdivision tree with a few shared
inequalities. No optimization result or floating-point computation is
used as a proof premise. No admission, custom axiom, or new unchecked
certificate was introduced.

## Source and review boundary

- Original ownership, transformations, signed-frame covers and final
  vector theorem: `Compact/Bridge/C981FullAuxNegative.lean`.
- Exact clearance: `FullAuxWallRightSupport` and `FullAuxWallSharpClearance`.
- C/B angle bounds: `FullAuxWallPositiveLowerAngleSupport` and
  `FullAuxWallPositiveUpperAngleSupport`.
- Complete left-wall sign sectors: `FullAuxWallNegativeLeft` and
  `FullAuxWallPositiveLeft`.
- The positive sector includes both neighboring-axis alternatives,
  both relative-angle signs, the exact `PositiveLeftOwn` support identities,
  and `PositiveLeftNeighbor` plus the two scalar margin modules.

The parent and independent reasoning workers reviewed the support signs,
circle identities, endpoint arithmetic and premise bindings. These checks
do not establish that every Lean tactic elaborates. The final complete
assembly must still compile and pass its admission/axiom audit.

The bounded literal diagnostic `evidence/c981-full-aux-signature.json`
matches representatives 3, 4 and 6. Representative 6 was already closed by
the diagonal-corner argument, so this generalization contributes only
representative 3 as a newly finished obligation. The diagnostic checks
source data only; the Lean query checks still await the final replay.
Other C981 vectors require their own original-data bindings or new geometry.
