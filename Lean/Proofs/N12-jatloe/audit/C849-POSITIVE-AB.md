# Cases 849 and 851: complete positive-B source argument

Status: source assembled, mathematically reviewed, **not yet compiled**.
The original two cases are not claimed closed by this record. The negative
canonical-B sector and the original-family entrance must also be supplied.

The terminal theorem is `N12Compact.C849Positive.impossible` in
`Compact/Geometry/C849Positive.lean`. It retains five actual `OpenSquare`
objects, their strict or closed point ownership, and actual disjointness.
Only B has a canonical orientation assumption: `0 < B.c` and
`0 ≤ B.s ≤ B.c`. The other four orientations are unrestricted.

## Exact original roles and premises

The authenticated inputs are `evidence/historical/data/case849-input.json.gz`
and `case851-input.json.gz`. Both have the following role masks:

| Role | Mask | Premises used by the positive-sector theorem |
| --- | ---: | --- |
| A | 1024 | Closed `(2,2.26)`, `(2.26,2)`; strict marker `(2.35,2.35)`; missing markers `(1.65,1.65)`, `(2.35,1.65)` |
| B | 34816 | Closed `(1.65,2.35)`, `(1.6,3)`; strict marker `(2,3.086)` |
| R | 16384 / 16416 | Closed `(3,2.4)`, `(3.086,2)`; missing `(3.24,1.87)`; actual container inclusion and side greater than one |
| C | 16 | Strict auxiliary point `(2.26,3)` |
| E | 192 | Strict seed-forced point `(1,3)` |

A and B have equal side greater than one. The required disjoint pairs are
A/B, A/R, B/C and B/E. No independent orientation, center, or support bound
is assumed. In particular, neither C's upper-U missing-point mode nor its
lower-V missing-point mode is assumed. L is unnecessary in this sector.

The parent is separately binding these premises from the original normalized
packing and checked owner domains. A strict original marker is deliberately
retained in A and B: replacing either one by arbitrary closed ownership would
lose an endpoint argument.

## Continuous proof

1. The existing all-angle A/R argument forces A to contain `(2,2.5)`.
   Its exclusion from B forces `B.loV ≥ -2s + 2.5c`. B's actual bottom
   marker then gives `3c ≤ 7s`.
2. The foreign corner seed `(1,3)` is excluded from B. Its other two faces
   are strictly inside, so it lies either below B's U face or above B's V
   face. These two alternatives are exhaustive.
3. In the upper-V alternative, the side satisfies `a ≤ s+c/2`.
   `C849SteepAB.impossible` excludes this entire steep interval using A's
   real compulsory triangle and both actual transverse SAT alternatives.
4. In the lower-U alternative, the strict foreign C point `(2.26,3)` caps
   B's upper-U face. Hence `1 < a ≤ 1.26c`, so `c > 50/63`. The unit-normal
   identity implies `s ≤ (4/5)c`. This is the only shallow interval bound.
5. A's missing lower marker forces exactly two A face modes. Their
   additional lower bounds come from the actual foreign B bottom and R
   point, not a guessed separating face. `ABTransverse.alternatives`
   derives the remaining two transverse separating axes from true A/B
   disjointness and eliminates both longitudinal axes.
6. `C849ShallowAB.in_frame` excludes both transverse alternatives in both
   A face modes and both relative-angle signs. Consequently the complete
   lower-U branch is impossible.

There is no angle grid, numerical search, or expanded case certificate in
this argument. The finite split is two B faces, two A faces, two transverse
axes, and the sign of the relative angle.

## Exact quartic and its actual interval

Write A's positive frame as `(p,q)` and B's as `(c,s)`. In the only branch
requiring the quartic, `e = cq-sp ≤ 0` and `s ≤ (4/5)c`, with `c,p>0`.
Therefore `q ≤ (4/5)p`. Since `p²+q²=1` and `p,q≥0`, the substitution

```
t = q/(1+p)
```

has `0 ≤ t ≤ 2/5`. This interval follows from the actual face/relative-angle
branch and unit-normal identity; it is not an extra angle assumption.
The rational parametrization is

```
p(1+t²) = 1-t²
q(1+t²) = 2t.
```

The required margin, multiplied by `(1+t²)²`, is exactly

```
P(t) = 1/50 - (19/250)t - (16/25)t² + (819/250)t³ - (99/50)t⁴.
```

With `z=t-1/5`, the source proves the polynomial identity

```
25000 P(t) = 56(1-z) + z²(21260 + 42300z - 49500z²).
```

On `-1/5 ≤ z ≤ 1/5`, the bracket is at least `10820` and `56(1-z)`
is at least `224/5`, so the margin is strictly positive at both endpoints
as well. An independent reasoning worker checked the identity and interval
by hand. Lean replay remains deferred until the complete source assembly.

## Files and validation boundary

The new shared geometry is in `ABTransverse.lean`, `C849SteepMargins.lean`,
`C849SteepAB.lean`, `C849ShallowMargins.lean`, `C849ShallowAB.lean`, and
`C849Positive.lean`, all under `Compact/Geometry`.

No new axiom, admission, unchecked arithmetic oracle, compiler job, or
numerical process was used to prepare these files. Their proof terms must
still pass the final ordinary Lean kernel replay. This is a complete
**positive-sector source proof**, not a claimed accepted exclusion of either
whole original case.
