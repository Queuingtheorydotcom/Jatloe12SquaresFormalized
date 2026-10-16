# C981 row 4: the last positive-left sector

Status: the continuous argument and its Lean source are assembled. These new
modules have **not been compiled**. This note records a signed sector of the
original row-4 proof; the original-family wrapper and final replay are separate
acceptance steps.

The entry is `FullAuxWallPositiveLeft.impossible`. It keeps three actual squares:
the positive opposite-central square C, the positive upper-central square B,
and the positive left-wall square L. Their sides agree and exceed 1. The entry
uses the genuine L container, marker (0.914,2), low point (1,1.6), and both physical
disjointness relations LC and LB. It also uses previously derived C/B faces,
owned points and **both** C/B transverse separation alternatives. It does not
assume a chosen LC or LB separator.

The shared original-square chain supplies C's positive U excess `u < 0.001`,
`0.05 < C.s < 0.22`, and B's exact faces

```
B.hiU ≤ 1.6 B.c + 3 B.s
B.hiV ≤ 3 B.c − B.s
B.loU ≥ 0.914 B.c + 2 B.s.
```

Both C/B transverse alternatives give `B.s < 0.46`. The width between B's U
faces gives `1 < 0.686 B.c + B.s`. The full LB separating-axis theorem removes
both transverse axes and retains the two longitudinal ones. For `L.s ≤ 0.16`,
both longitudinal alternatives contradict the original L wall and marker. The
proof uses unit-circle identities and rational polynomial chords, not an angle
grid. Consequently `L.s > 0.16`.

The full LC separating-axis theorem likewise retains precisely its two
longitudinal alternatives. `FullAuxWallPositiveLeftNeighbor.impossible`
eliminates C's own U axis on the entire canonical arc.

For L's own U axis, write `(l,r)=L.normal`, `(C,S)=C.normal`,
`alpha=l*C+r*S`, and `H=r*C-l*S`. The actual wall and marker give

```
l L.hiU ≥ a l + 2lr − 0.914 r².
```

If `H ≥ 0`, C's actual point (2,1.5) makes the selector imply

```
0 < 2 − 1.086r² − l(1+alpha) − 0.5lCH + l alpha u.
```

If `H ≤ 0`, C's actual lower V face `C.loV ≥ C−1.6S` instead implies

```
0 < 2 − 1.086r² − l(1+alpha) + lH(1−C+0.4S) + l alpha u.
```

The two `PositiveLeftAboveMargin`/`PositiveLeftBelowMargin` theorems prove the
corresponding expressions nonpositive over their full continuous domains.
The first uses a diagonal comparison followed by an affine circle chord and
two exact rational quadratic endpoints. The second is a direct diagonal
comparison. Every boundary, including `H=0`, is retained; strict contradiction
comes from the common side exceeding 1.

This closes the entire positive-C/positive-B/positive-L sector in source.
`FullAuxWallNegativeLeft.impossible` independently closes negative L. These
results consume the original chart's genuine points; the unavailable earlier
point assumptions are not reintroduced.
