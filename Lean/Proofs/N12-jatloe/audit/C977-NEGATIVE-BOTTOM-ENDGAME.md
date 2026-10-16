# C977: the negative singleton and negative bottom wall

This is a source-only mathematical receipt. None of the new Lean modules
has been compiled. It excludes one complete original orientation cell;
it is not an assertion of the unrestricted packing theorem.

Let the actual bottom singleton, bottom wall and southeast central owner
be O, D and B. Write their canonical frames as `(p,-s)`, `(d,-r)` and
`(c,-t)`. Every normal has nonnegative sine at most its cosine, and every
square has the same side a>1. The original singleton misses (1,1), and
the actual southwest central owner owns (2,2); its orientation is free.

The original full-square arguments supply

* O owns (1,.914), (1.12,1), (1.74,1), (1.87,.76), and (1.96,.76).
* D owns (2,.914), (2,1), (2.6,1), and (2.86,1).
* B owns (2.35,1.65), (3,1.74), and (3,1.6).
* B's actual upper faces satisfy Uhi<=3c-t and Vhi<=2c+3t.
* Full D/B and A/B separation, together with D(2.86,1), give t<.3.

All these facts are bound to the unchanged original family in
`C977NegativeBottomNegativeWall.frame_excludes`. In particular, the last
angle bound is a consequence of a real farther wall point, not a pose
enclosure or an extra hypothesis about the central square.

O's bottom containment and missing corner give Ulo>=p-s and
s(Ulo+a)<=p Vlo. Therefore

    O.Vhi > boundary(p,s) = 1+s+s(1-s)/p.

The genuine next marker (2,.914), which O does not own, selects either
O.Uhi<=2p-.914s or O.Vhi<=2s+.914p. The first gives s<.172 and is excluded
by the existing original next-wall ending. The second gives s>.47 and
p+s>1.35. No orientation interval is sampled.

The actual inner point D(2,1) removes both longitudinal O/D axes. The
remaining two incoming axes are O.V and D.V. Full D/B separation leaves
only B.V and D.V as outgoing axes. The resulting four cells close as
follows.

1. **O.V to B.V.** Put P=td-cr, Q=tr+cd, H=sd-pr,
   K=sr+pd and J=sc-pt. The genuine steep/small bounds imply J>=0.
   The support formulas, for either sign of P and H, give

       Q lower_D(s,p) <= J(2d-.914r)+K(2c+3t-1-Q).

   Subtract Q(2s+.6p). The exact remainder is

       sr[c(1.086-d)+t(1-r)-1]
       +pd[c(1.4-d)+t-1]+ptr(.314-d),

   whose three terms are nonpositive from d>=.7, t<=.3 and c<=1.
   On the other hand,

       p[boundary(p,s)-2s-.6p]=(1-s)(p+.4s-.6)>0.

2. **O.V to D.V.** The actual B marker and both B caps give
   lower_B(r,d)<=2.35r+1.3d. The actual D marker then gives

       lower_D(s,p)<=2s+.914p-Q[1-.35r-.386d].

   The coefficient norm bounds .35r+.386d by .55. Also Q>=p on the
   steep singleton arc, using 1-d<=3r/7. Thus the same `(2,.6)` bound
   applies, again below the true singleton boundary.

3. **D.V to B.V.** O's real far point gives D.Vlo>1.87r+.76d.
   The actual D marker is used on one relative-angle side and its
   actual farther point on the other. The two normalized continuous
   margins are at least .095 and .321 when t<=.3.

4. **D.V to D.V.** A full square of side greater than one would lie on
   this common separating axis between O(1.96,.76) and B(2.35,1.65).
   Their squared distance is .39^2+.89^2=.9442<1, a contradiction.

`NegativeBottomNegativeWallClosure.impossible` assembles all four cells.
The original bridge also handles the shallow marker face, so no signed
singleton/wall subcase remains in this cell. Source and mathematical
audits by the parent and an independent worker found no premise gap;
Lean replay remains outstanding.
