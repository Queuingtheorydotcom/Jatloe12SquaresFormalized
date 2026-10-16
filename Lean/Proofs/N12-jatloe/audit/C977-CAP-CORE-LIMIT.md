# Limit of the proposed opposed-cap core

Mathematical diagnostic, not a global packing counterexample and not a
new formal theorem. No computation or Lean replay was run by this worker.

The existing `CentralOpposedCornerChain.impossible` requires incoming
support inequalities on the neighboring central squares' axes. Those
inequalities cannot be replaced by an arbitrary A-owned incoming axis
while retaining only the southeast/northwest endpoint caps.

A concrete hand construction explaining the gap uses
`b=99/101`, `t=20/101`, `a=10001/10000`. Let A be axis-aligned with both
upper coordinate faces `2.01` and side `a`. Put B in frame `(b,-t)` with
upper U face `3b-t` and upper V face `2b+3t`; obtain C by transposition.
A contains the center and the usual southwest marker/crosspoints. B and
C have the southeast/northwest caps and the relevant inner and outer
central anchors. Their A-owned separating directions leave positive
clearance. Thus the neighbor-axis support premises do essential work.

Even retaining an actual axis-aligned southeast paired corner alone does
not obviously repair this relaxation. Take its square as
`[4-a,4]×[0,a]`, and lower B's upper U face to `(4-a)b-a*t`, keeping the
upper V face unchanged. The corner's entire square is then separated on
B's U axis, while this changes the first construction by only
`(a-1)(b+t)`. The transposed northwest corner can be included similarly.
This extension is a hand-derived diagnostic requiring independent exact
checking before any machine-verified claim. It does not include the full
original bottom/right/top chains or all twelve owners.

The honest remaining C977 cap branch must keep additional actual square
couplings. The bottom `O0 → D9 → B6 → A5` chain is assigned separately;
no cap-only exclusion theorem has been added to the completion skeleton.
