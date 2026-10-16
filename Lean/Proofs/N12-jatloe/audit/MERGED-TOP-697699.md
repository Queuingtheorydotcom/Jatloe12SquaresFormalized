# Three whole original cases reuse the same geometry

Source checkpoint, 11 October 2026. No new Lean compilation has been run.

Cases697,698,699 now have complete source exclusions in
`Compact/Assembly/MergedTopFurther.lean`, bound to retained rows378,379,380.
The common theorem is `MergedTopFurther.impossible`. An independent source
review found no missing original point, orientation, or disjointness premise.
This is source completion, not Lean acceptance.

The original budget and checked ownership domains leave one assignment
for697 and two for each of698/699. In the latter two cases the extra
assignment puts the merged top owner's actual marker(2,3.086) and an
auxiliary point farther apart than one normalized square's diameter.
The exact squared distances are1104749/250000 and802049/250000;
both exceed2000000/982081. Removing these genuine impossibilities leaves
one original assignment in each case. The finite diagnostic, with both
unfiltered and filtered vectors, is in
`evidence/c697699-original-domain-audit.json`.

The right singleton32 provides the strict vertical segment from(3,2.26)
to(3,2.88). Its strict interpolated points(3,2.4) and(3,2.5) force the
actual central elbow to reach(2,2.5). The two signed canonical orientations
of the merged top square now use the complete849/851 geometry, retaining
its actual left wall and northwest corner neighbor. Thus these are three
whole exclusions without a new angle table or saved pose-transition tree.

The main assembly now has75 whole original-case source terms and42 actual
remaining original case contracts. The historical accepted58-case registry
is a separate earlier validation boundary; no receipt certifies this new
75-case source assembly.
