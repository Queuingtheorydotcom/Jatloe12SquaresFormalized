import Compact.Geometry.PositiveWallUpperUPositiveLeft

/-! The genuine upper marker, rather than a nonexistent singleton seed,
restricts a positive left-wall square. The upper-U escape is impossible
in the small negative-bottom / positive-left cycle. The remaining upper-V
face is stated explicitly for subsequent coupling to the actual corner. -/
namespace N12Compact.PositiveWallMarker

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic

theorem upper_faces (W : OpenSquare) (normal : Normal W.c W.s)
    (marker : W.Inside (457/500) 2)
    (missing : ¬W.Inside (457/500) 3) :
    W.loU+W.side≤(457/500)*W.c+3*W.s ∨
      W.loV+W.side≤3*W.c-(457/500)*W.s := by
  have b := normal_bounds normal
  by_cases upperU : W.loU+W.side≤(457/500)*W.c+3*W.s
  · exact Or.inl upperU
  · right
    apply le_of_not_gt
    intro upperV
    apply missing
    refine ⟨?_,lt_of_not_ge upperU,?_,upperV⟩ <;>
      linarith only [marker.1,marker.2.2.1,normal.1,b.1]

/-- Every actual separating axis is retained: the shared full-square
cycle removes the first marker escape and leaves only the upper-V face.
No condition at `(1,2.88)` occurs in this statement or its proof. -/
theorem upper_v (O L W : OpenSquare) (t : ℝ) (os : O.s=-t)
    (on : Normal O.c t) (ln : Normal L.c L.s) (wn : Normal W.c W.s)
    (positive : 0<t) (small : t≤1/5)
    (sameOL : O.side=L.side) (sameLW : L.side=W.side) (side : 1<L.side)
    (lBox : InsideContainer L) (wBox : InsideContainer W)
    (bottom : t*(O.loU+O.side)≤O.c*O.loV)
    (oCap : O.loU+O.side≤2*O.c-(457/500)*t)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oFar : O.Inside (187/100) (19/25))
    (lMarker : L.Inside (457/500) 1) (lCorner : L.Inside 1 1)
    (lFar : L.Inside (19/25) (187/100))
    (wMarker : W.Inside (457/500) 2)
    (wMissing : ¬W.Inside (457/500) 3)
    (apartOL : ∀ x y, ¬(O.Inside x y ∧ L.Inside x y))
    (apartLW : ∀ x y, ¬(L.Inside x y ∧ W.Inside x y)) :
    W.loV+W.side≤3*W.c-(457/500)*W.s := by
  rcases upper_faces W wn wMarker wMissing with upperU | upperV
  · exact False.elim (PositiveWallUpperUPositiveLeft.impossible_relaxed
      O L W t os on ln wn positive small sameOL sameLW side lBox wBox bottom
      oCap (PositiveWallUpperUPositiveLeft.marker_cap W wn upperU)
      oMarker oNear oFar lMarker lCorner lFar wMarker apartOL apartLW)
  · exact upperV

end N12Compact.PositiveWallMarker
