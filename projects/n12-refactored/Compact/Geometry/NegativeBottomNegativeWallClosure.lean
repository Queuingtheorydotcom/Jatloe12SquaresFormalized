import Compact.Geometry.NegativeBottomNextAxes
import Compact.Geometry.NegativeBottomCentralAxis
import Compact.Geometry.NegativeBottomOwnTransverse
import Compact.Geometry.NegativeBottomTransverseChain
import Compact.Geometry.ShortMiddleSquare

/-! All four directed transverse selectors of the steep negative
singleton / negative bottom wall / negative central neighbor are
excluded. The small central tilt is supplied by the actual farther wall
point in the original family, uniformly over the central square's sign. -/
namespace N12Compact.NegativeBottomNegativeWallClosure

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

theorem impossible (O D B : OpenSquare) (s r t : ℝ)
    (os : O.s=-s) (ds : D.s=-r) (bs : B.s=-t)
    (on : Normal O.c s) (dn : Normal D.c r) (bn : Normal B.c t)
    (sameOD : O.side=D.side) (sameDB : D.side=B.side)
    (side : 1<O.side) (steep : 47/100<s) (small : t≤3/10)
    (oBox : InsideContainer O)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oMiddle : O.Inside (87/50) 1)
    (oFar : O.Inside (187/100) (19/25)) (oStrong : O.Inside (49/25) (19/25))
    (missingCorner : ¬O.Inside 1 1)
    (dMarker : D.Inside 2 (457/500)) (dHigh : D.Inside (13/5) 1)
    (dFar : D.Inside (143/50) 1) (dInner : D.Inside 2 1)
    (bMarker : B.Inside (47/20) (33/20)) (bWall : B.Inside 3 (87/50))
    (capU : B.loU+B.side≤3*B.c-t) (capV : B.loV+B.side≤2*B.c+3*t)
    (odApart : ∀ x y, ¬(O.Inside x y ∧ D.Inside x y))
    (dbApart : ∀ x y, ¬(D.Inside x y ∧ B.Inside x y)) : False := by
  have dSide : 1<D.side := by simpa only [sameOD] using side
  have bSide : 1<B.side := by simpa only [sameDB] using dSide
  have bounds := normal_bounds dn
  have dc : 0<D.c := by linarith only [bounds.1]
  have canonicalD : |D.s|≤D.c := by
    rw [ds,abs_neg,abs_of_nonneg dn.1]
    exact dn.2.1
  have faces := corner_face O s os on side oBox oMarker oNear oFar missingCorner
  have od := NegativeBottomNextAxes.negative_wall O D s r os ds on dn sameOD side
    faces.1 faces.2.1 oMarker oMiddle oFar dMarker dInner odApart
  have db := CentralNegativeBottomAxes.alternatives D B t bs bn dc canonicalD
    sameDB bSide dMarker dHigh bMarker bWall capU capV dbApart
  rcases od with incoming | incoming
  · rcases db with outgoing | outgoing
    · exact NegativeBottomCentralAxis.impossible O D B s r t on dn bn ds sameDB
        bSide.le steep small dMarker faces.2.2 incoming outgoing capV
    · rw [ds,neg_neg] at outgoing
      exact NegativeBottomOwnTransverse.impossible D B r t ds bs on dn bn sameDB
        dSide.le small steep.le dMarker bMarker capU capV
        (lt_of_lt_of_le faces.2.2 incoming) outgoing
  · rcases db with outgoing | outgoing
    · exact NegativeBottomTransverseChain.impossible O D B r t dn bn ds sameDB
        bSide small oFar dMarker dFar incoming outgoing capV
    · rw [ds,neg_neg] at outgoing
      have lowerOwn : lower D r D.c=D.loV := by
        simpa only [ds,neg_neg] using (ownV D).1
      have upperOwn : upper D r D.c=D.loV+D.side := by
        simpa only [ds,neg_neg] using (ownV D).2
      apply ShortMiddleSquare.impossible O D B (49/25) (19/25) (47/20) (33/20)
        r D.c (by nlinarith only [dn.2.2]) dSide oStrong bMarker (by norm_num)
      · rw [lowerOwn,upperOwn]
      · simpa only [lowerOwn] using incoming
      · simpa only [upperOwn] using outgoing

#print axioms impossible
end N12Compact.NegativeBottomNegativeWallClosure
