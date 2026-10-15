import Compact.Geometry.PositiveBottomNegativeWallMixed
import Compact.Geometry.NegativeBottomTransverseChain
import Compact.Geometry.ShortMiddleSquare

/-! The complete positive-singleton / negative-bottom-wall / negative
central-neighbor cycle. The small central tilt remains an explicit
entrance, to be supplied by the actual farther wall point in the original
family. Every directed separation of both square pairs is exhausted. -/
namespace N12Compact.PositiveBottomNegativeWallClosure

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

theorem impossible (O D B : OpenSquare) (r t : ℝ)
    (ds : D.s=-r) (bs : B.s=-t)
    (on : Normal O.c O.s) (dn : Normal D.c r) (bn : Normal B.c t)
    (sameOD : O.side=D.side) (sameDB : D.side=B.side)
    (side : 1<O.side) (small : t≤3/10)
    (oBox : InsideContainer O) (dBox : InsideContainer D)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oFar : O.Inside (187/100) (19/25)) (oStrong : O.Inside (49/25) (19/25))
    (missingCorner : ¬O.Inside 1 1) (missingMarker : ¬O.Inside 2 (457/500))
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
  have faces := C696PositiveCorner.corner_faces O on side oBox oMarker oNear
    missingCorner missingMarker
  have od := PositiveBottomNextAxes.negative_wall O D r ds on dn sameOD side
    faces.1 faces.2.1 faces.2.2.2.1 oMarker oFar dMarker dInner odApart
  have db := CentralNegativeBottomAxes.alternatives D B t bs bn dc canonicalD
    sameDB bSide dMarker dHigh bMarker bWall capU capV dbApart
  rcases od with incoming | incoming
  · rcases db with outgoing | outgoing
    · exact PositiveBottomNegativeWallCycle.own_transverse O D B r t ds bs on dn bn
        sameOD sameDB dSide faces.2.2.2.1 faces.2.1 dBox capV incoming outgoing
    · rw [ds,neg_neg] at outgoing
      exact PositiveBottomNegativeWallMixed.own_wall_transverse O D B r t ds bs on dn bn
        sameOD sameDB dSide small faces.2.2.2.1 faces.2.1 dMarker bMarker
        capU capV incoming outgoing
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
end N12Compact.PositiveBottomNegativeWallClosure
