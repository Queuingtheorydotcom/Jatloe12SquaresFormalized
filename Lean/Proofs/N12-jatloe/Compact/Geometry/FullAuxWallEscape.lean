import Compact.Geometry.DoubleAuxWallCenter

/-! Exact remaining sector for a fully occupied opposite wall segment.
This is a genuine reduction, not a whole configuration exclusion. The
outer endpoint excluded by DoubleAuxWallCenter is deliberately absent.
All moderate and steep angles close through the actual neighboring square;
the residual narrow square has two tightly bounded actual face offsets. -/
namespace N12Compact.FullAuxWallEscape
open S12 S12Pilot FourSquareAnchors CentralWallEscape CentralWallPairAxes
set_option Elab.async false

theorem narrow_faces_of_missing (A R : OpenSquare) (ha : 1 < A.side)
    (sameR : A.side=R.side) (boxR : InsideContainer R)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (order : A.s ≤ A.c)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (missingB : ¬ A.Inside (33/20) (47/20))
    (rMarker : R.Inside (1543/500) 2) (rHigh : R.Inside 3 (12/5))
    (missingTop : ¬ A.Inside (12/5) 3)
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y))
    (missing : ¬ A.Inside 2 2) :
    0 < A.s ∧ 4*A.s < A.c ∧
    2*A.c+2*A.s ≤ A.loU ∧ A.loU < 2*A.c+(113/50)*A.s ∧
    3*A.c-(5/2)*A.s < A.loV+A.side ∧
    A.loV+A.side ≤ 3*A.c-(12/5)*A.s ∧ A.Inside (5/2) 3 := by
  have missingR : ¬ A.Inside 3 (12/5) := fun h => ar _ _ ⟨h,rHigh⟩
  have narrow : 4*A.s < A.c := by
    apply lt_of_not_ge
    intro moderate
    by_cases steep : (16/25)*A.c ≤ A.s
    · exact missing (CentralEscapeSegment.shallow_center A R ha hc hs order steep
        p q m missingTop rMarker rHigh ar)
    · have sector : A.s ≤ (16/25)*A.c := (lt_of_not_ge steep).le
      let z := A.s/(1+A.c)
      have denominator : 0 < 1+A.c := by linarith only [hc]
      have hz : 0 ≤ z := div_nonneg hs denominator.le
      have angle : (1+A.c)*z=A.s := by
        dsimp [z]; field_simp [ne_of_gt denominator]
      have unitAngle : A.s*z=1-A.c := by
        dsimp [z]
        field_simp [ne_of_gt denominator]
        nlinarith only [A.unit_normal]
      have crossing := DoubleAuxWallCenter.moderate_crossing A ha hc hs order
        moderate z hz angle unitAngle p q m missingTop missing
      exact missing (CentralWallCenter.center_of_crossing A R ha sameR boxR hc hs
        sector p q m missingG missingB missingR missingTop rMarker rHigh ar
        z hz angle unitAngle crossing)
  have faces := central_lower_faces A hc hs (by linarith only [narrow,hc])
    p q m missing missingG
  have positive : 0 < A.s := by linarith only [faces.1,p.1]
  have strong : A.Inside (5/2) 3 := by
    apply Classical.byContradiction
    intro absent
    exact missing (CentralWallCenter.shallow A R ha sameR boxR hc hs order p q m
      missingG missingB missingR missingTop absent rMarker rHigh ar)
  have cu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,hc]
  have topUlo : A.loU < A.c*(12/5)+A.s*3 := by
    linarith only [m.1,hc,hs]
  have topUhi : A.c*(12/5)+A.s*3 < A.loU+A.side := by
    linarith only [faces.1,ha,narrow,cu]
  have topVlo : A.loV < -A.s*(12/5)+A.c*3 := by
    linarith only [q.2.2.1,narrow,hc]
  have topVhi : A.loV+A.side ≤ -A.s*(12/5)+A.c*3 :=
    le_of_not_gt (fun h => missingTop ⟨topUlo,topUhi,topVlo,h⟩)
  exact ⟨positive,narrow,faces.1,by linarith only [p.1],
    by linarith only [strong.2.2.2],by linarith only [topVhi],strong⟩

/-- The earlier foreign-owner entrance remains available.  The core
argument only needs the exact exclusion, which an ownership query may
also supply when the auxiliary point has no owner. -/
theorem narrow_faces (A R T : OpenSquare) (ha : 1 < A.side)
    (sameR : A.side=R.side) (boxR : InsideContainer R)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (order : A.s ≤ A.c)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (missingB : ¬ A.Inside (33/20) (47/20))
    (rMarker : R.Inside (1543/500) 2) (rHigh : R.Inside 3 (12/5))
    (tHigh : T.Inside (12/5) 3)
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y))
    (apartTop : ∀ x y, ¬ (A.Inside x y ∧ T.Inside x y))
    (missing : ¬ A.Inside 2 2) :
    0 < A.s ∧ 4*A.s < A.c ∧
    2*A.c+2*A.s ≤ A.loU ∧ A.loU < 2*A.c+(113/50)*A.s ∧
    3*A.c-(5/2)*A.s < A.loV+A.side ∧
    A.loV+A.side ≤ 3*A.c-(12/5)*A.s ∧ A.Inside (5/2) 3 :=
  narrow_faces_of_missing A R ha sameR boxR hc hs order p q m missingG missingB
    rMarker rHigh (fun h => apartTop _ _ ⟨h,tHigh⟩) ar missing

#print axioms narrow_faces
end N12Compact.FullAuxWallEscape
