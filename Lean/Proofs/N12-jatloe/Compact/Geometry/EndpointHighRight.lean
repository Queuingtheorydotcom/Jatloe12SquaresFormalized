import Compact.Geometry.EndpointRowTemplate

/-! The endpoint contradiction with a directly owned high right point.
The right owner need not have a wall marker: strict convexity of its original
owned segment can already supply both right-hand points. -/
namespace N12Compact.EndpointHighRight
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

structure Premises (A B L R : OpenSquare) : Prop where
  aSide : 1 < A.side
  bSide : 1 < B.side
  aP : ClosedInside A 2 (113/50)
  aQ : ClosedInside A (113/50) 2
  aT : ClosedInside A (47/20) (47/20)
  aF : ¬ A.Inside (33/20) (33/20)
  aG : ¬ A.Inside (47/20) (33/20)
  bMarker : ClosedInside B (33/20) (47/20)
  bLow : B.Inside (87/50) 2
  bHigh : B.Inside (8/5) 3
  lQ : ClosedInside L 1 (12/5)
  rQ : ClosedInside R 3 (12/5)
  rHigh : R.Inside 3 (5/2)
  ab : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y)
  ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)
  bl : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y)

theorem impossible (A B L R : OpenSquare) (h : Premises A B L R) : False := by
  have foreignB := ClosedPointExclusion.outside_of_closed A B _ _ h.ab h.bMarker
  have foreignR := ClosedPointExclusion.outside_of_closed A R _ _ h.ar h.rQ
  have foreignHigh : ¬ A.Inside 3 (5/2) := fun hp => h.ar _ _ ⟨hp,h.rHigh⟩
  obtain ⟨a,hc,hs,hside,hi,hcl⟩ := ClosedFrames.positive_frame A
  have highA : A.Inside 2 (5/2) := (hi _ _).mp
    (FourSquareANarrow.point_of_higher_R a (by simpa only [hside] using h.aSide) hc hs
      ((hcl _ _).mpr h.aP) ((hcl _ _).mpr h.aQ) ((hcl _ _).mpr h.aT)
      (fun hp => h.aF ((hi _ _).mp hp)) (fun hp => h.aG ((hi _ _).mp hp))
      (fun hp => foreignB ((hi _ _).mp hp)) (fun hp => foreignR ((hi _ _).mp hp))
      (fun hp => foreignHigh ((hi _ _).mp hp)))
  have rowA := FourSquareAForced.row_point A h.aP highA
  have leftB := EndpointRowTemplate.forced_left B h.bSide h.bLow h.bHigh
    (fun hp => h.ab _ _ ⟨rowA,hp⟩) (fun hp => h.ab _ _ ⟨highA,hp⟩)
  exact ClosedPointExclusion.outside_of_closed B L _ _ h.bl h.lQ leftB

#print axioms impossible
end N12Compact.EndpointHighRight
