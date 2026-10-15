import Compact.Bridge.C977CentralReach
import Compact.Geometry.CentralCenterCaps

/-! Both upper support faces of the actual southwest central owner in the
center-owned C977 branch. No conditional auxiliary ownership is introduced. -/
namespace N12Compact.C977CenterCaps

open S12 S12Pilot S12Completion.C977

/-- Every signed canonical representation of actual owner 5 receives the
two caps from its original central-marker exclusions and genuine crosspoints. -/
theorem frame_caps (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (A : OpenSquare) (positive : 0<A.c) (canonical : |A.s|≤A.c)
    (shape : A.side=(p.square (orderedOwner p 5)).side)
    (equivalent : ∀ x y, A.Inside x y↔(p.square (orderedOwner p 5)).Inside x y)
    (center : (p.square (orderedOwner p 5)).Inside 2 2) :
    A.loU+A.side≤(47/20)*A.c+(33/20)*A.s ∧
      A.loV+A.side≤(47/20)*A.c-(33/20)*A.s := by
  have side : 1<A.side := by
    rw [shape,p.congruent]
    exact p.side_gt_one
  have points := C977CentralReach.central_points p hf
  have markers := C977CentralReach.central_data p hf
  exact CentralCenterCaps.signed_caps A positive canonical side
    ((equivalent 2 2).mpr center)
    ((equivalent (3/2) 2).mpr points.2)
    ((equivalent 2 (3/2)).mpr points.1)
    (fun h => markers.2.2.2.2.1 ((equivalent (33/20) (47/20)).mp h))
    (fun h => markers.2.2.2.2.2 ((equivalent (47/20) (33/20)).mp h))

#print axioms frame_caps
end N12Compact.C977CenterCaps
