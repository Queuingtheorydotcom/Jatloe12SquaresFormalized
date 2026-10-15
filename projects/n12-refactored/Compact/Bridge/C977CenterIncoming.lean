import Compact.Bridge.C977CenterCaps
import Compact.Geometry.CentralCenterPairIncoming
import Compact.Geometry.CentralPositiveTransverse
import Compact.Bridge.C977RightCornerSupport

/-! Complete original-center incoming-axis classification. Both central
pairs retain their genuine steep transverse alternatives. No chosen
auxiliary vector or conditional inner-point ownership is assumed. -/
namespace N12Compact.C977CenterIncoming

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic
set_option Elab.async false

theorem frame_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (center : (p.square (orderedOwner p 5)).Inside 2 2) :
    ((q 5).loU+(q 5).side≤lower (q 6) (q 5).c (q 5).s ∨
      upper (q 5) (q 6).c (q 6).s≤(q 6).loU ∨
      (3*(q 6).c<7*(q 6).s ∧
        (q 6).loV+(q 6).side≤lower (q 5) (-(q 6).s) (q 6).c)) ∧
    ((q 5).loV+(q 5).side≤lower (q 7) (-(q 5).s) (q 5).c ∨
      upper (q 5) (-(q 7).s) (q 7).c≤(q 7).loV ∨
      (7*(q 7).s< -3*(q 7).c ∧
        (q 7).loU+(q 7).side≤lower (q 5) (q 7).c (q 7).s)) := by
  have caps := C977CenterCaps.frame_caps p hf (q 5) (canonical 5).1 (canonical 5).2
    (shape 5) (equivalent 5) center
  have data := C977CentralReach.central_data p hf
  have points := C977CentralReach.central_points p hf
  have aCenter := (equivalent 5 _ _).mpr center
  have aLow := (equivalent 5 _ _).mpr points.1
  have aLeft := (equivalent 5 _ _).mpr points.2
  have aRight := (equivalent 5 _ _).mpr data.2.1
  have aTop := (equivalent 5 _ _).mpr data.2.2.1
  have bm := coded_exact p (orderedOwner p 6)
  rw [ordered_owner_code p hf 6] at bm
  have bMarker : (q 6).Inside (47/20) (33/20) := (equivalent 6 _ _).mpr (by
    have point := (bm 9).mpr (by decide)
    simpa [Owns,marker] using point)
  have cm := coded_exact p (orderedOwner p 7)
  rw [ordered_owner_code p hf 7] at cm
  have cMarker : (q 7).Inside (33/20) (47/20) := (equivalent 7 _ _).mpr (by
    have point := (cm 11).mpr (by decide)
    simpa [Owns,marker] using point)
  have bWall : (q 6).Inside 3 (87/50) := (equivalent 6 _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 6, 8∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 6)
    have point := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have cWall : (q 7).Inside (87/50) 3 := (equivalent 7 _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 7, 14∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 7)
    have point := (nat_combined_exact p (orderedOwner p 7) 14 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have apart (i j : Fin 12) (different : i≠j) :
      ∀ x y, ¬((q i).Inside x y ∧ (q j).Inside x y) := fun x y h =>
    p.disjoint _ _ (fun eq => different (ordered_owner_injective p hf eq)) x y
      ⟨(equivalent i _ _).mp h.1,(equivalent j _ _).mp h.2⟩
  have side : 1<(q 5).side := by rw [shape,p.congruent]; exact p.side_gt_one
  constructor
  · exact CentralCenterPairIncoming.right_alternatives (q 5) (q 6)
      (canonical 5).1 (canonical 5).2 (canonical 6).1 (canonical 6).2
      (by rw [shape,shape,p.congruent,p.congruent]) side aCenter aLow aRight
      caps.2 bMarker bWall (apart 5 6 (by decide))
  · exact CentralCenterPairIncoming.top_alternatives (q 5) (q 7)
      (canonical 5).1 (canonical 5).2 (canonical 7).1 (canonical 7).2
      (by rw [shape,shape,p.congruent,p.congruent]) side aCenter aLeft aTop
      caps.1 cMarker cWall (apart 5 7 (by decide))

/-- Actual positive A excludes the southeast neighbor's transverse
selector, including its full southeast paired-corner exclusion. -/
theorem positive_right_transverse_excludes (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (an : Normal (q 5).c (q 5).s) (bn : Normal (q 6).c (q 6).s)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (separator : (q 6).loV+(q 6).side≤lower (q 5) (-(q 6).s) (q 6).c) : False := by
  have ab := C977CornerCubic.normal_bounds an
  have caps := C977CenterCaps.frame_caps p hf (q 5)
    (by linarith only [ab.1]) (by simpa only [abs_of_nonneg an.1] using an.2.1)
    (shape 5) (equivalent 5) center
  have bm := coded_exact p (orderedOwner p 6)
  rw [ordered_owner_code p hf 6] at bm
  have marker : (q 6).Inside (47/20) (33/20) := (equivalent 6 _ _).mpr (by
    have point := (bm 9).mpr (by decide)
    simpa [Owns,marker] using point)
  have wall : (q 6).Inside 3 (87/50) := (equivalent 6 _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 6, 8∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 6)
    have point := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have missing : ¬(q 6).Inside 3 1 := fun h => p.disjoint _ _
    (fun eq => (by decide : (6 : Fin 12)≠2) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent 6 _ _).mp h,C977RightCornerSupport.southeast_corner p hf⟩
  exact CentralPositiveTransverse.impossible (q 5) (q 6) an bn
    (by rw [shape,shape,p.congruent,p.congruent])
    (by rw [shape,p.congruent]; exact p.side_gt_one)
    ((equivalent 5 _ _).mpr center) caps.2 marker wall missing separator

/-- Every original B frame has only two possible incoming axes when
the actual center owner A has a positive canonical frame. -/
theorem positive_right_alternatives (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (an : Normal (q 5).c (q 5).s)
    (center : (p.square (orderedOwner p 5)).Inside 2 2) :
    (q 5).loU+(q 5).side≤lower (q 6) (q 5).c (q 5).s ∨
      upper (q 5) (q 6).c (q 6).s≤(q 6).loU := by
  rcases (frame_cover p hf q shape equivalent canonical center).1 with own | next | transverse
  · exact Or.inl own
  · exact Or.inr next
  · have sign : 0≤(q 6).s := by linarith only [transverse.1,(canonical 6).1]
    have bn : Normal (q 6).c (q 6).s :=
      ⟨sign,by simpa only [abs_of_nonneg sign] using (canonical 6).2,(q 6).unit_normal⟩
    exact False.elim (positive_right_transverse_excludes p hf q shape equivalent
      an bn center transverse.2)

#print axioms frame_cover
#print axioms positive_right_transverse_excludes
#print axioms positive_right_alternatives
end N12Compact.C977CenterIncoming
