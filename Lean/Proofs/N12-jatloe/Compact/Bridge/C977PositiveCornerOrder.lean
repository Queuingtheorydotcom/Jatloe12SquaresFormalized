import Compact.Bridge.C977CentralReach
import Compact.Geometry.PositiveCentralWallAngleOrder

/-! A correct original-packing entrance to the owned-west-point angle
comparison. All three squares may be independently reindexed in their own
face frames, while the actual packing and owner labels are unchanged.
This proves an angle order, not a whole C977 exclusion. No point (1,2.88)
is assumed or inferred from the paired upper corner. -/
namespace N12Compact.C977PositiveCornerOrder

open S12 S12Pilot S12Completion.C977 C977CornerCubic
set_option Elab.async false

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y, ¬((p.square (orderedOwner p i)).Inside x y ∧
      (p.square (orderedOwner p j)).Inside x y) := by
  apply p.disjoint
  exact fun h => different (ordered_owner_injective p hf h)

private theorem forced_auxiliary (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (i : Fin 12) (n : Nat)
    (check : ∀ owned ∈ pruningDomain4 i, n∈owned) :
    n∈natCombinedOwners p (orderedOwner p i) :=
  check _ (pruned_auxiliary_domain_actual p hf i)

/-- In the actual C977 family, the positive bottom / negative wall cell
with central (1,2) owned has the strict bottom-to-wall angle order.
Missing-center and owned-west are honest branch premises. -/
theorem frame_angle_order_of_west (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12 → OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (t : ℝ) (on : Normal (q 0).c (q 0).s)
    (an : Normal (q 5).c (q 5).s) (wn : Normal (q 8).c t)
    (ws : (q 8).s=-t)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (missingCenter : ¬(p.square (orderedOwner p 5)).Inside 2 2)
    (west : (p.square (orderedOwner p 5)).Inside 1 2) : (q 0).s<t := by
  have side : 1<(q 5).side := by rw [shape,p.congruent]; exact p.side_gt_one
  have sideCap : (q 5).side≤1001/1000 := by rw [shape,p.congruent]; exact p.side_le
  have sameOA : (q 0).side=(q 5).side := by rw [shape,shape,p.congruent,p.congruent]
  have sameAW : (q 5).side=(q 8).side := by rw [shape,shape,p.congruent,p.congruent]
  have oBox : InsideContainer (q 0) :=
    fun x y h => p.contained _ x y ((equivalent 0 x y).mp h)
  have wBox : InsideContainer (q 8) :=
    fun x y h => p.contained _ x y ((equivalent 8 x y).mp h)
  have oAnchors := code_one_anchors p (orderedOwner p 0)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 0)
  have lAnchors := code_two_original_anchors p (orderedOwner p 1)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 1)
  have om := coded_exact p (orderedOwner p 0)
  rw [ordered_owner_code p hf 0] at om
  have wm := coded_exact p (orderedOwner p 8)
  rw [ordered_owner_code p hf 8] at wm
  have oMarker : (q 0).Inside 1 (457/500) := (equivalent 0 _ _).mpr (by
    have h := (om 0).mpr (by decide)
    simpa [Owns,S12.marker] using h)
  have oNear := (equivalent 0 _ _).mpr oAnchors.near_point
  have oFar := (equivalent 0 _ _).mpr oAnchors.lower_point
  have oMissing : ¬(q 0).Inside 1 1 :=
    fun h => missingCorner ((equivalent 0 _ _).mp h)
  have oNext : ¬(q 0).Inside 2 (457/500) := by
    intro h
    have absent : (13 : Marker)∉maskSupport (auxiliaryCode 0) := by decide
    apply absent
    apply (om 13).mp
    simpa [Owns,S12.marker] using (equivalent 0 _ _).mp h
  obtain ⟨marker0,d0,e0,_,northwest0,_⟩ := C977CentralReach.central_data p hf
  have marker := (equivalent 5 _ _).mpr marker0
  have aD := (equivalent 5 _ _).mpr d0
  have aE := (equivalent 5 _ _).mpr e0
  have cross := C977CentralReach.central_points p hf
  have aLow := (equivalent 5 _ _).mpr cross.1
  have aLeft := (equivalent 5 _ _).mpr cross.2
  have aWest := (equivalent 5 _ _).mpr west
  have missingNW : ¬(q 5).Inside (33/20) (47/20) :=
    fun h => northwest0 ((equivalent 5 _ _).mp h)
  have lowOriginal : (p.square (orderedOwner p 1)).Inside 1 (8/5) := by
    have owned := forced_auxiliary p hf 1 10 (by decide)
    have point := (nat_combined_exact p (orderedOwner p 1) 10 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point
  have foreignLow : ¬(q 5).Inside 1 (8/5) := fun h =>
    apart p hf 5 1 (by decide) _ _ ⟨(equivalent 5 _ _).mp h,lowOriginal⟩
  have wMarker : (q 8).Inside (457/500) 2 := (equivalent 8 _ _).mpr (by
    have h := (wm 12).mpr (by decide)
    simpa [Owns,S12.marker] using h)
  have wPoint : (q 8).Inside 1 (113/50) := (equivalent 8 _ _).mpr (by
    have owned := forced_auxiliary p hf 8 1 (by decide)
    have point := (nat_combined_exact p (orderedOwner p 8) 1 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have wMissingTop : ¬(q 8).Inside (457/500) 3 := by
    intro h
    have absent : (7 : Marker)∉maskSupport (auxiliaryCode 8) := by decide
    apply absent
    apply (wm 7).mp
    simpa [Owns,S12.marker] using (equivalent 8 _ _).mp h
  have wMissingFar : ¬(q 8).Inside (19/25) (187/100) := fun h =>
    apart p hf 8 1 (by decide) _ _ ⟨(equivalent 8 _ _).mp h,lAnchors.2.2⟩
  have oa : ∀ x y, ¬((q 0).Inside x y ∧ (q 5).Inside x y) :=
    fun x y h => apart p hf 0 5 (by decide) x y
      ⟨(equivalent 0 x y).mp h.1,(equivalent 5 x y).mp h.2⟩
  have aw : ∀ x y, ¬((q 5).Inside x y ∧ (q 8).Inside x y) :=
    fun x y h => apart p hf 5 8 (by decide) x y
      ⟨(equivalent 5 x y).mp h.1,(equivalent 8 x y).mp h.2⟩
  have ab := normal_bounds an
  have centerCap : (q 5).loU+(q 5).side≤2*((q 5).c+(q 5).s) := by
    apply le_of_not_gt
    intro high
    apply missingCenter
    apply (equivalent 5 2 2).mp
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [marker.1,ab.1,an.1]
    · linarith only [high]
    · linarith only [aD.2.2.1,ab.1]
    · linarith only [aE.2.2.2,an.1]
  exact PositiveCentralWallAngleOrder.angle_order (q 0) (q 5) (q 8) t
    on an wn ws sameOA sameAW side sideCap oBox wBox oMarker oNear oFar
    oMissing oNext marker aD aLeft aLow aWest missingNW foreignLow centerCap
    wMarker wPoint wMissingTop wMissingFar oa aw

#print axioms frame_angle_order_of_west
end N12Compact.C977PositiveCornerOrder
