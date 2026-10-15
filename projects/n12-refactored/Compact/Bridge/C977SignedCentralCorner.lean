import Compact.Bridge.C977CenterIncoming
import Compact.Bridge.C977CenterCornerAlternatives
import Compact.Bridge.C977BottomExtendedReach
import Compact.Bridge.C977WallMiddle
import Compact.Geometry.CentralBottomTransverse
import Compact.Geometry.CentralNegativeIncoming
import Compact.Geometry.CentralSteeperBottomReach

/-! The original missing-bottom-corner root forces the genuine negative
southeast cap for every signed central frame. No diagonal transport of
the missing-corner hypothesis or auxiliary ownership selection is used. -/
namespace N12Compact.C977SignedCentralCorner

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

/-- The complete right incoming classification has one remaining cap,
for arbitrary signed canonical A. Its full bottom and paired-corner
continuation remains a separate geometric obligation. -/
theorem frame_cap (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (center : (p.square (orderedOwner p 5)).Inside 2 2) :
    (q 6).s<0 ∧ (q 6).loU+(q 6).side≤3*(q 6).c+(q 6).s := by
  have side : 1<(q 6).side := by rw [shape,p.congruent]; exact p.side_gt_one
  have aCenter := (equivalent 5 _ _).mpr center
  have aLow := (equivalent 5 _ _).mpr (C977CentralReach.central_points p hf).1
  have markers := coded_exact p (orderedOwner p 6)
  rw [ordered_owner_code p hf 6] at markers
  have marker : (q 6).Inside (47/20) (33/20) := (equivalent 6 _ _).mpr (by
    have point := (markers 9).mpr (by decide)
    simpa [Owns,marker] using point)
  have wall : (q 6).Inside 3 (87/50) := (equivalent 6 _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 6, 8∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 6)
    have point := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have cornerMissing : ¬(q 6).Inside 3 1 := fun h => p.disjoint _ _
    (fun eq => (by decide : (6 : Fin 12)≠2) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent 6 _ _).mp h,C977RightCornerSupport.southeast_corner p hf⟩
  have middle := C977WallMiddle.right_point p hf
  have middleMissing : ¬(q 6).Inside 3 2 := fun h => p.disjoint _ _
    (fun eq => (by decide : (6 : Fin 12)≠10) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent 6 _ _).mp h,middle⟩
  have dLow : (p.square (orderedOwner p 9)).Inside (12/5) 1 := by
    have check : ∀ owned∈pruningDomain4 9, 6∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 9)
    have point := (nat_combined_exact p (orderedOwner p 9) 6 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point
  have dHigh := C977BottomExtendedReach.point p hf missingCorner
  have lowMissing : ¬(q 6).Inside (12/5) 1 := fun h => p.disjoint _ _
    (fun eq => (by decide : (6 : Fin 12)≠9) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent 6 _ _).mp h,dLow⟩
  have highMissing : ¬(q 6).Inside (13/5) 1 := fun h => p.disjoint _ _
    (fun eq => (by decide : (6 : Fin 12)≠9) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent 6 _ _).mp h,dHigh⟩
  have noShift (shift : 0≤(q 10).s ∧
      3*(q 10).c+2*(q 10).s≤(q 10).loU) : False := by
    have point := (equivalent 10 _ _).mpr middle
    linarith only [point.1,shift.2]
  have positiveFloor (bn : Normal (q 6).c (q 6).s) :
      (q 6).c-3*(q 6).s≤(q 6).loV := by
    rcases CentralRightCornerAlternatives.canonical_corner_faces (q 6)
        (canonical 6).2 marker cornerMissing with cap | escape
    · exfalso
      nlinarith only [cap,wall.2.1,bn.1]
    · exact escape
  have inwardCap (floor : (q 6).c-3*(q 6).s≤(q 6).loV) :
      (q 6).loU+(q 6).side≤3*(q 6).c+2*(q 6).s :=
    CentralBottomTransverse.inward_cap (q 6) (canonical 6).2 side marker wall
      floor middleMissing
  rcases (C977CenterIncoming.frame_cover p hf q shape equivalent canonical center).1 with
      own | neighboring | transverse
  · by_cases ordered : 0≤(q 5).s*(q 6).c-(q 5).c*(q 6).s
    · rcases C977CenterCornerAlternatives.ordered_axis_alternatives p hf q shape equivalent
        (canonical 5).2 (canonical 6).2 (canonical 10).2 ordered center own with cap | shift
      · exact cap
      · exact False.elim (noShift shift)
    · have reverse : (q 5).s*(q 6).c<(q 5).c*(q 6).s := by
        linarith only [ordered]
      by_cases positiveB : 0≤(q 6).s
      · have bn : Normal (q 6).c (q 6).s :=
          ⟨positiveB,by simpa only [abs_of_nonneg positiveB] using (canonical 6).2,
            (q 6).unit_normal⟩
        have cap := inwardCap (positiveFloor bn)
        exfalso
        by_cases positiveA : 0≤(q 5).s
        · have an : Normal (q 5).c (q 5).s :=
            ⟨positiveA,by simpa only [abs_of_nonneg positiveA] using (canonical 5).2,
              (q 5).unit_normal⟩
          exact CentralSteeperBottomReach.impossible (q 6) an bn side reverse.le cap
            (by linarith only [aCenter.2.1,own]) wall lowMissing highMissing
        · have negativeA : (q 5).s<0 := lt_of_not_ge positiveA
          have an : Normal (q 5).c (-(q 5).s) :=
            ⟨by linarith only [negativeA],
              by simpa only [abs_of_neg negativeA] using (canonical 5).2,
              by nlinarith only [(q 5).unit_normal]⟩
          exact CentralSteeperBottomReach.negative_impossible (q 6) an bn side cap
            (by linarith only [aLow.2.1,own]) wall lowMissing highMissing
      · have negativeB : (q 6).s<0 := lt_of_not_ge positiveB
        rcases CentralRightCornerAlternatives.canonical_corner_faces (q 6)
            (canonical 6).2 marker cornerMissing with cap | floor
        · exact ⟨negativeB,cap⟩
        · have negativeA : (q 5).s<0 := by
            by_contra no
            have nonneg := mul_nonneg (le_of_not_gt no) (canonical 6).1.le
            have negative := mul_neg_of_pos_of_neg (canonical 5).1 negativeB
            linarith only [reverse,nonneg,negative]
          have an : Normal (q 5).c (-(q 5).s) :=
            ⟨by linarith only [negativeA],
              by simpa only [abs_of_neg negativeA] using (canonical 5).2,
              by nlinarith only [(q 5).unit_normal]⟩
          have bn : Normal (q 6).c (-(q 6).s) :=
            ⟨by linarith only [negativeB],
              by simpa only [abs_of_neg negativeB] using (canonical 6).2,
              by nlinarith only [(q 6).unit_normal]⟩
          have bound := CentralNegativeIncoming.lower_bound (q 6) (-(q 6).s)
            (C := (q 5).c) (S := -(q 5).s) (by ring) an bn side.le
            (by nlinarith only [reverse]) (by nlinarith only [floor])
            (by nlinarith only [inwardCap floor])
          simp only [neg_neg] at bound
          exfalso
          nlinarith only [bound,own,aLow.2.1]
  · rcases C977CenterCornerAlternatives.all_frame_alternatives p hf q shape equivalent
      (canonical 6).2 (canonical 10).2 center neighboring with cap | shift
    · exact cap
    · exact False.elim (noShift shift)
  · have positiveB : 0≤(q 6).s := by
      linarith only [transverse.1,(canonical 6).1]
    have bn : Normal (q 6).c (q 6).s :=
      ⟨positiveB,by simpa only [abs_of_nonneg positiveB] using (canonical 6).2,
        (q 6).unit_normal⟩
    have strict := strict_bounds (q 5) _ _ (-(q 6).s) (q 6).c
      (by nlinarith only [(q 6).unit_normal]) aLow
    exact False.elim (highMissing (CentralBottomTransverse.point (q 6) bn side wall
      (inwardCap (positiveFloor bn)) (by linarith only [strict.1,transverse.2])))

#print axioms frame_cap
end N12Compact.C977SignedCentralCorner
