import Compact.Completion.C1092.MMMP.SoutheastSign
import Compact.Completion.C1092.MMMP.RightInnerActual
import Compact.Completion.C1092.MixedWideCrossing
import Compact.Completion.C1092.InwardMissingProfile
import Compact.Completion.C1092.InwardCrossingConflict

/-! Actual MMMP right G8 forces G9. The contrary G9 absence uses the
genuine reflected right wall with its nonpositive center, then the actual
bottom wall in the downstream obstruction. Every square is retained. -/
namespace N12Compact.C1092MMMPRightFar
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092AuxiliaryCover
open C1092MMMPEntrance C1092MMMPOrigins C1092MMMPPointCore C1092RigidCharts
set_option Elab.async false

theorem near_of_lower (p : NormalizedPacking) (hb : WallContext p mmmp)
    (lower : (owners p 10).Inside 3 (8/5)) : (owners p 10).Inside 3 (87/50) := by
  have h := inside_segment (owners p 10) 3 (8/5) 3 (113/50) (7/33)
    lower (wall_auxiliaries p hb).2.2.1 (by norm_num) (by norm_num)
  norm_num at h
  exact h

theorem upper_of_lower (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) (lower : (owners p 10).Inside 3 (8/5)) :
    (owners p 10).Inside 3 (12/5) := by
  classical
  by_contra missing
  have near := near_of_lower p hb lower
  have inward := C1092MMMPSoutheastSign.inward_pair p hf hb near
  have bottom := C1092MMMPBottomPair.pair p hf hb
  obtain ⟨E,ep⟩ := C1092MMMPSoutheastSign.exists_positive p hf hb near
  let C := swap E
  have actual (x y : ℝ) : C.Inside x y ↔ (owners p 5).Inside (2+x) (2-y) :=
    (inside_swap E x y).trans (ep.actual y x)
  have side : 1<C.side := by dsimp [C,swap]; rw [ep.side]; exact side_gt p 5
  have cp : 0<C.c := by
    have h := (C977CornerCubic.normal_bounds ep.normal).1
    dsimp [C,swap]
    linarith only [h]
  have markC : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  have markSW : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have M : C.Inside (7/20) (7/20) := by
    apply (actual _ _).mpr
    norm_num
    exact markC
  have P : C.Inside 0 (13/50) := by
    apply (actual _ _).mpr
    norm_num
    exact inward.1
  have Q : C.Inside (13/50) 0 := by
    apply (actual _ _).mpr
    norm_num
    exact inward.2
  have profile := C1092InwardMissingProfile.profile C side cp
    (by dsimp [C,swap]; linarith only [ep.positive])
    (by dsimp [C,swap]; exact ep.normal.2.1) M P Q
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 5 7 (by decide) _ _ ⟨h,northwest_center p hf hb⟩)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨h,lower⟩)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,bottom.1⟩)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 5 4 (by decide) _ _ ⟨h,markSW⟩)
  let z := C1092WallProfileScalars.half C.c (-C.s)
  have den : 0<1+C.c := by linarith only [cp]
  have zn : 0≤z := by
    dsimp [z,C1092WallProfileScalars.half]
    exact div_nonneg (by linarith only [profile.sine]) den.le
  have angle : z*(1+C.c)=-C.s := by
    dsimp [z,C1092WallProfileScalars.half]
    field_simp [den.ne']
  have unitAngle : (-C.s)*z=1-C.c := by
    dsimp [z,C1092WallProfileScalars.half]
    field_simp [den.ne']
    nlinarith only [C.unit_normal]
  let W := (pullY (owners p 10)).translated 2 2
  have wallInside (x y : ℝ) : W.Inside x y ↔ (owners p 10).Inside (2+x) (2-y) := by
    simp only [W,inside_translated_iff,inside_pullY]
    rw [show 4-(2+y)=2-y by ring]
  have markW : (owners p 10).Inside (1543/500) 2 := by
    simpa [marker] using marker_point p hf 10 14 (by decide +kernel)
  have tipW : (owners p 10).Inside 3 (239/100) := by
    have h := local_wall_segment p mmmp hb 2 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmp,wallOwner,pointMap,branchY] at h
    exact h
  have cutW : centerY W≤0 := by
    have cut : 2≤centerY (owners p 10) := by
      have h : 2≤centerY (pullX (owners p 10)) := by
        simpa [mmmp,wallFrame,localFrame,wallOwner] using (hb 2).1
      have center : centerY (pullX (owners p 10))=centerY (owners p 10) := by
        dsimp [centerY,pullX]
        ring
      rwa [center] at h
    have center : centerY W=2-centerY (owners p 10) := by
      dsimp [W,OpenSquare.translated,pullY,centerY]
      linear_combination 2*(owners p 10).unit_normal
    rw [center]
    linarith only [cut]
  have crossing := C1092MixedWideCrossing.point C W C.c (-C.s) z rfl (by ring) side
    (by
      dsimp [C,swap]
      rw [ep.side]
      change (p.square _).side≤1001/1000
      rw [p.congruent]
      exact p.side_le)
    (by dsimp [C,swap,W]; exact ep.side.trans (side_same p 5 10)) cp
    (by linarith only [profile.sine]) (by dsimp [C,swap]; exact ep.normal.2.1)
    angle unitAngle P Q M profile.lowerV
    (by apply (wallInside _ _).mpr; norm_num; exact markW)
    (by apply (wallInside _ _).mpr; norm_num; exact tipW)
    (by apply (wallInside _ _).mpr; norm_num; exact lower)
    (by
      intro own
      have h := (wallInside _ _).mp own
      norm_num at h
      exact missing h)
    (by
      intro x y own
      have h := (wallInside _ _).mp own
      have box := p.contained _ _ _ h
      linarith only [box.2.1]) cutW
    (fun x y own => owners_disjoint p hf 5 10 (by decide) _ _
      ⟨(actual _ _).mp own.1,(wallInside _ _).mp own.2⟩)
  let A := translate (swap C) (-2) (-2)
  let R := pullSwap (pullY (owners p 9))
  have aInside (x y : ℝ) : A.Inside x y ↔ (owners p 5).Inside y (4-x) := by
    change (translate (swap C) (-2) (-2)).Inside x y ↔ _
    rw [inside_translate,inside_swap,actual]
    rw [show 2+(y+-2)=y by ring,show 2-(x+-2)=4-x by ring]
  have escape : 2*A.c+2*A.s≤A.loU := by
    dsimp [A,translate,swap]
    linarith only [profile.lowerV]
  have floor : -(47/20)*A.s+(33/20)*A.c≤A.loV := by
    dsimp [A,translate,swap]
    linarith only [profile.lowerU]
  have markB : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_point p hf 9 13 (by decide +kernel)
  exact C1092InwardCrossingConflict.impossible A R side
    (by dsimp [A,translate,swap,C,R]; exact ep.side.trans (side_same p 5 9)) cp
    (by dsimp [A,translate,swap]; linarith only [profile.sine]) escape floor
    (by
      apply (aInside _ _).mpr
      norm_num
      exact inward.1)
    (by
      change (translate (swap C) (-2) (-2)).Inside _ _
      rw [inside_translate,inside_swap]
      norm_num
      exact profile.outer)
    z zn profile.halfSmall
    (by simpa only [A,translate,swap,mul_comm] using angle)
    (by simpa only [A,translate,swap] using unitAngle)
    (by
      change (translate (swap C) (-2) (-2)).Inside _ _
      rw [inside_translate,inside_swap]
      convert crossing.2 using 1 <;> ring)
    (container_transform ⟨true,false,true⟩ _ (p.contained _))
    (by norm_num [R,inside_pullSwap,inside_pullY]; exact markB)
    (by norm_num [R,inside_pullSwap,inside_pullY]; exact bottom.1)
    (fun x y own => owners_disjoint p hf 5 9 (by decide) _ _
      ⟨(aInside _ _).mp own.1,(inside_pullY _ _ _).mp ((inside_pullSwap _ _ _).mp own.2)⟩)

theorem point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 10).Inside 3 (12/5) := by
  rcases right_g_cover p hf with h|h|h
  · exact False.elim (C1092MMMPRightInnerActual.right_missing_inner p hf hb h)
  · exact upper_of_lower p hf hb h
  · exact h

#print axioms upper_of_lower
#print axioms point
end N12Compact.C1092MMMPRightFar
