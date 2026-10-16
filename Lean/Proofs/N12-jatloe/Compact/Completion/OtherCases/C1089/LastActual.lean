import Compact.Completion.OtherCases.C1089.SectorEntrances
import Compact.Completion.CommonCases.SingletonMissing

/-! The complete actual-family producer for C1089's last-sector input.
Every former finite point premise is proved from compact actual domains
and continuous ownership arguments. The stronger singleton seeds are
proved only under the genuine omitted-corner assumption, using its exact
singleton marker set. The southwest corner is never assumed. Source only.
-/
namespace N12Compact.Completion.OtherCases.C1089.LastActual
open S12 S12Pilot OriginalData WallCore SectorEntrances
set_option Elab.async false
noncomputable section

theorem stronger_singleton_seeds (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 0).Inside 1 1) :
    (owners p 0).Inside (91/50) 1 ∧ (owners p 0).Inside (49/25) (19/25) := by
  have exactMarkers : ExactMarkers (owners p 0) (maskSupport 1) := by
    have code := CommonCases.OriginalOwners.code family p hf 1 (by decide +kernel)
    change ExactMarkers (p.square (ownerIndex p 1)) (maskSupport 1)
    simpa only [code] using coded_exact p (ownerIndex p 1)
  have support : maskSupport 1=({0} : Finset Marker) := by decide +kernel
  rw [support] at exactMarkers
  have cap : (owners p 0).side≤1001/1000 := by
    change (p.square (ownerIndex p 1)).side≤1001/1000
    rw [p.congruent]
    exact p.side_le
  exact CommonCases.SingletonMissing.zero_missing_points _ ((frame p hf).side 0)
    cap ((frame p hf).box 0) exactMarkers missing

theorem input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) (top : 2≤centerX (owners p 11)) :
    LastSectorRawPoints.Input (owners p) := by
  let h := frame p hf
  have se := southeast_inward p hf right
  have ne := last_ne_pair p hf right top
  have l := last_left_pair p hf right
  have r := last_right_pair p hf right top
  have rightLow := WallOrigins.right_low (owners p) (h.side 10) (h.box 10) h.apart
    h.rightMarker r.2 ne.1 h.southeastMarker
  have rightMiddle : (owners p 10).Inside 3 (3/2) := by
    convert inside_segment (owners p 10) 3 (36/25) 3 (8/5) (3/8)
      rightLow r.2 (by norm_num) (by norm_num) using 1 <;> norm_num
  have sSouth : (owners p 5).Inside 2 (3/2) := by
    have point := C981CompletionCrosspoint.point (pullY (owners p 5)) (h.side 5)
      (by norm_num [inside_pullY]; exact se.1)
      (by norm_num [inside_pullY]; exact se.2)
      (by norm_num [inside_pullY]; exact h.southeastMarker)
      (by norm_num [inside_pullY]; exact fun own =>
        h.apart 5 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
      (by norm_num [inside_pullY]; exact fun own =>
        h.apart 5 4 (by decide) _ _ ⟨own,h.southwestMarker⟩)
      (by norm_num [inside_pullY]; exact fun own =>
        h.apart 5 10 (by decide) _ _ ⟨own,r.2⟩)
      (by norm_num [inside_pullY]; exact fun own =>
        h.apart 5 10 (by decide) _ _ ⟨own,rightMiddle⟩)
    norm_num [inside_pullY] at point
    exact point
  have aF0 : (owners p 4).Inside 1 (87/50) := by
    rcases AuxiliaryCover.southwest_f_cover p hf with own | own | own
    · exact own
    · exact False.elim (h.apart 4 0 (by decide) _ _
        ⟨own,singleton_bar p hf _ (by norm_num) (by norm_num)⟩)
    · exact False.elim (h.apart 4 5 (by decide) _ _ ⟨own,se.1⟩)
  have aG0 : (owners p 4).Inside 1 (8/5) := by
    by_contra missing
    have g3 : (owners p 4).Inside (87/50) 2 := by
      rcases AuxiliaryCover.southwest_g_cover p hf with own | own | own
      · exact False.elim (missing own)
      · exact False.elim (h.apart 4 0 (by decide) _ _ ⟨own,h.singletonFar⟩)
      · exact own
    have point := ElbowPoint.points_original (pullX (owners p 4)) (h.side 4)
      (by norm_num [inside_pullX]; exact h.southwestMarker)
      (by norm_num [inside_pullX]; exact g3)
      (by norm_num [inside_pullX]; exact aF0)
      (by norm_num [inside_pullX]; exact fun own =>
        h.apart 4 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
      (by norm_num [inside_pullX]; exact missing)
      (by norm_num [inside_pullX]; exact fun own =>
        h.apart 4 8 (by decide) _ _ ⟨own,h.leftMarker⟩)
    norm_num [inside_pullX] at point
    exact h.apart 4 5 (by decide) _ _ ⟨point.1,sSouth⟩
  have nw := LastSectorNorthwest.ordinary_pair (owners p) {
    side := h.side
    apart := h.apart
    singletonNear := h.singletonNear
    singletonFar := h.singletonFar
    absentMarker := h.absentMarker 4
    southwestMarker := h.southwestMarker
    southwestF0 := aF0
    southwestG0 := aG0
    southeastSouth := sSouth
    northeastMarker := h.northeastMarker
    northwestMarker := h.northwestMarker
    northwestF := AuxiliaryCover.northwest_f_cover p hf
    northwestG := AuxiliaryCover.northwest_g_cover p hf
    leftMarker := h.leftMarker
    leftF1 := l.1
    leftG1 := l.2
    topMarker := h.topMarker }
  exact {
    side := h.side
    same := h.same
    contained := h.box
    apart := h.apart
    absentMarker := h.absentMarker
    singletonMarker := h.singletonMarker
    singletonNear := h.singletonNear
    singletonFar := h.singletonFar
    singletonOffRow := h.singletonSeed
    strongerSeeds := stronger_singleton_seeds p hf
    southeastCornerMarker := h.southeastCornerBottom
    southeastCornerEastMarker := h.southeastCornerRight
    southeastCorner := h.southeastCorner
    northeastCornerMarker := h.northeastCornerTop
    northeastCorner := h.northeastCorner
    northwestCorner := h.northwestCorner
    southwestMarker := h.southwestMarker
    southwestF := AuxiliaryCover.southwest_f_cover p hf
    southwestG := AuxiliaryCover.southwest_g_cover p hf
    southeastMarker := h.southeastMarker
    southeastF4 := se.1
    southeastG6 := se.2
    northeastMarker := h.northeastMarker
    northeastF9 := ne.1
    northeastG9 := ne.2
    northwestMarker := h.northwestMarker
    northwestF := AuxiliaryCover.northwest_f_cover p hf
    northwestG := AuxiliaryCover.northwest_g_cover p hf
    leftMarker := h.leftMarker
    leftF1 := l.1
    leftG1 := l.2
    bottomMarker := h.bottomMarker
    bottomF6 := DirectDomains.bottom_far p hf
    bottomG5 := (bottom p hf).2.2 _ (by norm_num) (by norm_num)
    rightMarker := h.rightMarker
    rightF8 := r.1
    rightG8 := r.2
    rightSign := right
    topMarker := h.topMarker
    topF7 := DirectDomains.top_f7 p hf
      (fun own => h.apart 11 7 (by decide) _ _ ⟨own,nw.1⟩)
    topG7 := top_high p hf top _ (by norm_num) (by norm_num) }

theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) (top : 2≤centerX (owners p 11)) : False :=
  LastSectorRawPoints.impossible _ (input p hf right top)

end
#print axioms stronger_singleton_seeds
#print axioms input
#print axioms impossible
end N12Compact.Completion.OtherCases.C1089.LastActual
