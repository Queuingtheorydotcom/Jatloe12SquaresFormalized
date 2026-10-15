import Compact.Cases.C868.UpperNegativeCapFaces
import Compact.Cases.C868.UpperNegativeCapScalars
import Compact.Cases.C868.UpperNegativeTopFaces
import Compact.Geometry.ClosedPointExclusion
import Compact.Completion.OtherCases.WallProfile.VertexGeometry

/-! The surviving merged square supplies two closed points of the same
physical square. The top square contains one strictly in either of its
two exhaustive first-quadrant angle ranges. Boundary contact is handled
by ClosedPointExclusion, not by treating a vertex as a strict point. -/
namespace N12Compact.C868.UpperNegativeCap
open S12 S12Pilot C977CornerCubic MergedPending.NegativeUpperFaces
open FourSquareAnchors
set_option Elab.async false

structure Data (H : OpenSquare) : Prop extends Input H where
  nearFloor : -(1/20)*(H.c-H.s)≤H.loV
  topCap : H.loV+H.side≤(543/500)*H.c
  nearCap : H.loU+H.side≤(23/50)*H.c+(1/100)*H.s

private theorem scalar_inputs (H : OpenSquare) (h : Data H) :
    1<(18/25)*H.c-(99/100)*H.s ∧
      1<(142/125)*H.c-(1/20)*H.s := by
  exact ⟨span H h.toInput h.nearCap,by linarith only [h.side,h.nearFloor,h.topCap]⟩

private def peakX (H : OpenSquare) : ℝ := H.c*H.loU-H.s*(H.loV+H.side)
private def peakY (H : OpenSquare) : ℝ := H.s*H.loU+H.c*(H.loV+H.side)

theorem peak_closed (H : OpenSquare) : ClosedInside H (peakX H) (peakY H) := by
  exact Completion.OtherCases.WallProfile.vertex H H.loU (H.loV+H.side)
    ⟨le_rfl,by linarith only [H.side_pos]⟩
    ⟨by linarith only [H.side_pos],le_rfl⟩

theorem peak_bounds (H : OpenSquare) (h : Data H) :
    -(13/50)≤peakX H ∧ peakX H< -(1/25) ∧
      53/50<peakY H ∧ peakY H<59/50 ∧
      (543/500)+(43/400)*peakX H<peakY H := by
  have bounds := normal_bounds h.normal
  have cp : 0<H.c := by linarith only [bounds.1]
  have sn : 0≤-H.s := h.normal.1
  have floorU := lower_u H h.toInput
  have floorV := lower_v H h.toInput
  have inputs := scalar_inputs H h
  have height := UpperNegativeCapScalars.height H.c (-H.s) h.normal inputs.1 inputs.2
  have left := UpperNegativeCapScalars.left H.c (-H.s) h.normal inputs.1 inputs.2
  have top := UpperNegativeCapScalars.top H.c (-H.s) h.normal inputs.1 inputs.2
  have chord := UpperNegativeCapScalars.chord H.c (-H.s) h.normal inputs.1 inputs.2
  have uLow := mul_nonneg cp.le (sub_nonneg.mpr floorU)
  have vLow := mul_nonneg sn (sub_nonneg.mpr floorV)
  have uCap := mul_nonneg cp.le (sub_nonneg.mpr h.nearCap)
  have vCap := mul_nonneg sn (sub_nonneg.mpr h.topCap)
  have cWidth := mul_pos cp (sub_pos.mpr h.side)
  have sWidth := mul_nonneg sn (sub_nonneg.mpr h.side.le)
  have cShort := mul_nonneg sn (sub_nonneg.mpr bounds.2.1)
  have xLow : -(13/50)≤peakX H := by
    dsimp only [peakX]
    nlinarith only [uLow,vLow,sWidth,cShort,H.unit_normal]
  have xHigh : peakX H< -(1/25) := by
    dsimp only [peakX]
    nlinarith only [uCap,vCap,cWidth,left]
  have uLowY := mul_nonneg sn (sub_nonneg.mpr floorU)
  have vCapY := mul_nonneg cp.le (sub_nonneg.mpr h.topCap)
  have yHigh : peakY H<59/50 := by
    dsimp only [peakY]
    nlinarith only [uLowY,vCapY,top,H.unit_normal]
  have uCapY := mul_nonneg sn (sub_nonneg.mpr h.nearCap)
  have vNearY := mul_nonneg cp.le (sub_nonneg.mpr h.nearFloor)
  have yLow : 53/50<peakY H := by
    dsimp only [peakY]
    nlinarith only [uCapY,vNearY,cWidth,sWidth,height]
  have coeffU : 0< -H.s+(43/400)*H.c := by linarith only [cp,sn]
  have coeffV : 0<H.c+(43/400)*H.s := by linarith only [cp,h.normal.2.1]
  have uChord := mul_nonneg coeffU.le (sub_nonneg.mpr h.nearCap)
  have vChord := mul_nonneg coeffV.le (sub_nonneg.mpr h.nearFloor)
  have widthChord := mul_pos (add_pos coeffU coeffV) (sub_pos.mpr h.side)
  have above : (543/500)+(43/400)*peakX H<peakY H := by
    dsimp only [peakX,peakY]
    nlinarith only [uChord,vChord,widthChord,chord]
  exact ⟨xLow,xHigh,yLow,yHigh,above⟩

/-- A closed point on the same square's left U edge, at the fixed height
1.06. Its other three bands are strict, but the U equality is retained. -/
theorem edge_point (H : OpenSquare) (h : Data H) :
    ∃ x : ℝ, -(13/50)≤x ∧ x≤ -(7/100) ∧ ClosedInside H x (53/50) := by
  have bounds := normal_bounds h.normal
  have cp : 0<H.c := by linarith only [bounds.1]
  have inputs := scalar_inputs H h
  have scalar := UpperNegativeCapScalars.edge H.c (-H.s) h.normal inputs.1 inputs.2
  have high := (peak_bounds H h).2.2.1
  have floor := lower_u H h.toInput
  let x := (H.loU-(53/50)*H.s)/H.c
  have ux : H.c*x+(53/50)*H.s=H.loU := by
    dsimp only [x]
    field_simp [ne_of_gt cp]
    ring
  have vx : H.c*(-H.s*x+H.c*(53/50))=53/50-H.s*H.loU := by
    calc
      _ = -H.s*(H.c*x+(53/50)*H.s)+(53/50)*(H.c^2+H.s^2) := by ring
      _ = _ := by rw [ux,H.unit_normal]; ring
  have xLow : -(13/50)≤x := by
    nlinarith only [ux,floor,h.normal.1,cp]
  have xHigh : x≤ -(7/100) := by
    nlinarith only [ux,h.nearCap,h.side,scalar,cp]
  have lowerU := mul_nonneg h.normal.1 (sub_nonneg.mpr floor)
  have upperV := mul_pos cp (sub_pos.mpr h.northwest.2.2.1)
  have sign := mul_nonneg cp.le h.normal.1
  have low : H.s*H.loU+H.c*H.loV<1 := by
    nlinarith only [lowerU,upperV,sign,H.unit_normal,sq_nonneg H.c]
  refine ⟨x,xLow,xHigh,?_,?_,?_,?_⟩
  · linarith only [ux]
  · linarith only [ux,H.side_pos]
  · nlinarith only [vx,low,cp]
  · dsimp only [peakY] at high
    nlinarith only [vx,high,cp]

theorem impossible (H T : OpenSquare) (h : Data H)
    (side : 1<T.side) (cp : 0<T.c) (sn : 0≤T.s)
    (far : T.Inside (-4/5) 1) (marker : T.Inside 0 (543/500))
    (apart : ∀ x y,¬(H.Inside x y ∧ T.Inside x y)) : False := by
  have missing : ¬T.Inside (-7/20) (7/20) := fun own =>
    apart _ _ ⟨h.northwest,own⟩
  have exclusion (x y : ℝ) (closed : ClosedInside H x y) : ¬T.Inside x y :=
    ClosedPointExclusion.outside_of_closed T H x y
      (fun x y own => apart x y ⟨own.2,own.1⟩) closed
  by_cases shallow : T.s≤(2/5)*T.c
  · have b := peak_bounds H h
    apply exclusion _ _ (peak_closed H)
    exact UpperNegativeTopFaces.shallow_region_tight T side cp sn shallow far marker missing
      (peakX H) (peakY H) (by linarith only [b.1]) b.2.1.le
      (by linarith only [b.2.2.1]) b.2.2.2.1.le b.2.2.2.2
  · obtain ⟨x,left,right,closed⟩ := edge_point H h
    exact exclusion x (53/50) closed
      (UpperNegativeTopFaces.steep_region T cp sn (le_of_not_ge shallow)
        far marker x left right)

#print axioms peak_bounds
#print axioms edge_point
#print axioms impossible
end N12Compact.C868.UpperNegativeCap
