import Compact.Completion.OtherCases.C1091.EntranceFrame
import Compact.Completion.OtherCases.C1089.WallCore
import Compact.Completion.OtherCases.C1089.ContinuousActual

/-! The original C1091 wall signs and ordinary inward pairs. These are
point-level applications of the shared continuous incoming-pair theorem.
Q4 remains merged258. The real left square is Q8=4096. Source only. -/
namespace N12Compact.Completion.OtherCases.C1091.EntranceWalls
open S12 S12Pilot OriginalData EntranceFrame
set_option Elab.async false
noncomputable section

theorem left_high (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (sign : 2≤centerY (owners p 8)) (y : ℝ) (low : 111/50≤y) (high : y≤239/100) :
    (owners p 8).Inside 1 y := by
  let h := frame p hf
  exact WallSignChord.chord _ (h.side 8) (fun x y own => (h.box 8 x y own).1)
    h.leftMarker (fun own => h.apart 8 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
    sign y low high

theorem left_low (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (sign : centerY (owners p 8)≤2) (y : ℝ) (low : 161/100≤y) (high : y≤89/50) :
    (owners p 8).Inside 1 y := by
  let h := frame p hf
  have point := WallSignChord.chord (pullY (owners p 8)) (h.side 8)
    (fun x y own => (h.box 8 _ _ ((inside_pullY _ _ _).mp own)).1)
    (by norm_num [inside_pullY]; exact h.leftMarker)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 8 4 (by decide) _ _ ⟨own,h.southwestMarker⟩)
    (by rw [center_pullY_y]; linarith only [sign]) (4-y)
    (by linarith only [high]) (by linarith only [low])
  norm_num [inside_pullY] at point
  exact point

theorem right_high (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (sign : 2≤centerY (owners p 10)) (y : ℝ) (low : 111/50≤y) (high : y≤239/100) :
    (owners p 10).Inside 3 y := by
  let h := frame p hf
  have point := WallSignChord.chord (pullX (owners p 10)) (h.side 10)
    (by
      intro x y own
      have wall := (h.box 10 _ _ ((inside_pullX _ _ _).mp own)).2.1
      linarith only [wall])
    (by norm_num [inside_pullX]; exact h.rightMarker)
    (by norm_num [inside_pullX]; exact fun own =>
      h.apart 10 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
    (by simpa only [center_pullX_y] using sign) y low high
  norm_num [inside_pullX] at point
  exact point

theorem right_low (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (sign : centerY (owners p 10)≤2) (y : ℝ) (low : 161/100≤y) (high : y≤89/50) :
    (owners p 10).Inside 3 y := by
  let h := frame p hf
  have point := WallSignChord.chord (pullY (pullX (owners p 10))) (h.side 10)
    (by
      intro x y own
      have wall := (h.box 10 _ _ ((inside_pullX _ _ _).mp
        ((inside_pullY _ _ _).mp own))).2.1
      linarith only [wall])
    (by norm_num [inside_pullY,inside_pullX]; exact h.rightMarker)
    (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
      h.apart 10 5 (by decide) _ _ ⟨own,h.southeastMarker⟩)
    (by rw [center_pullY_y,center_pullX_y]; linarith only [sign]) (4-y)
    (by linarith only [high]) (by linarith only [low])
  norm_num [inside_pullY,inside_pullX] at point
  exact point

theorem top_high (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (sign : 2≤centerX (owners p 11)) (x : ℝ) (low : 111/50≤x) (high : x≤239/100) :
    (owners p 11).Inside x 3 := by
  let h := frame p hf
  have point := WallSignChord.chord (pullSwap (pullY (owners p 11))) (h.side 11)
    (by
      intro x y own
      have wall := (h.box 11 _ _ ((inside_pullY _ _ _).mp
        ((inside_pullSwap _ _ _).mp own))).2.2.2
      linarith only [wall])
    (by norm_num [inside_pullSwap,inside_pullY]; exact h.topMarker)
    (by norm_num [inside_pullSwap,inside_pullY]; exact fun own =>
      h.apart 11 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
    (by simpa only [center_pullSwap_y,center_pullY_x] using sign) x low high
  norm_num [inside_pullSwap,inside_pullY] at point
  exact point

theorem top_low (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (sign : centerX (owners p 11)≤2) (x : ℝ) (low : 161/100≤x) (high : x≤89/50) :
    (owners p 11).Inside x 3 := by
  let h := frame p hf
  have point := WallSignChord.chord (pullSwap (pullY (pullX (owners p 11)))) (h.side 11)
    (by
      intro x y own
      have wall := (h.box 11 _ _ ((inside_pullX _ _ _).mp ((inside_pullY _ _ _).mp
        ((inside_pullSwap _ _ _).mp own)))).2.2.2
      linarith only [wall])
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact h.topMarker)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact fun own =>
      h.apart 11 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
    (by rw [center_pullSwap_y,center_pullY_x,center_pullX_x]; linarith only [sign]) (4-x)
    (by linarith only [high]) (by linarith only [low])
  norm_num [inside_pullSwap,inside_pullY,inside_pullX] at point
  exact point

abbrev incoming_pair := C1089.WallCore.incoming_pair

theorem northwest_inward (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (left : 2≤centerY (owners p 8)) (top : centerX (owners p 11)≤2) :
    (owners p 7).Inside 2 (113/50) ∧ (owners p 7).Inside (87/50) 2 := by
  let h := frame p hf
  exact incoming_pair _ (h.side 7) h.northwestMarker
    (EntranceDomains.northwest_f p hf) (EntranceDomains.northwest_g p hf)
    (fun own => h.apart 7 8 (by decide) _ _
      ⟨own,left_high p hf left _ (by norm_num) (by norm_num)⟩)
    (fun own => h.apart 7 11 (by decide) _ _
      ⟨own,top_low p hf top _ (by norm_num) (by norm_num)⟩)
    (fun own => h.apart 7 11 (by decide) _ _
      ⟨own,top_low p hf top _ (by norm_num) (by norm_num)⟩)
    (fun own => h.apart 7 8 (by decide) _ _
      ⟨own,left_high p hf left _ (by norm_num) (by norm_num)⟩)
    (fun own => h.apart 7 3 (by decide) _ _ ⟨own,h.northwestCorner⟩)

theorem northeast_inward (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : 2≤centerY (owners p 10)) (top : 2≤centerX (owners p 11)) :
    (owners p 6).Inside 2 (113/50) ∧ (owners p 6).Inside (113/50) 2 := by
  let h := frame p hf
  have fc := EntranceDomains.northeast_f p hf
  have gc := EntranceDomains.northeast_g p hf
  have result := incoming_pair (pullX (owners p 6)) (h.side 6)
    (by norm_num [inside_pullX]; exact h.northeastMarker)
    (by norm_num [inside_pullX]; tauto)
    (by norm_num [inside_pullX]; tauto)
    (by norm_num [inside_pullX]; exact fun own => h.apart 6 10 (by decide) _ _
      ⟨own,right_high p hf right _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullX]; exact fun own => h.apart 6 11 (by decide) _ _
      ⟨own,top_high p hf top _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullX]; exact fun own => h.apart 6 11 (by decide) _ _
      ⟨own,top_high p hf top _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullX]; exact fun own => h.apart 6 10 (by decide) _ _
      ⟨own,right_high p hf right _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullX]; exact fun own =>
      h.apart 6 2 (by decide) _ _ ⟨own,h.northeastCorner⟩)
  norm_num [inside_pullX] at result
  exact result

theorem southeast_inward (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) :
    (owners p 5).Inside 2 (87/50) ∧ (owners p 5).Inside (113/50) 2 := by
  let h := frame p hf
  have fc := EntranceDomains.southeast_f p hf
  have gc := EntranceDomains.southeast_g p hf
  have result := incoming_pair (pullSwap (owners p 5)) (h.side 5)
    (by norm_num [inside_pullSwap]; exact h.southeastMarker)
    (by norm_num [inside_pullSwap]; tauto)
    (by norm_num [inside_pullSwap]; tauto)
    (by norm_num [inside_pullSwap]; exact fun own => h.apart 5 9 (by decide) _ _
      ⟨own,(EntranceDomains.bottom_bar p hf).2.2 _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap]; exact fun own => h.apart 5 10 (by decide) _ _
      ⟨own,right_low p hf right _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap]; exact fun own => h.apart 5 10 (by decide) _ _
      ⟨own,right_low p hf right _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap]; exact fun own => h.apart 5 9 (by decide) _ _
      ⟨own,(EntranceDomains.bottom_bar p hf).2.2 _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap]; exact fun own =>
      h.apart 5 1 (by decide) _ _ ⟨own,h.southeastCorner⟩)
  norm_num [inside_pullSwap] at result
  exact ⟨result.2,result.1⟩


/-- Equality belongs to the excluded low sign: F0 would have two actual
strict owners. This uses the merged-marker proof, not a mask256 domain. -/
theorem left_above (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    2<centerY (owners p 8) := by
  by_contra failure
  have low : centerY (owners p 8)≤2 := le_of_not_gt failure
  exact apart p hf 4 8 (by decide) _ _
    ⟨EntranceMergedLow.original p hf,
      left_low p hf low (87/50) (by norm_num) (by norm_num)⟩

theorem southeast_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) :
    (owners p 5).Inside 2 2 ∧ (owners p 10).Inside 3 2 := by
  let h := frame p hf
  have se := southeast_inward p hf right
  exact C1089.ContinuousActual.southeast (owners p) h.side h.same h.box h.apart
    h.southeastMarker se.1 se.2 h.southwestMarker h.rightMarker
    (right_low p hf right _ (by norm_num) (by norm_num)) right
    h.bottomMarker (EntranceDomains.bottom_far p hf) h.singletonFar
    h.southeastCornerRight h.southeastCorner

theorem northwest_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (top : centerX (owners p 11)≤2) :
    (owners p 7).Inside 2 2 ∧ (owners p 11).Inside 2 3 := by
  let h := frame p hf
  have nw := northwest_inward p hf (left_above p hf).le top
  exact C1089.ContinuousActual.northwest (owners p) h.side h.same h.box h.apart
    h.northwestMarker nw.2 nw.1 h.southwestMarker h.topMarker
    (top_low p hf top _ (by norm_num) (by norm_num)) top
    h.leftMarker (EntranceDomains.left_pair p hf).2 h.mergedLow
    h.northwestCornerTop h.northwestCorner

theorem right_low_top_low_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) (top : centerX (owners p 11)≤2) : False :=
  apart p hf 5 7 (by decide) _ _
    ⟨(southeast_center p hf right).1,(northwest_center p hf top).1⟩

end
#print axioms southeast_inward
#print axioms northwest_inward
#print axioms northeast_inward
end N12Compact.Completion.OtherCases.C1091.EntranceWalls
