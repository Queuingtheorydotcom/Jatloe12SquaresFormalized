import Compact.Completion.OtherCases.C1089.DirectDomains
import Compact.Completion.OtherCases.C1089.ContinuousBottom
import Compact.Completion.C1092.CornerTwoGaps
import Compact.Completion.C1092.MixedSpan

/-! C1089's actual wall chords and incoming central pairs. The chords
retain their proved closed endpoints 2.22 and 2.39. The pair proof uses
only the complete ordinary covers, actual foreign chord points and the
actual paired corner; no strengthened chord or auxiliary label is assumed.
Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1089.WallCore
open S12 S12Pilot OriginalData
set_option Elab.async false
noncomputable section

theorem singleton_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (x : ℝ) (low : 28/25≤x) (high : x≤87/50) : (owners p 0).Inside x 1 :=
  CommonCases.OriginalOwners.horizontal_segment _ _ _ _ _ (frame p hf).singletonNear
    (frame p hf).singletonFar (by norm_num) low high

theorem bottom (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    51/25<centerX (owners p 9) ∧ (owners p 9).Inside (14/5) 1 ∧
      ∀ x : ℝ,113/50≤x → x≤14/5 → (owners p 9).Inside x 1 := by
  let h := frame p hf
  exact ContinuousBottom.reach_of_far _ (h.side 9) (h.box 9) h.bottomMarker
    (DirectDomains.bottom_far p hf)
    (fun own => h.apart 9 0 (by decide) _ _ ⟨own,h.singletonFar⟩)
    (fun own => h.apart 9 0 (by decide) _ _ ⟨own,h.singletonSeed⟩)
    (fun own => h.apart 9 5 (by decide) _ _ ⟨own,h.southeastMarker⟩)

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

/-- The complete northwest incoming-pair proof, before any family join.
The two gap points lie on the actual strict foreign chords. -/
theorem incoming_pair (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (33/20) (47/20))
    (fcover : q.Inside 1 (113/50) ∨ q.Inside (8/5) 3 ∨ q.Inside 2 (113/50))
    (gcover : q.Inside 1 (12/5) ∨ q.Inside (87/50) 2 ∨ q.Inside (87/50) 3)
    (missingF1 : ¬q.Inside 1 (113/50)) (missingG4 : ¬q.Inside (87/50) 3)
    (topGap : ¬q.Inside (161/100) 3) (leftGap : ¬q.Inside 1 (239/100))
    (corner : ¬q.Inside 1 3) : q.Inside 2 (113/50) ∧ q.Inside (87/50) 2 := by
  have noBoth : ¬(q.Inside (8/5) 3 ∧ q.Inside 1 (12/5)) := by
    rintro ⟨f3,g1⟩
    exact C1092CornerTwoGaps.impossible (pullX q) side (39/100) (39/100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [inside_pullX]; exact marker)
      (by norm_num [inside_pullX]; exact f3)
      (by norm_num [inside_pullX]; exact g1)
      (by norm_num [inside_pullX]; exact topGap)
      (by norm_num [inside_pullX]; exact leftGap)
      (by norm_num [inside_pullX]; exact corner)
  have f5 : q.Inside 2 (113/50) := by
    by_contra absent
    have f3 := (fcover.resolve_left missingF1).resolve_right absent
    have noG1 : ¬q.Inside 1 (12/5) := fun own => noBoth ⟨f3,own⟩
    have g3 := (gcover.resolve_left noG1).resolve_right missingG4
    exact C1092MixedSpan.impossible (pullSwap q) side
      (by norm_num [inside_pullSwap]; exact g3)
      (by norm_num [inside_pullSwap]; exact f3)
      (by norm_num [inside_pullSwap]; exact absent)
      (by norm_num [inside_pullSwap]; exact missingG4)
      (by norm_num [inside_pullSwap]; exact missingF1)
      (by norm_num [inside_pullSwap]; exact noG1)
  have g3 : q.Inside (87/50) 2 := by
    by_contra absent
    have g1 : q.Inside 1 (12/5) := by
      rcases gcover with own | own | own
      · exact own
      · exact False.elim (absent own)
      · exact False.elim (missingG4 own)
    have noF3 : ¬q.Inside (8/5) 3 := fun own => noBoth ⟨own,g1⟩
    exact C1092MixedSpan.impossible (pullY (pullX q)) side
      (by norm_num [inside_pullY,inside_pullX]; exact f5)
      (by norm_num [inside_pullY,inside_pullX]; exact g1)
      (by norm_num [inside_pullY,inside_pullX]; exact absent)
      (by norm_num [inside_pullY,inside_pullX]; exact missingF1)
      (by norm_num [inside_pullY,inside_pullX]; exact missingG4)
      (by norm_num [inside_pullY,inside_pullX]; exact noF3)
  exact ⟨f5,g3⟩

theorem northwest_inward (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (left : 2≤centerY (owners p 8)) (top : centerX (owners p 11)≤2) :
    (owners p 7).Inside 2 (113/50) ∧ (owners p 7).Inside (87/50) 2 := by
  let h := frame p hf
  exact incoming_pair _ (h.side 7) h.northwestMarker
    (AuxiliaryCover.northwest_f_cover p hf) (AuxiliaryCover.northwest_g_cover p hf)
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
  have fc := AuxiliaryCover.northeast_f_cover p hf
  have gc := AuxiliaryCover.northeast_g_cover p hf
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
  have fc := AuxiliaryCover.southeast_f_cover p hf
  have gc := AuxiliaryCover.southeast_g_cover p hf
  have result := incoming_pair (pullSwap (owners p 5)) (h.side 5)
    (by norm_num [inside_pullSwap]; exact h.southeastMarker)
    (by norm_num [inside_pullSwap]; tauto)
    (by norm_num [inside_pullSwap]; tauto)
    (by norm_num [inside_pullSwap]; exact fun own => h.apart 5 9 (by decide) _ _
      ⟨own,(bottom p hf).2.2 _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap]; exact fun own => h.apart 5 10 (by decide) _ _
      ⟨own,right_low p hf right _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap]; exact fun own => h.apart 5 10 (by decide) _ _
      ⟨own,right_low p hf right _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap]; exact fun own => h.apart 5 9 (by decide) _ _
      ⟨own,(bottom p hf).2.2 _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap]; exact fun own =>
      h.apart 5 1 (by decide) _ _ ⟨own,h.southeastCorner⟩)
  norm_num [inside_pullSwap] at result
  exact ⟨result.2,result.1⟩

theorem southwest_inward (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (left : centerY (owners p 8)≤2) :
    (owners p 4).Inside 2 (87/50) ∧ (owners p 4).Inside (87/50) 2 := by
  let h := frame p hf
  have f4 : (owners p 4).Inside 2 (87/50) := by
    rcases AuxiliaryCover.southwest_f_cover p hf with own | own | own
    · exact False.elim (h.apart 4 8 (by decide) _ _
        ⟨own,left_low p hf left _ (by norm_num) (by norm_num)⟩)
    · exact False.elim (h.apart 4 0 (by decide) _ _
        ⟨own,singleton_bar p hf _ (by norm_num) (by norm_num)⟩)
    · exact own
  refine ⟨f4,?_⟩
  by_contra missing
  have g0 : (owners p 4).Inside 1 (8/5) := by
    rcases AuxiliaryCover.southwest_g_cover p hf with own | own | own
    · exact own
    · exact False.elim (h.apart 4 0 (by decide) _ _ ⟨own,h.singletonFar⟩)
    · exact False.elim (missing own)
  exact C1092MixedSpan.impossible (pullX (owners p 4)) (h.side 4)
    (by norm_num [inside_pullX]; exact f4)
    (by norm_num [inside_pullX]; exact g0)
    (by norm_num [inside_pullX]; exact missing)
    (by norm_num [inside_pullX]; exact fun own => h.apart 4 8 (by decide) _ _
      ⟨own,left_low p hf left _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullX]; exact fun own =>
      h.apart 4 0 (by decide) _ _ ⟨own,h.singletonFar⟩)
    (by norm_num [inside_pullX]; exact fun own => h.apart 4 0 (by decide) _ _
      ⟨own,singleton_bar p hf _ (by norm_num) (by norm_num)⟩)

theorem two_low_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (left : centerY (owners p 8)≤2) (right : centerY (owners p 10)≤2) : False :=
  (frame p hf).apart 4 5 (by decide) _ _
    ⟨(southwest_inward p hf left).1,(southeast_inward p hf right).1⟩

end
#print axioms bottom
#print axioms incoming_pair
end N12Compact.Completion.OtherCases.C1089.WallCore
