import Compact.Completion.OtherCases.SharpPointScalars
import Compact.Completion.OtherCases.SharpBarGeometry

/-! The upper square reaches the sharp common point from its marker and
outer top anchor alone. The original whole vertical bar is used to obtain
a true vertex crossing contradiction; all signed orientations are included. -/
namespace N12Compact.Completion.OtherCases.UpperBarPoint
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem negative_point (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : q.s ≤ 0) (order : -q.s ≤ q.c)
    (marker : q.Inside (7/20) (7/20)) (anchor : q.Inside (2/5) 1)
    (missingP0 : ¬q.Inside 0 1) (missingP1 : ¬q.Inside 1 1) :
    q.Inside (21/40) (1/8) := by
  by_contra missing
  have cu : q.c ≤ 1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have p0HighU : q.s < q.loU+q.side := by linarith only [anchor.2.1,cp]
  have p0LowV : q.loV < q.c := by linarith only [marker.2.2.1,cp,order]
  have p0HighV : q.c < q.loV+q.side := by linarith only [anchor.2.2.2,sn]
  have p0Face : q.s ≤ q.loU := by
    apply le_of_not_gt
    intro low
    apply missingP0
    simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add,mul_one] using
      And.intro low (And.intro p0HighU (And.intro p0LowV p0HighV))
  have yLowU : q.loU < q.c*(21/40)+q.s*(1/8) := by
    linarith only [marker.1,cp,sn]
  have yHighV : -q.s*(21/40)+q.c*(1/8) < q.loV+q.side := by
    linarith only [marker.2.2.2,cp,order]
  have gap := CommonCases.OutwardScalars.increasing_projection q.c (-q.s) (21/40) (7/8)
    cp (by linarith only [sn]) order (by simpa only [neg_sq] using q.unit_normal)
    (by norm_num) (by norm_num) (by norm_num)
  have yHighU : q.c*(21/40)+q.s*(1/8) < q.loU+q.side := by
    linarith only [p0Face,side,gap]
  have yFace : -q.s*(21/40)+q.c*(1/8) ≤ q.loV :=
    le_of_not_gt (fun h => missing ⟨yLowU,yHighU,h,yHighV⟩)
  have p1LowU : q.loU < q.c+q.s := by linarith only [marker.1,cp,order]
  have p1LowV : q.loV < -q.s+q.c := by linarith only [marker.2.2.1,cp,sn]
  have short := (short_projections q (19/40) (7/8) (by norm_num)).2.2.2
  have p1HighV : -q.s+q.c < q.loV+q.side := by linarith only [yFace,short,side]
  have p1Face : q.loU+q.side ≤ q.c+q.s := by
    apply le_of_not_gt
    intro high
    apply missingP1
    simpa only [OpenSquare.Inside,InBands,mul_one] using
      And.intro p1LowU (And.intro high (And.intro p1LowV p1HighV))
  linarith only [p0Face,p1Face,side,cu]

private theorem positive_point (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (7/20) (7/20)) (anchor : q.Inside (2/5) 1)
    (missingL : ¬q.Inside 0 (13/50))
    (missingP0 : ¬q.Inside 0 1) (missingP1 : ¬q.Inside 1 1)
    (avoid : ∀ y : ℝ,13/50≤y → y≤14/25 → ¬q.Inside 1 y) :
    q.Inside (21/40) (1/8) := by
  by_contra missing
  classical
  have missingB0 := avoid (13/50) le_rfl (by norm_num)
  have missingB1 := avoid (14/25) (by norm_num) le_rfl
  simp only [OpenSquare.Inside,InBands,mul_one,mul_zero,neg_zero,zero_add]
    at missingL missingP0 missingP1 missingB0 missingB1
  have cu : q.c ≤ 1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have yHighV : -q.s*(21/40)+q.c*(1/8) < q.loV+q.side := by
    linarith only [marker.2.2.2,cp,sn]
  have p1LowU : q.loU < q.c+q.s := by linarith only [marker.1,cp,sn]
  have p1LowV : q.loV < -q.s+q.c := by linarith only [marker.2.2.1,cp,order]
  have p0HighU : q.s < q.loU+q.side := by linarith only [anchor.2.1,cp]
  have p0LowV : q.loV < q.c := by linarith only [marker.2.2.1,cp,sn]
  have lHighU : q.s*(13/50) < q.loU+q.side := by
    linarith only [marker.2.1,cp,sn]
  have lHighV : q.c*(13/50) < q.loV+q.side := by
    linarith only [anchor.2.2.2,cp,order]
  have b0LowU : q.loU < q.c+q.s*(13/50) := by
    linarith only [marker.1,cp,order]
  have b0HighV : -q.s+q.c*(13/50) < q.loV+q.side := by
    linarith only [anchor.2.2.2,cp,sn]
  have b1LowU : q.loU < q.c+q.s*(14/25) := by
    linarith only [marker.1,cp,sn]
  have b1HighV : -q.s+q.c*(14/25) < q.loV+q.side := by
    linarith only [anchor.2.2.2,cp,sn]
  have yLowU : q.loU < q.c*(21/40)+q.s*(1/8) := by
    by_contra failed
    have yLower : q.c*(21/40)+q.s*(1/8) ≤ q.loU := le_of_not_gt failed
    have shortP1 := CommonCases.OutwardScalars.increasing_projection q.c q.s (19/40) (7/8)
      cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
    have p1HighU : q.c+q.s < q.loU+q.side := by
      linarith only [yLower,shortP1,side]
    have p1UpperV : q.loV+q.side ≤ -q.s+q.c :=
      le_of_not_gt (fun h => missingP1 ⟨p1LowU,p1HighU,p1LowV,h⟩)
    have shortB0 := (short_projections q (19/40) (27/200) (by norm_num)).2.1
    have b0HighU : q.c+q.s*(13/50) < q.loU+q.side := by
      linarith only [yLower,shortB0,side]
    have b0LowerV : -q.s+q.c*(13/50) ≤ q.loV :=
      le_of_not_gt (fun h => missingB0 ⟨b0LowU,b0HighU,h,b0HighV⟩)
    linarith only [p1UpperV,b0LowerV,side,cu]
  have yHighU : q.c*(21/40)+q.s*(1/8) < q.loU+q.side := by
    by_contra failed
    have yUpper : q.loU+q.side ≤ q.c*(21/40)+q.s*(1/8) := le_of_not_gt failed
    have p0LowU : q.loU < q.s := by linarith only [yUpper,side,cu,sn]
    have p0UpperV : q.loV+q.side ≤ q.c :=
      le_of_not_gt (fun h => missingP0 ⟨p0LowU,p0HighU,p0LowV,h⟩)
    have lLowV : q.loV < q.c*(13/50) := by linarith only [p0UpperV,side,cu]
    have lLowerU : q.s*(13/50) ≤ q.loU :=
      le_of_not_gt (fun h => missingL ⟨h,lHighU,lLowV,lHighV⟩)
    linarith only [lLowerU,yUpper,side,cu,sn]
  have yLowerV : -q.s*(21/40)+q.c*(1/8) ≤ q.loV :=
    le_of_not_gt (fun h => missing ⟨yLowU,yHighU,h,yHighV⟩)
  have p1HighV : -q.s+q.c < q.loV+q.side := by
    linarith only [yLowerV,side,cu,sn]
  have p1UpperU : q.loU+q.side ≤ q.c+q.s :=
    le_of_not_gt (fun h => missingP1 ⟨p1LowU,h,p1LowV,p1HighV⟩)
  have p0LowU : q.loU < q.s := by linarith only [p1UpperU,side,cu]
  have p0UpperV : q.loV+q.side ≤ q.c :=
    le_of_not_gt (fun h => missingP0 ⟨p0LowU,p0HighU,p0LowV,h⟩)
  have lLowV : q.loV < q.c*(13/50) := by linarith only [p0UpperV,side,cu]
  have lLowerU : q.s*(13/50) ≤ q.loU :=
    le_of_not_gt (fun h => missingL ⟨h,lHighU,lLowV,lHighV⟩)
  have b0HighU : q.c+q.s*(13/50) < q.loU+q.side := by
    linarith only [lLowerU,side,cu]
  have b0LowerV : -q.s+q.c*(13/50) ≤ q.loV :=
    le_of_not_gt (fun h => missingB0 ⟨b0LowU,b0HighU,h,b0HighV⟩)
  have sp : 0 < q.s := by linarith only [b0LowerV,p0UpperV,side,cu]
  have upperSpan : 1 < (11/25)*q.c+q.s := by
    by_contra failed
    have span : (11/25)*q.c+q.s ≤ 1 := le_of_not_gt failed
    have b1LowV : q.loV < -q.s+q.c*(14/25) := by
      linarith only [p0UpperV,side,span]
    have b1UpperU : q.loU+q.side ≤ q.c+q.s*(14/25) :=
      le_of_not_gt (fun h => missingB1 ⟨b1LowU,h,b1LowV,b1HighV⟩)
    let X := q.c*(q.loU+q.side)-q.s*q.loV
    let Y := q.s*(q.loU+q.side)+q.c*q.loV
    have closed : ClosedInside q X Y :=
      WallProfile.vertex q (q.loU+q.side) q.loV
        ⟨by linarith only [q.side_pos],le_rfl⟩
        ⟨le_rfl,by linarith only [q.side_pos]⟩
    have arc := SharpPointScalars.arc q.c q.s cp sp q.unit_normal
    have cross := mul_nonneg cp.le sn
    have firstX := mul_nonneg cp.le (sub_nonneg.mpr lLowerU)
    have lastX := mul_nonneg sn (sub_nonneg.mpr p0UpperV)
    have height := mul_pos (sub_pos.mpr side)
      (show 0 < q.c+q.s by linarith only [cp,sn])
    have xHigh : 1 < X := by
      dsimp only [X]
      nlinarith only [firstX,lastX,height,arc,cross]
    have firstY := mul_nonneg sn (sub_nonneg.mpr lLowerU)
    have lastY := mul_nonneg cp.le (sub_nonneg.mpr b0LowerV)
    have length := mul_pos sp (show 0 < q.side-q.c by linarith only [side,cu])
    have yLow : 13/50 < Y := by
      dsimp only [Y]
      nlinarith only [firstY,lastY,length,q.unit_normal]
    have firstUpper := mul_nonneg sn (sub_nonneg.mpr b1UpperU)
    have lastUpper := mul_nonneg cp.le (sub_nonneg.mpr p0UpperV)
    have remaining := mul_pos cp
      (show 0 < q.side-((11/25)*q.c+q.s) by linarith only [side,span])
    have yHigh : Y < 14/25 := by
      dsimp only [Y]
      nlinarith only [firstUpper,lastUpper,remaining,q.unit_normal]
    exact SharpBarGeometry.vertical_crossing q X Y (7/20) (7/20) 1 (13/50) (14/25)
      closed marker (by norm_num) xHigh yLow.le yHigh.le
      (by norm_num) (by norm_num) avoid
  have short := SharpPointScalars.upper_lower_v q.c q.s cp sn order q.unit_normal upperSpan
  linarith only [yLowerV,p0UpperV,side,short]

/-- Theorem3 of OUTWARD-BAR-AND-UPPER-SPAN with no angle premise. -/
theorem point (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (7/20) (7/20)) (anchor : q.Inside (2/5) 1)
    (missingL : ¬q.Inside 0 (13/50))
    (missingP0 : ¬q.Inside 0 1) (missingP1 : ¬q.Inside 1 1)
    (avoid : ∀ y : ℝ,13/50≤y → y≤14/25 → ¬q.Inside 1 y) :
    q.Inside (21/40) (1/8) := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have a := (same _ _).mpr anchor
  have l : ¬r.Inside 0 (13/50) := fun h => missingL ((same _ _).mp h)
  have p0 : ¬r.Inside 0 1 := fun h => missingP0 ((same _ _).mp h)
  have p1 : ¬r.Inside 1 1 := fun h => missingP1 ((same _ _).mp h)
  by_cases sign : 0 ≤ r.s
  · exact (same _ _).mp (positive_point r side' cp sign
      (by simpa only [abs_of_nonneg sign] using range) m a l p0 p1
      (fun y lower upper h => avoid y lower upper ((same _ _).mp h)))
  · exact (same _ _).mp (negative_point r side' cp (le_of_not_ge sign)
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range) m a p0 p1)

theorem point_original (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (47/20) (47/20)) (anchor : q.Inside (12/5) 3)
    (missingL : ¬q.Inside 2 (113/50))
    (missingP0 : ¬q.Inside 2 3) (missingP1 : ¬q.Inside 3 3)
    (avoid : ∀ y : ℝ,113/50≤y → y≤64/25 → ¬q.Inside 3 y) :
    q.Inside (101/40) (17/8) := by
  have point := point (q.translated 2 2) side
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact anchor)
    (by norm_num [inside_translated_iff]; exact missingL)
    (by norm_num [inside_translated_iff]; exact missingP0)
    (by norm_num [inside_translated_iff]; exact missingP1)
    (by
      intro y lower upper own
      have original : q.Inside 3 (y+2) := by
        convert (inside_translated_iff q 2 2 1 y).mp own using 1 <;> ring
      exact avoid (y+2) (by linarith only [lower]) (by linarith only [upper]) original)
  norm_num [inside_translated_iff] at point
  exact point

#print axioms point_original
end N12Compact.Completion.OtherCases.UpperBarPoint

