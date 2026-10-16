import Compact.Completion.OtherCases.SharpPointScalars
import Compact.Completion.OtherCases.SharpBarGeometry
import Compact.Completion.C981.OutwardAnchor

/-! The full actual outward bar forces a sharp strict point and its true
support faces. The whole segment supplies a vertex crossing obstruction,
and exact circle projection margins discharge both remaining target bands. -/
namespace N12Compact.Completion.OtherCases.OutwardBarPoint
open S12 S12Pilot FourSquareAnchors
open SharpPointScalars
set_option Elab.async false

structure Faces (q : OpenSquare) : Prop where
  lowerU : (13/50)*q.c ≤ q.loU
  lowerV : -(543/500)*q.s ≤ q.loV
  upperU : q.loU+q.side ≤ q.c+q.s
  upperV : q.loV+q.side ≤ q.c-(4/5)*q.s
  sinePositive : 0 < q.s
  upperSpan : 1 < q.c+(143/500)*q.s
  lowerSpan : 1 < (37/50)*q.c+q.s

theorem positive_faces (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (7/20) (7/20)) (outward : q.Inside 1 (13/50))
    (missingG : ¬q.Inside (13/50) 0)
    (missingR : ¬q.Inside (543/500) 0)
    (missingP : ¬q.Inside 1 1)
    (missingH : ¬q.Inside (543/500) 1)
    (avoid : ∀ z : ℝ,13/50≤z → z≤4/5 → ¬q.Inside z 1) : Faces q := by
  classical
  have missingF := avoid (13/50) le_rfl (by norm_num)
  have missingT := avoid (4/5) (by norm_num) le_rfl
  simp only [OpenSquare.Inside, InBands, mul_one, mul_zero, add_zero]
    at missingG missingR missingF missingT missingP missingH
  have cu := (CommonCases.CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  have gHighU : q.c*(13/50) < q.loU+q.side := by
    linarith only [marker.2.1,cp,sn]
  have gHighV : -q.s*(13/50) < q.loV+q.side := by
    linarith only [marker.2.2.2,cp,order]
  have gLowV : q.loV < -q.s*(13/50) := by
    by_contra failed
    have low : -q.s*(13/50) ≤ q.loV := le_of_not_gt failed
    have fHighU : q.c*(13/50)+q.s < q.loU+q.side := by
      linarith only [outward.2.1,order]
    have fLowV : q.loV < -q.s*(13/50)+q.c := by
      linarith only [marker.2.2.1,cp,sn]
    have fHighV : -q.s*(13/50)+q.c < q.loV+q.side := by
      linarith only [low,side,cu]
    have fFace : q.c*(13/50)+q.s ≤ q.loU :=
      le_of_not_gt (fun h => missingF ⟨h,fHighU,fLowV,fHighV⟩)
    have tLowU : q.loU < q.c*(4/5)+q.s := by
      linarith only [marker.1,cp,sn]
    have tLowV : q.loV < -q.s*(4/5)+q.c := by
      linarith only [marker.2.2.1,cp,order]
    have tHighV : -q.s*(4/5)+q.c < q.loV+q.side := by
      linarith only [low,side,cu,sn]
    have tFace : q.loU+q.side ≤ q.c*(4/5)+q.s :=
      le_of_not_gt (fun h => missingT ⟨tLowU,h,tLowV,tHighV⟩)
    linarith only [fFace,tFace,side,cu]
  have gFace : q.c*(13/50) ≤ q.loU :=
    le_of_not_gt (fun h => missingG ⟨h,gHighU,gLowV,gHighV⟩)
  have rLowU : q.loU < q.c*(543/500) := by
    linarith only [marker.1,cp,order]
  have rHighU : q.c*(543/500) < q.loU+q.side := by
    linarith only [gFace,side,cu]
  have rHighV : -q.s*(543/500) < q.loV+q.side := by
    linarith only [outward.2.2.2,cp,sn]
  have rFace : -q.s*(543/500) ≤ q.loV :=
    le_of_not_gt (fun h => missingR ⟨rLowU,rHighU,h,rHighV⟩)
  have hLowU : q.loU < q.c*(543/500)+q.s := by
    linarith only [outward.1,cp,sn]
  have hLowV : q.loV < -q.s*(543/500)+q.c := by
    linarith only [outward.2.2.1,cp,order]
  have hHighV : -q.s*(543/500)+q.c < q.loV+q.side := by
    linarith only [rFace,side,cu]
  have hFace : q.loU+q.side ≤ q.c*(543/500)+q.s :=
    le_of_not_gt (fun h => missingH ⟨hLowU,h,hLowV,hHighV⟩)
  have sineLow : 87/500 < q.s := by linarith only [gFace,hFace,side,cu]
  have sp : 0 < q.s := (by norm_num : (0:ℝ) < 87/500).trans sineLow
  have cosineUpper : q.c ≤ 1-q.s^2/2 := by
    nlinarith only [q.unit_normal,sq_nonneg (q.c-1)]
  have pLowU : q.loU < q.c+q.s := by
    linarith only [marker.1,cp,sn]
  have pLowV : q.loV < -q.s+q.c := by
    linarith only [marker.2.2.1,order]
  have pHighV : -q.s+q.c < q.loV+q.side := by
    have gap : q.c+(43/500)*q.s < 1 := by
      have product := mul_pos sp
        (show 0 < q.s-43/250 by linarith only [sineLow])
      nlinarith only [cosineUpper,product]
    linarith only [rFace,side,gap]
  have pFace : q.loU+q.side ≤ q.c+q.s :=
    le_of_not_gt (fun h => missingP ⟨pLowU,h,pLowV,pHighV⟩)
  have fHighU : q.c*(13/50)+q.s < q.loU+q.side := by
    linarith only [outward.2.1,order]
  have fLowV : q.loV < -q.s*(13/50)+q.c := by
    linarith only [marker.2.2.1,cp,sn]
  have fLowU : q.loU < q.c*(13/50)+q.s := by
    linarith only [pFace,side,cu]
  have fFace : q.loV+q.side ≤ -q.s*(13/50)+q.c :=
    le_of_not_gt (fun h => missingF ⟨fLowU,fHighU,fLowV,h⟩)
  have tLowU : q.loU < q.c*(4/5)+q.s := by
    linarith only [marker.1,cp,sn]
  have tLowV : q.loV < -q.s*(4/5)+q.c := by
    linarith only [marker.2.2.1,cp,order]
  have upperSpan : 1 < q.c+(143/500)*q.s := by
    by_contra failed
    have span : q.c+(143/500)*q.s ≤ 1 := le_of_not_gt failed
    have tHighV : -q.s*(4/5)+q.c < q.loV+q.side := by
      linarith only [rFace,side,span]
    have tFace : q.loU+q.side ≤ q.c*(4/5)+q.s :=
      le_of_not_gt (fun h => missingT ⟨tLowU,h,tLowV,tHighV⟩)
    let X := q.c*(q.loU+q.side)-q.s*(q.loV+q.side)
    let Y := q.s*(q.loU+q.side)+q.c*(q.loV+q.side)
    have closed : ClosedInside q X Y :=
      WallProfile.vertex q (q.loU+q.side) (q.loV+q.side)
        ⟨by linarith only [q.side_pos],le_rfl⟩
        ⟨by linarith only [q.side_pos],le_rfl⟩
    have long := mul_pos cp
      (show 0 < q.side-q.s by linarith only [side,order,cu])
    have firstLow := mul_nonneg cp.le (sub_nonneg.mpr gFace)
    have lastHigh := mul_nonneg sn (sub_nonneg.mpr fFace)
    have xLow : 13/50 < X := by
      dsimp only [X]
      nlinarith only [firstLow,lastHigh,long,q.unit_normal]
    have firstHigh := mul_nonneg cp.le (sub_nonneg.mpr tFace)
    have lastLow := mul_nonneg sn (sub_nonneg.mpr rFace)
    have width := mul_pos sp
      (show 0 < q.side-(q.c+(143/500)*q.s) by linarith only [side,span])
    have xHigh : X < 4/5 := by
      dsimp only [X]
      nlinarith only [firstHigh,lastLow,width,q.unit_normal]
    have arcBound := arc q.c q.s cp sp q.unit_normal
    have height := mul_pos (sub_pos.mpr side)
      (show 0 < q.c+q.s by linarith only [cp,sn])
    have firstHeight := mul_nonneg sn (sub_nonneg.mpr gFace)
    have lastHeight := mul_nonneg cp.le (sub_nonneg.mpr rFace)
    have yHigh : 1 < Y := by
      dsimp only [Y]
      nlinarith only [firstHeight,lastHeight,height,arcBound]
    exact SharpBarGeometry.horizontal_crossing q X Y (7/20) (7/20) 1 (13/50) (4/5)
      closed marker (by norm_num) yHigh xLow.le xHigh.le
      (by norm_num) (by norm_num) avoid
  have short := outward_short_u q.c q.s cp sp q.unit_normal upperSpan
  have tHighU : q.c*(4/5)+q.s < q.loU+q.side := by
    linarith only [gFace,side,short]
  have tFace : q.loV+q.side ≤ -q.s*(4/5)+q.c :=
    le_of_not_gt (fun h => missingT ⟨tLowU,tHighU,tLowV,h⟩)
  have lowerSpan : 1 < (37/50)*q.c+q.s := by linarith only [gFace,pFace,side]
  exact ⟨by linarith only [gFace],by linarith only [rFace],pFace,
    by linarith only [tFace],sp,upperSpan,lowerSpan⟩

theorem positive_point (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (7/20) (7/20)) (outward : q.Inside 1 (13/50))
    (missingG : ¬q.Inside (13/50) 0)
    (missingR : ¬q.Inside (543/500) 0)
    (missingP : ¬q.Inside 1 1)
    (missingH : ¬q.Inside (543/500) 1)
    (avoid : ∀ z : ℝ,13/50≤z → z≤4/5 → ¬q.Inside z 1) :
    q.Inside (21/40) (-1/8) := by
  have faces := positive_faces q side cp sn order marker outward
    missingG missingR missingP missingH avoid
  have uGap := outward_lower_u q.c q.s cp faces.sinePositive q.unit_normal faces.upperSpan
  have vGap := outward_lower_v q.c q.s cp sn order q.unit_normal faces.lowerSpan
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [faces.upperU,side,uGap]
  · linarith only [outward.2.1,cp,sn]
  · linarith only [faces.upperV,side,vGap]
  · linarith only [marker.2.2.2,cp,sn]

theorem positive_point_original (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (47/20) (47/20)) (outward : q.Inside 3 (113/50))
    (missingG : ¬q.Inside (113/50) 2)
    (missingR : ¬q.Inside (1543/500) 2)
    (missingP : ¬q.Inside 3 3)
    (missingH : ¬q.Inside (1543/500) 3)
    (avoid : ∀ z : ℝ,113/50≤z → z≤14/5 → ¬q.Inside z 3) :
    q.Inside (101/40) (15/8) := by
  have point := positive_point (q.translated 2 2) side cp sn order
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact outward)
    (by norm_num [inside_translated_iff]; exact missingG)
    (by norm_num [inside_translated_iff]; exact missingR)
    (by norm_num [inside_translated_iff]; exact missingP)
    (by norm_num [inside_translated_iff]; exact missingH)
    (by
      intro z lower upper own
      have original : q.Inside (z+2) 3 := by
        convert (inside_translated_iff q 2 2 z 1).mp own using 1 <;> ring
      exact avoid (z+2) (by linarith only [lower]) (by linarith only [upper]) original)
  norm_num [inside_translated_iff] at point
  exact point

/-- Every orientation is included. The actual outward upper anchor and
the same whole foreign bar rule out the other canonical sign. -/
theorem point_original (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (47/20) (47/20))
    (outward : q.Inside 3 (113/50)) (upper : q.Inside 3 (12/5))
    (missingG : ¬q.Inside (113/50) 2)
    (missingR : ¬q.Inside (1543/500) 2)
    (missingP : ¬q.Inside 3 3)
    (missingH : ¬q.Inside (1543/500) 3)
    (avoid : ∀ z : ℝ,113/50≤z → z≤14/5 → ¬q.Inside z 3) :
    q.Inside (101/40) (15/8) := by
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have a := (same _ _).mpr outward
  have b := (same _ _).mpr upper
  have g : ¬r.Inside (113/50) 2 := fun h => missingG ((same _ _).mp h)
  have rr : ¬r.Inside (1543/500) 2 := fun h => missingR ((same _ _).mp h)
  have p : ¬r.Inside 3 3 := fun h => missingP ((same _ _).mp h)
  have h : ¬r.Inside (1543/500) 3 := fun h => missingH ((same _ _).mp h)
  have segment (z : ℝ) (low : 113/50 ≤ z) (high : z ≤ 14/5) : ¬r.Inside z 3 :=
    fun own => avoid z low high ((same _ _).mp own)
  by_cases sign : 0 ≤ r.s
  · exact (same _ _).mp (positive_point_original r side' cp sign
      (by simpa only [abs_of_nonneg sign] using canonical) m a g rr p h segment)
  · exfalso
    apply C981CompletionOutwardAnchor.nonnegative_impossible (pullY r) side' cp
      (by change 0 ≤ -r.s; linarith only [sign])
      (by change -r.s ≤ r.c; simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical)
    · norm_num [inside_pullY]; exact m
    · norm_num [inside_pullY]; exact b
    · norm_num [inside_pullY]; exact p
    · norm_num [inside_pullY]; exact rr
    · norm_num [inside_pullY]; exact g
    · intro z low high own
      exact segment z low high (by norm_num [inside_pullY] at own; exact own)

#print axioms positive_faces
#print axioms point_original
end N12Compact.Completion.OtherCases.OutwardBarPoint

