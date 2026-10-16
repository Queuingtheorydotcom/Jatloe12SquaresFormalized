import Compact.Completion.OtherCases.InnerCornerObstruction.Faces
import Compact.Completion.OtherCases.InnerCornerObstruction.Scalars

/-! The complete parameter-rectangle theorem of INNER-CORNER-INWARD-POINT.
All parameter and slope endpoints are included; the physical canonical
reframe preserves the one actual square. Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.InnerCornerObstruction
open S12 S12Pilot
set_option Elab.async false

theorem positive_inward_impossible (q : OpenSquare) (h : Input q) (k y : ℝ)
    (kl : 1/2≤k) (ku : k≤27/50) (yl : 101/100≤y) (yu : y≤26/25)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (missingD : ¬q.Inside (37/50) 1) (missingK : ¬q.Inside k y) : False := by
  obtain ⟨lowerU,lowerV⟩ := positive_faces q h cp sn order
  have cu := (CommonCases.CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  have o := h.origin
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_add] at o
  have m := h.marker
  have dLowerU : q.loU<(37/50)*q.c+q.s := by linarith only [o.1,cp,sn]
  have dLowerV : q.loV<q.c-(37/50)*q.s := by linarith only [m.2.2.1,cp,order]
  have dUpperV : q.c-(37/50)*q.s<q.loV+q.side := by
    linarith only [lowerV,h.side,cu,sn]
  have upperU : q.loU+q.side≤(37/50)*q.c+q.s := by
    apply le_of_not_gt
    intro high
    apply missingD
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [dLowerU,high,dLowerV,dUpperV]
  have sixth : q.c<6*q.s := by
    apply lt_of_not_ge
    intro shallow
    have short := Scalars.before_sixth q.c q.s cp.le sn q.unit_normal shallow
    linarith only [upperU,lowerU,h.side,short]
  have rLowerU : q.loU< -(43/500)*q.c+q.s := by
    linarith only [o.1,sixth,cp]
  have rUpperU : -(43/500)*q.c+q.s<q.loU+q.side := by
    linarith only [m.2.1,cp,order]
  have rLowerV : q.loV<(43/500)*q.s+q.c := by
    linarith only [m.2.2.1,cp,sn]
  have upperV : q.loV+q.side≤(43/500)*q.s+q.c := by
    apply le_of_not_gt
    intro high
    apply h.missingUpper
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [rLowerU,rUpperU,rLowerV,high]
  have ninth : 9*q.s<4*q.c := by
    apply lt_of_not_ge
    intro steep
    have short := Scalars.after_four_ninth q.c q.s cp.le sn q.unit_normal steep
    linarith only [upperV,lowerV,h.side,short]
  have first := mul_pos cp (show 0<k by linarith only [kl])
  have last := mul_nonneg sn (show 0≤y by linarith only [yl])
  have kLowerU : q.loU<q.c*k+q.s*y := by nlinarith only [o.1,first,last]
  have firstGap := mul_nonneg sn (show 0≤13/20-k by linarith only [ku])
  have lastGap := mul_pos cp (show 0<y-13/20 by linarith only [yl])
  have kLowerV : q.loV< -q.s*k+q.c*y := by
    nlinarith only [m.2.2.1,firstGap,lastGap]
  have highY := mul_nonneg cp.le (sub_nonneg.mpr yu)
  have lowK := mul_nonneg sn (sub_nonneg.mpr kl)
  have shortV := Scalars.upper_v q.c q.s cp.le sn q.unit_normal sixth.le
  have kUpperV : -q.s*k+q.c*y<q.loV+q.side := by
    nlinarith only [lowerV,h.side,highY,lowK,shortV]
  have kUpperU : q.loU+q.side≤q.c*k+q.s*y := by
    apply le_of_not_gt
    intro high
    exact missingK ⟨kLowerU,high,kLowerV,kUpperV⟩
  have highK := mul_nonneg cp.le (sub_nonneg.mpr ku)
  have highS := mul_nonneg sn (sub_nonneg.mpr yu)
  have shortU := Scalars.upper_u q.c q.s cp.le sn q.unit_normal ninth.le
  nlinarith only [kUpperU,lowerU,h.side,highK,highS,shortU]

theorem inward_impossible (q : OpenSquare) (h : Input q) (k y : ℝ)
    (kl : 1/2≤k) (ku : k≤27/50) (yl : 101/100≤y) (yu : y≤26/25)
    (missingD : ¬q.Inside (37/50) 1) (missingK : ¬q.Inside k y) : False := by
  obtain ⟨r,cp,range,side,same,_⟩ := ClosedFrames.canonical_frame q
  have data := h.reframe side same
  by_cases sign : 0≤r.s
  · exact positive_inward_impossible r data k y kl ku yl yu cp sign
      (by simpa only [abs_of_nonneg sign] using range)
      (fun own => missingD ((same _ _).mp own))
      (fun own => missingK ((same _ _).mp own))
  · exact negative_impossible r data (-r.s) (by ring) cp (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range)

theorem inward_corner_excluded (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (13/20) (13/20))
    (missingLeft : ¬q.Inside (-43/500) 0)
    (missingNear : ¬q.Inside (3/25) 0)
    (missingUpper : ¬q.Inside (-43/500) 1)
    (k y : ℝ) (kl : 1/2≤k) (ku : k≤27/50) (yl : 101/100≤y) (yu : y≤26/25)
    (missingD : ¬q.Inside (37/50) 1) (missingK : ¬q.Inside k y) :
    ¬q.Inside 0 0 := by
  intro origin
  exact inward_impossible q ⟨side,origin,marker,missingLeft,missingNear,missingUpper⟩
    k y kl ku yl yu missingD missingK

/-- The original-coordinate application permits exactly both intended
points (1.54,2.01) and (1.50,2.04), including their parameter endpoints. -/
theorem inward_corner_excluded_original (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (33/20) (33/20))
    (missingLeft : ¬q.Inside (457/500) 1)
    (missingNear : ¬q.Inside (28/25) 1)
    (missingUpper : ¬q.Inside (457/500) 2)
    (k y : ℝ) (kl : 1/2≤k) (ku : k≤27/50) (yl : 101/100≤y) (yu : y≤26/25)
    (missingD : ¬q.Inside (87/50) 2)
    (missingK : ¬q.Inside (1+k) (1+y)) : ¬q.Inside 1 1 := by
  have result := inward_corner_excluded (q.translated 1 1) side
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact missingLeft)
    (by norm_num [inside_translated_iff]; exact missingNear)
    (by norm_num [inside_translated_iff]; exact missingUpper)
    k y kl ku yl yu
    (by norm_num [inside_translated_iff]; exact missingD)
    (by simpa only [inside_translated_iff] using missingK)
  simpa only [inside_translated_iff,add_zero] using result

#print axioms inward_impossible
#print axioms inward_corner_excluded_original
end N12Compact.Completion.OtherCases.InnerCornerObstruction
