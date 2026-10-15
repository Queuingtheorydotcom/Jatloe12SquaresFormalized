import Compact.Completion.CommonCases.CanonicalProjection
import Compact.Geometry.ClosedFrames

/-! Two strict vertical markers and the four actual omitted chord endpoints
force four complete face bounds, without a chord formula or angle split. -/
namespace N12Compact.Completion.OtherCases.TwoChordFaces
open S12 S12Pilot
set_option Elab.async false

structure Faces (q : OpenSquare) : Prop where
  lowerU : -(13/50)*q.s≤q.loU
  lowerV : -(13/50)*q.c-q.s≤q.loV
  upperU : q.loU+q.side≤q.c+(13/50)*q.s
  upperV : q.loV+q.side≤(13/50)*q.c
  sinePositive : 0<q.s
  span : 1<(13/25)*q.c+q.s
  cutoff : (228/397)*q.c<(325/397)*q.s

theorem positive (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (south : q.Inside (7/20) (-7/20)) (north : q.Inside (7/20) (7/20))
    (missingF : ¬q.Inside 0 (-13/50)) (missingH : ¬q.Inside 0 (13/50))
    (missingJ : ¬q.Inside 1 (-13/50)) (missingG : ¬q.Inside 1 (13/50)) :
    Faces q := by
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_add,add_zero,mul_one]
    at missingF missingH missingJ missingG
  have cu := (CommonCases.CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  have fHighU : q.s*(-13/50)<q.loU+q.side := by
    linarith only [north.2.1,cp,sn]
  have fLowV : q.loV<q.c*(-13/50) := by
    linarith only [south.2.2.1,cp,sn]
  have fHighV : q.c*(-13/50)<q.loV+q.side := by
    linarith only [north.2.2.2,cp,order]
  have fFace : q.s*(-13/50)≤q.loU :=
    le_of_not_gt (fun h => missingF ⟨h,fHighU,fLowV,fHighV⟩)
  have jLowU : q.loU<q.c+q.s*(-13/50) := by
    linarith only [south.1,cp,sn]
  have jHighU : q.c+q.s*(-13/50)<q.loU+q.side := by
    linarith only [fFace,side,cu]
  have jHighV : -q.s+q.c*(-13/50)<q.loV+q.side := by
    linarith only [north.2.2.2,cp,sn]
  have jFace : -q.s+q.c*(-13/50)≤q.loV :=
    le_of_not_gt (fun h => missingJ ⟨jLowU,jHighU,h,jHighV⟩)
  have hHighU : q.s*(13/50)<q.loU+q.side := by
    linarith only [north.2.1,cp,sn]
  have hLowV : q.loV<q.c*(13/50) := by
    linarith only [south.2.2.1,cp,sn]
  have gLowU : q.loU<q.c+q.s*(13/50) := by
    linarith only [north.1,cp,order]
  have gHighV : -q.s+q.c*(13/50)<q.loV+q.side := by
    linarith only [north.2.2.2,cp,sn]
  have hFace : q.loV+q.side≤q.c*(13/50) := by
    by_contra bad
    have hHighV := lt_of_not_ge bad
    have hLowFace : q.s*(13/50)≤q.loU :=
      le_of_not_gt (fun h => missingH ⟨h,hHighU,hLowV,hHighV⟩)
    have slope : 61*q.s<35*q.c := by linarith only [hLowFace,south.1]
    have gHighU : q.c+q.s*(13/50)<q.loU+q.side := by
      linarith only [hLowFace,side,cu]
    have gLowFace : -q.s+q.c*(13/50)≤q.loV :=
      le_of_not_gt (fun h => missingG ⟨gLowU,gHighU,h,gHighV⟩)
    linarith only [slope,gLowFace,south.2.2.1,cp]
  have gLowV : q.loV< -q.s+q.c*(13/50) := by
    linarith only [hFace,side,cu,order]
  have gFace : q.loU+q.side≤q.c+q.s*(13/50) :=
    le_of_not_gt (fun h => missingG ⟨gLowU,h,gLowV,gHighV⟩)
  have span : 1<(13/25)*q.c+q.s := by linarith only [hFace,jFace,side]
  have sp : 0<q.s := by linarith only [span,cu]
  have cutoff : (228/397)*q.c<(325/397)*q.s := by
    by_contra bad
    have short := CommonCases.CanonicalProjection.before q.c q.s (325/397) (228/397)
      (13/25) 1 q.unit_normal (by norm_num) (le_of_not_gt bad) (by norm_num) (by norm_num)
    norm_num at short
    linarith only [span,short]
  exact ⟨by linarith only [fFace],by linarith only [jFace],by linarith only [gFace],
    by linarith only [hFace],sp,span,cutoff⟩

#print axioms positive
end N12Compact.Completion.OtherCases.TwoChordFaces

