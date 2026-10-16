import Compact.Geometry.ClosedFrames
import Compact.Completion.CommonCases.CanonicalScalars

/-! The nearer upper auxiliary fixes the merged owner's canonical sign
and forces its inward upper point, for every permitted angle. -/
namespace N12Compact.Completion.OtherCases.MergedNearTopPoint
open S12 S12Pilot
set_option Elab.async false

theorem negative_span_impossible (c t : ℝ) (cp : 0<c) (tn : 0≤t)
    (order : t≤c) (unit : c^2+t^2=1)
    (span : (27/20)*c+(9/100)*t<1001/1000) : False := by
  have lower := (CommonCases.CanonicalScalars.bounds c t cp tn order unit).1
  have cSmall : c<3/4 := by linarith only [span,tn]
  have cSquare := mul_pos (sub_pos.mpr cSmall)
    (show 0<3/4+c by linarith only [cp])
  have tLarge : 16/25<t := by
    by_contra bad
    have small : t≤16/25 := le_of_not_gt bad
    have tSquare := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤16/25+t by linarith only [tn])
    nlinarith only [unit,cSquare,tSquare]
  linarith only [lower,tLarge,span]

private theorem positive_point (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (33/20) (33/20)) (top : q.Inside (87/50) 3)
    (missingLeft : ¬q.Inside 1 (113/50)) : q.Inside 2 (113/50) := by
  have cosine := (CommonCases.CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  have jHighU : q.c+q.s*(113/50)<q.loU+q.side := by
    linarith only [top.2.1,cp,sn]
  have jLowV : q.loV< -q.s+q.c*(113/50) := by
    linarith only [marker.2.2.1,cp,sn]
  have jHighV : -q.s+q.c*(113/50)<q.loV+q.side := by
    linarith only [top.2.2.2,order]
  have face : q.c+q.s*(113/50)≤q.loU := by
    apply le_of_not_gt
    intro low
    exact missingLeft (by
      simpa only [OpenSquare.Inside,InBands,mul_one] using
        And.intro low (And.intro jHighU (And.intro jLowV jHighV)))
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [marker.1,cp,sn]
  · linarith only [face,side,cosine]
  · linarith only [marker.2.2.1,cp,order]
  · linarith only [top.2.2.2,cp,sn]

theorem point (q : OpenSquare) (side : 1<q.side) (cap : q.side≤1001/1000)
    (marker : q.Inside (33/20) (33/20)) (top : q.Inside (87/50) 3)
    (missingLeft : ¬q.Inside 1 (113/50)) : q.Inside 2 (113/50) := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have p := (same _ _).mpr marker
  have t := (same _ _).mpr top
  have bounds := abs_le.mp range
  apply (same _ _).mp
  by_cases positive : 0<r.s
  · exact positive_point r (by simpa only [shape] using side) cp positive.le bounds.2 p t
      (fun h => missingLeft ((same _ _).mp h))
  · exfalso
    have sn : 0≤ -r.s := by linarith only [positive]
    have order : -r.s≤r.c := by linarith only [bounds.1]
    have unit : r.c^2+(-r.s)^2=1 := by simpa only [neg_sq] using r.unit_normal
    have span : (27/20)*r.c+(9/100)*(-r.s)<1001/1000 := by
      have cap' : r.side≤1001/1000 := by simpa only [shape] using cap
      linarith only [p.2.2.1,t.2.2.2,cap']
    exact negative_span_impossible r.c (-r.s) cp sn order unit span

#print axioms point
end N12Compact.Completion.OtherCases.MergedNearTopPoint

