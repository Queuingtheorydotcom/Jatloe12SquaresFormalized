import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! ORDINARY-MARKER-HALFPOINT, retaining the foreign wall marker offset.
The full interval0≤d≤.26 and both canonical signs need no wall or side cap. -/
namespace N12Compact.C1092MMMPMarkerHalfpoint
open S12 S12Pilot
set_option Elab.async false

private theorem positive (q : OpenSquare) (d : ℝ) (dn : 0≤d) (du : d≤13/50)
    (side : 1<q.side) (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (-7/20))
    (a : q.Inside 1 (-13/50)) (b : q.Inside 1 (-2/5))
    (missingD : ¬q.Inside (13/50) 0) (missingR : ¬q.Inside (1+d) 0)
    (missingK : ¬q.Inside 1 (-1)) (missingF : ¬q.Inside (13/50) (-1)) :
    q.Inside 1 (-1/2) := by
  simp only [OpenSquare.Inside,InBands,mul_one,mul_zero,zero_add,add_zero,mul_neg_one]
    at missingD missingR missingK missingF ⊢
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have dc := mul_le_mul_of_nonneg_right du cp.le
  have ds := mul_le_mul_of_nonneg_right du sn
  have dcp := mul_nonneg dn cp.le
  have dsp := mul_nonneg dn sn
  have kLowU : q.loU<q.c-q.s := by linarith only [marker.1,order]
  have kHighU : q.c-q.s<q.loU+q.side := by linarith only [b.2.1,sn]
  have kHighV : -q.s-q.c<q.loV+q.side := by linarith only [b.2.2.2,cp]
  have kFace : -q.s-q.c≤q.loV :=
    le_of_not_gt (fun own => missingK ⟨kLowU,kHighU,own,kHighV⟩)
  have rLowU : q.loU<q.c*(1+d) := by nlinarith only [marker.1,cp,sn,dcp]
  have rLowV : q.loV< -q.s*(1+d) := by nlinarith only [b.2.2.1,ds,cp,order]
  have rHighV : -q.s*(1+d)<q.loV+q.side := by
    nlinarith only [kFace,side,cu,dsp]
  have rFace : q.loU+q.side≤q.c*(1+d) :=
    le_of_not_gt (fun own => missingR ⟨rLowU,own,rLowV,rHighV⟩)
  have dLowU : q.loU<q.c*(13/50) := by nlinarith only [rFace,side,dc,cu]
  have dHighU : q.c*(13/50)<q.loU+q.side := by linarith only [a.2.1,cp,order]
  have dLowV : q.loV< -q.s*(13/50) := by linarith only [marker.2.2.1,cp,sn]
  have dFace : q.loV+q.side≤ -q.s*(13/50) :=
    le_of_not_gt (fun own => missingD ⟨dLowU,dHighU,dLowV,own⟩)
  have short := (short_projections q (1/2) (37/50) (by norm_num)).2.1
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [marker.1,cp,order]
  · linarith only [b.2.1,sn]
  · linarith only [dFace,side,short]
  · linarith only [b.2.2.2,cp]

private theorem negative (q : OpenSquare) (t d : ℝ) (signed : q.s=-t)
    (dn : 0≤d) (du : d≤13/50) (side : 1<q.side)
    (cp : 0<q.c) (tn : 0≤t) (order : t≤q.c)
    (marker : q.Inside (7/20) (-7/20))
    (a : q.Inside 1 (-13/50)) (b : q.Inside 1 (-2/5))
    (missingD : ¬q.Inside (13/50) 0) (missingR : ¬q.Inside (1+d) 0)
    (missingK : ¬q.Inside 1 (-1)) (missingF : ¬q.Inside (13/50) (-1)) :
    q.Inside 1 (-1/2) := by
  classical
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have dc := mul_le_mul_of_nonneg_right du cp.le
  have dt := mul_le_mul_of_nonneg_right du tn
  have dcp := mul_nonneg dn cp.le
  have dtp := mul_nonneg dn tn
  have first := (short_projections q (37/50) (-1/2) (by norm_num)).2.1
  have second := (short_projections q (1/2) (-13/50) (by norm_num)).2.1
  simp only [OpenSquare.Inside,InBands,signed,mul_one,mul_zero,zero_add,add_zero,
    mul_neg_one,neg_neg] at marker a b missingD missingR missingK missingF first second ⊢
  have dHighU : q.c*(13/50)<q.loU+q.side := by linarith only [marker.2.1,cp,tn]
  have dLowV : q.loV<t*(13/50) := by linarith only [marker.2.2.1,cp,order]
  have rLowU : q.loU<q.c*(1+d) := by nlinarith only [marker.1,cp,order,dcp]
  have rLowV : q.loV<t*(1+d) := by nlinarith only [b.2.2.1,cp,dtp]
  have yLowU : q.loU<q.c+(-t)*(-1/2) := by linarith only [marker.1,cp,tn]
  have yHighV : t+q.c*(-1/2)<q.loV+q.side := by linarith only [b.2.2.2,cp]
  have yLowV : q.loV<t+q.c*(-1/2) := by
    by_contra bad
    have face : t+q.c*(-1/2)≤q.loV := by exact le_of_not_gt bad
    have dHighV : t*(13/50)<q.loV+q.side := by linarith only [face,side,cu,tn]
    have dFace : q.c*(13/50)≤q.loU :=
      le_of_not_gt (fun own => missingD ⟨own,dHighU,dLowV,dHighV⟩)
    have rHighV : t*(1+d)<q.loV+q.side := by
      nlinarith only [face,side,second,dt]
    have rFace : q.loU+q.side≤q.c*(1+d) :=
      le_of_not_gt (fun own => missingR ⟨rLowU,own,rLowV,rHighV⟩)
    nlinarith only [dFace,rFace,side,dc,cu]
  have yHighU : q.c+(-t)*(-1/2)<q.loU+q.side := by
    by_contra bad
    have yFace : q.loU+q.side≤q.c+(-t)*(-1/2) := by exact le_of_not_gt bad
    have dLowU : q.loU<q.c*(13/50) := by linarith only [yFace,side,first]
    have dFace : q.loV+q.side≤t*(13/50) :=
      le_of_not_gt (fun own => missingD ⟨dLowU,dHighU,dLowV,own⟩)
    have kLowU : q.loU<q.c+t := by linarith only [marker.1,cp,tn]
    have kLowV : q.loV<t-q.c := by linarith only [dFace,side,cu,tn]
    have kHighV : t-q.c<q.loV+q.side := by linarith only [marker.2.2.2,order]
    have kFace : q.loU+q.side≤q.c+t :=
      le_of_not_gt (fun own => missingK ⟨kLowU,own,kLowV,kHighV⟩)
    have fLowU : q.loU<q.c*(13/50)+t := by linarith only [kFace,side,cu]
    have fLowV : q.loV<t*(13/50)-q.c := by linarith only [dFace,side,cu]
    have fHighV : t*(13/50)-q.c<q.loV+q.side := by linarith only [marker.2.2.2,cp,tn]
    have fFace : q.loU+q.side≤q.c*(13/50)+t :=
      le_of_not_gt (fun own => missingF ⟨fLowU,own,fLowV,fHighV⟩)
    have gap : (37/50)*q.c < (3/5)*t := by linarith only [fFace,b.2.1]
    linarith only [gap,cp,order]
  exact ⟨yLowU,yHighU,yLowV,yHighV⟩

theorem point (q : OpenSquare) (d : ℝ) (dn : 0≤d) (du : d≤13/50)
    (side : 1<q.side) (marker : q.Inside (7/20) (-7/20))
    (a : q.Inside 1 (-13/50)) (b : q.Inside 1 (-2/5))
    (missingD : ¬q.Inside (13/50) 0) (missingR : ¬q.Inside (1+d) 0)
    (missingK : ¬q.Inside 1 (-1)) (missingF : ¬q.Inside (13/50) (-1)) :
    q.Inside 1 (-1/2) := by
  classical
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  by_cases sign : 0≤r.s
  · exact (same _ _).mp (positive r d dn du side' cp sign
      (by simpa only [abs_of_nonneg sign] using canonical)
      ((same _ _).mpr marker) ((same _ _).mpr a) ((same _ _).mpr b)
      (fun h => missingD ((same _ _).mp h)) (fun h => missingR ((same _ _).mp h))
      (fun h => missingK ((same _ _).mp h)) (fun h => missingF ((same _ _).mp h)))
  · exact (same _ _).mp (negative r (-r.s) d (by ring) dn du side' cp
      (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical)
      ((same _ _).mpr marker) ((same _ _).mpr a) ((same _ _).mpr b)
      (fun h => missingD ((same _ _).mp h)) (fun h => missingR ((same _ _).mp h))
      (fun h => missingK ((same _ _).mp h)) (fun h => missingF ((same _ _).mp h)))

#print axioms point
end N12Compact.C1092MMMPMarkerHalfpoint
