import S12.ShortCluster.Projections
import Compact.Completion.OtherCases.OutwardPairScalars
import Compact.Completion.OtherCases.WallProfile.SupportGeometry

/-! The actual northeast frame forced by its omitted sharp point. Its
two weak support faces retain the same three strict original anchors. -/
namespace N12Compact.Completion.OtherCases.OutwardPairFaces
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem negative_point (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : q.s ≤ 0) (order : -q.s ≤ q.c)
    (marker : q.Inside (7/20) (7/20)) (anchor : q.Inside (13/50) 1)
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


theorem positive_faces (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (7/20))
    (inward : q.Inside 0 (13/50)) (top : q.Inside (13/50) 1)
    (missingL : ¬q.Inside (-7/20) (7/20))
    (missingP0 : ¬q.Inside 0 1) (missingP1 : ¬q.Inside 1 1)
    (missingY : ¬q.Inside (21/40) (1/8)) :
    (7/20)*(q.s-q.c) ≤ q.loU ∧ q.loV+q.side ≤ q.c := by
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have lHighU : q.c*(-7/20)+q.s*(7/20)<q.loU+q.side := by
    linarith only [inward.2.1,cp,order]
  have lLowV : q.loV < -q.s*(-7/20)+q.c*(7/20) := by
    linarith only [inward.2.2.1,cp,sn]
  have lHighV : -q.s*(-7/20)+q.c*(7/20)<q.loV+q.side := by
    linarith only [top.2.2.2,cp,order]
  have lFace : q.c*(-7/20)+q.s*(7/20) ≤ q.loU :=
    le_of_not_gt (fun h => missingL ⟨h,lHighU,lLowV,lHighV⟩)
  have yLowU : q.loU < q.c*(21/40)+q.s*(1/8) := by
    linarith only [inward.1,cp,order]
  have yHighU : q.c*(21/40)+q.s*(1/8)<q.loU+q.side := by
    linarith only [lFace,side,cu,sn]
  have yHighV : -q.s*(21/40)+q.c*(1/8)<q.loV+q.side := by
    linarith only [marker.2.2.2,cp,sn]
  have yFace : -q.s*(21/40)+q.c*(1/8) ≤ q.loV :=
    le_of_not_gt (fun h => missingY ⟨yLowU,yHighU,h,yHighV⟩)
  have p1LowU : q.loU<q.c+q.s := by linarith only [marker.1,cp,sn]
  have p1LowV : q.loV< -q.s+q.c := by linarith only [marker.2.2.1,cp,order]
  have p1HighV : -q.s+q.c<q.loV+q.side := by linarith only [yFace,side,cu,sn]
  have p1Face : q.loU+q.side ≤ q.c+q.s := by
    apply le_of_not_gt
    intro high
    apply missingP1
    simpa only [OpenSquare.Inside,InBands,mul_one] using
      And.intro p1LowU (And.intro high (And.intro p1LowV p1HighV))
  have p0LowU : q.loU<q.s := by linarith only [p1Face,side,cu]
  have p0HighU : q.s<q.loU+q.side := by linarith only [top.2.1,cp]
  have p0LowV : q.loV<q.c := by linarith only [marker.2.2.1,cp,sn]
  have p0Face : q.loV+q.side ≤ q.c := by
    apply le_of_not_gt
    intro high
    apply missingP0
    simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add,mul_one] using
      And.intro p0LowU (And.intro p0HighU (And.intro p0LowV high))
  exact ⟨by linarith only [lFace],p0Face⟩

theorem frame (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (7/20) (7/20))
    (inward : q.Inside 0 (13/50)) (top : q.Inside (13/50) 1)
    (missingL : ¬q.Inside (-7/20) (7/20))
    (missingP0 : ¬q.Inside 0 1) (missingP1 : ¬q.Inside 1 1)
    (missingY : ¬q.Inside (21/40) (1/8)) :
    ∃ r : OpenSquare,0<r.c ∧ 0≤r.s ∧ r.s≤r.c ∧ r.side=q.side ∧
      (∀ x y,r.Inside x y ↔ q.Inside x y) ∧
      (7/20)*(r.s-r.c)≤r.loU ∧ r.loV+r.side≤r.c := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have a := (same _ _).mpr inward
  have t := (same _ _).mpr top
  have p0 : ¬r.Inside 0 1 := fun h => missingP0 ((same _ _).mp h)
  have p1 : ¬r.Inside 1 1 := fun h => missingP1 ((same _ _).mp h)
  by_cases sign : 0≤r.s
  · have order : r.s≤r.c := by simpa only [abs_of_nonneg sign] using range
    exact ⟨r,cp,sign,order,shape,same,positive_faces r side' cp sign order m a t
      (fun h => missingL ((same _ _).mp h)) p0 p1
      (fun h => missingY ((same _ _).mp h))⟩
  · have point := negative_point r side' cp (le_of_not_ge sign)
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range) m t p0 p1
    exact False.elim (missingY ((same _ _).mp point))

#print axioms frame
end N12Compact.Completion.OtherCases.OutwardPairFaces

