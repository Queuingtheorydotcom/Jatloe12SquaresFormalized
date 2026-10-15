import Compact.Completion.OtherCases.ShorterCornerScalars
import Compact.Completion.OtherCases.DerivedWalls
import Compact.Completion.CommonCases.CanonicalProjection
import Compact.Completion.CommonCases.OutwardScalars
import Compact.Geometry.ClosedFrames

/-! The genuine right wall and the shorter corner reach exclude the three
forced near-wall points, for every square orientation including tangencies. -/
namespace N12Compact.Completion.OtherCases.ShorterCornerWall
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem positive (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (wall : ∀ x y,q.Inside x y → x≤1)
    (marker : q.Inside (43/500) 0) (upper : q.Inside 0 (4/5))
    (missing0 : ¬q.Inside (1/50) 0) (missingCorner : ¬q.Inside (11/50) 1) : False := by
  have dHighU : q.c*(1/50)<q.loU+q.side := by
    linarith only [marker.2.1,cp]
  have dLowV : q.loV< -q.s*(1/50) := by
    linarith only [marker.2.2.1,sn]
  have dHighV : -q.s*(1/50)<q.loV+q.side := by
    linarith only [upper.2.2.2,cp,sn]
  have uFace : q.c*(1/50)≤q.loU := by
    apply le_of_not_gt
    intro low
    exact missing0 (by
      simpa only [OpenSquare.Inside,InBands,mul_zero,add_zero] using
        And.intro low (And.intro dHighU (And.intro dLowV dHighV)))
  have eLowU : q.loU<q.c*(11/50)+q.s := by
    linarith only [marker.1,cp,sn]
  have eLowV : q.loV< -q.s*(11/50)+q.c := by
    linarith only [marker.2.2.1,cp,order]
  have short := CommonCases.OutwardScalars.increasing_projection q.c q.s (1/5) 1
    cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
  have eHighU : q.c*(11/50)+q.s<q.loU+q.side := by
    linarith only [uFace,side,short]
  have vFace : q.loV+q.side≤ -q.s*(11/50)+q.c := by
    apply le_of_not_gt
    intro high
    exact missingCorner (by
      simpa only [OpenSquare.Inside,InBands,mul_one] using
        And.intro eLowU (And.intro eHighU (And.intro eLowV high)))
  have closed := WallProfile.vertex q (q.loU+q.side) q.loV
    ⟨by linarith only [q.side_pos],le_rfl⟩
    ⟨le_rfl,by linarith only [q.side_pos]⟩
  have closedWall := DerivedWalls.closed_affine_bound q (-1) 0 (-1) (43/500) 0
    (by
      intro x y own
      have h := wall x y own
      linarith only [h])
    marker _ _ closed
  have support : q.c*(q.loU+q.side)-q.s*q.loV≤1 := by
    linarith only [closedWall]
  have first := mul_nonneg cp.le (show 0≤q.loU-(1/50)*q.c by
    linarith only [uFace])
  have last := mul_nonneg sn (show 0≤q.c-(11/50)*q.s-(q.loV+q.side) by
    linarith only [vFace])
  have extra := mul_pos (sub_pos.mpr side)
    (show 0<q.c+q.s by linarith only [cp,sn])
  have margin := ShorterCornerScalars.margin q.c q.s cp sn order q.unit_normal
  nlinarith only [support,first,last,extra,margin]

private theorem negative (q : OpenSquare) (t : ℝ) (signed : q.s= -t)
    (side : 1<q.side) (cp : 0<q.c) (tn : 0≤t) (order : t≤q.c)
    (marker : q.Inside (43/500) 0) (lower : q.Inside 0 (13/50))
    (upper : q.Inside 0 (4/5))
    (missing0 : ¬q.Inside (1/50) 0)
    (missing1 : ¬q.Inside (1/50) (1/50))
    (missing2 : ¬q.Inside (-(1/25)) (11/100))
    (missingCorner : ¬q.Inside (11/50) 1) : False := by
  have p := marker
  have b := lower
  have c := upper
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,add_zero,zero_add]
    at p b c
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have dLowU : q.loU<q.c*(1/50) := by linarith only [c.1,cp,tn]
  have dHighU : q.c*(1/50)<q.loU+q.side := by linarith only [p.2.1,cp]
  have dHighV : t*(1/50)<q.loV+q.side := by linarith only [c.2.2.2,cp,order]
  have vFace : t*(1/50)≤q.loV := by
    apply le_of_not_gt
    intro low
    exact missing0 (by
      simpa only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,add_zero] using
        And.intro dLowU (And.intro dHighU (And.intro low dHighV)))
  by_cases steep : 5*q.c≤6*t
  · have eLowU : q.loU<q.c*(11/50)-t := by linarith only [c.1,cp,order]
    have eHighU : q.c*(11/50)-t<q.loU+q.side := by
      linarith only [b.2.1,cp,steep]
    have eLowV : q.loV<t*(11/50)+q.c := by linarith only [p.2.2.1,cp,tn]
    have eFace : q.loV+q.side≤t*(11/50)+q.c := by
      apply le_of_not_gt
      intro high
      exact missingCorner (by
        simpa only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one] using
          And.intro eLowU (And.intro eHighU (And.intro eLowV high)))
    have bound := CommonCases.CanonicalProjection.after q.c t (4/5) (3/5) 1 (1/5)
      unit (by norm_num) (by linarith only [steep,tn]) (by norm_num) (by norm_num)
    linarith only [eFace,vFace,side,bound]
  · have slope : 6*t<5*q.c := lt_of_not_ge steep
    by_cases small : 4*t≤q.c
    · apply missing1
      simp only [OpenSquare.Inside,InBands,signed,neg_neg]
      refine ⟨?_,?_,?_,?_⟩
      · linarith only [c.1,cp,tn]
      · linarith only [p.2.1,cp,tn]
      · linarith only [p.2.2.1,cp,small]
      · linarith only [c.2.2.2,cp,order]
    · have large : q.c<4*t := lt_of_not_ge small
      apply missing2
      simp only [OpenSquare.Inside,InBands,signed,neg_neg]
      refine ⟨?_,?_,?_,?_⟩
      · linarith only [c.1,large,cp]
      · linarith only [p.2.1,cp,tn]
      · linarith only [p.2.2.1,slope,cp]
      · linarith only [c.2.2.2,cp,tn]

/-- Complete shorter-corner wall obstruction. Only the displayed actual
right wall is assumed; there is no side cap or orientation premise. -/
theorem impossible (q : OpenSquare) (side : 1<q.side)
    (wall : ∀ x y,q.Inside x y → x≤1)
    (marker : q.Inside (43/500) 0) (lower : q.Inside 0 (13/50))
    (upper : q.Inside 0 (4/5))
    (missing0 : ¬q.Inside (1/50) 0)
    (missing1 : ¬q.Inside (1/50) (1/50))
    (missing2 : ¬q.Inside (-(1/25)) (11/100))
    (missingCorner : ¬q.Inside (11/50) 1) : False := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have bounds := abs_le.mp range
  have p := (same _ _).mpr marker
  have b := (same _ _).mpr lower
  have c := (same _ _).mpr upper
  have m0 : ¬r.Inside (1/50) 0 := fun h => missing0 ((same _ _).mp h)
  have m1 : ¬r.Inside (1/50) (1/50) := fun h => missing1 ((same _ _).mp h)
  have m2 : ¬r.Inside (-(1/25)) (11/100) := fun h => missing2 ((same _ _).mp h)
  have me : ¬r.Inside (11/50) 1 := fun h => missingCorner ((same _ _).mp h)
  have side' : 1<r.side := by simpa only [shape] using side
  by_cases sign : 0≤r.s
  · exact positive r side' cp sign bounds.2
      (fun x y own => wall x y ((same _ _).mp own)) p c m0 me
  · exact negative r (-r.s) (by ring) side' cp (by linarith only [sign])
      (by linarith only [bounds.1]) p b c m0 m1 m2 me

#print axioms impossible
end N12Compact.Completion.OtherCases.ShorterCornerWall

