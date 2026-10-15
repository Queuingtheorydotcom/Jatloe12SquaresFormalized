import Compact.Completion.C981.ShallowCap

/-! The top-wall reach in the presence of the actual foreign circular
cap. The normal-dependent arc point is used as a real strict point of
that same foreign owner; no mesh or sampled pose enters the proof. -/
namespace N12Compact.C981CompletionShallowWall

open S12 S12Pilot C977CornerCubic C981CompletionShallowCap
set_option Elab.async false

private theorem negative_wall (q : OpenSquare)
    (wall : ∀ x y, q.Inside x y → y ≤ 1) :
    q.s*q.loU+q.c*(q.loV+q.side) ≤ 1 := by
  have turned : ∀ x y, (turnFrame q).Inside x y → y ≤ 1 :=
    fun x y h => wall x y ((turnFrame_inside q _ _).mp h)
  have raw := C981CompletionCornerAdvance.upper_wall (turnFrame q) turned
  dsimp [turnFrame] at raw
  linarith only [raw]

private theorem positive (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (wall : ∀ x y, q.Inside x y → y ≤ 1)
    (north : q.Inside 0 (43/500)) (east : q.Inside (2/5) 0)
    (avoid : ∀ x y, Cap x y → ¬ q.Inside x y) : q.Inside (73/100) 0 := by
  have normal : Normal q.c q.s := ⟨hs,order,q.unit_normal⟩
  have bounds := normal_bounds normal
  have capF : Cap (-(13/50)) 0 := by norm_num [Cap]
  have capY : Cap 0 (-(69/2000)) := by norm_num [Cap]
  have capZ : Cap (-(1/5)) (-(1/500)) := by norm_num [Cap]
  have top := C981CompletionCornerAdvance.upper_wall q wall
  have curved := arc828 normal
  have cross := mul_nonneg hc.le hs
  have strict := mul_pos (sub_pos.mpr side)
    (show 0 < q.c+q.s by linarith only [hc,hs])
  have uLow : q.loU < (73/100)*q.c := by linarith only [east.1,hc]
  have vHigh : -(73/100)*q.s < q.loV+q.side := by linarith only [north.2.2.2,hc,hs]
  have fHighU : -(13/50)*q.c < q.loU+q.side := by linarith only [east.2.1,hc]
  have fLowV : q.loV < (13/50)*q.s := by linarith only [east.2.2.1,hs]
  have uHigh : (73/100)*q.c < q.loU+q.side := by
    apply lt_of_not_ge
    intro upper
    have fLowU : q.loU < -(13/50)*q.c := by linarith only [upper,side,bounds.2.1]
    have fFace : q.loV+q.side ≤ (13/50)*q.s := by
      apply le_of_not_gt
      intro high
      apply avoid _ _ capF
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [fLowU,fHighU,fLowV,high]
    have ratio : 43*q.c < 130*q.s := by linarith only [north.2.2.2,fFace]
    have yLowV : q.loV < -(69/2000)*q.c := by linarith only [east.2.2.1,ratio,hc]
    have yHighU : -(69/2000)*q.s < q.loU+q.side := by linarith only [east.2.1,hc,hs]
    have yHighV : -(69/2000)*q.c < q.loV+q.side := by linarith only [north.2.2.2,hc]
    have short := (short_projections q (73/100) (69/2000) (by norm_num)).2.1
    have yLowU : q.loU < -(69/2000)*q.s := by linarith only [upper,side,short]
    apply avoid _ _ capY
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [yLowU,yHighU,yLowV,yHighV]
  have vLow : q.loV < -(73/100)*q.s := by
    apply lt_of_not_ge
    intro lower
    have fHighV : (13/50)*q.s < q.loV+q.side := by
      linarith only [lower,side,bounds.2.2.2.1]
    have fFace : -(13/50)*q.c ≤ q.loU := by
      apply le_of_not_gt
      intro low
      apply avoid _ _ capF
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [low,fHighU,fLowV,fHighV]
    have one := mul_nonneg hs
      (show 0 ≤ q.loU+(13/50)*q.c by linarith only [fFace])
    have two := mul_nonneg hc.le
      (show 0 ≤ q.loV+(73/100)*q.s by linarith only [lower])
    have upper : q.side*(q.c+q.s) ≤ 1+(99/100)*q.c*q.s := by
      nlinarith only [top,one,two]
    have sine : 2/99 < q.s := by
      apply lt_of_not_ge
      intro small
      have high : q.c+q.s ≤ 101/99 := by linarith only [bounds.2.1,small]
      have product := mul_nonneg (sub_nonneg.mpr bounds.2.2.2.2.1) (sub_nonneg.mpr high)
      have curved99 : 1+(99/100)*q.c*q.s ≤ q.c+q.s := by
        nlinarith only [product,q.unit_normal,cross]
      nlinarith only [upper,strict,curved99]
    have yHighU : -(69/2000)*q.s < q.loU+q.side := by linarith only [north.2.1,hs]
    have yHighV : -(69/2000)*q.c < q.loV+q.side := by linarith only [north.2.2.2,hc]
    have yLowU : q.loU < -(69/2000)*q.s := by
      apply lt_of_not_ge
      intro face
      have first := mul_nonneg hs
        (show 0 ≤ q.loU+(69/2000)*q.s by linarith only [face])
      have canonical := mul_nonneg hs (sub_nonneg.mpr order)
      nlinarith only [top,first,two,canonical,strict,curved,cross]
    have yFace : -(69/2000)*q.c ≤ q.loV := by
      apply le_of_not_gt
      intro low
      apply avoid _ _ capY
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [yLowU,yHighU,low,yHighV]
    have ratio : 800*q.s < 69*q.c := by linarith only [yFace,east.2.2.1]
    have hUpper : q.c+q.s ≤ 869/800 := by linarith only [ratio,bounds.2.1]
    have product := mul_nonneg (sub_nonneg.mpr bounds.2.2.2.2.1) (sub_nonneg.mpr hUpper)
    have curved932 : 1+(233/250)*q.c*q.s ≤ q.c+q.s := by
      nlinarith only [product,q.unit_normal,cross]
    have zHighU : -(1/5)*q.c-(1/500)*q.s < q.loU+q.side := by
      linarith only [east.2.1,hc,hs]
    have zHighV : (1/5)*q.s-(1/500)*q.c < q.loV+q.side := by
      linarith only [north.2.2.2,ratio,hc]
    have zLowU : q.loU < -(1/5)*q.c-(1/500)*q.s := by
      apply lt_of_not_ge
      intro face
      have first := mul_nonneg hs
        (show 0 ≤ q.loU+(1/5)*q.c+(1/500)*q.s by linarith only [face])
      have canonical := mul_nonneg hs (sub_nonneg.mpr order)
      nlinarith only [top,first,two,canonical,strict,curved932]
    have zFace : (1/5)*q.s-(1/500)*q.c ≤ q.loV := by
      apply le_of_not_gt
      intro low
      apply avoid _ _ capZ
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [zLowU,zHighU,low,zHighV]
    linarith only [zFace,east.2.2.1,sine,bounds.2.1]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLow,uHigh,vLow,vHigh]

private theorem negative (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : q.s ≤ 0) (order : -q.s ≤ q.c)
    (wall : ∀ x y, q.Inside x y → y ≤ 1)
    (north : q.Inside 0 (43/500)) (east : q.Inside (2/5) 0)
    (avoid : ∀ x y, Cap x y → ¬ q.Inside x y) : q.Inside (73/100) 0 := by
  have normal : Normal q.c (-q.s) := ⟨by linarith only [hs],order,
    by nlinarith only [q.unit_normal]⟩
  have bounds := normal_bounds normal
  have capY : Cap 0 (-(69/2000)) := by norm_num [Cap]
  have top := negative_wall q wall
  have strict := mul_pos (sub_pos.mpr side)
    (show 0 < q.c+(-q.s) by linarith only [bounds.2.2.2.2.1])
  have uLow : q.loU < (73/100)*q.c := by linarith only [east.1,hc]
  have vLow : q.loV < -(73/100)*q.s := by linarith only [east.2.2.1,hs]
  have vHigh : -(73/100)*q.s < q.loV+q.side := by
    apply lt_of_not_ge
    intro upper
    have yLowU : q.loU < -(69/2000)*q.s := by linarith only [north.1,hs]
    have yHighU : -(69/2000)*q.s < q.loU+q.side := by linarith only [east.2.1,hc,order]
    have yHighV : -(69/2000)*q.c < q.loV+q.side := by linarith only [north.2.2.2,hc]
    have short := (short_projections q (73/100) (69/2000) (by norm_num)).2.2.2
    have yLowV : q.loV < -(69/2000)*q.c := by linarith only [upper,short,side]
    apply avoid _ _ capY
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [yLowU,yHighU,yLowV,yHighV]
  have uHigh : (73/100)*q.c < q.loU+q.side := by
    apply lt_of_not_ge
    intro upper
    have capFaces (x y : ℝ) (cap : Cap x y) : -q.s*x+q.c*y ≤ q.loV := by
      have dx := mul_nonneg hc.le (show 0 ≤ x+13/50 by linarith only [cap.1])
      have yy := mul_nonneg_of_nonpos_of_nonpos hs cap.2.2.2.1
      have lowU : q.loU < q.c*x+q.s*y := by nlinarith only [upper,side,bounds.2.1,dx,yy]
      have xx := mul_nonneg hc.le (show 0 ≤ -x by linarith only [cap.2.1])
      have ys := mul_nonneg (show 0 ≤ -q.s by linarith only [hs])
        (show 0 ≤ y+69/2000 by linarith only [cap.2.2.1])
      have highU : q.c*x+q.s*y < q.loU+q.side := by
        nlinarith only [east.2.1,xx,ys,order,hc]
      have xv := mul_nonneg (show 0 ≤ -q.s by linarith only [hs])
        (show 0 ≤ -x by linarith only [cap.2.1])
      have yv := mul_nonneg hc.le (show 0 ≤ -y by linarith only [cap.2.2.2.1])
      have highV : -q.s*x+q.c*y < q.loV+q.side := by
        nlinarith only [north.2.2.2,xv,yv,hc]
      apply le_of_not_gt
      intro low
      apply avoid x y cap
      exact ⟨lowU,highU,low,highV⟩
    by_cases small : (-q.s) ≤ 13/50
    · have tSquare : (-q.s)^2 ≤ 169/2500 := by
        have product := mul_nonneg (sub_nonneg.mpr small)
          (show 0 ≤ 13/50+(-q.s) by linarith only [normal.1])
        nlinarith only [product]
      have cLow : 1931/2000 ≤ q.c := by
        apply le_of_not_gt
        intro low
        have product := mul_nonneg
          (show 0 ≤ 1931/2000-q.c by linarith only [low])
          (show 0 ≤ 1931/2000+q.c by linarith only [hc])
        nlinarith only [product,normal.2.2,tSquare]
      have arcCap : Cap ((-q.s)-13/50) (q.c-1) := by
        dsimp [Cap]
        refine ⟨?_,?_,?_,?_,?_⟩
        · linarith only [normal.1]
        · linarith only [small]
        · linarith only [cLow]
        · linarith only [bounds.2.1]
        · nlinarith only [normal.2.2]
      have raw := capFaces _ _ arcCap
      have face : 1-q.c-(13/50)*(-q.s) ≤ q.loV := by

        nlinarith only [raw,q.unit_normal]
      have one := mul_nonneg normal.1 (sub_nonneg.mpr upper)
      have two := mul_nonneg hc.le (sub_nonneg.mpr face)
      have cross := mul_nonneg hc.le normal.1
      have product := mul_nonneg (sub_nonneg.mpr bounds.2.1)
        (show 0 ≤ (-q.s)-(1-q.c) by linarith only [bounds.2.2.2.2.1])

      nlinarith only [top,one,two,strict,cross,product,q.unit_normal]
    · have large : 13/50 < (-q.s) := lt_of_not_ge small
      have raw := capFaces _ _ capY
      have face : -(69/2000)*q.c ≤ q.loV := by
        norm_num at raw
        linarith only [raw]
      have one := mul_nonneg normal.1 (sub_nonneg.mpr upper)
      have two := mul_nonneg hc.le (sub_nonneg.mpr face)
      have bound : q.side*(q.c+(-q.s)) ≤ 1+(73/100)*q.c*(-q.s)+(69/2000)*q.c^2 := by

        nlinarith only [top,one,two]
      have cSquare : 0 < q.c^2 := by nlinarith only [mul_pos hc hc]
      by_cases moderate : (-q.s) < 1/3
      · have cs := mul_nonneg normal.1 (sub_nonneg.mpr bounds.2.1)
        have high : q.c+(-q.s) ≤ 13/10 := by
          nlinarith only [normal.2.2,cs,moderate,sq_nonneg (q.c+(-q.s)-13/10)]
        have product := mul_nonneg (sub_nonneg.mpr bounds.2.2.2.2.1) (sub_nonneg.mpr high)
        have cross := mul_nonneg hc.le normal.1
        have curved : 1+(20/23)*q.c*(-q.s) ≤ q.c+(-q.s) := by
          nlinarith only [product,normal.2.2,cross]
        have ratio := mul_pos hc
          (show 0 < (-q.s)-(13/50)*q.c by linarith only [large,bounds.2.1])
        nlinarith only [bound,strict,curved,ratio,cSquare]
      · have tLow : 1/3 ≤ (-q.s) := le_of_not_gt moderate
        have tSquare := mul_nonneg (sub_nonneg.mpr tLow)
          (show 0 ≤ (-q.s)+1/3 by linarith only [normal.1])
        have ratio : (353/1000)*q.c < (-q.s) := by
          apply lt_of_not_ge
          intro low
          have product := mul_nonneg (sub_nonneg.mpr low)
            (show 0 ≤ (353/1000)*q.c+(-q.s) by linarith only [hc,normal.1])
          nlinarith only [product,tSquare,normal.2.2]
        have weighted := mul_pos hc (sub_pos.mpr ratio)
        have curved := arc828 normal
        nlinarith only [bound,strict,curved,weighted,cSquare]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLow,uHigh,vLow,vHigh]

theorem point (q : OpenSquare) (side : 1 < q.side)
    (wall : ∀ x y, q.Inside x y → y ≤ 1)
    (north : q.Inside 0 (43/500)) (east : q.Inside (2/5) 0)
    (avoid : ∀ x y, Cap x y → ¬ q.Inside x y) : q.Inside (73/100) 0 := by
  obtain ⟨r,hc,canon,shape,equivalent,_⟩ := ClosedFrames.canonical_frame q
  have rSide : 1 < r.side := by simpa only [shape] using side
  have rWall : ∀ x y, r.Inside x y → y ≤ 1 :=
    fun x y h => wall x y ((equivalent _ _).mp h)
  have rAvoid : ∀ x y, Cap x y → ¬ r.Inside x y := by
    intro x y cap point
    exact avoid x y cap ((equivalent _ _).mp point)
  by_cases sign : 0 ≤ r.s
  · exact (equivalent _ _).mp (positive r rSide hc sign
      (by simpa only [abs_of_nonneg sign] using canon) rWall
      ((equivalent _ _).mpr north) ((equivalent _ _).mpr east) rAvoid)
  · have nonpositive : r.s ≤ 0 := le_of_lt (lt_of_not_ge sign)
    exact (equivalent _ _).mp (negative r rSide hc nonpositive
      (by simpa only [abs_of_nonpos nonpositive] using canon) rWall
      ((equivalent _ _).mpr north) ((equivalent _ _).mpr east) rAvoid)

#print axioms point
end N12Compact.C981CompletionShallowWall
