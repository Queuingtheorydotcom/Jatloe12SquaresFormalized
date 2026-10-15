import Compact.Completion.C981.CornerAdvance
import Compact.Completion.C981.WallScalars
import Compact.Geometry.C977CornerCubic

/-! The three actual-support lemmas from C981-WALL-CYCLES Theorems 11--13.
All coordinates here are translated by (-2,-3). The only boundary is the
real top wall, and every absence remains a weak four-face exclusion. -/
namespace N12Compact.C981CompletionTopReach

open S12 S12Pilot C977CornerCubic
set_option Elab.async false

private theorem arc {c s : ℝ} (normal : Normal c s) :
    1+(4/5)*c*s ≤ c+s := by
  have bounds := normal_bounds normal
  have product := mul_nonneg (sub_nonneg.mpr bounds.2.2.2.2.1)
    (sub_nonneg.mpr bounds.2.2.2.2.2)
  have cross := mul_nonneg (show 0 ≤ c by linarith only [bounds.1]) normal.1
  nlinarith only [product,normal.2.2,cross]

private theorem negative_wall (q : OpenSquare)
    (wall : ∀ x y, q.Inside x y → y ≤ 1) :
    q.s*q.loU+q.c*(q.loV+q.side) ≤ 1 := by
  have turned : ∀ x y, (turnFrame q).Inside x y → y ≤ 1 :=
    fun x y h => wall x y ((turnFrame_inside q _ _).mp h)
  have raw := C981CompletionCornerAdvance.upper_wall (turnFrame q) turned
  dsimp [turnFrame] at raw
  linarith only [raw]

private theorem origin_positive (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (wall : ∀ x y, q.Inside x y → y ≤ 1)
    (north : q.Inside 0 (43/500)) (east : q.Inside (2/5) 0)
    (missing : ¬ q.Inside 0 0) : q.Inside (4/5) 0 := by
  have normal : Normal q.c q.s := ⟨hs,order,q.unit_normal⟩
  have bounds := normal_bounds normal
  have uHi : 0 < q.loU+q.side := by linarith only [east.2.1,hc]
  have vLo : q.loV < 0 := by linarith only [east.2.2.1,hs]
  have vHi : 0 < q.loV+q.side := by linarith only [north.2.2.2,hc]
  have uFace : 0 ≤ q.loU := by
    apply le_of_not_gt
    intro low
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [low,uHi,vLo,vHi]
  have uLow : q.loU < (4/5)*q.c := by linarith only [east.1,hc]
  have uHigh : (4/5)*q.c < q.loU+q.side := by
    linarith only [uFace,side,bounds.2.1]
  have vHigh : -(4/5)*q.s < q.loV+q.side := by linarith only [north.2.2.2,hc,hs]
  have vLow : q.loV < -(4/5)*q.s := by
    apply lt_of_not_ge
    intro face
    have top := C981CompletionCornerAdvance.upper_wall q wall
    have one := mul_nonneg hs uFace
    have two := mul_nonneg hc.le
      (show 0 ≤ q.loV+(4/5)*q.s by linarith only [face])
    have strict := mul_pos (sub_pos.mpr side)
      (show 0 < q.c+q.s by linarith only [bounds.2.2.2.2.1])
    have curved := arc normal
    nlinarith only [top,one,two,strict,curved]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLow,uHigh,vLow,vHigh]

private theorem origin_negative (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : q.s ≤ 0) (order : -q.s ≤ q.c)
    (wall : ∀ x y, q.Inside x y → y ≤ 1)
    (north : q.Inside 0 (43/500)) (east : q.Inside (2/5) 0)
    (missing : ¬ q.Inside 0 0) : q.Inside (4/5) 0 := by
  have normal : Normal q.c (-q.s) := ⟨by linarith only [hs],order,
    by nlinarith only [q.unit_normal]⟩
  have bounds := normal_bounds normal
  have uLo : q.loU < 0 := by linarith only [north.1,hs]
  have uHi : 0 < q.loU+q.side := by linarith only [east.2.1,hc]
  have vHi : 0 < q.loV+q.side := by linarith only [north.2.2.2,hc]
  have vFace : 0 ≤ q.loV := by
    apply le_of_not_gt
    intro low
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLo,uHi,low,vHi]
  have uLow : q.loU < (4/5)*q.c := by linarith only [east.1,hc]
  have vLow : q.loV < -(4/5)*q.s := by linarith only [east.2.2.1,hs]
  have vHigh : -(4/5)*q.s < q.loV+q.side := by
    linarith only [vFace,side,bounds.2.2.2.1]
  have uHigh : (4/5)*q.c < q.loU+q.side := by
    apply lt_of_not_ge
    intro face
    have top := negative_wall q wall
    have one := mul_nonneg (show 0 ≤ -q.s by linarith only [hs])
      (show 0 ≤ (4/5)*q.c-q.loU-q.side by linarith only [face])
    have two := mul_nonneg hc.le vFace
    have strict := mul_pos (sub_pos.mpr side)
      (show 0 < q.c-q.s by linarith only [bounds.2.2.2.2.1])
    have curved := arc normal
    nlinarith only [top,one,two,strict,curved]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLow,uHigh,vLow,vHigh]

theorem origin_alternative (q : OpenSquare) (side : 1 < q.side)
    (wall : ∀ x y, q.Inside x y → y ≤ 1)
    (north : q.Inside 0 (43/500)) (east : q.Inside (2/5) 0)
    (missing : ¬ q.Inside 0 0) : q.Inside (4/5) 0 := by
  obtain ⟨r,hc,canon,shape,equivalent,_⟩ := ClosedFrames.canonical_frame q
  have rSide : 1 < r.side := by simpa only [shape] using side
  have rWall : ∀ x y, r.Inside x y → y ≤ 1 :=
    fun x y h => wall x y ((equivalent _ _).mp h)
  by_cases sign : 0 ≤ r.s
  · exact (equivalent _ _).mp (origin_positive r rSide hc sign
      (by simpa only [abs_of_nonneg sign] using canon) rWall
      ((equivalent _ _).mpr north) ((equivalent _ _).mpr east)
      (fun h => missing ((equivalent _ _).mp h)))
  · have negative : r.s ≤ 0 := le_of_lt (lt_of_not_ge sign)
    exact (equivalent _ _).mp (origin_negative r rSide hc negative
      (by simpa only [abs_of_nonpos negative] using canon) rWall
      ((equivalent _ _).mpr north) ((equivalent _ _).mpr east)
      (fun h => missing ((equivalent _ _).mp h)))

private theorem tip_negative_impossible (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : q.s ≤ 0) (order : -q.s ≤ q.c)
    (f : q.Inside (-(13/50)) 0) (a : q.Inside 0 (-(37/50)))
    (marker : q.Inside (-(7/20)) (-(13/20)))
    (missingZ : ¬ q.Inside (-(2/5)) 0)
    (missingR : ¬ q.Inside (7/20) (-(13/20))) : False := by
  have zHighU : -(2/5)*q.c < q.loU+q.side := by linarith only [a.2.1,hc,hs]
  have zLowV : q.loV < (2/5)*q.s := by linarith only [marker.2.2.1,hc,order]
  have zHighV : (2/5)*q.s < q.loV+q.side := by linarith only [f.2.2.2,hs]
  have zFace : -(2/5)*q.c ≤ q.loU := by
    apply le_of_not_gt
    intro low
    apply missingZ
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [low,zHighU,zLowV,zHighV]
  have rLowU : q.loU < (7/20)*q.c-(13/20)*q.s := by linarith only [f.1,hc,hs]
  have rLowV : q.loV < -(7/20)*q.s-(13/20)*q.c := by
    linarith only [a.2.2.1,hc,hs]
  have rHighV : -(7/20)*q.s-(13/20)*q.c < q.loV+q.side := by
    linarith only [f.2.2.2,hc,order]
  have rFace : q.loU+q.side ≤ (7/20)*q.c-(13/20)*q.s := by
    apply le_of_not_gt
    intro high
    apply missingR
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [rLowU,high,rLowV,rHighV]
  have short := (short_projections q (3/4) (-(13/20)) (by norm_num)).2.1
  linarith only [zFace,rFace,short,side]

private theorem tip_positive (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (f : q.Inside (-(13/50)) 0) (a : q.Inside 0 (-(37/50)))
    (marker : q.Inside (-(7/20)) (-(13/20)))
    (missingO : ¬ q.Inside 0 0) (missingZ : ¬ q.Inside (-(2/5)) 0)
    (missingB : ¬ q.Inside (-(13/50)) (-1))
    (missingL : ¬ q.Inside (-1) (-(1/5))) : q.Inside (-(3/100)) 0 := by
  have normal : Normal q.c q.s := ⟨hs,order,q.unit_normal⟩
  have bounds := normal_bounds normal
  have oLowU : q.loU < 0 := by linarith only [f.1,hc]
  have oLowV : q.loV < 0 := by linarith only [a.2.2.1,hc]
  have oHighV : 0 < q.loV+q.side := by linarith only [f.2.2.2,hs]
  have oFace : q.loU+q.side ≤ 0 := by
    apply le_of_not_gt
    intro high
    apply missingO
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [oLowU,high,oLowV,oHighV]
  have zHighU : -(2/5)*q.c < q.loU+q.side := by linarith only [f.2.1,hc]
  have zLowV : q.loV < (2/5)*q.s := by linarith only [a.2.2.1,hc,hs]
  have zLowU : q.loU < -(2/5)*q.c := by linarith only [oFace,side,bounds.2.1]
  have zFace : q.loV+q.side ≤ (2/5)*q.s := by
    apply le_of_not_gt
    intro high
    apply missingZ
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [zLowU,zHighU,zLowV,high]
  have bHighU : -(13/50)*q.c-q.s < q.loU+q.side := by linarith only [f.2.1,hs]
  have bHighV : (13/50)*q.s-q.c < q.loV+q.side := by linarith only [f.2.2.2,hc]
  have projection := C981CompletionWallScalars.canonical_projection q.c q.s hc.le hs order q.unit_normal
  have bLowU : q.loU < -(13/50)*q.c-q.s := by
    linarith only [oFace,side,projection,hc]
  have bFace : (13/50)*q.s-q.c ≤ q.loV := by
    apply le_of_not_gt
    intro low
    apply missingB
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [bLowU,bHighU,low,bHighV]
  have width : q.side ≤ q.c+(7/50)*q.s := by linarith only [zFace,bFace]
  have lHighU : -q.c-(1/5)*q.s < q.loU+q.side := by linarith only [f.2.1,hc,hs]
  have lLowV : q.loV < q.s-(1/5)*q.c := by linarith only [a.2.2.1,hc,hs]
  have lHighV : q.s-(1/5)*q.c < q.loV+q.side := by
    have short := (short_projections q (19/20) (29/100) (by norm_num)).2.1
    apply lt_of_not_ge
    intro cap
    have other : q.side ≤ (4/5)*q.c+(37/50)*q.s := by linarith only [cap,bFace]
    linarith only [width,other,short,side]
  have lFace : -q.c-(1/5)*q.s ≤ q.loU := by
    apply le_of_not_gt
    intro low
    apply missingL
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [low,lHighU,lLowV,lHighV]
  have xLowU : q.loU < -(3/100)*q.c := by linarith only [f.1,hc]
  have xLowV : q.loV < (3/100)*q.s := by linarith only [a.2.2.1,hc,hs]
  have xHighV : (3/100)*q.s < q.loV+q.side := by linarith only [f.2.2.2,hs]
  have short := (short_projections q (97/100) (1/5) (by norm_num)).2.1
  have xHighU : -(3/100)*q.c < q.loU+q.side := by linarith only [lFace,short,side]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [xLowU,xHighU,xLowV,xHighV]

theorem central_tip (q : OpenSquare) (side : 1 < q.side)
    (f : q.Inside (-(13/50)) 0) (a : q.Inside 0 (-(37/50)))
    (marker : q.Inside (-(7/20)) (-(13/20)))
    (missingO : ¬ q.Inside 0 0) (missingZ : ¬ q.Inside (-(2/5)) 0)
    (missingB : ¬ q.Inside (-(13/50)) (-1))
    (missingR : ¬ q.Inside (7/20) (-(13/20)))
    (missingL : ¬ q.Inside (-1) (-(1/5))) : q.Inside (-(3/100)) 0 := by
  obtain ⟨r,hc,canon,shape,equivalent,_⟩ := ClosedFrames.canonical_frame q
  have rSide : 1 < r.side := by simpa only [shape] using side
  by_cases sign : 0 ≤ r.s
  · exact (equivalent _ _).mp (tip_positive r rSide hc sign
      (by simpa only [abs_of_nonneg sign] using canon)
      ((equivalent _ _).mpr f) ((equivalent _ _).mpr a) ((equivalent _ _).mpr marker)
      (fun h => missingO ((equivalent _ _).mp h))
      (fun h => missingZ ((equivalent _ _).mp h))
      (fun h => missingB ((equivalent _ _).mp h))
      (fun h => missingL ((equivalent _ _).mp h)))
  · have negative : r.s ≤ 0 := le_of_lt (lt_of_not_ge sign)
    exact False.elim (tip_negative_impossible r rSide hc negative
      (by simpa only [abs_of_nonpos negative] using canon)
      ((equivalent _ _).mpr f) ((equivalent _ _).mpr a) ((equivalent _ _).mpr marker)
      (fun h => missingZ ((equivalent _ _).mp h))
      (fun h => missingR ((equivalent _ _).mp h)))

private theorem foreign_positive (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (wall : ∀ x y, q.Inside x y → y ≤ 1)
    (north : q.Inside 0 (43/500)) (east : q.Inside (2/5) 0)
    (missingTip : ¬ q.Inside (-(3/100)) 0) : q.Inside (73/100) 0 := by
  have normal : Normal q.c q.s := ⟨hs,order,q.unit_normal⟩
  have bounds := normal_bounds normal
  have lHighU : -(3/100)*q.c < q.loU+q.side := by linarith only [east.2.1,hc]
  have lLowV : q.loV < (3/100)*q.s := by linarith only [east.2.2.1,hs]
  have lHighV : (3/100)*q.s < q.loV+q.side := by linarith only [north.2.2.2,hc,order]
  have lFace : -(3/100)*q.c ≤ q.loU := by
    apply le_of_not_gt
    intro low
    apply missingTip
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [low,lHighU,lLowV,lHighV]
  have uLow : q.loU < (73/100)*q.c := by linarith only [east.1,hc]
  have uHigh : (73/100)*q.c < q.loU+q.side := by linarith only [lFace,side,bounds.2.1]
  have vHigh : -(73/100)*q.s < q.loV+q.side := by linarith only [north.2.2.2,hc,hs]
  have vLow : q.loV < -(73/100)*q.s := by
    apply lt_of_not_ge
    intro face
    have top := C981CompletionCornerAdvance.upper_wall q wall
    have one := mul_nonneg hs
      (show 0 ≤ q.loU+(3/100)*q.c by linarith only [lFace])
    have two := mul_nonneg hc.le
      (show 0 ≤ q.loV+(73/100)*q.s by linarith only [face])
    have strict := mul_pos (sub_pos.mpr side)
      (show 0 < q.c+q.s by linarith only [bounds.2.2.2.2.1])
    have curved := arc normal
    have cross := mul_nonneg hc.le hs
    nlinarith only [top,one,two,strict,curved,cross]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLow,uHigh,vLow,vHigh]

private theorem foreign_negative (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : q.s ≤ 0) (order : -q.s ≤ q.c)
    (wall : ∀ x y, q.Inside x y → y ≤ 1)
    (north : q.Inside 0 (43/500)) (east : q.Inside (2/5) 0)
    (missingTip : ¬ q.Inside (-(3/100)) 0)
    (missingBelow : ¬ q.Inside 0 (-(37/50))) : q.Inside (73/100) 0 := by
  have normal : Normal q.c (-q.s) := ⟨by linarith only [hs],order,
    by nlinarith only [q.unit_normal]⟩
  have bounds := normal_bounds normal
  have lHighU : -(3/100)*q.c < q.loU+q.side := by linarith only [east.2.1,hc]
  have lHighV : (3/100)*q.s < q.loV+q.side := by linarith only [north.2.2.2,hc,hs]
  have modes : -(3/100)*q.c ≤ q.loU ∨ (3/100)*q.s ≤ q.loV := by
    by_cases first : -(3/100)*q.c ≤ q.loU
    · exact Or.inl first
    · right
      apply le_of_not_gt
      intro low
      apply missingTip
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [first,lHighU,low,lHighV]
  have uLow : q.loU < (73/100)*q.c := by linarith only [east.1,hc]
  have vLow : q.loV < -(73/100)*q.s := by linarith only [east.2.2.1,hs]
  rcases modes with uFace | vFace
  · have ratio : 43*(-q.s) < 15*q.c := by linarith only [uFace,north.1]
    have aLowU : q.loU < -(37/50)*q.s := by linarith only [north.1,hs]
    have aHighU : -(37/50)*q.s < q.loU+q.side := by linarith only [east.2.1,ratio,hc]
    have aHighV : -(37/50)*q.c < q.loV+q.side := by linarith only [north.2.2.2,hc]
    have aFace : -(37/50)*q.c ≤ q.loV := by
      apply le_of_not_gt
      intro low
      apply missingBelow
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [aLowU,aHighU,low,aHighV]
    have uHigh : (73/100)*q.c < q.loU+q.side := by linarith only [uFace,side,bounds.2.1]
    have vHigh : -(73/100)*q.s < q.loV+q.side := by
      linarith only [aFace,side,ratio,bounds.2.1]
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLow,uHigh,vLow,vHigh]
  · have vHigh : -(73/100)*q.s < q.loV+q.side := by
      linarith only [vFace,side,bounds.2.2.2.1]
    have uHigh : (73/100)*q.c < q.loU+q.side := by
      apply lt_of_not_ge
      intro face
      have top := negative_wall q wall
      have one := mul_nonneg (show 0 ≤ -q.s by linarith only [hs])
        (show 0 ≤ (73/100)*q.c-q.loU-q.side by linarith only [face])
      have two := mul_nonneg hc.le
        (show 0 ≤ q.loV-(3/100)*q.s by linarith only [vFace])
      have strict := mul_pos (sub_pos.mpr side)
        (show 0 < q.c-q.s by linarith only [bounds.2.2.2.2.1])
      have curved := arc normal
      have cross := mul_nonneg hc.le normal.1
      nlinarith only [top,one,two,strict,curved,cross]
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLow,uHigh,vLow,vHigh]

theorem foreign_tip (q : OpenSquare) (side : 1 < q.side)
    (wall : ∀ x y, q.Inside x y → y ≤ 1)
    (north : q.Inside 0 (43/500)) (east : q.Inside (2/5) 0)
    (missingTip : ¬ q.Inside (-(3/100)) 0)
    (missingBelow : ¬ q.Inside 0 (-(37/50))) : q.Inside (73/100) 0 := by
  obtain ⟨r,hc,canon,shape,equivalent,_⟩ := ClosedFrames.canonical_frame q
  have rSide : 1 < r.side := by simpa only [shape] using side
  have rWall : ∀ x y, r.Inside x y → y ≤ 1 :=
    fun x y h => wall x y ((equivalent _ _).mp h)
  by_cases sign : 0 ≤ r.s
  · exact (equivalent _ _).mp (foreign_positive r rSide hc sign
      (by simpa only [abs_of_nonneg sign] using canon) rWall
      ((equivalent _ _).mpr north) ((equivalent _ _).mpr east)
      (fun h => missingTip ((equivalent _ _).mp h)))
  · have negative : r.s ≤ 0 := le_of_lt (lt_of_not_ge sign)
    exact (equivalent _ _).mp (foreign_negative r rSide hc negative
      (by simpa only [abs_of_nonpos negative] using canon) rWall
      ((equivalent _ _).mpr north) ((equivalent _ _).mpr east)
      (fun h => missingTip ((equivalent _ _).mp h))
      (fun h => missingBelow ((equivalent _ _).mp h)))

#print axioms origin_alternative
#print axioms central_tip
#print axioms foreign_tip
end N12Compact.C981CompletionTopReach
