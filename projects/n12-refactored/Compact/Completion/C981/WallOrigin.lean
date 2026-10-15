import Compact.Completion.C981.CornerAdvance
import Compact.Geometry.C977CornerCubic
import S12.Convex
import Mathlib.Tactic.LinearCombination

/-! Actual wall-origin completion from an actual perpendicular whole
foreign corner segment. This is OTHER-GEOMETRY Theorem9 at the exact
C981 parameters e=.086, r=.4, q=.6, including all canonical endpoints. -/
namespace N12Compact.C981CompletionWallOrigin

open S12 S12Pilot FourSquareAnchors C977CornerCubic
set_option Elab.async false

private theorem vertex (q : OpenSquare) (U V : ℝ)
    (hu : q.loU ≤ U ∧ U ≤ q.loU+q.side)
    (hv : q.loV ≤ V ∧ V ≤ q.loV+q.side) :
    ClosedInside q (q.c*U-q.s*V) (q.s*U+q.c*V) := by
  have u : q.c*(q.c*U-q.s*V)+q.s*(q.s*U+q.c*V)=U := by
    linear_combination U*q.unit_normal
  have v : -q.s*(q.c*U-q.s*V)+q.c*(q.s*U+q.c*V)=V := by
    linear_combination V*q.unit_normal
  dsimp [ClosedInside]
  rw [u,v]
  exact ⟨hu.1,hu.2,hv.1,hv.2⟩

private theorem mixed (q : OpenSquare) (x y t : ℝ)
    (closed : ClosedInside q x y) (strict : q.Inside (2/5) 0)
    (positive : 0 < t) (small : t < 1) :
    q.Inside ((1-t)*(2/5)+t*x) (t*y) := by
  have first : 0 < 1-t := by linarith only [small]
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [mul_nonneg positive.le (sub_nonneg.mpr closed.1),
      mul_pos first (sub_pos.mpr strict.1)]
  · nlinarith only [mul_nonneg positive.le (sub_nonneg.mpr closed.2.1),
      mul_pos first (sub_pos.mpr strict.2.1)]
  · nlinarith only [mul_nonneg positive.le (sub_nonneg.mpr closed.2.2.1),
      mul_pos first (sub_pos.mpr strict.2.2.1)]
  · nlinarith only [mul_nonneg positive.le (sub_nonneg.mpr closed.2.2.2),
      mul_pos first (sub_pos.mpr strict.2.2.2)]

private theorem crossing (q : OpenSquare) (x y : ℝ)
    (closed : ClosedInside q x y) (right : 1 < x) (above : 0 < y) (below : y < 3/5)
    (strict : q.Inside (2/5) 0)
    (avoid : ∀ z : ℝ, 0 ≤ z → z ≤ 3/5 → ¬ q.Inside 1 z) : False := by
  let t := (3/5)/(x-2/5)
  have denominator : 0 < x-2/5 := by linarith only [right]
  have positive : 0 < t := div_pos (by norm_num) denominator
  have small : t < 1 := (div_lt_one denominator).mpr (by linarith only [right])
  have relation : t*(x-2/5)=3/5 := div_mul_cancel₀ _ denominator.ne'
  have identity : (1-t)*(2/5)+t*x=1 := by nlinarith only [relation]
  have lower : 0 ≤ t*y := (mul_pos positive above).le
  have upper : t*y ≤ 3/5 := by
    have remaining := mul_nonneg (show 0 ≤ 1-t by linarith only [small]) above.le
    nlinarith only [remaining,below]
  have point := mixed q x y t closed strict positive small
  rw [identity] at point
  exact avoid _ lower upper point

private theorem positive_origin (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (wall : ∀ x y, q.Inside x y → y ≤ 1)
    (north : q.Inside 0 (43/500)) (east : q.Inside (2/5) 0)
    (avoid : ∀ z : ℝ, 0 ≤ z → z ≤ 3/5 → ¬ q.Inside 1 z) : q.Inside 0 0 := by
  have normal : Normal q.c q.s := ⟨hs,order,q.unit_normal⟩
  have bounds := normal_bounds normal
  have uHi : 0 < q.loU+q.side := by linarith only [east.2.1,hc]
  have vLo : q.loV < 0 := by linarith only [east.2.2.1,hs]
  have vHi : 0 < q.loV+q.side := by linarith only [north.2.2.2,hc]
  have uLo : q.loU < 0 := by
    apply lt_of_not_ge
    intro face
    have sp : 0 < q.s := by linarith only [face,north.1]
    have bUlo : q.loU < q.c := by linarith only [east.1,hc]
    have bUhi : q.c < q.loU+q.side := by linarith only [face,side,bounds.2.1]
    have bVhi : -q.s < q.loV+q.side := by linarith only [north.2.2.2,hc,hs]
    have bFace : -q.s ≤ q.loV := by
      apply le_of_not_gt
      intro low
      apply avoid 0 le_rfl (by norm_num)
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [bUlo,bUhi,low,bVhi]
    have top := C981CompletionCornerAdvance.upper_wall q wall
    let x := q.c*(q.loU+q.side)-q.s*q.loV
    let y := q.s*(q.loU+q.side)+q.c*q.loV
    have closed : ClosedInside q x y := vertex q (q.loU+q.side) q.loV
      ⟨by linarith only [q.side_pos],le_rfl⟩ ⟨le_rfl,by linarith only [q.side_pos]⟩
    have identity : q.c*x=q.loU+q.side-q.s*y := by
      dsimp [x,y]
      linear_combination (q.loU+q.side)*q.unit_normal
    have topY : y+q.c*q.side ≤ 1 := by dsimp [y]; nlinarith only [top]
    have cross := mul_nonneg hc.le hs
    have strict := mul_pos (sub_pos.mpr side) (show 0 < 1+q.c*q.s by linarith only [cross])
    have base := mul_nonneg (sub_nonneg.mpr bounds.2.1) (sub_nonneg.mpr bounds.2.2.2.1)
    have wallWeight := mul_nonneg hs (show 0 ≤ 1-y-q.c*q.side by linarith only [topY])
    have xRight : 1 < x := by
      apply lt_of_not_ge
      intro no
      have product := mul_nonneg hc.le (show 0 ≤ 1-x by linarith only [no])
      nlinarith only [identity,strict,base,wallWeight,face,product]
    have yAbove : 0 < y := by
      have first := mul_nonneg hs face
      have last := mul_nonneg hc.le (show 0 ≤ q.loV+q.s by linarith only [bFace])
      have strict := mul_pos sp (show 0 < q.side-q.c by linarith only [side,bounds.2.1])
      dsimp [y]
      nlinarith only [first,last,strict]
    have yBelow : y < 3/5 := by
      dsimp only [y] at topY ⊢
      have strict := mul_pos hc (sub_pos.mpr side)
      have below : q.s*(q.loU+q.side)+q.c*q.loV+q.c < 1 := by
        nlinarith only [topY,strict]
      linarith only [below,bounds.1]
    exact crossing q x y closed xRight yAbove yBelow east avoid
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLo,uHi,vLo,vHi]

private theorem negative_origin (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : q.s ≤ 0) (order : -q.s ≤ q.c)
    (wall : ∀ x y, q.Inside x y → y ≤ 1)
    (north : q.Inside 0 (43/500)) (east : q.Inside (2/5) 0)
    (avoid : ∀ z : ℝ, 0 ≤ z → z ≤ 3/5 → ¬ q.Inside 1 z) : q.Inside 0 0 := by
  let t := -q.s
  have normal : Normal q.c t := ⟨by dsimp [t]; linarith only [hs],order,
    by dsimp [t]; nlinarith only [q.unit_normal]⟩
  have bounds := normal_bounds normal
  have uLo : q.loU < 0 := by linarith only [north.1,hs]
  have uHi : 0 < q.loU+q.side := by linarith only [east.2.1,hc]
  have vHi : 0 < q.loV+q.side := by linarith only [north.2.2.2,hc]
  have vLo : q.loV < 0 := by
    apply lt_of_not_ge
    intro face
    have tp : 0 < t := by dsimp [t]; linarith only [face,east.2.2.1]
    have bUlo : q.loU < q.c := by linarith only [east.1,hc]
    have bVlo : q.loV < -q.s := by linarith only [east.2.2.1,hs]
    have bVhi : -q.s < q.loV+q.side := by
      dsimp [t] at bounds
      linarith only [face,side,bounds.2.2.2.1]
    have bFace : q.loU+q.side ≤ q.c := by
      apply le_of_not_gt
      intro upper
      apply avoid 0 le_rfl (by norm_num)
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [bUlo,upper,bVlo,bVhi]
    have rotatedWall : ∀ x y, (turnFrame q).Inside x y → y ≤ 1 :=
      fun x y h => wall x y ((turnFrame_inside q _ _).mp h)
    have raw := C981CompletionCornerAdvance.upper_wall (turnFrame q) rotatedWall
    have top : q.s*q.loU+q.c*(q.loV+q.side) ≤ 1 := by
      dsimp [turnFrame] at raw
      linarith only [raw]
    let x := q.c*(q.loU+q.side)-q.s*(q.loV+q.side)
    let y := q.s*(q.loU+q.side)+q.c*(q.loV+q.side)
    have closed : ClosedInside q x y := vertex q (q.loU+q.side) (q.loV+q.side)
      ⟨by linarith only [q.side_pos],le_rfl⟩ ⟨by linarith only [q.side_pos],le_rfl⟩
    have topY : y+t*q.side ≤ 1 := by dsimp [y,t]; nlinarith only [top]
    have identity : t*x=q.loV+q.side-q.c*y := by
      dsimp [x,y,t]
      linear_combination (q.loV+q.side)*q.unit_normal
    have cross := mul_nonneg hc.le normal.1
    have strict := mul_pos (sub_pos.mpr side) (show 0 < 1+q.c*t by linarith only [cross])
    have base := mul_nonneg (sub_nonneg.mpr bounds.2.1) (sub_nonneg.mpr bounds.2.2.2.1)
    have wallWeight := mul_nonneg hc.le (show 0 ≤ 1-y-t*q.side by linarith only [topY])
    have xRight : 1 < x := by
      apply lt_of_not_ge
      intro no
      have product := mul_nonneg tp.le (show 0 ≤ 1-x by linarith only [no])
      nlinarith only [identity,strict,base,wallWeight,face,product]
    have yAbove : 0 < y := by
      have first := mul_nonneg tp.le (sub_nonneg.mpr bFace)
      have last := mul_nonneg hc.le face
      have strict := mul_pos hc (show 0 < q.side-t by linarith only [side,bounds.2.2.2.1])
      dsimp [y,t] at first last strict ⊢
      nlinarith only [first,last,strict]
    have arc : 0 ≤ q.c+t-1-q.c*t+t^2/2 := by
      have product := mul_nonneg (sq_nonneg t)
        (show 0 ≤ q.c+2*t-1 by linarith only [bounds.2.2.2.2.1,normal.1])
      have identity : (1+q.c)*(q.c+t-1-q.c*t+t^2/2)=
          (t^2/2)*(q.c+2*t-1) := by
        linear_combination (1-t)*normal.2.2
      have scaled : 0 ≤ (1+q.c)*(q.c+t-1-q.c*t+t^2/2) := by
        rw [identity]
        exact mul_nonneg (div_nonneg (sq_nonneg t) (by norm_num))
          (show 0 ≤ q.c+2*t-1 by linarith only [bounds.2.2.2.2.1,normal.1])
      exact nonneg_of_mul_nonneg_right scaled (by linarith only [hc])
    have upperU : q.c+(3/5)*q.s < q.loU+q.side := by
      apply lt_of_not_ge
      intro cap
      have first := mul_nonneg tp.le (sub_nonneg.mpr cap)
      have last := mul_nonneg hc.le face
      have strict := mul_pos (sub_pos.mpr side)
        (show 0 < q.c+t by linarith only [bounds.2.2.2.2.1])
      dsimp [t] at first last strict arc
      nlinarith only [first,last,strict,top,arc,sq_nonneg q.s]
    have b1Ulo : q.loU < q.c+(3/5)*q.s := by linarith only [north.1,hc,order]
    have b1Vlo : q.loV < -q.s+(3/5)*q.c := by linarith only [east.2.2.1,hc,hs]
    have b1Face : q.loV+q.side ≤ -q.s+(3/5)*q.c := by
      apply le_of_not_gt
      intro upper
      apply avoid (3/5) (by norm_num) le_rfl
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [b1Ulo,upperU,b1Vlo,upper]
    have yBelow : y < 3/5 := by
      have strict := mul_pos tp (sub_pos.mpr side)
      have reach : 1 < t+(3/5)*q.c := by
        dsimp [t]
        linarith only [b1Face,face,side]
      have tLower : 2/5 < t := by linarith only [reach,bounds.2.1]
      dsimp only [y,t] at topY strict tLower ⊢
      have below : q.s*(q.loU+q.side)+q.c*(q.loV+q.side)-q.s < 1 := by
        nlinarith only [topY,strict]
      linarith only [below,tLower]
    exact crossing q x y closed xRight yAbove yBelow east avoid
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLo,uHi,vLo,vHi]

theorem point (q : OpenSquare) (side : 1 < q.side)
    (wall : ∀ x y, q.Inside x y → y ≤ 1)
    (north : q.Inside 0 (43/500)) (east : q.Inside (2/5) 0)
    (avoid : ∀ z : ℝ, 0 ≤ z → z ≤ 3/5 → ¬ q.Inside 1 z) : q.Inside 0 0 := by
  obtain ⟨r,hc,canon,shape,equivalent,_⟩ := ClosedFrames.canonical_frame q
  have rSide : 1 < r.side := by simpa only [shape] using side
  have rWall : ∀ x y, r.Inside x y → y ≤ 1 := fun x y h => wall x y ((equivalent _ _).mp h)
  have rAvoid : ∀ z : ℝ, 0 ≤ z → z ≤ 3/5 → ¬ r.Inside 1 z := by
    intro z lo hi point
    exact avoid z lo hi ((equivalent _ _).mp point)
  by_cases sign : 0 ≤ r.s
  · exact (equivalent _ _).mp (positive_origin r rSide hc sign
      (by simpa only [abs_of_nonneg sign] using canon) rWall
      ((equivalent _ _).mpr north) ((equivalent _ _).mpr east) rAvoid)
  · have negative : r.s ≤ 0 := le_of_lt (lt_of_not_ge sign)
    exact (equivalent _ _).mp (negative_origin r rSide hc negative
      (by simpa only [abs_of_nonpos negative] using canon) rWall
      ((equivalent _ _).mpr north) ((equivalent _ _).mpr east) rAvoid)

#print axioms point
end N12Compact.C981CompletionWallOrigin
