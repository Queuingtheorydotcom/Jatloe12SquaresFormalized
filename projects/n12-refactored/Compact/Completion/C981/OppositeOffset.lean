import Compact.Completion.C981.CornerAdvance
import S12.Convex
import Mathlib.Tactic.LinearCombination

/-! The inward owner's small lower-face offset in the final C981 pair.
Its positive-quadrant frame has no ordering premise. The whole foreign
wall segment is retained when its rightmost vertex is ruled out. -/
namespace N12Compact.C981CompletionOppositeOffset

open S12 S12Pilot
set_option Elab.async false

private theorem components (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (unit : c^2+s^2=1) (wide : 50/37 < c+s) : 23/50 < c ∧ 23/50 < s := by
  have one (x y : ℝ) (xn : 0 ≤ x) (yn : 0 ≤ y)
      (norm : x^2+y^2=1) (sum : 50/37 < x+y) : 23/50 < x := by
    apply lt_of_not_ge
    intro low
    have first := mul_pos
      (show 0 < y-(27/20-x) by linarith only [sum])
      (show 0 < y+(27/20-x) by linarith only [yn,low])
    have last := mul_nonneg (sub_nonneg.mpr low)
      (show 0 ≤ 27/10-2*(x+23/50) by linarith only [low])
    nlinarith only [first,last,norm]
  exact ⟨one c s hc hs unit wide,one s c hs hc (by linarith only [unit])
    (by linarith only [wide])⟩

private theorem vertex_margin (c s : ℝ) (hc : 0 < c) (hs : 0 ≤ s)
    (unit : c^2+s^2=1) (wide : 50/37 < c+s) :
    0 < (17/500)*c+(13/50)*s^2-(1-c)*(1-s) := by
  have bounds := components c s hc.le hs unit wide
  have cOne : c ≤ 1 := by nlinarith only [unit,sq_nonneg s,sq_nonneg (c-1)]
  have sOne : s ≤ 1 := by nlinarith only [unit,sq_nonneg c,sq_nonneg (s-1)]
  have identity : (1+c)*((17/500)*c+(13/50)*s^2-(1-c)*(1-s))=
      (1+c)*((17/500)*c-(1/25)*s^2)+
        s^2*((3/10)*(1+c)-(1-s)) := by
    linear_combination (1-s)*unit
  by_cases small : s ≤ 3/5
  · have cLow : 4/5 ≤ c := by
      have sine := mul_nonneg (sub_nonneg.mpr small)
        (show 0 ≤ 3/5+s by linarith only [hs])
      apply le_of_not_gt
      intro low
      have cosine := mul_pos
        (show 0 < 4/5-c by linarith only [low])
        (show 0 < 4/5+c by linarith only [hc])
      nlinarith only [sine,cosine,unit]
    have square : s^2 ≤ 9/25 := by
      have product := mul_nonneg (sub_nonneg.mpr small)
        (show 0 ≤ 3/5+s by linarith only [hs])
      nlinarith only [product]
    have bracket : 0 ≤ (3/10)*(1+c)-(1-s) := by linarith only [cLow,bounds.2]
    have first := mul_pos (show 0 < 1+c by linarith only [hc])
      (show 0 < (17/500)*c-(1/25)*s^2 by linarith only [cLow,square])
    have last := mul_nonneg (sq_nonneg s) bracket
    have positive : 0 < (1+c)*((17/500)*c+(13/50)*s^2-(1-c)*(1-s)) := by
      rw [identity]
      linarith only [first,last]
    exact pos_of_mul_pos_right positive (by linarith only [hc])
  · have large : 3/5 ≤ s := (lt_of_not_ge small).le
    have bracket : 0 ≤ s+(13/50)*c-37/50 := by
      by_cases high : 37/50 ≤ s
      · linarith only [high,hc]
      · have sLow : s ≤ 37/50 := le_of_lt (lt_of_not_ge high)
        have cLow : 67/100 ≤ c := by
          have sine := mul_nonneg (sub_nonneg.mpr sLow)
            (show 0 ≤ 37/50+s by linarith only [hs])
          apply le_of_not_gt
          intro low
          have cosine := mul_pos
            (show 0 < 67/100-c by linarith only [low])
            (show 0 < 67/100+c by linarith only [hc])
          nlinarith only [sine,cosine,unit]
        linarith only [large,cLow]
    have otherIdentity : (1+c)*((17/500)*c+(13/50)*s^2-(1-c)*(1-s))=
        (17/500)*c*(1+c)+s^2*(s+(13/50)*c-37/50) := by
      linear_combination (1-s)*unit
    have first := mul_pos hc (show 0 < 1+c by linarith only [hc])
    have last := mul_nonneg (sq_nonneg s) bracket
    have positive : 0 < (1+c)*((17/500)*c+(13/50)*s^2-(1-c)*(1-s)) := by
      rw [otherIdentity]
      nlinarith only [first,last]
    exact pos_of_mul_pos_right positive (by linarith only [hc])

theorem bounds (A : OpenSquare) (side : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s)
    (north : A.Inside 0 (13/50)) (east : A.Inside (13/50) 0)
    (marker : A.Inside (7/20) (7/20))
    (missingO : ¬ A.Inside 0 0) (missingF : ¬ A.Inside (13/50) 1)
    (segment : ∀ y : ℝ, 13/50 ≤ y → y ≤ 4/5 → ¬ A.Inside 1 y) :
    0 < A.s ∧ 0 ≤ A.loU ∧ A.loU < 17/500 := by
  have cOne : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,sq_nonneg (A.c-1)]
  have sOne : A.s ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.c,sq_nonneg (A.s-1)]
  have oUhi : 0 < A.loU+A.side := by linarith only [marker.2.1,hc,hs]
  have oVlo : A.loV < 0 := by linarith only [east.2.2.1,hs]
  have oVhi : 0 < A.loV+A.side := by linarith only [north.2.2.2,hc]
  have eNonnegative : 0 ≤ A.loU := by
    apply le_of_not_gt
    intro low
    apply missingO
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [low,oUhi,oVlo,oVhi]
  have sp : 0 < A.s := by linarith only [north.1,eNonnegative]
  have small : A.loU < 17/500 := by
    apply lt_of_not_ge
    intro offset
    have projectionF : (13/50)*A.c+A.s < 517/500 := by
      have identity : ((13/50)*A.c+A.s)^2+(A.c-(13/50)*A.s)^2=
          (2669/2500)*(A.c^2+A.s^2) := by ring
      rw [A.unit_normal] at identity
      nlinarith only [identity,sq_nonneg (A.c-(13/50)*A.s),sq_nonneg ((13/50)*A.c+A.s-517/500)]
    have projectionR : A.c+(13/50)*A.s < 517/500 := by
      have identity : (A.c+(13/50)*A.s)^2+((13/50)*A.c-A.s)^2=
          (2669/2500)*(A.c^2+A.s^2) := by ring
      rw [A.unit_normal] at identity
      nlinarith only [identity,sq_nonneg ((13/50)*A.c-A.s),sq_nonneg (A.c+(13/50)*A.s-517/500)]
    have fLowU : A.loU < (13/50)*A.c+A.s := by linarith only [north.1,hc,hs]
    have fHighU : (13/50)*A.c+A.s < A.loU+A.side := by linarith only [projectionF,offset,side]
    have fLowV : A.loV < A.c-(13/50)*A.s := by linarith only [east.2.2.1,hc]
    have fFace : A.loV+A.side ≤ A.c-(13/50)*A.s := by
      apply le_of_not_gt
      intro high
      apply missingF
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [fLowU,fHighU,fLowV,high]
    have rLowU : A.loU < A.c+(13/50)*A.s := by linarith only [east.1,hc,hs]
    have rHighU : A.c+(13/50)*A.s < A.loU+A.side := by linarith only [projectionR,offset,side]
    have rHighV : -A.s+(13/50)*A.c < A.loV+A.side := by linarith only [north.2.2.2,hs]
    have rFace : -A.s+(13/50)*A.c ≤ A.loV := by
      apply le_of_not_gt
      intro low
      apply segment (13/50) le_rfl (by norm_num)
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [rLowU,rHighU,low,rHighV]
    have wide : 50/37 < A.c+A.s := by linarith only [fFace,rFace,side]
    have comps := components A.c A.s hc.le hs A.unit_normal wide
    have margin := vertex_margin A.c A.s hc hs A.unit_normal wide
    have faceWeight := mul_nonneg hs (sub_nonneg.mpr fFace)
    have offsetWeight := mul_nonneg hc.le (sub_nonneg.mpr offset)
    have strict := mul_pos (sub_pos.mpr side) (show 0 < A.c+A.s by linarith only [hc,hs])
    have right : 1 < A.c*(A.loU+A.side)-A.s*A.loV := by
      nlinarith only [faceWeight,offsetWeight,strict,margin,A.unit_normal]
    have jLowU : A.loU < A.c+(14/25)*A.s := by linarith only [east.1,hc,hs]
    have jHighV : -A.s+(14/25)*A.c < A.loV+A.side := by
      linarith only [north.2.2.2,comps.2,cOne]
    have short := (short_projections A (-(37/50)) (11/25) (by norm_num)).2.2.2
    have jLowV : A.loV < -A.s+(14/25)*A.c := by linarith only [fFace,short,side]
    have jFace : A.loU+A.side ≤ A.c+(14/25)*A.s := by
      apply le_of_not_gt
      intro high
      apply segment (14/25) (by norm_num) (by norm_num)
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [jLowU,high,jLowV,jHighV]
    have noLine : ∀ y : ℝ, ¬ A.Inside 1 y := by
      intro y point
      have lower : 13/50 < y := by
        have product : 0 < A.c*(y-13/50) := by linarith only [point.2.2.1,rFace]
        exact sub_pos.mp (pos_of_mul_pos_right product hc.le)
      have upper : y < 14/25 := by
        have product : 0 < A.s*(14/25-y) := by linarith only [point.2.1,jFace]
        exact sub_pos.mp (pos_of_mul_pos_right product hs)
      exact segment y lower.le (by linarith only [upper]) point
    have below (x y : ℝ) (point : A.Inside x y) : x ≤ 1 := by
      apply le_of_not_gt
      intro above
      let t := 1/x
      have xp : 0 < x := by linarith only [above]
      have positive : 0 < t := div_pos (by norm_num) xp
      have small : t < 1 := (div_lt_one xp).mpr (by linarith only [above])
      have relation : t*x=1 := div_mul_cancel₀ _ xp.ne'
      have point' := inside_segment A 0 (13/50) x y t north point positive.le small.le
      have identity : (1-t)*0+t*x=1 := by linarith only [relation]
      rw [identity] at point'
      exact noLine _ point'
    have limit : 0 ≤ 1-(A.c*(A.loU+A.side)-A.s*A.loV) := by
      apply affine_endpoint_nonnegative A.side (A.c+A.s) _ A.side_pos
      intro t positive small
      let u := A.loU+A.side-t
      let v := A.loV+t
      have point : A.Inside (A.c*u-A.s*v) (A.s*u+A.c*v) := by
        apply (inside_iff_rotated_box A _ _).mpr
        refine ⟨u,v,?_,rfl,rfl⟩
        dsimp [u,v,InBands]
        refine ⟨?_,?_,?_,?_⟩ <;> linarith only [positive,small]
      have bound := below _ _ point
      dsimp [u,v] at bound
      nlinarith only [bound]
    linarith only [right,limit]
  exact ⟨sp,eNonnegative,small⟩

#print axioms bounds
end N12Compact.C981CompletionOppositeOffset
