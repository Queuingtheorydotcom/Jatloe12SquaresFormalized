import Compact.Completion.C1092.MMMP.TwoFifthsEntranceNortheast
import Compact.Completion.OtherCases.WallProfile.VertexGeometry
import Compact.Geometry.ClosedPointExclusion

/-! The actual bottom-bar floor in both right-near alternatives.
This is the closure-vertex argument of SOUTHEAST-FLOOR-RIGHT-SIGN §2
and PARTIAL-RIGHT-SOUTHEAST-FLOOR §§2--4. A rational upper bound for
the same vertex replaces the displayed derivative. The final angle
comparison uses the rational circle point (24/25,7/25), below the
paper's endpoint; the full canonical interval is retained. -/
namespace N12Compact.C1092MMMPTwoFifthsEntrance
open S12 S12Pilot FourSquareAnchors
open Completion.OtherCases
set_option Elab.async false

theorem southeast_caps (E : OpenSquare) (side : 1<E.side)
    (cp : 0<E.c) (sp : 0<E.s) (order : E.s≤E.c)
    (marker : E.Inside (7/20) (-7/20))
    (inner : E.Inside 0 (-13/50)) (forward : E.Inside (13/50) 0)
    (origin : ¬E.Inside 0 0) (near : ¬E.Inside 1 (-13/50)) :
    E.loV+E.side≤0 ∧ E.loU+E.side≤E.c-(13/50)*E.s := by
  have upperV : E.loV+E.side≤0 := by
    apply le_of_not_gt
    intro high
    apply origin
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [inner.1,forward.2.1,marker.2.2.1,high,cp,sp]
  have short := CommonCases.OutwardScalars.increasing_projection
    E.c E.s (13/50) 1 cp sp.le order E.unit_normal
    (by norm_num) (by norm_num) (by norm_num)
  have upperU : E.loU+E.side≤E.c-(13/50)*E.s := by
    apply le_of_not_gt
    intro high
    apply near
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [forward.1,forward.2.2.2,upperV,side,short,high,cp,sp,order]
  exact ⟨upperV,upperU⟩

theorem southeast_outer_cap (E : OpenSquare)
    (cp : 0<E.c) (sp : 0<E.s) (order : E.s≤E.c)
    (inner : E.Inside 0 (-13/50)) (forward : E.Inside (13/50) 0)
    (outer : E.Inside 1 (-2/5)) (sharp : ¬E.Inside (47/100) (3/25)) :
    E.loV+E.side≤(3/25)*E.c-(47/100)*E.s ∧ E.s<1/2 := by
  have cap : E.loV+E.side≤(3/25)*E.c-(47/100)*E.s := by
    apply le_of_not_gt
    intro high
    apply sharp
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [inner.1,outer.2.1,outer.2.2.1,high,cp,sp,order]
  have ratio : 7*E.s<4*E.c := by linarith only [cap,forward.2.2.2]
  have squared := mul_pos (show 0<4*E.c-7*E.s by linarith only [ratio])
    (show 0<4*E.c+7*E.s by linarith only [cp,sp])
  have small : E.s<1/2 := by
    apply lt_of_not_ge
    intro bad
    have gap := mul_nonneg (show 0≤E.s-1/2 by linarith only [bad])
      (show 0≤E.s+1/2 by linarith only [sp])
    nlinarith only [squared,gap,E.unit_normal]
  exact ⟨cap,small⟩

/-- A closed bottom vertex cannot touch the strict interior of the
foreign bar owner. This keeps the equality case in the paper's floor. -/
private theorem vertex_above_bar (E B : OpenSquare) (X Y : ℝ)
    (closed : ClosedInside E X Y) (marker : E.Inside (7/20) (-7/20))
    (xl : 0≤X) (xu : X≤2/5)
    (bar : ∀ x : ℝ,0≤x → x≤2/5 → B.Inside x (-1))
    (apart : ∀ x y,¬(E.Inside x y ∧ B.Inside x y)) : -1<Y := by
  apply lt_of_not_ge
  intro below
  by_cases equal : Y= -1
  · have foreign : ClosedInside E X (-1) := by simpa only [equal] using closed
    exact ClosedPointExclusion.outside_of_closed B E X (-1)
      (fun x y own => apart x y ⟨own.2,own.1⟩) foreign (bar X xl xu)
  · have strict : Y< -1 := lt_of_le_of_ne below equal
    let t := (-1-Y)/(-7/20-Y)
    have den : 0< -7/20-Y := by linarith only [strict]
    have positive : 0<t := div_pos (by linarith only [strict]) den
    have small : t<1 := (div_lt_one den).mpr (by norm_num)
    have relation : t*(-7/20-Y)= -1-Y := div_mul_cancel₀ _ den.ne'
    have coordinate : (1-t)*Y+t*(-7/20)= -1 := by nlinarith only [relation]
    have lower : 0≤(1-t)*X+t*(7/20) := by
      have first := mul_nonneg (show 0≤1-t by linarith only [small]) xl
      nlinarith only [first,positive]
    have upper : (1-t)*X+t*(7/20)≤2/5 := by
      have first := mul_nonneg (show 0≤1-t by linarith only [small])
        (show 0≤2/5-X by linarith only [xu])
      nlinarith only [first,positive]
    have own := WallProfile.strict_closed_segment E X Y (7/20) (-7/20) t
      closed marker positive small
    rw [coordinate] at own
    exact apart _ _ ⟨own,bar _ lower upper⟩

theorem southeast_floor (E B : OpenSquare) (side : 1<E.side)
    (cp : 0<E.c) (sp : 0<E.s) (order : E.s≤E.c) (small : E.s<1/2)
    (marker : E.Inside (7/20) (-7/20))
    (inner : E.Inside 0 (-13/50)) (forward : E.Inside (13/50) 0)
    (upperV : E.loV+E.side≤0)
    (upperU : E.loU+E.side≤E.c-(13/50)*E.s)
    (bar : ∀ x : ℝ,0≤x → x≤2/5 → B.Inside x (-1))
    (apart : ∀ x y,¬(E.Inside x y ∧ B.Inside x y)) :
    E.side*(E.c+E.s)-1<E.s*(E.loU+E.side)+E.c*(E.loV+E.side) := by
  have cu : E.c≤1 := by nlinarith only [E.unit_normal,sq_nonneg E.s,cp]
  have close : 4/5<E.c := by
    have first := mul_pos (show 0<1/2-E.s by linarith only [small])
      (show 0<1/2+E.s by linarith only [sp])
    apply lt_of_not_ge
    intro bad
    have last := mul_nonneg (show 0≤4/5-E.c by linarith only [bad])
      (show 0≤4/5+E.c by linarith only [cp])
    nlinarith only [first,last,E.unit_normal]
  have lowerU : -E.s≤E.loU := by
    apply le_of_not_gt
    intro low
    apply apart 0 (-1)
    refine ⟨?_,bar 0 le_rfl (by norm_num)⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,inner.2.1,inner.2.2.2,upperV,side,cu,cp,sp]
  let X := E.c*E.loU-E.s*E.loV
  let Y := E.s*E.loU+E.c*E.loV
  have closed : ClosedInside E X Y := WallProfile.vertex E E.loU E.loV
    ⟨le_rfl,by linarith only [E.side_pos]⟩
    ⟨le_rfl,by linarith only [E.side_pos]⟩
  have positiveX : 0<X := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr lowerU)
    have last := mul_nonneg sp.le (show 0≤-E.side-E.loV by linarith only [upperV])
    have excess := mul_pos sp (show 0<E.side-E.c by linarith only [side,cu])
    dsimp [X]
    nlinarith only [first,last,excess]
  have first := mul_nonneg cp.le (sub_nonneg.mpr upperU)
  have last := mul_pos sp
    (show 0<E.loV+E.side+(13/50)*E.s by linarith only [forward.2.2.2])
  have excess := mul_pos (sub_pos.mpr side)
    (show 0<E.c-E.s by linarith only [close,small])
  have boundX : X<1-(37/50)*E.s^2-(13/50)*E.c*E.s+E.s-E.c := by
    dsimp [X]
    nlinarith only [first,last,excess,E.unit_normal]
  have chord := mul_nonneg (show 0≤E.c-4/5 by linarith only [close])
    (show 0≤1-E.c by linarith only [cu])
  have deficit : 1-E.c≤(5/9)*E.s^2 := by nlinarith only [chord,E.unit_normal]
  have weight := mul_nonneg (show 0≤1+(13/50)*E.s by linarith only [sp])
    (sub_nonneg.mpr deficit)
  have endpoint := mul_nonneg (sq_nonneg E.s)
    (show 0≤1/2-E.s by linarith only [small])
  have upperX : X<2/5 := by
    nlinarith only [boundX,weight,endpoint,small,sq_nonneg E.s]
  have floor := vertex_above_bar E B X Y closed marker positiveX.le upperX.le bar apart
  dsimp [Y] at floor
  nlinarith only [floor]

/-- The strict outer branch's same-face floor forces its shallow angle.
The rational endpoint has a positive exact margin on the entire later
canonical arc, so no sampled angle or derivative premise is introduced. -/
theorem southeast_outer_small (E : OpenSquare) (side : 1<E.side)
    (cp : 0<E.c) (sp : 0<E.s) (order : E.s≤E.c)
    (upperU : E.loU+E.side≤E.c-(13/50)*E.s)
    (upperV : E.loV+E.side≤(3/25)*E.c-(47/100)*E.s)
    (floor : E.side*(E.c+E.s)-1<
      E.s*(E.loU+E.side)+E.c*(E.loV+E.side)) : 3*E.s<E.c := by
  have first := mul_nonneg sp.le (sub_nonneg.mpr upperU)
  have last := mul_nonneg cp.le (sub_nonneg.mpr upperV)
  have strict := mul_pos (sub_pos.mpr side) (show 0<E.c+E.s by linarith only [cp,sp])
  have negative : E.c+E.s-1-(53/100)*E.c*E.s-(3/25)*E.c^2+(13/50)*E.s^2<0 := by
    nlinarith only [first,last,strict,floor]
  apply lt_of_not_ge
  intro large
  have sine : 7/25≤E.s := by
    apply le_of_not_gt
    intro bad
    have cosine : E.c<21/25 := by linarith only [large,bad]
    have one := mul_pos (show 0<7/25-E.s by linarith only [bad])
      (show 0<7/25+E.s by linarith only [sp])
    have two := mul_pos (show 0<21/25-E.c by linarith only [cosine])
      (show 0<21/25+E.c by linarith only [cp])
    nlinarith only [one,two,E.unit_normal]
  have sineSq := mul_nonneg (show 0≤E.s-7/25 by linarith only [sine])
    (show 0≤E.s+7/25 by linarith only [sp])
  have cosine : E.c≤24/25 := by
    apply le_of_not_gt
    intro bad
    have one := mul_pos (show 0<E.c-24/25 by linarith only [bad])
      (show 0<E.c+24/25 by linarith only [cp])
    nlinarith only [one,sineSq,E.unit_normal]
  have sumLow : 31/25≤E.c+E.s := by
    have product := mul_nonneg (show 0≤E.s-7/25 by linarith only [sine])
      (show 0≤E.c+24/25-E.s-7/25 by linarith only [order])
    have scaled : 0≤(E.c+E.s-31/25)*(E.c+24/25) := by
      nlinarith only [product,E.unit_normal]
    have gap := nonneg_of_mul_nonneg_right scaled
      (show 0<E.c+24/25 by linarith only [cp])
    linarith only [gap]
  have sumHigh : E.c+E.s≤3/2 := by
    nlinarith only [E.unit_normal,sq_nonneg (E.c-E.s),cp,sp]
  have chord := mul_nonneg (show 0≤E.c+E.s-31/25 by linarith only [sumLow])
    (show 0≤1-(53/200)*(E.c+E.s+31/25) by linarith only [sumHigh])
  have identity :
      E.c+E.s-1-(53/100)*E.c*E.s-(3/25)*E.c^2+(13/50)*E.s^2 =
      916/125000+(E.c+E.s-31/25)*(1-(53/200)*(E.c+E.s+31/25))+
        (19/50)*(E.s^2-(7/25)^2) := by
    linear_combination (29/200)*E.unit_normal
  nlinarith only [negative,chord,sineSq,identity]

#print axioms southeast_floor
#print axioms southeast_outer_small
end N12Compact.C1092MMMPTwoFifthsEntrance
