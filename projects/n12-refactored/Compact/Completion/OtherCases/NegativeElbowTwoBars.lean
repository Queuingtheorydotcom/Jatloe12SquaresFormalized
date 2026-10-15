import Compact.Completion.OtherCases.BottomBarSupport
import Compact.Completion.OtherCases.DerivedWalls

/-! A negative inward elbow cannot avoid the actual bottom and right bars
while omitting its center. Both bottom face alternatives and all weak
bar contacts are retained. -/
namespace N12Compact.Completion.OtherCases.NegativeElbowTwoBars
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

theorem impossible (q : OpenSquare) (t : ℝ) (signed : q.s= -t)
    (side : 1<q.side) (cp : 0<q.c) (tn : 0≤t) (order : t≤q.c)
    (marker : q.Inside (7/20) (-7/20)) (inner : q.Inside 0 (-13/50))
    (elbow : q.Inside (13/50) 0) (missingCenter : ¬q.Inside 0 0)
    (bottom : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬q.Inside x (-1))
    (right : ∀ y : ℝ,-13/50≤y → y≤0 → ¬q.Inside 1 y) : False := by
  have m := marker
  have i := inner
  have d := elbow
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,zero_add,add_zero]
    at m i d
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have bounds := CommonCases.CanonicalScalars.bounds q.c t cp tn order unit
  have cu := bounds.2.1
  have uFace : 0≤q.loU := by
    apply le_of_not_gt
    intro low
    apply missingCenter
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,zero_add,add_zero]
    refine ⟨low,?_,?_,?_⟩ <;> linarith only [m.2.1,i.2.2.1,d.2.2.2,cp,tn]
  have tp : 0<t := by linarith only [uFace,i.1]
  have hCap : q.loV+q.side≤t := by
    apply le_of_not_gt
    intro high
    exact right 0 (by norm_num) le_rfl (by
      simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one,mul_zero,add_zero]
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [d.1,i.2.2.1,uFace,side,cu,cp,high])
  have bar := BottomBarSupport.negative q t signed side cp tn order uFace marker elbow bottom
  have fLowU : q.loU<q.c+t*(13/50) := by linarith only [d.1,cp,tn]
  have fLowV : q.loV<t-q.c*(13/50) := by linarith only [i.2.2.1,tp]
  have fHighV : t-q.c*(13/50)<q.loV+q.side := by
    by_contra high
    have cap : q.loV+q.side≤t-q.c*(13/50) := le_of_not_gt high
    rcases bar.2 with face | floor
    · have short := (short_projections q (37/50) (-(1/5)) (by norm_num)).2.1
      rw [signed] at short
      nlinarith only [face,cap,side,short]
    · have first := mul_nonneg tn uFace
      have last := mul_nonneg cp.le (sub_nonneg.mpr cap)
      have extra := mul_pos (sub_pos.mpr side)
        (show 0<q.c+t by linarith only [cp,tn])
      have margin := mul_nonneg cp.le (sub_nonneg.mpr order)
      nlinarith only [floor,first,last,extra,margin,bounds.2.2.2.2,sq_nonneg q.c,cp]
  have aCap : q.loU+q.side≤q.c+t*(13/50) := by
    apply le_of_not_gt
    intro high
    exact right (-13/50) le_rfl (by norm_num) (by
      simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [fLowU,high,fLowV,fHighV])
  have line : ∀ y : ℝ,¬q.Inside 1 y := by
    intro y own
    have point := own
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one] at point
    have low : -13/50<y := by
      apply (mul_lt_mul_left tp).mp
      nlinarith only [point.2.1,aCap]
    have high : y<0 := by
      apply (mul_lt_mul_left cp).mp
      linarith only [point.2.2.2,hCap]
    exact right y low.le high.le own
  have reflectedMarker : (pullX q).Inside (73/20) (-7/20) := by
    norm_num [inside_pullX]
    exact marker
  have reflectedLine : ∀ y : ℝ,¬(pullX q).Inside 3 y := by
    intro y own
    apply line y
    simpa only [inside_pullX,show (4:ℝ)-3=1 by norm_num] using own
  have reflectedWall := DerivedWalls.vertical_right (pullX q) (73/20) (-7/20) 3
    reflectedMarker (by norm_num) reflectedLine
  have wall : ∀ x y,q.Inside x y → x≤1 := by
    intro x y own
    have reflected : (pullX q).Inside (4-x) y := by
      rw [inside_pullX]
      convert own using 1 <;> ring
    have inequality := reflectedWall (4-x) y reflected
    linarith only [inequality]
  have closed := WallProfile.vertex q (q.loU+q.side) (q.loV+q.side)
    ⟨by linarith only [q.side_pos],le_rfl⟩
    ⟨by linarith only [q.side_pos],le_rfl⟩
  have closedWall := DerivedWalls.closed_affine_bound q (-1) 0 (-1) (7/20) (-7/20)
    (by
      intro x y own
      have bound := wall x y own
      linarith only [bound])
    marker _ _ closed
  rw [signed] at closedWall
  have upperRight : q.c*(q.loU+q.side)+t*(q.loV+q.side)≤1 := by
    nlinarith only [closedWall]
  rcases bar.2 with face | floor
  · have coefficient : 0<(4/5)*(1+q.c)-(1-t) := by linarith only [bounds.1,tn]
    have positive := mul_pos (sq_pos_of_pos tp) coefficient
    have identity : (1+q.c)*(q.c+t-1-q.c*t+(4/5)*t^2) =
        t^2*((4/5)*(1+q.c)-(1-t)) := by
      linear_combination (1-t)*unit
    have scaled : 0<(1+q.c)*(q.c+t-1-q.c*t+(4/5)*t^2) := by
      rwa [identity]
    have margin := (mul_pos_iff_of_pos_left
      (show 0<1+q.c by linarith only [cp])).mp scaled
    have first := mul_nonneg cp.le uFace
    have last := mul_nonneg tn (sub_nonneg.mpr face)
    have extra := mul_pos (sub_pos.mpr side)
      (show 0<q.c+t by linarith only [cp,tn])
    nlinarith only [upperRight,first,last,extra,margin]
  · have first := mul_nonneg cp.le (sub_nonneg.mpr upperRight)
    have last := mul_nonneg tn (show 0≤ -t*(q.loU+q.side)+q.c*q.loV+1 by
      linarith only [floor])
    have identity :
        q.c*(1-(q.c*(q.loU+q.side)+t*(q.loV+q.side)))+
          t*(-t*(q.loU+q.side)+q.c*q.loV+1) =
        q.c+t-q.side*q.c*t-(q.loU+q.side) := by
      linear_combination -(q.loU+q.side)*unit
    have elimination : q.loU+q.side≤q.c+t-q.side*q.c*t := by
      linarith only [first,last,identity]
    have defect := mul_nonneg (sub_nonneg.mpr cu)
      (show 0≤1-t by linarith only [order,cu])
    have extra := mul_pos (sub_pos.mpr side)
      (show 0<1+q.c*t by
        have product := mul_nonneg cp.le tn
        linarith only [product])
    nlinarith only [elimination,uFace,defect,extra]

#print axioms impossible
end N12Compact.Completion.OtherCases.NegativeElbowTwoBars

