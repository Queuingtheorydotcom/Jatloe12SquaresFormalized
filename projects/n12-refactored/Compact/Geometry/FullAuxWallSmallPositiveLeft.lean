import Compact.Geometry.FullAuxWallPositiveLeftAxes
import Compact.Geometry.FourSquareBLBridge

/-! The genuine small positive left-wall frame cannot use its own
longitudinal separator against the steep upper square. The remaining
neighbor-owned U selector is deliberately retained. -/
namespace N12Compact.FullAuxWallSmallPositiveLeft

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

private theorem margin {l r b t : ℝ} (ln : Normal l r) (bn : Normal b t)
    (small : r≤1/5) (steep : 3/10<t) :
    l^2*((8/5)-b-(3/5)*t^2+(3/5)*b*t)+
      l*r*((2/5)-t+(3/5)*t^2+(3/5)*b*t)+
      (457/500)*r^2-l≤0 := by
  have lb := normal_bounds ln
  have bb := normal_bounds bn
  have lp : 0≤l := le_trans ln.1 ln.2.1
  have bp : 0≤b := le_trans bn.1 bn.2.1
  have first := mul_nonneg bp (sub_nonneg.mpr bb.2.2.2.2.2)
  have second := mul_nonneg bn.1 (sub_nonneg.mpr bb.2.2.2.2.2)
  have f : (8/5)-b-(3/5)*t^2+(3/5)*b*t≤9/10 := by
    nlinarith only [first,bb.1,bn.2.2]
  have g : (2/5)-t+(3/5)*t^2+(3/5)*b*t≤9/25 := by
    nlinarith only [second,steep]
  have wf := mul_nonneg (sq_nonneg l) (sub_nonneg.mpr f)
  have wg := mul_nonneg (mul_nonneg lp ln.1) (sub_nonneg.mpr g)
  have defectProduct := mul_nonneg (sub_nonneg.mpr lb.2.1)
    (show 0≤3*l-2 by linarith only [lb.1])
  have defect : 1-l≤(3/5)*r^2 := by
    nlinarith only [defectProduct,ln.2.2]
  have square := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤1/5+r by linarith only [ln.1])
  have mixed := mul_nonneg ln.1 (sub_nonneg.mpr lb.2.1)
  nlinarith only [wf,wg,defect,square,mixed,small,ln.2.2]

theorem no_left_u (L B : OpenSquare)
    (ln : Normal L.c L.s) (bn : Normal B.c B.s)
    (same : L.side=B.side) (side : 1<B.side)
    (small : L.s≤1/5) (steep : 3/10<B.s)
    (box : InsideContainer L) (marker : L.Inside (457/500) 2)
    (high : B.Inside 1 (12/5))
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (axis : L.loU+L.side≤lower B L.c L.s) : False := by
  have lb := normal_bounds ln
  have bb := normal_bounds bn
  have lc : 0<L.c := by linarith only [lb.1]
  have bc : 0<B.c := by linarith only [bb.1]
  have order : L.s<B.s := by linarith only [small,steep]
  have cosine := cosine_order bn ln order.le
  let alpha := L.c*B.c+L.s*B.s
  let h := L.c*B.s-L.s*B.c
  have ap : 0<alpha := by
    exact add_pos_of_pos_of_nonneg (mul_pos lc bc) (mul_nonneg ln.1 bn.1)
  have hp : 0<h := by
    have first := mul_pos lc (sub_pos.mpr order)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr cosine)
    dsimp [h]; nlinarith only [first,second]
  have support : lower B L.c L.s=alpha*B.loU-h*(B.loV+B.side) := by
    dsimp [lower,supportRadius,centerX,centerY]
    rw [abs_of_nonneg ap.le,abs_of_nonpos (show -L.c*B.s+L.s*B.c≤0 by
      dsimp [h] at hp; linarith only [hp])]
    dsimp [alpha,h]
    ring
  have wall := FourSquareBLBridge.left_wall L lc.le box
  rw [abs_of_nonneg ln.1] at wall
  dsimp [centerX] at wall
  have wallFace : 0≤L.c*L.loU-L.s*(L.loV+L.side) := by linarith only [wall]
  have markerWeight := mul_nonneg ln.1
    (sub_nonneg.mpr marker.2.2.2.le)
  have wallLower : L.c*L.side+2*L.c*L.s-(457/500)*L.s^2≤
      L.c*(L.loU+L.side) := by
    nlinarith only [wallFace,markerWeight]
  have first := mul_nonneg ap.le (sub_nonneg.mpr upperU)
  have second := mul_pos hp (sub_pos.mpr high.2.2.2)
  have axisWeight := mul_nonneg lc.le (sub_nonneg.mpr axis)
  rw [support] at axisWeight
  have firstWeight := mul_nonneg lc.le first
  have secondWeight := mul_pos lc second
  have sideWeight := mul_pos (mul_pos lc (show 0<1+alpha by linarith only [ap]))
    (sub_pos.mpr side)
  have identity :
      L.c*(alpha*((8/5)*B.c+3*B.s)-h*((12/5)*B.c-B.s))-
        L.c*(1+alpha)-2*L.c*L.s+(457/500)*L.s^2=
      L.c^2*((8/5)-B.c-(3/5)*B.s^2+(3/5)*B.c*B.s)+
        L.c*L.s*((2/5)-B.s+(3/5)*B.s^2+(3/5)*B.c*B.s)+
        (457/500)*L.s^2-L.c := by
    dsimp [alpha,h]
    linear_combination (L.c*((8/5)*L.c+(12/5)*L.s))*B.unit_normal
  have bound := margin ln bn small steep
  rw [same] at wallLower axisWeight
  nlinarith only [wallLower,axisWeight,firstWeight,secondWeight,sideWeight,identity,bound]

#print axioms no_left_u
end N12Compact.FullAuxWallSmallPositiveLeft
