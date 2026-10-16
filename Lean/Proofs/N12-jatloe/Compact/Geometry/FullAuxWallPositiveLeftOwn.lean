import Compact.Geometry.FullAuxWallSmallPositiveLeftB

/-! Exact support inequalities for the remaining left-owned longitudinal
separator. The two relative-angle signs retain the original central square's
lower point or lower face, respectively; no point-only replacement is used. -/
namespace N12Compact.FullAuxWallPositiveLeftOwn
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds FullAuxWallTopEndpoint
set_option Elab.async false

private theorem wall_support (L : OpenSquare) (ln : Normal L.c L.s)
    (box : InsideContainer L) (marker : L.Inside (457/500) 2) :
    L.side*L.c+2*L.c*L.s-(457/500)*L.s^2≤L.c*(L.loU+L.side) := by
  have bounds := normal_bounds ln
  have wall := FourSquareBLBridge.left_wall L (by linarith only [bounds.1]) box
  rw [abs_of_nonneg ln.1] at wall
  dsimp [centerX] at wall
  have face : 0≤L.c*L.loU-L.s*(L.loV+L.side) := by
    nlinarith only [wall]
  have mark := mul_nonneg ln.1 (sub_nonneg.mpr marker.2.2.2.le)
  nlinarith only [face,mark]

/-- The upper relative-angle sector uses C's genuine low point. -/
theorem above (L D : OpenSquare) (ln : Normal L.c L.s) (dn : Normal D.c D.s)
    (side : 1<D.side) (same : L.side=D.side)
    (box : InsideContainer L) (marker : L.Inside (457/500) 2)
    (bottom : D.Inside 2 (3/2))
    (order : 0≤L.s*D.c-L.c*D.s)
    (axis : L.loU+L.side≤lower D L.c L.s) :
    0<2-(543/500)*L.s^2-L.c*(1+(L.c*D.c+L.s*D.s))-
      (1/2)*L.c*D.c*(L.s*D.c-L.c*D.s)+
      L.c*(L.c*D.c+L.s*D.s)*(D.loU+D.side-2*(D.c+D.s)) := by
  have lb := normal_bounds ln
  have db := normal_bounds dn
  have lp : 0<L.c := by linarith only [lb.1]
  have cp : 0<D.c := by linarith only [db.1]
  let alpha := L.c*D.c+L.s*D.s
  let H := L.s*D.c-L.c*D.s
  let u := D.loU+D.side-2*(D.c+D.s)
  have ap : 0<alpha := by
    exact add_pos_of_pos_of_nonneg (mul_pos lp cp) (mul_nonneg ln.1 dn.1)
  have hp : 0≤H := order
  have form : lower D L.c L.s=alpha*D.loU+H*D.loV := by
    rw [lower_pp D L.c L.s
      (by dsimp [alpha] at ap; nlinarith only [ap])
      (by dsimp [H] at hp; nlinarith only [hp])]
    dsimp [alpha,H]; ring
  have wall := wall_support L ln box marker
  have axisWeight := mul_nonneg lp.le (sub_nonneg.mpr axis)
  have lowWeight := mul_nonneg (mul_nonneg lp.le hp)
    (sub_nonneg.mpr bottom.2.2.1.le)
  have strict := mul_pos (sub_pos.mpr side)
    (mul_pos lp (show 0<1+alpha by linarith only [ap]))
  have identity :
      (2-(543/500)*L.s^2-L.c*(1+alpha)-
        (1/2)*L.c*D.c*H+L.c*alpha*u)-
        (D.side-1)*L.c*(1+alpha)=
      L.c*(alpha*D.loU+H*((3/2)*D.c-2*D.s))-
        (D.side*L.c+2*L.c*L.s-(457/500)*L.s^2) := by
    dsimp [alpha,H,u]
    linear_combination -2*ln.2.2-(2*L.c^2+2*L.c*L.s)*dn.2.2
  rw [same] at wall axisWeight
  rw [form] at axisWeight
  dsimp [alpha,H,u] at identity strict lowWeight axisWeight ⊢
  nlinarith only [wall,axisWeight,lowWeight,strict,identity]

/-- The lower relative-angle sector uses C's genuine lower V face. -/
theorem below (L D : OpenSquare) (ln : Normal L.c L.s) (dn : Normal D.c D.s)
    (side : 1<D.side) (same : L.side=D.side)
    (box : InsideContainer L) (marker : L.Inside (457/500) 2)
    (bottom : D.c-(8/5)*D.s≤D.loV)
    (order : L.s*D.c-L.c*D.s≤0)
    (axis : L.loU+L.side≤lower D L.c L.s) :
    0<2-(543/500)*L.s^2-L.c*(1+(L.c*D.c+L.s*D.s))+
      L.c*(L.s*D.c-L.c*D.s)*(1-D.c+(2/5)*D.s)+
      L.c*(L.c*D.c+L.s*D.s)*(D.loU+D.side-2*(D.c+D.s)) := by
  have lb := normal_bounds ln
  have db := normal_bounds dn
  have lp : 0<L.c := by linarith only [lb.1]
  have cp : 0<D.c := by linarith only [db.1]
  let alpha := L.c*D.c+L.s*D.s
  let H := L.s*D.c-L.c*D.s
  let u := D.loU+D.side-2*(D.c+D.s)
  have ap : 0<alpha := by
    exact add_pos_of_pos_of_nonneg (mul_pos lp cp) (mul_nonneg ln.1 dn.1)
  have hn : H≤0 := order
  have form : lower D L.c L.s=alpha*D.loU+H*(D.loV+D.side) := by
    dsimp [lower,supportRadius,centerX,centerY]
    rw [abs_of_nonneg (show 0≤L.c*D.c+L.s*D.s by
      dsimp [alpha] at ap; nlinarith only [ap]),
      abs_of_nonpos (show -L.c*D.s+L.s*D.c≤0 by
        dsimp [H] at hn; nlinarith only [hn])]
    dsimp [alpha,H]; ring
  have wall := wall_support L ln box marker
  have axisWeight := mul_nonneg lp.le (sub_nonneg.mpr axis)
  have lowWeight := mul_nonneg
    (mul_nonneg lp.le (show 0≤-H by linarith only [hn]))
    (sub_nonneg.mpr bottom)
  have strict := mul_pos (sub_pos.mpr side)
    (mul_pos lp (show 0<1+alpha-H by linarith only [ap,hn]))
  have identity :
      (2-(543/500)*L.s^2-L.c*(1+alpha)+
        L.c*H*(1-D.c+(2/5)*D.s)+L.c*alpha*u)-
        (D.side-1)*L.c*(1+alpha-H)=
      L.c*(alpha*D.loU+H*(D.side+D.c-(8/5)*D.s))-
        (D.side*L.c+2*L.c*L.s-(457/500)*L.s^2) := by
    dsimp [alpha,H,u]
    linear_combination -2*ln.2.2-(2*L.c^2+2*L.c*L.s)*dn.2.2
  rw [same] at wall axisWeight
  rw [form] at axisWeight
  dsimp [alpha,H,u] at identity strict lowWeight axisWeight ⊢
  nlinarith only [wall,axisWeight,lowWeight,strict,identity]

#print axioms above
#print axioms below
end N12Compact.FullAuxWallPositiveLeftOwn
