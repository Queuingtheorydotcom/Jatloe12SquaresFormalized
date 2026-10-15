import Compact.Geometry.FullAuxWallSmallPositiveLeft

/-! The neighbor-owned longitudinal separator is also impossible for
a small positive left-wall frame, once the genuine C/B cycle bounds the
upper frame's sine. No additional separating-axis choice is assumed. -/
namespace N12Compact.FullAuxWallSmallPositiveLeftB

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

private def polynomial (t r : ℝ) : ℝ :=
  -(2/5)+t-(3/10)*t^2-(3/40)*t^4+
    (63/125)*r^2*(1-t^2/2)-(73/1000)*r*t

private theorem polynomial_nonpos {t r : ℝ}
    (tp : 0≤t) (tcap : t≤23/50) (rp : 0≤r) (rcap : r≤4/25) :
    polynomial t r≤0 := by
  have tSquare := mul_nonneg (sub_nonneg.mpr tcap)
    (show 0≤23/50+t by linarith only [tp])
  have rSquare := mul_nonneg (sub_nonneg.mpr rcap)
    (show 0≤4/25+r by linarith only [rp])
  have q0 : 0≤(23/50 : ℝ)+t := by linarith only [tp]
  have q1 : (23/50 : ℝ)+t≤1 := by linarith only [tcap]
  have z0 : 0≤(23/50 : ℝ)^2+t^2 := by positivity
  have z1 : (23/50 : ℝ)^2+t^2≤1 := by nlinarith only [tSquare]
  have mixed := mul_nonneg (sub_nonneg.mpr q1) z0
  have fourth : ((23/50 : ℝ)+t)*((23/50 : ℝ)^2+t^2)≤1 := by
    nlinarith only [mixed,z1]
  have coefficient : 0≤(3/10 : ℝ)+(63/250)*r^2 := by positivity
  have coefficientCap : (3/10 : ℝ)+(63/250)*r^2≤69/125 := by
    nlinarith only [rSquare]
  have coefficientWeight := mul_nonneg coefficient (sub_nonneg.mpr q1)
  have bracket : 0≤1-(73/1000)*r-
      ((3/10)+(63/250)*r^2)*((23/50)+t)-
      (3/40)*((23/50)+t)*((23/50)^2+t^2) := by
    nlinarith only [fourth,coefficientWeight,coefficientCap,rcap]
  have weighted := mul_nonneg (sub_nonneg.mpr tcap) bracket
  have difference : polynomial (23/50) r-polynomial t r=
      ((23/50)-t)*(1-(73/1000)*r-
        ((3/10)+(63/250)*r^2)*((23/50)+t)-
        (3/40)*((23/50)+t)*((23/50)^2+t^2)) := by
    unfold polynomial; ring
  have first : polynomial (23/50) 0≤0 := by norm_num [polynomial]
  have last : polynomial (23/50) (4/25)≤0 := by norm_num [polynomial]
  have firstWeight := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr rcap) first
  have lastWeight := mul_nonpos_of_nonneg_of_nonpos rp last
  have convex := mul_nonneg rp (sub_nonneg.mpr rcap)
  have interpolation :
      ((4/25)-r)*polynomial (23/50) 0+r*polynomial (23/50) (4/25)-
        (4/25)*polynomial (23/50) r=
      (4/25)*(63/125)*(1-(23/50 : ℝ)^2/2)*r*((4/25)-r) := by
    unfold polynomial; ring
  nlinarith only [weighted,difference,firstWeight,lastWeight,convex,interpolation]

private theorem margin {l r b t : ℝ} (ln : Normal l r) (bn : Normal b t)
    (small : r≤4/25) (cap : t≤23/50) :
    l*((8/5-l)*b+(1-r)*t-1)+(457/500)*r*t≤0 := by
  have lb := normal_bounds ln
  have bb := normal_bounds bn
  have lp : 0≤l := le_trans ln.1 ln.2.1
  have bp : 0≤b := le_trans bn.1 bn.2.1
  have square := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤4/25+r by linarith only [ln.1])
  have cosine : 493/500≤l := by
    apply le_of_not_gt
    intro no
    have comparison := mul_nonneg (sub_nonneg.mpr no.le)
      (show 0≤493/500+l by linarith only [lb.1])
    nlinarith only [comparison,square,ln.2.2]
  have defectProduct := mul_nonneg (sub_nonneg.mpr lb.2.1)
    (show 0≤(63/125)*l-62/125 by linarith only [cosine])
  have defect : 1-l≤(63/125)*r^2 := by
    nlinarith only [defectProduct,ln.2.2]
  have marker : (457/500 : ℝ)≤(927/1000)*l := by linarith only [cosine]
  have quarticProduct := mul_nonneg (sq_nonneg (1-b))
    (mul_nonneg (sub_nonneg.mpr bb.2.1)
      (show 0≤3+b by linarith only [bb.1]))
  have quarticIdentity : 8*(1-b)-4*t^2-t^4=(1-b)^3*(3+b) := by
    linear_combination (b^2-t^2-5)*bn.2.2
  have quartic : b≤1-t^2/2-t^4/8 := by
    nlinarith only [quarticProduct,quarticIdentity]
  have quadratic : b≤1-t^2/2 := by
    nlinarith only [bn.2.2,sq_nonneg (b-1)]
  have ld := mul_nonneg bp (sub_nonneg.mpr defect)
  have bd := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr quadratic)
  have mark := mul_nonneg (mul_nonneg ln.1 bn.1) (sub_nonneg.mpr marker)
  have intermediate :
      (3/5)*b+t-1+b*(1-l)-(73/1000)*r*t≤polynomial t r := by
    unfold polynomial
    nlinarith only [ld,bd,quartic]
  have weight := mul_nonneg lp (sub_nonneg.mpr intermediate)
  have last := mul_nonpos_of_nonneg_of_nonpos lp
    (polynomial_nonpos bn.1 cap ln.1 small)
  nlinarith only [weight,last,mark]

theorem no_neighbor_u (L B : OpenSquare)
    (ln : Normal L.c L.s) (bn : Normal B.c B.s)
    (same : L.side=B.side) (side : 1<B.side)
    (small : L.s≤4/25) (steep : 3/10<B.s) (cap : B.s≤23/50)
    (box : InsideContainer L) (marker : L.Inside (457/500) 2)
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (axis : upper L B.c B.s≤B.loU) : False := by
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
  have support : upper L B.c B.s=alpha*(L.loU+L.side)+h*(L.loV+L.side) := by
    dsimp [upper,supportRadius,centerX,centerY]
    rw [abs_of_nonneg (show 0≤B.c*L.c+B.s*L.s by
      dsimp [alpha] at ap; nlinarith only [ap]),
      abs_of_nonneg (show 0≤-B.c*L.s+B.s*L.c by
        dsimp [h] at hp; nlinarith only [hp])]
    dsimp [alpha,h]; ring
  have wall := FourSquareBLBridge.left_wall L lc.le box
  rw [abs_of_nonneg ln.1] at wall
  dsimp [centerX] at wall
  have wallFace : 0≤L.c*L.loU-L.s*(L.loV+L.side) := by linarith only [wall]
  have wallWeight := mul_nonneg ap.le wallFace
  have markerWeight := mul_nonneg bn.1 (sub_nonneg.mpr marker.2.2.2.le)
  have lower : L.c*alpha*L.side+2*L.c*B.s-(457/500)*L.s*B.s≤
      L.c*upper L B.c B.s := by
    have identity :
        L.c*upper L B.c B.s-L.c*alpha*L.side-B.s*(L.loV+L.side)=
        alpha*(L.c*L.loU-L.s*(L.loV+L.side)) := by
      rw [support]
      dsimp [alpha,h]
      linear_combination (B.s*(L.loV+L.side))*L.unit_normal
    nlinarith only [wallWeight,markerWeight,identity]
  have axisWeight := mul_nonneg lc.le (sub_nonneg.mpr axis)
  have upperWeight := mul_nonneg lc.le (sub_nonneg.mpr upperU)
  have sideWeight := mul_pos (mul_pos lc (show 0<1+alpha by linarith only [ap]))
    (sub_pos.mpr side)
  have bound := margin ln bn small cap
  rw [same] at lower
  dsimp [alpha] at lower sideWeight
  nlinarith only [lower,axisWeight,upperWeight,sideWeight,bound]

/-- Every positive left-wall frame in the genuine residual lies above
sine 4/25; both longitudinal alternatives are discharged below that value. -/
theorem sine (L B : OpenSquare)
    (ln : Normal L.c L.s) (bn : Normal B.c B.s)
    (same : L.side=B.side) (side : 1<B.side)
    (steep : 3/10<B.s) (cap : B.s≤23/50)
    (box : InsideContainer L) (marker : L.Inside (457/500) 2)
    (low : L.Inside 1 (8/5)) (high : B.Inside 1 (12/5))
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (upperV : B.loV+B.side≤3*B.c-B.s)
    (lowerU : (457/500)*B.c+2*B.s≤B.loU)
    (width : 1<(343/500)*B.c+B.s)
    (apart : ∀ x y, ¬(L.Inside x y ∧ B.Inside x y)) : 4/25<L.s := by
  apply lt_of_not_ge
  intro small
  have axes := FullAuxWallPositiveLeftAxes.alternatives L B ln bn same side
    upperU upperV lowerU width marker low high apart
  rcases axes with own | neighbor
  · exact FullAuxWallSmallPositiveLeft.no_left_u L B ln bn same side
      (by linarith only [small]) steep box marker high upperU own
  · exact no_neighbor_u L B ln bn same side small steep cap box marker upperU neighbor

#print axioms no_neighbor_u
#print axioms sine
end N12Compact.FullAuxWallSmallPositiveLeftB
