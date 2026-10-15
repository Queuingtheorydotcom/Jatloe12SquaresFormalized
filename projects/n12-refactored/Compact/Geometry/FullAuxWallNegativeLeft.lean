import Compact.Geometry.FullAuxWallLeftResidual
import Compact.Geometry.FullAuxWallSmallOffset
import Compact.Geometry.FourSquareBLBridge
import Compact.Geometry.FullAuxWallSharpClearance
import Compact.Geometry.FullAuxWallPositiveUpperAngleSupport

/-! Full-square support at the genuine left container wall in the
positive-opposite/positive-upper sector. This module retains the actual
negative canonical frame of L. -/
namespace N12Compact.FullAuxWallNegativeLeft
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C977CornerSectorBounds FullAuxWallTopEndpoint
set_option Elab.async false

private theorem half_arc {l r : ℝ} (ln : Normal l r) : r/2≤l+r-1 := by
  have lb := normal_bounds ln
  have lp : 0<l := by linarith only [lb.1]
  have product := mul_nonneg ln.1
    (show 0≤1+l-2*r by linarith only [ln.2.1,lb.2.2.2.1])
  have identity : (1+l)*(2*l+r-2)=r*(1+l-2*r) := by
    linear_combination 2*ln.2.2
  have scaled : 0≤(1+l)*(2*l+r-2) := by linarith only [product,identity]
  have result := nonneg_of_mul_nonneg_right scaled (show 0<1+l by linarith only [lp])
  linarith only [result]

/-- The support lower bound keeps the whole original left square. -/
theorem upper_support (L : OpenSquare) (r X Y : ℝ)
    (ls : L.s=-r) (ln : Normal L.c r) (xn : Normal X Y) (yp : 0<Y)
    (box : InsideContainer L) (marker : L.Inside (457/500) 2) :
    2*Y*L.c+(457/500)*Y*r+L.side*(L.c*X-r*Y)*(L.c+r)<
      L.c*upper L X Y := by
  have lb := normal_bounds ln
  have xb := normal_bounds xn
  have lp : 0<L.c := by linarith only [lb.1]
  have xp : 0<X := by linarith only [xb.1]
  let d := L.c*X-r*Y
  let h := r*X+L.c*Y
  have dp : 0≤d := by
    have first := mul_nonneg xp.le (sub_nonneg.mpr ln.2.1)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr xn.2.1)
    dsimp [d]
    nlinarith only [first,second]
  have hp : 0≤h := by
    exact add_nonneg (mul_nonneg ln.1 xp.le) (mul_nonneg lp.le yp.le)
  have form : upper L X Y=d*(L.loU+L.side)+h*(L.loV+L.side) := by
    have hu : 0≤X*L.c+Y*L.s := by rw [ls]; dsimp [d] at dp; nlinarith only [dp]
    have hv : 0≤-X*L.s+Y*L.c := by rw [ls]; dsimp [h] at hp; nlinarith only [hp]
    dsimp [upper,supportRadius,centerX,centerY]
    rw [abs_of_nonneg hu,abs_of_nonneg hv,ls]
    dsimp [d,h]
    ring
  have wall0 := FourSquareBLBridge.left_wall L lp.le box
  rw [ls,abs_neg,abs_of_nonneg ln.1] at wall0
  dsimp [centerX] at wall0
  rw [ls] at wall0
  have wall : 0≤L.c*L.loU+r*L.loV := by nlinarith only [wall0]
  have weighted := mul_nonneg dp wall
  have mark := marker.2.2.2
  rw [ls] at mark
  have point := mul_pos yp (sub_pos.mpr mark)
  have identity : L.c*upper L X Y=
      d*(L.c*L.loU+r*L.loV)+Y*(L.loV+L.side)+L.side*d*(L.c+r) := by
    rw [form]
    dsimp [d,h]
    linear_combination (Y*(L.loV+L.side))*ln.2.2
  dsimp [d] at identity weighted
  nlinarith only [identity,weighted,point]

/-- C's own longitudinal axis is impossible once the genuine small
offset and the strict lower-angle bound have been established. -/
theorem no_central_u (L D : OpenSquare) (r : ℝ)
    (ls : L.s=-r) (ln : Normal L.c r) (dn : Normal D.c D.s)
    (side : 1<L.side) (same : L.side=D.side) (box : InsideContainer L)
    (marker : L.Inside (457/500) 2)
    (slope : 25*D.s≤9*D.c) (positive : 1/20<D.s)
    (offset : D.loU+D.side-2*(D.c+D.s)≤1/1000)
    (axis : upper L D.c D.s≤D.loU) : False := by
  have lb := normal_bounds ln
  have db := normal_bounds dn
  have lp : 0<L.c := by linarith only [lb.1]
  have dc := FullAuxWallSmallOffset.cosine dn slope
  have small : D.s≤9/25 := by linarith only [slope,db.2.1]
  let d := L.c*D.c-r*D.s
  let u := D.loU+D.side-2*(D.c+D.s)
  have first := mul_nonneg (sub_nonneg.mpr ln.2.1) dn.1
  have second := mul_nonneg lp.le
    (show 0≤D.c-D.s-29/50 by linarith only [dc,small])
  have dp : 2/5≤d := by
    dsimp [d]
    nlinarith only [first,second,lb.1]
  have projection := upper_support L r D.c D.s ls ln dn
    (by linarith only [positive]) box marker
  have scaledAxis := mul_le_mul_of_nonneg_left axis lp.le
  have strict := mul_pos (sub_pos.mpr side)
    (show 0<L.c+d*(L.c+r) by
      have product := mul_nonneg (show 0≤d by linarith only [dp])
        (show 0≤L.c+r by linarith only [lp,ln.1])
      linarith only [product,lp])
  have necessary : L.c*(1-D.c-u)+d*(L.c+r-1)-(43/500)*D.s*r<0 := by
    rw [same] at projection strict
    dsimp [u,d] at projection strict ⊢
    nlinarith only [projection,scaledAxis,strict]
  have radial : D.s^2/2≤1-D.c := by
    nlinarith only [dn.2.2,sq_nonneg (1-D.c)]
  have sSquare := mul_pos (sub_pos.mpr positive)
    (show 0<D.s+1/20 by linarith only [positive])
  have gap : 0<1-D.c-u := by
    change u≤1/1000 at offset
    nlinarith only [radial,sSquare,offset]
  have firstTerm := mul_pos lp gap
  have half := half_arc ln
  have main := mul_nonneg (show 0≤d by linarith only [dp]) (sub_nonneg.mpr half)
  have remainder := mul_nonneg ln.1
    (show 0≤d/2-(43/500)*D.s by linarith only [dp,small])
  nlinarith only [necessary,firstTerm,main,remainder]

/-- The other transverse axis is removed by C's full lower corner,
using its strict low point; a point-distance replacement is insufficient. -/
theorem no_left_v (L D : OpenSquare) (r : ℝ)
    (ls : L.s=-r) (ln : Normal L.c r) (dn : Normal D.c D.s)
    (side : 1<D.side) (marker : L.Inside (457/500) 2)
    (bottom : D.Inside 2 (3/2))
    (offset : D.loU+D.side-2*(D.c+D.s)≤1/112)
    (axis : L.loV+L.side≤lower D r L.c) : False := by
  have lb := normal_bounds ln
  have db := normal_bounds dn
  have lp : 0<L.c := by linarith only [lb.1]
  have cp : 0<D.c := by linarith only [db.1]
  let h := r*D.c+L.c*D.s
  let d := L.c*D.c-r*D.s
  let u := D.loU+D.side-2*(D.c+D.s)
  have hp : 0≤h := by exact add_nonneg (mul_nonneg ln.1 cp.le) (mul_nonneg lp.le dn.1)
  have dp : 0≤d := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr ln.2.1)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr dn.2.1)
    dsimp [d]; nlinarith only [first,second]
  have form : lower D r L.c=h*D.loU+d*D.loV := by
    rw [lower_pp D r L.c
      (by dsimp [h] at hp; nlinarith only [hp])
      (by dsimp [d] at dp; nlinarith only [dp])]
    dsimp [h,d]; ring
  have weightedU := mul_nonneg hp (show 0≤2*(D.c+D.s)+1/112-1-D.loU by
    linarith only [offset,side])
  have weightedV := mul_nonneg dp (sub_nonneg.mpr bottom.2.2.1.le)
  let F := 543/500-D.c+(1/2)*D.c*D.s+D.c/112
  let G := -(1/2)-D.s+(1/2)*D.s^2+D.s/112
  have fp : 0≤F := by
    have cross := mul_nonneg cp.le dn.1
    dsimp [F]; nlinarith only [db.2.1,cross,cp]
  have sCap : D.s≤5/7 := by linarith only [dn.2.1,db.2.2.2.2.2]
  have factor : 0≤1-D.s/2-1/112 := by linarith only [sCap]
  have sumProduct := mul_nonneg (show 0≤D.c+D.s-1 by linarith only [db.2.2.2.2.1]) factor
  have sum : F+G<0 := by dsimp [F,G]; nlinarith only [sumProduct,sCap]
  have orderTerm := mul_nonneg (sub_nonneg.mpr ln.2.1) fp
  have sumTerm := mul_neg_of_pos_of_neg lp sum
  have identity : h*(2*(D.c+D.s)+1/112-1)+d*((3/2)*D.c-2*D.s)-
      ((457/500)*r+2*L.c)=r*F+L.c*G := by
    dsimp [h,d,F,G]
    linear_combination (2*r+(3/2)*L.c)*dn.2.2
  have mark := marker.2.2.2
  rw [ls] at mark
  nlinarith only [axis,form,weightedU,weightedV,identity,mark,orderTerm,sumTerm]

#print axioms no_central_u
#print axioms no_left_v

private theorem cosine97 {C S : ℝ} (dn : Normal C S) (small : S≤11/50) :
    97/100≤C := by
  have db := normal_bounds dn
  have first := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤11/50+S by linarith only [dn.1])
  apply le_of_not_gt
  intro wrong
  have second := mul_pos (sub_pos.mpr wrong)
    (show 0<97/100+C by linarith only [db.1])
  nlinarith only [first,second,dn.2.2]

private theorem defect_bound {C S : ℝ} (dn : Normal C S)
    (small : S≤11/50) (positive : 1/20<S) :
    (1-C)*(1-S)-(2/5)*S^2<1/1000 := by
  have db := normal_bounds dn
  have cp := cosine97 dn small
  have narrow : 4*S≤C := by linarith only [small,cp]
  have cu : C<1 := by
    have positiveSquare : 0<S^2 := sq_pos_of_pos (by linarith only [positive])
    nlinarith only [dn.2.2,positiveSquare,db.1]
  apply lt_of_not_ge
  intro wrong
  have impossible := FullAuxWallSharpClearance.excess (e:=1/1000) dn narrow
    (by nlinarith only [wrong,cu])
  norm_num at impossible

/-- The sole surviving C/L longitudinal selector requires L to be
almost horizontal. This bound comes from the full squares and their
common side, not a comparison of owned-point distances. -/
theorem tilt_of_left_u (L D : OpenSquare) (r : ℝ)
    (ls : L.s=-r) (ln : Normal L.c r) (dn : Normal D.c D.s)
    (side : 1<D.side) (same : L.side=D.side)
    (small : D.s≤11/50) (positive : 1/20<D.s)
    (center : D.Inside 2 2) (low : L.Inside 1 (8/5))
    (bottom : D.c-(8/5)*D.s≤D.loV)
    (offset : D.loU+D.side-2*(D.c+D.s)≤1/1000)
    (axis : L.loU+L.side≤lower D L.c (-r)) : r<1/50 := by
  have lb := normal_bounds ln
  have db := normal_bounds dn
  have lp : 0<L.c := by linarith only [lb.1]
  have cp : 0<D.c := by linarith only [db.1]
  let d := L.c*D.c-r*D.s
  let h := r*D.c+L.c*D.s
  let u := D.loU+D.side-2*(D.c+D.s)
  let F := (1-D.c)*(1-D.s)-(2/5)*D.s^2
  let G := 3/5-D.s^2-(2/5)*D.c*D.s+D.s-D.c
  have dp : 0≤d := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr ln.2.1)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr dn.2.1)
    dsimp [d]; nlinarith only [first,second]
  have hp : 0≤h := by exact add_nonneg (mul_nonneg ln.1 cp.le) (mul_nonneg lp.le dn.1)
  have up : 0≤u := by dsimp [u]; linarith only [center.2.1]
  have dotBound := dot_le_one ln dn
  have crossNonnegative := mul_nonneg ln.1 dn.1
  have du : d≤1 := by dsimp [d]; nlinarith only [dotBound,crossNonnegative]
  have form : lower D L.c (-r)=d*D.loU-h*(D.loV+D.side) := by
    have hu : 0≤L.c*D.c+(-r)*D.s := by dsimp [d] at dp; nlinarith only [dp]
    have hv : -L.c*D.s+(-r)*D.c≤0 := by dsimp [h] at hp; nlinarith only [hp]
    dsimp [lower,supportRadius,centerX,centerY]
    rw [abs_of_nonneg hu,abs_of_nonpos hv]
    dsimp [d,h]; ring
  have vWeight := mul_nonneg hp (sub_nonneg.mpr bottom)
  have sideWeight := mul_nonneg (show 0≤D.side-1 by linarith only [side])
    (add_nonneg dp hp)
  have identity :
      d*(2*(D.c+D.s))-h*(D.c-(8/5)*D.s)-(d+h)-(L.c-(8/5)*r)=
        L.c*F+r*G := by
    dsimp [d,h,F,G]
    linear_combination (2*L.c-r)*dn.2.2
  have point := low.2.1
  rw [ls,same] at point
  rw [same] at axis
  have necessary : 0<L.c*F+r*G+d*u := by
    dsimp [u]
    nlinarith only [point,axis,form,vWeight,sideWeight,identity]
  have fCap := defect_bound dn small positive
  have cLower := cosine97 dn small
  have cross := mul_nonneg cp.le dn.1
  have gCap : G≤-(3/20) := by
    dsimp [G]
    nlinarith only [small,cLower,cross,sq_nonneg D.s]
  have first := mul_nonneg lp.le (show 0≤1/1000-F by dsimp [F]; linarith only [fCap])
  have second := mul_nonneg ln.1 (sub_nonneg.mpr gCap)
  have third := mul_nonneg (sub_nonneg.mpr du) up
  change u≤1/1000 at offset
  nlinarith only [necessary,first,second,third,offset,lb.2.1]

/-- Exhaustive actual C/L separation leaves only the selector above. -/
theorem small_tilt (L D : OpenSquare) (r : ℝ)
    (ls : L.s=-r) (ln : Normal L.c r) (dn : Normal D.c D.s)
    (side : 1<D.side) (same : L.side=D.side) (box : InsideContainer L)
    (small : D.s≤11/50) (positive : 1/20<D.s)
    (marker : L.Inside (457/500) 2) (low : L.Inside 1 (8/5))
    (center : D.Inside 2 2) (bottomPoint : D.Inside 2 (3/2))
    (left : D.Inside (6/5) (19/10))
    (bottom : D.c-(8/5)*D.s≤D.loV)
    (offset : D.loU+D.side-2*(D.c+D.s)≤1/1000)
    (apart : ∀ x y, ¬(L.Inside x y ∧ D.Inside x y)) : r<1/50 := by
  have lb := normal_bounds ln
  have db := normal_bounds dn
  have lp : 0<L.c := by linarith only [lb.1]
  have dp : 0<D.c := by linarith only [db.1]
  have cLower := cosine97 dn small
  have slope : 25*D.s≤9*D.c := by linarith only [small,cLower]
  have offset' : D.loU+D.side-2*(D.c+D.s)≤1/112 := by linarith only [offset]
  have noLV (axis : upper L (-L.s) L.c≤lower D (-L.s) L.c ∨
      upper D (-L.s) L.c≤lower L (-L.s) L.c) : False := by
    rcases axis with forward | reverse
    · rw [(ownV L).2,ls,neg_neg] at forward
      exact no_left_v L D r ls ln dn side marker bottomPoint offset' forward
    · have unit : (-L.s)^2+L.c^2=1 := by nlinarith only [L.unit_normal]
      have d := (strict_bounds D _ _ (-L.s) L.c unit center).2
      have l := (strict_bounds L _ _ (-L.s) L.c unit low).1
      rw [ls,neg_neg] at reverse d l
      nlinarith only [reverse,d,l,lp,ln.1]
  have forward (x y : ℝ) (xp : 0<x) (unit : x^2+y^2=1)
      (axis : upper L x y≤lower D x y ∨ upper D x y≤lower L x y) :
      upper L x y≤lower D x y := by
    rcases axis with yes | no
    · exact yes
    · have d := (strict_bounds D _ _ x y unit center).2
      have l := (strict_bounds L _ _ x y unit marker).1
      exact False.elim (by nlinarith only [no,d,l,xp])
  have axes := CongruentSAT.faceSeparation_of_disjoint L D same apart
  change pairRadius L D≤|L.c*(centerX D-centerX L)+L.s*(centerY D-centerY L)| ∨
    pairRadius L D≤|-L.s*(centerX D-centerX L)+L.c*(centerY D-centerY L)| ∨
    pairRadius D L≤|D.c*(centerX D-centerX L)+D.s*(centerY D-centerY L)| ∨
    pairRadius D L≤|-D.s*(centerX D-centerX L)+D.c*(centerY D-centerY L)| at axes
  have separateAxis (x y R : ℝ)
      (identity : supportRadius L x y+supportRadius D x y=R)
      (axis : R≤|x*(centerX D-centerX L)+y*(centerY D-centerY L)|) :=
    separated L D x y (by rwa [identity])
  rcases axes with lu | lv | du | dv
  · have selected := forward _ _ lp L.unit_normal
      (separateAxis _ _ _ (parallel_radius L D) lu)
    rw [(ownU L).2,ls] at selected
    exact tilt_of_left_u L D r ls ln dn side same small positive center low
      bottom offset selected
  · exact False.elim (noLV (separateAxis _ _ _ (transverse_radius L D) lv))
  · have identity : supportRadius L D.c D.s+supportRadius D D.c D.s=pairRadius D L := by
      rw [add_comm]; exact parallel_radius D L
    have selected := forward _ _ dp D.unit_normal (separateAxis _ _ _ identity du)
    rw [(ownU D).1] at selected
    exact False.elim (no_central_u L D r ls ln dn (by simpa only [same] using side)
      same box marker slope positive offset selected)
  · have identity : supportRadius L (-D.s) D.c+supportRadius D (-D.s) D.c=pairRadius D L := by
      rw [add_comm]; exact transverse_radius D L
    exact False.elim (FullAuxWallLeftResidual.no_opposite_v L D dn marker low bottomPoint left
      (separateAxis _ _ _ identity dv))

#print axioms small_tilt

private theorem no_upper_left_v (L B : OpenSquare) (r : ℝ)
    (ls : L.s=-r) (ln : Normal L.c r) (bn : Normal B.c B.s)
    (side : 1<B.side) (small : r<1/50) (steep : 3/10<B.s)
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (upperV : B.loV+B.side≤3*B.c-B.s)
    (marker : L.Inside (457/500) 2)
    (axis : L.loV+L.side≤lower B r L.c) : False := by
  have lb := normal_bounds ln
  have bb := normal_bounds bn
  have order := FullAuxWallLeftResidual.negative_v_order L B r ls ln bn side
    upperU upperV marker axis
  have arcProduct := mul_nonneg
    (show 0≤B.c+B.s-1 by linarith only [bb.2.2.2.2.1])
    (show 0≤(3/2 : ℝ)-(B.c+B.s) by linarith only [bb.2.2.2.2.2])
  have arc : (4/5)*B.c*B.s≤B.c+B.s-1 := by
    nlinarith only [arcProduct,bn.2.2]
  have product := mul_nonneg bn.1 (show 0≤B.c-7/10 by linarith only [bb.1])
  have kBound : 1/25≤FullAuxWallLeftResidual.K B.c B.s := by
    dsimp [FullAuxWallLeftResidual.K]
    nlinarith only [arc,product,steep]
  have qBound : FullAuxWallLeftResidual.Q B.c B.s≤343/500 := by
    dsimp [FullAuxWallLeftResidual.Q]
    nlinarith only [bn.2.1,sq_nonneg B.s]
  have first := mul_nonneg (show 0≤L.c by linarith only [lb.1])
    (sub_nonneg.mpr kBound)
  have second := mul_nonneg ln.1 (sub_nonneg.mpr qBound)
  nlinarith only [order,first,second,lb.1,small]

/-- The complete B/L separating-axis alternatives leave B's own
longitudinal axis once the actual C/L geometry has made L nearly flat. -/
theorem upper_axis (L B : OpenSquare) (r : ℝ)
    (ls : L.s=-r) (ln : Normal L.c r) (bn : Normal B.c B.s)
    (side : 1<B.side) (same : L.side=B.side)
    (small : r<1/50) (steep : 3/10<B.s)
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (upperV : B.loV+B.side≤3*B.c-B.s)
    (marker : L.Inside (457/500) 2) (low : L.Inside 1 (8/5))
    (bMarker : B.Inside (33/20) (47/20)) (high : B.Inside 1 (12/5))
    (apart : ∀ x y, ¬(L.Inside x y ∧ B.Inside x y)) :
    upper L B.c B.s≤B.loU := by
  have lb := normal_bounds ln
  have bb := normal_bounds bn
  have lp : 0<L.c := by linarith only [lb.1]
  have bp : 0<B.c := by linarith only [bb.1]
  have noLU (axis : upper L L.c L.s≤lower B L.c L.s ∨
      upper B L.c L.s≤lower L L.c L.s) : False := by
    rcases axis with forward | reverse
    · have first := (strict_bounds L _ _ L.c L.s L.unit_normal low).2
      have second := (strict_bounds B _ _ L.c L.s L.unit_normal high).1
      rw [ls] at first second forward
      nlinarith only [forward,first,second,ln.1]
    · have first := (strict_bounds B _ _ L.c L.s L.unit_normal bMarker).2
      have second := (strict_bounds L _ _ L.c L.s L.unit_normal marker).1
      rw [ls] at first second reverse
      nlinarith only [reverse,first,second,ln.2.1,lp]
  have noLV (axis : upper L (-L.s) L.c≤lower B (-L.s) L.c ∨
      upper B (-L.s) L.c≤lower L (-L.s) L.c) : False := by
    rcases axis with forward | reverse
    · rw [(ownV L).2,ls,neg_neg] at forward
      exact no_upper_left_v L B r ls ln bn side small steep upperU upperV marker forward
    · have unit : (-L.s)^2+L.c^2=1 := by nlinarith only [L.unit_normal]
      have first := (strict_bounds B _ _ (-L.s) L.c unit high).2
      have second := (strict_bounds L _ _ (-L.s) L.c unit low).1
      nlinarith only [reverse,first,second,lp]
  have forward (axis : upper L B.c B.s≤lower B B.c B.s ∨
      upper B B.c B.s≤lower L B.c B.s) : upper L B.c B.s≤B.loU := by
    rcases axis with yes | no
    · simpa only [(ownU B).1] using yes
    · have first := (strict_bounds B _ _ B.c B.s B.unit_normal high).2
      have second := (strict_bounds L _ _ B.c B.s B.unit_normal marker).1
      exact False.elim (by nlinarith only [no,first,second,bp,bn.1])
  have axes := CongruentSAT.faceSeparation_of_disjoint L B same apart
  change pairRadius L B≤|L.c*(centerX B-centerX L)+L.s*(centerY B-centerY L)| ∨
    pairRadius L B≤|-L.s*(centerX B-centerX L)+L.c*(centerY B-centerY L)| ∨
    pairRadius B L≤|B.c*(centerX B-centerX L)+B.s*(centerY B-centerY L)| ∨
    pairRadius B L≤|-B.s*(centerX B-centerX L)+B.c*(centerY B-centerY L)| at axes
  have separateAxis (x y R : ℝ)
      (identity : supportRadius L x y+supportRadius B x y=R)
      (axis : R≤|x*(centerX B-centerX L)+y*(centerY B-centerY L)|) :=
    separated L B x y (by rwa [identity])
  rcases axes with lu | lv | bu | bv
  · exact False.elim (noLU (separateAxis _ _ _ (parallel_radius L B) lu))
  · exact False.elim (noLV (separateAxis _ _ _ (transverse_radius L B) lv))
  · have identity : supportRadius L B.c B.s+supportRadius B B.c B.s=pairRadius B L := by
      rw [add_comm]; exact parallel_radius B L
    exact forward (separateAxis _ _ _ identity bu)
  · have identity : supportRadius L (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B L := by
      rw [add_comm]; exact transverse_radius B L
    exact False.elim (FullAuxWallLeftResidual.no_upper_v L B bn side upperV marker low high
      (separateAxis _ _ _ identity bv))

/-- The real left container wall forces B above sine 23/50 in the
remaining selector. The common side is kept strictly larger than one. -/
theorem upper_steep (L B : OpenSquare) (r : ℝ)
    (ls : L.s=-r) (ln : Normal L.c r) (bn : Normal B.c B.s)
    (side : 1<L.side) (same : L.side=B.side)
    (small : r<1/50) (steep : 3/10<B.s)
    (box : InsideContainer L) (marker : L.Inside (457/500) 2)
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (axis : upper L B.c B.s≤B.loU) : 23/50<B.s := by
  have lb := normal_bounds ln
  have bb := normal_bounds bn
  have lp : 0<L.c := by linarith only [lb.1]
  have bp : 0<B.c := by linarith only [bb.1]
  let d := L.c*B.c-r*B.s
  have dp : 0≤d := by
    have first := mul_nonneg bp.le (sub_nonneg.mpr ln.2.1)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr bn.2.1)
    dsimp [d]; nlinarith only [first,second]
  have projection := upper_support L r B.c B.s ls ln bn
    (by linarith only [steep]) box marker
  have scaledAxis := mul_le_mul_of_nonneg_left axis lp.le
  have scaledCap := mul_le_mul_of_nonneg_left upperU lp.le
  have strict := mul_pos (sub_pos.mpr side)
    (show 0<L.c+d*(L.c+r) by
      have product := mul_nonneg dp (show 0≤L.c+r by linarith only [lp,ln.1])
      linarith only [lp,product])
  have necessary :
      L.c*(1-(3/5)*B.c-B.s)+d*(L.c+r-1)-(43/500)*B.s*r<0 := by
    rw [same] at projection strict
    dsimp [d] at projection strict ⊢
    nlinarith only [projection,scaledAxis,scaledCap,strict]
  apply lt_of_not_ge
  intro flat
  have radial : B.c≤1-B.s^2/2 := by
    nlinarith only [bn.2.2,sq_nonneg (1-B.c)]
  have endpoint := mul_nonneg (sub_nonneg.mpr flat)
    (show 0≤1-(3/10)*(23/50+B.s) by linarith only [flat])
  have gap : 3/1000≤1-(3/5)*B.c-B.s := by
    nlinarith only [radial,endpoint]
  have first := mul_nonneg lp.le (sub_nonneg.mpr gap)
  have second := mul_nonneg dp
    (show 0≤L.c+r-1 by linarith only [lb.2.2.2.2.1])
  have product := mul_nonneg ln.1 (sub_nonneg.mpr flat)
  have last : B.s*r≤23/2500 := by nlinarith only [product,small]
  nlinarith only [necessary,first,second,last,lb.1]

/-- Complete negative-L sector of the actual three-square C/B/L
coupling. Each of the four square axes is handled before the two
independent bounds on B's angle are compared. -/
theorem impossible (L D B : OpenSquare) (r : ℝ)
    (ls : L.s=-r) (ln : Normal L.c r)
    (dn : Normal D.c D.s) (bn : Normal B.c B.s)
    (side : 1<D.side) (sameLD : L.side=D.side) (sameDB : D.side=B.side)
    (box : InsideContainer L)
    (small : D.s≤11/50) (positive : 1/20<D.s)
    (marker : L.Inside (457/500) 2) (low : L.Inside 1 (8/5))
    (center : D.Inside 2 2) (bottomPoint : D.Inside 2 (3/2))
    (left : D.Inside (6/5) (19/10))
    (bottom : D.c-(8/5)*D.s≤D.loV)
    (offset : D.loU+D.side-2*(D.c+D.s)≤1/1000)
    (bMarker : B.Inside (33/20) (47/20)) (high : B.Inside 1 (12/5))
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (upperV : B.loV+B.side≤3*B.c-B.s)
    (steep : 3/10<B.s) (ordered : D.s*B.c≤D.c*B.s)
    (modes : D.loV+D.side≤lower B (-D.s) D.c ∨ upper D (-B.s) B.c≤B.loV)
    (apartLD : ∀ x y, ¬(L.Inside x y ∧ D.Inside x y))
    (apartLB : ∀ x y, ¬(L.Inside x y ∧ B.Inside x y)) : False := by
  have smallL := small_tilt L D r ls ln dn side sameLD box small positive
    marker low center bottomPoint left bottom offset apartLD
  have sideB : 1<B.side := by simpa only [sameDB] using side
  have sameLB : L.side=B.side := sameLD.trans sameDB
  have axis := upper_axis L B r ls ln bn sideB sameLB smallL steep upperU upperV
    marker low bMarker high apartLB
  have lowerBound := upper_steep L B r ls ln bn
    (by simpa only [sameLD] using side) sameLB smallL steep box marker upperU axis
  have upperBound := FullAuxWallPositiveUpperAngleSupport.sine D B dn bn side sameDB
    bottom upperU upperV small offset ordered modes
  linarith only [lowerBound,upperBound]

#print axioms impossible
end N12Compact.FullAuxWallNegativeLeft
