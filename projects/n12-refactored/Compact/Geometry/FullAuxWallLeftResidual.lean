import Compact.Geometry.FullAuxWallPositiveTop

noncomputable section

/-! Necessary angle inequalities from the genuine left wall and positive
upper central square. No unresolved separating axis is removed by a point
relaxation. This module is a reduction, not a whole-row exclusion. -/
namespace N12Compact.FullAuxWallLeftResidual
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic FullAuxWallTopEndpoint
set_option Elab.async false

def K (b t : ℝ) : ℝ := b+t-1-(3/5)*b*t
def Q (b t : ℝ) : ℝ := t-b+(343/500)-(3/5)*t^2

theorem coefficient_signs {b t : ℝ} (bn : Normal b t)
    (width : 1<(343/500)*b+t) : 0≤K b t ∧ 0<Q b t := by
  have bounds := normal_bounds bn
  have arcProduct := mul_nonneg
    (show 0≤b+t-1 by linarith only [bounds.2.2.2.2.1])
    (show 0≤(3/2 : ℝ)-(b+t) by linarith only [bounds.2.2.2.2.2])
  have arc : (4/5)*b*t≤b+t-1 := by nlinarith only [arcProduct,bn.2.2]
  have product := mul_nonneg (show 0≤b by linarith only [bounds.1]) bn.1
  have defect : t^2/2≤1-b := by nlinarith only [bn.2.2,sq_nonneg (b-1)]
  constructor
  · dsimp [K]; nlinarith only [arc,product]
  · dsimp [Q]; nlinarith only [width,defect,sq_nonneg t]

/-- B's own V axis cannot separate it from the original left wall. -/
theorem no_upper_v (L B : OpenSquare) (bn : Normal B.c B.s)
    (side : 1<B.side) (cap : B.loV+B.side≤3*B.c-B.s)
    (marker : L.Inside (457/500) 2) (low : L.Inside 1 (8/5))
    (high : B.Inside 1 (12/5))
    (axis : upper L (-B.s) B.c≤lower B (-B.s) B.c ∨
      upper B (-B.s) B.c≤lower L (-B.s) B.c) : False := by
  have bounds := normal_bounds bn
  have bc : 0<B.c := by linarith only [bounds.1]
  have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
  rcases axis with before | after
  · rw [(ownV B).1] at before
    have bound := (strict_bounds L _ _ (-B.s) B.c unit marker).2
    nlinarith only [before,bound,cap,side,bounds.2.1,bn.1]
  · have first := (strict_bounds B _ _ (-B.s) B.c unit high).2
    have second := (strict_bounds L _ _ (-B.s) B.c unit low).1
    nlinarith only [after,first,second,bc]

/-- A positive left-wall V separator forces its angle to exceed B's.
The opposite relative-angle branch is excluded by the two actual caps
and the width between B's original left-wall and top-wall exclusions. -/
theorem positive_v_order (L B : OpenSquare)
    (ln : Normal L.c L.s) (bn : Normal B.c B.s)
    (side : 1<B.side)
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (upperV : B.loV+B.side≤3*B.c-B.s)
    (width : 1<(343/500)*B.c+B.s)
    (marker : L.Inside (457/500) 2)
    (axis : L.loV+L.side≤lower B (-L.s) L.c) :
    L.c*B.s<L.s*B.c := by
  apply lt_of_not_ge
  intro order
  have lb := normal_bounds ln
  have bb := normal_bounds bn
  have lc : 0<L.c := by linarith only [lb.1]
  have bc : 0<B.c := by linarith only [bb.1]
  let h := L.c*B.s-L.s*B.c
  let alpha := L.c*B.c+L.s*B.s
  have hp : 0≤h := by dsimp [h]; linarith only [order]
  have ap : 0≤alpha := by dsimp [alpha]; positivity
  rw [lower_pp B (-L.s) L.c
    (by dsimp [h] at hp; nlinarith only [hp])
    (by dsimp [alpha] at ap; nlinarith only [ap])] at axis
  change L.loV+L.side≤h*B.loU+alpha*B.loV at axis
  have u := mul_nonneg hp
    (show 0≤(8/5)*B.c+3*B.s-1-B.loU by linarith only [upperU,side])
  have v := mul_nonneg ap
    (show 0≤3*B.c-B.s-1-B.loV by linarith only [upperV,side])
  have signs := coefficient_signs bn width
  have first := mul_nonneg lc.le signs.1
  have second := mul_nonneg ln.1 signs.2.le
  have identity : h*((8/5)*B.c+3*B.s-1)+alpha*(3*B.c-B.s-1)-
      (2*L.c-(457/500)*L.s)=-L.c*K B.c B.s-L.s*Q B.c B.s := by
    dsimp [h,alpha,K,Q]
    linear_combination (3*L.c-(8/5)*L.s)*bn.2.2
  nlinarith only [axis,u,v,marker.2.2.2,first,second,identity]

/-- A negative left-wall V separator has an explicit strict angle
condition. It is retained: these hypotheses do not eliminate that axis. -/
theorem negative_v_order (L B : OpenSquare) (r : ℝ)
    (ls : L.s=-r) (ln : Normal L.c r) (bn : Normal B.c B.s)
    (side : 1<B.side)
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (upperV : B.loV+B.side≤3*B.c-B.s)
    (marker : L.Inside (457/500) 2)
    (axis : L.loV+L.side≤lower B r L.c) :
    L.c*K B.c B.s<r*Q B.c B.s := by
  have lb := normal_bounds ln
  have bb := normal_bounds bn
  have lc : 0<L.c := by linarith only [lb.1]
  have bc : 0<B.c := by linarith only [bb.1]
  let h := r*B.c+L.c*B.s
  let alpha := L.c*B.c-r*B.s
  have hp : 0≤h := by dsimp [h]; positivity
  have ap : 0≤alpha := by
    have p := mul_nonneg bc.le (sub_nonneg.mpr ln.2.1)
    have q := mul_nonneg ln.1 (sub_nonneg.mpr bn.2.1)
    dsimp [alpha]; nlinarith only [p,q]
  rw [lower_pp B r L.c
    (by dsimp [h] at hp; nlinarith only [hp])
    (by dsimp [alpha] at ap; nlinarith only [ap])] at axis
  change L.loV+L.side≤h*B.loU+alpha*B.loV at axis
  have u := mul_nonneg hp
    (show 0≤(8/5)*B.c+3*B.s-1-B.loU by linarith only [upperU,side])
  have v := mul_nonneg ap
    (show 0≤3*B.c-B.s-1-B.loV by linarith only [upperV,side])
  have identity : h*((8/5)*B.c+3*B.s-1)+alpha*(3*B.c-B.s-1)-
      (2*L.c+(457/500)*r)=-L.c*K B.c B.s+r*Q B.c B.s := by
    dsimp [h,alpha,K,Q]
    linear_combination (3*L.c+(8/5)*r)*bn.2.2
  have mark := marker.2.2.2
  rw [ls,neg_neg] at mark
  nlinarith only [axis,u,v,mark,identity]

/-- C's transverse axis is impossible for every orientation of the
actual left wall. The shifted reach is the previously proved point,
not the unavailable horizontal point (1.1,2). -/
theorem no_opposite_v (L D : OpenSquare) (dn : Normal D.c D.s)
    (marker : L.Inside (457/500) 2) (low : L.Inside 1 (8/5))
    (bottom : D.Inside 2 (3/2)) (left : D.Inside (6/5) (19/10))
    (axis : upper L (-D.s) D.c≤lower D (-D.s) D.c ∨
      upper D (-D.s) D.c≤lower L (-D.s) D.c) : False := by
  have bounds := normal_bounds dn
  have dc : 0<D.c := by linarith only [bounds.1]
  have unit : (-D.s)^2+D.c^2=1 := by nlinarith only [D.unit_normal]
  rcases axis with before | after
  · have first := (strict_bounds L _ _ (-D.s) D.c unit marker).2
    have second := (strict_bounds D _ _ (-D.s) D.c unit bottom).1
    nlinarith only [before,first,second,dc,dn.1]
  · have first := (strict_bounds D _ _ (-D.s) D.c unit left).2
    have second := (strict_bounds L _ _ (-D.s) D.c unit low).1
    nlinarith only [after,first,second,dc,dn.2.1]

/-- When L is positive, its own transverse axis is impossible as well.
Only the two longitudinal actual-square selectors remain for L/C. -/
theorem positive_left_axes (L D : OpenSquare)
    (ln : Normal L.c L.s) (dn : Normal D.c D.s) (same : L.side=D.side)
    (marker : L.Inside (457/500) 2) (low : L.Inside 1 (8/5))
    (center : D.Inside 2 2) (bottom : D.Inside 2 (3/2))
    (left : D.Inside (6/5) (19/10))
    (apart : ∀ x y, ¬(L.Inside x y ∧ D.Inside x y)) :
    L.loU+L.side≤lower D L.c L.s ∨ upper L D.c D.s≤D.loU := by
  have lb := normal_bounds ln
  have db := normal_bounds dn
  have lc : 0<L.c := by linarith only [lb.1]
  have dc : 0<D.c := by linarith only [db.1]
  have noLV (axis : upper L (-L.s) L.c≤lower D (-L.s) L.c ∨
      upper D (-L.s) L.c≤lower L (-L.s) L.c) : False := by
    have unit : (-L.s)^2+L.c^2=1 := by nlinarith only [L.unit_normal]
    rcases axis with before | after
    · have first := (strict_bounds L _ _ (-L.s) L.c unit marker).2
      have second := (strict_bounds D _ _ (-L.s) L.c unit bottom).1
      nlinarith only [before,first,second,lc,ln.1]
    · have first := (strict_bounds D _ _ (-L.s) L.c unit left).2
      have second := (strict_bounds L _ _ (-L.s) L.c unit low).1
      nlinarith only [after,first,second,lc,ln.2.1]
  have forward (x y : ℝ) (xp : 0<x) (unit : x^2+y^2=1)
      (axis : upper L x y≤lower D x y ∨ upper D x y≤lower L x y) :
      upper L x y≤lower D x y := by
    rcases axis with before | after
    · exact before
    · have first := (strict_bounds D _ _ x y unit center).2
      have second := (strict_bounds L _ _ x y unit marker).1
      exact False.elim (by nlinarith only [after,first,second,xp])
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
  · have selected := forward L.c L.s lc L.unit_normal
      (separateAxis _ _ _ (parallel_radius L D) lu)
    left
    simpa only [(ownU L).2] using selected
  · exact False.elim (noLV (separateAxis _ _ _ (transverse_radius L D) lv))
  · have identity : supportRadius L D.c D.s+supportRadius D D.c D.s=pairRadius D L := by
      rw [add_comm]; exact parallel_radius D L
    have selected := forward D.c D.s dc D.unit_normal (separateAxis _ _ _ identity du)
    right
    simpa only [(ownU D).1] using selected
  · have identity : supportRadius L (-D.s) D.c+supportRadius D (-D.s) D.c=pairRadius D L := by
      rw [add_comm]; exact transverse_radius D L
    exact False.elim (no_opposite_v L D dn marker low bottom left
      (separateAxis _ _ _ identity dv))

#print axioms coefficient_signs
#print axioms no_upper_v
#print axioms positive_v_order
#print axioms negative_v_order
#print axioms no_opposite_v
#print axioms positive_left_axes
end N12Compact.FullAuxWallLeftResidual
