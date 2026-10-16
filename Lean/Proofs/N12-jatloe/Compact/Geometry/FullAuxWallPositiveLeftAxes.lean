import Compact.Geometry.FullAuxWallLeftResidual

/-! The actual left-marker lower U face of the steep upper square
removes the previously retained negative relative-angle V selector.
Together with the opposite-sign calculation, every positive left-wall
V separator is impossible. -/
namespace N12Compact.FullAuxWallPositiveLeftAxes

open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic FullAuxWallTopEndpoint FullAuxWallLeftResidual
set_option Elab.async false

theorem no_left_v (L B : OpenSquare)
    (ln : Normal L.c L.s) (bn : Normal B.c B.s)
    (side : 1<B.side)
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (upperV : B.loV+B.side≤3*B.c-B.s)
    (lowerU : (457/500)*B.c+2*B.s≤B.loU)
    (width : 1<(343/500)*B.c+B.s)
    (marker : L.Inside (457/500) 2)
    (axis : L.loV+L.side≤lower B (-L.s) L.c) : False := by
  have order := positive_v_order L B ln bn side upperU upperV width marker axis
  have lb := normal_bounds ln
  have bb := normal_bounds bn
  have lc : 0<L.c := by linarith only [lb.1]
  have bc : 0<B.c := by linarith only [bb.1]
  let h := L.c*B.s-L.s*B.c
  let alpha := L.c*B.c+L.s*B.s
  have hn : h<0 := by dsimp [h]; linarith only [order]
  have ap : 0<alpha := by
    exact add_pos_of_pos_of_nonneg (mul_pos lc bc) (mul_nonneg ln.1 bn.1)
  have u : (457/500)*B.c+2*B.s<B.loU+B.side := by
    linarith only [lowerU,B.side_pos]
  have v : B.loV<2*B.c-(457/500)*B.s := by
    linarith only [upperV,side,bb.2.1,bn.1]
  have first := mul_neg_of_neg_of_pos hn (sub_pos.mpr u)
  have second := mul_pos ap (sub_pos.mpr v)
  rw [lower_np B (-L.s) L.c
    (by dsimp [h] at hn; nlinarith only [hn])
    (by dsimp [alpha] at ap; nlinarith only [ap])] at axis
  have projection :
      h*((457/500)*B.c+2*B.s)+alpha*(2*B.c-(457/500)*B.s)=
        2*L.c-(457/500)*L.s := by
    dsimp [h,alpha]
    linear_combination (2*L.c-(457/500)*L.s)*B.unit_normal
  have axis' : L.loV+L.side≤h*(B.loU+B.side)+alpha*B.loV := by
    dsimp only [h, alpha]
    nlinarith only [axis]
  nlinarith only [axis',first,second,projection,marker.2.2.2]

/-- In the full positive B/L chart, the genuine left wall and upper
central square can separate only along their two longitudinal axes. -/
theorem alternatives (L B : OpenSquare)
    (ln : Normal L.c L.s) (bn : Normal B.c B.s)
    (same : L.side=B.side) (side : 1<B.side)
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (upperV : B.loV+B.side≤3*B.c-B.s)
    (lowerU : (457/500)*B.c+2*B.s≤B.loU)
    (width : 1<(343/500)*B.c+B.s)
    (marker : L.Inside (457/500) 2)
    (low : L.Inside 1 (8/5)) (high : B.Inside 1 (12/5))
    (apart : ∀ x y, ¬(L.Inside x y ∧ B.Inside x y)) :
    L.loU+L.side≤lower B L.c L.s ∨ upper L B.c B.s≤B.loU := by
  have lb := normal_bounds ln
  have bb := normal_bounds bn
  have lc : 0<L.c := by linarith only [lb.1]
  have bc : 0<B.c := by linarith only [bb.1]
  have forward (x y : ℝ) (yp : 0<y) (unit : x^2+y^2=1)
      (h : upper L x y≤lower B x y ∨ upper B x y≤lower L x y) :
      upper L x y≤lower B x y := by
    rcases h with h | h
    · exact h
    · have first := (strict_bounds B _ _ x y unit high).2
      have second := (strict_bounds L _ _ x y unit low).1
      exfalso; nlinarith only [first,second,h,yp]
  have forwardU (x y : ℝ) (xp : 0<x) (yp : 0≤y) (unit : x^2+y^2=1)
      (h : upper L x y≤lower B x y ∨ upper B x y≤lower L x y) :
      upper L x y≤lower B x y := by
    rcases h with h | h
    · exact h
    · have first := (strict_bounds B _ _ x y unit high).2
      have second := (strict_bounds L _ _ x y unit marker).1
      exfalso; nlinarith only [first,second,h,xp,yp]
  have axes := CongruentSAT.faceSeparation_of_disjoint L B same apart
  change pairRadius L B≤|L.c*(centerX B-centerX L)+L.s*(centerY B-centerY L)| ∨
    pairRadius L B≤|-L.s*(centerX B-centerX L)+L.c*(centerY B-centerY L)| ∨
    pairRadius B L≤|B.c*(centerX B-centerX L)+B.s*(centerY B-centerY L)| ∨
    pairRadius B L≤|-B.s*(centerX B-centerX L)+B.c*(centerY B-centerY L)| at axes
  have separateAxis (x y R : ℝ)
      (identity : supportRadius L x y+supportRadius B x y=R)
      (h : R≤|x*(centerX B-centerX L)+y*(centerY B-centerY L)|) :=
    separated L B x y (by rwa [identity])
  rcases axes with lu | lv | bu | bv
  · left
    have h := forwardU _ _ lc ln.1 L.unit_normal
      (separateAxis _ _ _ (parallel_radius L B) lu)
    simpa only [(ownU L).2] using h
  · have unit : (-L.s)^2+L.c^2=1 := by nlinarith only [L.unit_normal]
    have h := forward _ _ lc unit
      (separateAxis _ _ _ (transverse_radius L B) lv)
    have own : L.loV+L.side≤lower B (-L.s) L.c := by
      simpa only [(ownV L).2] using h
    exact False.elim (no_left_v L B ln bn side upperU upperV lowerU width marker own)
  · right
    have identity : supportRadius L B.c B.s+supportRadius B B.c B.s=pairRadius B L := by
      rw [add_comm]; exact parallel_radius B L
    have h := forwardU _ _ bc bn.1 B.unit_normal
      (separateAxis _ _ _ identity bu)
    simpa only [(ownU B).1] using h
  · have identity : supportRadius L (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B L := by
      rw [add_comm]; exact transverse_radius B L
    exact False.elim (no_upper_v L B bn side upperV marker low high
      (separateAxis _ _ _ identity bv))

#print axioms no_left_v
#print axioms alternatives
end N12Compact.FullAuxWallPositiveLeftAxes
