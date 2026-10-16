import Compact.Completion.C981.NegativePoint
import Compact.Geometry.FullAuxWallOppositeEscape
import Compact.Geometry.FullAuxWallOuterCorner

/-! The genuine top endpoint in the signed opposite-square cycle.
All four SAT axes and both contact directions are retained. Only a
positive B upper-U escape can remain; its upper-V strip is proved here. -/
namespace N12Compact.FullAuxWallTopEndpoint
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic
set_option Elab.async false

theorem lower_pp (q : OpenSquare) (x y : ℝ)
    (hu : 0≤x*q.c+y*q.s) (hv : 0≤-x*q.s+y*q.c) :
    lower q x y=(x*q.c+y*q.s)*q.loU+(-x*q.s+y*q.c)*q.loV := by
  dsimp [lower,supportRadius,centerX,centerY]
  rw [abs_of_nonneg hu,abs_of_nonneg hv]
  ring

theorem lower_np (q : OpenSquare) (x y : ℝ)
    (hu : x*q.c+y*q.s≤0) (hv : 0≤-x*q.s+y*q.c) :
    lower q x y=(x*q.c+y*q.s)*(q.loU+q.side)+(-x*q.s+y*q.c)*q.loV := by
  dsimp [lower,supportRadius,centerX,centerY]
  rw [abs_of_nonpos hu,abs_of_nonneg hv]
  ring

/-- Original NW/SW points remove the two longitudinal axes. -/
theorem transverse (D B : OpenSquare) (S : ℝ)
    (ds : D.s=-S) (dn : Normal D.c S) (bc : 0<B.c)
    (lowerSign : -B.c≤B.s) (upperSign : B.s≤B.c)
    (same : D.side=B.side)
    (center : D.Inside 2 2) (left : D.Inside (11/10) 2)
    (southwest : D.Inside (33/20) (33/20))
    (marker : B.Inside (33/20) (47/20)) (high : B.Inside 1 (12/5))
    (apart : ∀ x y, ¬(D.Inside x y ∧ B.Inside x y)) :
    D.loV+D.side≤lower B S D.c ∨ upper D (-B.s) B.c≤B.loV := by
  have db := normal_bounds dn
  have dc : 0<D.c := by linarith only [db.1]
  have noDU (h : upper D D.c D.s≤lower B D.c D.s ∨
      upper B D.c D.s≤lower D D.c D.s) : False := by
    have p := strict_bounds D _ _ D.c D.s D.unit_normal center
    have l := strict_bounds D _ _ D.c D.s D.unit_normal left
    have m := strict_bounds B _ _ D.c D.s D.unit_normal marker
    rw [ds] at p l m h
    rcases h with h | h <;> nlinarith only [h,p.2,l.1,m.1,m.2,dc,dn.1,dn.2.1]
  have noBU (h : upper D B.c B.s≤lower B B.c B.s ∨
      upper B B.c B.s≤lower D B.c B.s) : False := by
    have p := strict_bounds D _ _ B.c B.s B.unit_normal center
    have l := strict_bounds D _ _ B.c B.s B.unit_normal left
    have m := strict_bounds B _ _ B.c B.s B.unit_normal marker
    have f := strict_bounds B _ _ B.c B.s B.unit_normal high
    rcases h with h | h <;>
      nlinarith only [h,p.2,l.1,m.2,f.1,bc,lowerSign,upperSign]
  have forward (x y : ℝ) (yp : 0<y) (unit : x^2+y^2=1)
      (h : upper D x y≤lower B x y ∨ upper B x y≤lower D x y) :
      upper D x y≤lower B x y := by
    rcases h with h | h
    · exact h
    · have p := (strict_bounds D _ _ x y unit southwest).1
      have m := (strict_bounds B _ _ x y unit marker).2
      exfalso; nlinarith only [h,p,m,yp]
  have axes := CongruentSAT.faceSeparation_of_disjoint D B same apart
  change pairRadius D B≤|D.c*(centerX B-centerX D)+D.s*(centerY B-centerY D)| ∨
    pairRadius D B≤|-D.s*(centerX B-centerX D)+D.c*(centerY B-centerY D)| ∨
    pairRadius B D≤|B.c*(centerX B-centerX D)+B.s*(centerY B-centerY D)| ∨
    pairRadius B D≤|-B.s*(centerX B-centerX D)+B.c*(centerY B-centerY D)| at axes
  have separateAxis (x y R : ℝ)
      (identity : supportRadius D x y+supportRadius B x y=R)
      (h : R≤|x*(centerX B-centerX D)+y*(centerY B-centerY D)|) :=
    separated D B x y (by rwa [identity])
  rcases axes with du | dv | bu | bv
  · exact False.elim (noDU (separateAxis _ _ _ (parallel_radius D B) du))
  · have unit : (-D.s)^2+D.c^2=1 := by nlinarith only [D.unit_normal]
    have h := forward _ _ dc unit (separateAxis _ _ _ (transverse_radius D B) dv)
    rw [(ownV D).2] at h
    left; simpa only [ds,neg_neg] using h
  · have identity : supportRadius D B.c B.s+supportRadius B B.c B.s=pairRadius B D := by
      rw [add_comm]; exact parallel_radius B D
    exact False.elim (noBU (separateAxis _ _ _ identity bu))
  · have identity : supportRadius D (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B D := by
      rw [add_comm]; exact transverse_radius B D
    have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
    have h := forward _ _ bc unit (separateAxis _ _ _ identity bv)
    right; simpa only [(ownV B).1] using h

private theorem defect {b t : ℝ} (bn : Normal b t) : 1-b≤(3/5)*t^2 := by
  have bounds := normal_bounds bn
  have product := mul_nonneg (sub_nonneg.mpr bounds.2.1)
    (show 0≤3*b-2 by linarith only [bounds.1])
  nlinarith only [product,bn.2.2]

/-- The top endpoint is strictly below B's upper V face in every positive
canonical B frame. Only actual C-center/left reach and the two SAT modes
are used. -/
theorem positive_v (D B : OpenSquare) (S : ℝ)
    (ds : D.s=-S) (dn : Normal D.c S) (bn : Normal B.c B.s)
    (side : 1<B.side) (center : D.Inside 2 2) (left : D.Inside (11/10) 2)
    (low : B.Inside 1 (113/50))
    (modes : D.loV+D.side≤lower B S D.c ∨ upper D (-B.s) B.c≤B.loV) :
    3*B.c-(8/5)*B.s<B.loV+B.side := by
  apply lt_of_not_ge
  intro cap
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dc : 0<D.c := by linarith only [db.1]
  have bc : 0<B.c := by linarith only [bb.1]
  rcases modes with first | second
  · let k := S*B.c+D.c*B.s
    let alpha := -S*B.s+D.c*B.c
    have kp : 0≤k := add_nonneg (mul_nonneg dn.1 bc.le) (mul_nonneg dc.le bn.1)
    have ap : 0≤alpha := by
      have p := mul_nonneg (sub_nonneg.mpr dn.2.1) bc.le
      have q := mul_nonneg dn.1 (sub_nonneg.mpr bn.2.1)
      dsimp [alpha]; nlinarith only [p,q]
    rw [lower_pp B S D.c kp ap] at first
    have u := mul_nonneg kp (sub_nonneg.mpr low.1.le)
    have v := mul_nonneg ap
      (show 0≤3*B.c-(8/5)*B.s-1-B.loV by linarith only [cap,side])
    have firstCoefficient : 1-B.c-(37/50)*B.s^2-(3/5)*B.c*B.s≤0 := by
      have p := mul_nonneg bc.le bn.1
      nlinarith only [defect bn,p,sq_nonneg B.s]
    have secondCoefficient : -1+B.s+(3/5)*B.s^2-(37/50)*B.c*B.s≤0 := by
      have p := mul_nonneg bn.1 (sub_nonneg.mpr bn.2.1)
      nlinarith only [p,bb.2.2.2.1,sq_nonneg B.s]
    have f := mul_nonpos_of_nonneg_of_nonpos dc.le firstCoefficient
    have g := mul_nonpos_of_nonneg_of_nonpos dn.1 secondCoefficient
    have identity : k*(B.c+(113/50)*B.s)+alpha*(3*B.c-(8/5)*B.s-1)-2*(D.c+S)=
        D.c*(1-B.c-(37/50)*B.s^2-(3/5)*B.c*B.s)+
        S*(-1+B.s+(3/5)*B.s^2-(37/50)*B.c*B.s) := by
      dsimp [k,alpha]
      linear_combination (3*D.c+S)*bn.2.2
    have p := center.2.2.2
    rw [ds,neg_neg] at p
    change _≤k*B.loU+alpha*B.loV at first
    have weightedSum : k*B.loU+alpha*B.loV ≤
        k*(B.c+(113/50)*B.s)+alpha*(3*B.c-(8/5)*B.s-1) := by
      apply sub_nonneg.mp
      convert add_nonneg u v using 1 <;> ring
    have enclosure : k*(B.c+(113/50)*B.s)+alpha*(3*B.c-(8/5)*B.s-1) ≤
        2*(D.c+S) := by
      apply sub_nonpos.mp
      rw [identity]
      exact add_nonpos f g
    have strictCenter : 2*(D.c+S) < D.loV+D.side := by linarith only [p]
    exact (not_lt_of_ge (first.trans (weightedSum.trans enclosure))) strictCenter
  · have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
    have p := (strict_bounds D _ _ (-B.s) B.c unit left).2
    nlinarith only [p,second,cap,side,bb.2.1,bn.1]

/-- Negative B frames force the actual top endpoint, including both
relative-angle signs of C's own transverse separator. -/
theorem negative_point (D B : OpenSquare) (S t : ℝ)
    (ds : D.s=-S) (dn : Normal D.c S) (bs : B.s=-t) (bn : Normal B.c t)
    (side : 1<B.side) (center : D.Inside 2 2)
    (marker : B.Inside (33/20) (47/20)) (high : B.Inside 1 (12/5))
    (modes : D.loV+D.side≤lower B S D.c ∨ upper D (-B.s) B.c≤B.loV) :
    B.Inside (8/5) 3 := by
  exact C981CompletionNegativePoint.point D B S t ds dn bs bn side center marker high modes

#print axioms transverse
#print axioms positive_v
#print axioms negative_point
end N12Compact.FullAuxWallTopEndpoint
