import Compact.Completion.C981.SupportForms

/-! The standalone negative-neighbor point used by the C981 ending.
Only exact support formulas and the actual center and three anchors enter;
the unrelated full auxiliary-wall cycle is not imported. -/
namespace N12Compact.C981CompletionNegativePoint
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic
set_option Elab.async false

private theorem lower_pp (q : OpenSquare) (x y : ℝ)
    (hu : 0 ≤ x*q.c+y*q.s) (hv : 0 ≤ -x*q.s+y*q.c) :
    lower q x y=(x*q.c+y*q.s)*q.loU+(-x*q.s+y*q.c)*q.loV := by
  dsimp [lower,supportRadius,centerX,centerY]
  rw [abs_of_nonneg hu,abs_of_nonneg hv]
  ring

private theorem lower_np (q : OpenSquare) (x y : ℝ)
    (hu : x*q.c+y*q.s ≤ 0) (hv : 0 ≤ -x*q.s+y*q.c) :
    lower q x y=(x*q.c+y*q.s)*(q.loU+q.side)+(-x*q.s+y*q.c)*q.loV := by
  dsimp [lower,supportRadius,centerX,centerY]
  rw [abs_of_nonpos hu,abs_of_nonneg hv]
  ring

private theorem defect {b t : ℝ} (normal : Normal b t) : 1-b ≤ (3/5)*t^2 := by
  have bounds := normal_bounds normal
  have product := mul_nonneg (sub_nonneg.mpr bounds.2.1)
    (show 0 ≤ 3*b-2 by linarith only [bounds.1])
  nlinarith only [product,normal.2.2]

theorem point (D B : OpenSquare) (S t : ℝ)
    (ds : D.s=-S) (dn : Normal D.c S) (bs : B.s=-t) (bn : Normal B.c t)
    (side : 1<B.side) (center : D.Inside 2 2)
    (marker : B.Inside (33/20) (47/20)) (high : B.Inside 1 (12/5))
    (modes : D.loV+D.side≤lower B S D.c ∨ upper D (-B.s) B.c≤B.loV) :
    B.Inside (8/5) 3 := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dc : 0<D.c := by linarith only [db.1]
  have bc : 0<B.c := by linarith only [bb.1]
  have upperV : 3*B.c+(8/5)*t<B.loV+B.side := by
    apply lt_of_not_ge
    intro cap
    rcases modes with first | second
    · let h := B.c*S-t*D.c
      let d := t*S+B.c*D.c
      have dp : 0≤d := add_nonneg (mul_nonneg bn.1 dn.1) (mul_nonneg bc.le dc.le)
      have vlo : B.loV≤3*B.c+(8/5)*t-1 := by linarith only [cap,side]
      have v := mul_nonneg dp (sub_nonneg.mpr vlo)
      have centerV := center.2.2.2
      rw [ds,neg_neg] at centerV
      by_cases hp : 0≤h
      · have support := lower_pp B S D.c
          (by rw [bs]; dsimp [h] at hp; nlinarith only [hp])
          (by rw [bs]; dsimp [d] at dp; nlinarith only [dp])
        rw [support,bs] at first
        replace first : D.loV+D.side≤h*B.loU+d*B.loV := by
          convert first using 1 <;> dsimp [h,d] <;> ring
        have own := high.1
        rw [bs] at own
        have u := mul_nonneg hp (show 0≤B.c-(12/5)*t-B.loU by nlinarith only [own])
        let f := 1-B.c-(3/5)*t^2+(3/5)*B.c*t
        let g := -1-t+(3/5)*t^2+(3/5)*B.c*t
        have gn : g≤0 := by
          have p := mul_nonneg bn.1 (sub_nonneg.mpr bb.2.1)
          have q := mul_nonneg bn.1 (sub_nonneg.mpr bn.2.1)
          dsimp [g]; nlinarith only [p,q,bb.2.2.2.1,bn.1]
        have cancel : B.c*f+t*g=B.c-1-(2/5)*t := by
          dsimp [f,g]
          linear_combination ((3/5)*t-1)*bn.2.2
        have identity : h*(B.c-(12/5)*t)+d*(3*B.c+(8/5)*t-1)-2*(D.c+S)=D.c*f+S*g := by
          dsimp [h,d,f,g]
          linear_combination (3*D.c+S)*bn.2.2
        have gp := mul_nonpos_of_nonneg_of_nonpos hp gn
        have rest := mul_nonpos_of_nonneg_of_nonpos dc.le
          (show B.c-1-(2/5)*t≤0 by linarith only [bb.2.1,bn.1])
        have polynomial : D.c*f+S*g≤0 := by
          have equation : B.c*(D.c*f+S*g)=D.c*(B.c*f+t*g)+h*g := by dsimp [h]; ring
          have weighted : B.c*(D.c*f+S*g) ≤ 0 := by
            rw [equation,cancel]
            exact add_nonpos rest gp
          exact nonpos_of_mul_nonpos_right weighted bc
        have weightedSum : h*B.loU+d*B.loV ≤
            h*(B.c-(12/5)*t)+d*(3*B.c+(8/5)*t-1) := by
          apply sub_nonneg.mp
          convert add_nonneg u v using 1 <;> ring
        have enclosure : h*(B.c-(12/5)*t)+d*(3*B.c+(8/5)*t-1) ≤ 2*(D.c+S) := by
          apply sub_nonpos.mp
          rw [identity]
          exact polynomial
        have strictCenter : 2*(D.c+S) < D.loV+D.side := by linarith only [centerV]
        exact (not_lt_of_ge (first.trans (weightedSum.trans enclosure))) strictCenter
      · have hn : h≤0 := (lt_of_not_ge hp).le
        have support := lower_np B S D.c
          (by rw [bs]; dsimp [h] at hn; nlinarith only [hn])
          (by rw [bs]; dsimp [d] at dp; nlinarith only [dp])
        rw [support,bs] at first
        replace first : D.loV+D.side≤h*(B.loU+B.side)+d*B.loV := by
          convert first using 1 <;> dsimp [h,d] <;> ring
        have own := marker.2.1
        rw [bs] at own
        have u := mul_nonpos_of_nonpos_of_nonneg hn
          (show 0≤B.loU+B.side-((33/20)*B.c-(47/20)*t) by nlinarith only [own])
        have f : 1-B.c-(13/20)*t^2-(1/20)*B.c*t≤0 := by
          have p := mul_nonneg bc.le bn.1
          nlinarith only [defect bn,p,sq_nonneg t]
        have g : -(7/20)-(1/20)*t^2+(13/20)*B.c*t-t≤0 := by
          have p := mul_nonneg bn.1 (sub_nonneg.mpr bb.2.1)
          nlinarith only [p,bn.1,sq_nonneg t]
        have fp := mul_nonpos_of_nonneg_of_nonpos dc.le f
        have gp := mul_nonpos_of_nonneg_of_nonpos dn.1 g
        have identity : h*((33/20)*B.c-(47/20)*t)+d*(3*B.c+(8/5)*t-1)-2*(D.c+S)=
            D.c*(1-B.c-(13/20)*t^2-(1/20)*B.c*t)+
            S*(-(7/20)-(1/20)*t^2+(13/20)*B.c*t-t) := by
          dsimp [h,d]
          linear_combination (3*D.c+(33/20)*S)*bn.2.2
        have weightedSum : h*(B.loU+B.side)+d*B.loV ≤
            h*((33/20)*B.c-(47/20)*t)+d*(3*B.c+(8/5)*t-1) := by
          apply sub_nonneg.mp
          convert add_nonneg (neg_nonneg.mpr u) v using 1 <;> ring
        have enclosure : h*((33/20)*B.c-(47/20)*t)+d*(3*B.c+(8/5)*t-1) ≤ 2*(D.c+S) := by
          apply sub_nonpos.mp
          rw [identity]
          exact add_nonpos fp gp
        have strictCenter : 2*(D.c+S) < D.loV+D.side := by linarith only [centerV]
        exact (not_lt_of_ge (first.trans (weightedSum.trans enclosure))) strictCenter
    · have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
      have p := (strict_bounds D _ _ (-B.s) B.c unit center).2
      rw [bs,neg_neg] at p second
      nlinarith only [p,second,cap,side,bb.2.1,bn.1]
  have mUlo := marker.1
  have mUhi := marker.2.1
  have mVlo := marker.2.2.1
  have hUlo := high.1
  rw [bs] at mUlo mUhi mVlo hUlo
  refine ⟨?_,?_,?_,?_⟩ <;> rw [bs] <;>
    nlinarith only [mUlo,mUhi,mVlo,hUlo,upperV,bc,bn.1,bn.2.1]

#print axioms point
end N12Compact.C981CompletionNegativePoint
