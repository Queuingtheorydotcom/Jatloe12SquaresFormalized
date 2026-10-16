import Compact.Completion.C1092.ShortWallNarrow

/-! Every signed canonical right-wall frame leaves only its two forward
longitudinal separators. Both transverse orders are excluded from strict
physical point projections, retaining zero and relative-angle equality. -/
namespace N12Compact.C1092ShortWallRightAxes
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092ShortWallNarrow C1092ShortWallScalars
set_option Elab.async false

private theorem transverse (A R : OpenSquare)
    (cn : Normal A.c A.s) (data : NarrowData A)
    (rc : 0 < R.c) (range : |R.s| ≤ R.c)
    (ha : 1 < A.side)
    (q : A.Inside (113/50) 2) (m : A.Inside (47/20) (47/20)) :
    lower A (-R.s) R.c < -R.s*3+R.c*(1197/500) ∧
      -R.s*(1543/500)+R.c*2 < upper A (-R.s) R.c := by
  classical
  have cb := normal_bounds cn
  have nb := narrow_bounds cn data.narrow.le
  have rb := abs_le.mp range
  have cp : 0 < A.c := by linarith only [cb.1]
  by_cases sign : 0 ≤ R.s
  · have rn : Normal R.c R.s := ⟨sign,rb.2,R.unit_normal⟩
    have markerUpper := (strict_bounds A _ _ (-R.s) R.c
      (by nlinarith only [R.unit_normal]) m).2
    have second : -R.s*(1543/500)+R.c*2 < upper A (-R.s) R.c := by
      linarith only [markerUpper,rc,sign]
    have first : lower A (-R.s) R.c < -R.s*3+R.c*(1197/500) := by
      by_cases order : A.c*R.s ≤ A.s*R.c
      · have weight := mul_nonneg rc.le (sub_nonneg.mpr data.narrow.le)
        have wallNarrow : 4*R.s ≤ R.c := by
          apply (mul_le_mul_iff_right₀ cp).mp
          nlinarith only [weight,order]
        have pointLower := (strict_bounds A _ _ (-R.s) R.c
          (by nlinarith only [R.unit_normal]) q).1
        linarith only [pointLower,wallNarrow,rc]
      · let d := A.c*R.c+A.s*R.s
        let k := A.c*R.s-A.s*R.c
        have dp : 0 < d := add_pos_of_pos_of_nonneg (mul_pos cp rc)
          (mul_nonneg cn.1 sign)
        have kp : 0 ≤ k := by dsimp [k]; linarith only [order]
        have absDot : |(-R.s)*A.c+R.c*A.s|=k := by
          rw [abs_of_nonpos (by dsimp [k] at kp; nlinarith only [kp])]
          dsimp [k]
          ring
        have absCross : |-(-R.s)*A.s+R.c*A.c|=d := by
          rw [abs_of_nonneg (by dsimp [d] at dp; nlinarith only [dp])]
          dsimp [d]
          ring
        have formula : lower A (-R.s) R.c = -k*(A.loU+A.side)+d*A.loV := by
          dsimp [lower,supportRadius,centerX,centerY]
          rw [absDot,absCross]
          dsimp [d,k]
          ring
        have uWeight := mul_nonneg kp (sub_nonneg.mpr data.escape)
        have vWeight := mul_nonneg dp.le (sub_nonneg.mpr data.topcap)
        have strict := mul_pos (sub_pos.mpr ha) (show 0 < d+k by linarith only [dp,kp])
        have bound : lower A (-R.s) R.c <
            -k*(2*(A.c+A.s)+1)+d*(3*A.c-(1197/500)*A.s-1) := by
          apply sub_pos.mp
          calc
            -k*(2*(A.c+A.s)+1)+d*(3*A.c-(1197/500)*A.s-1)-
                lower A (-R.s) R.c =
                k*(A.loU-2*(A.c+A.s))+
                  d*(3*A.c-(1197/500)*A.s-(A.loV+A.side))+
                  (A.side-1)*(d+k) := by rw [formula]; ring
            _ > 0 := add_pos_of_nonneg_of_pos (add_nonneg uWeight vWeight) strict
        let F := A.c-A.s-303/500+A.s^2+(197/500)*A.c*A.s
        let G := A.c+A.s-1+(197/500)*A.s^2-A.c*A.s
        have cs := mul_nonneg cn.1 (sub_nonneg.mpr cb.2.1)
        have product := mul_nonneg cp.le cn.1
        have Flo : 13/125 ≤ F := by
          dsimp [F]
          nlinarith only [nb.1,nb.2.1,sq_nonneg A.s,product]
        have sumlo : 13/80 ≤ F+G := by
          dsimp [F,G]
          nlinarith only [nb.1,nb.2.1,cs,sq_nonneg A.s]
        have term0 := mul_nonneg (sub_nonneg.mpr rn.2.1)
          ((show (0:ℝ) ≤ 13/125 by norm_num).trans Flo)
        have term1 := mul_nonneg sign
          ((show (0:ℝ) ≤ 13/80 by norm_num).trans sumlo)
        have identity : (-R.s*3+R.c*(1197/500))-
            (-k*(2*(A.c+A.s)+1)+d*(3*A.c-(1197/500)*A.s-1)) = R.c*F+R.s*G := by
          dsimp [d,k,F,G]
          linear_combination (-3*R.c+2*R.s)*A.unit_normal
        have margin : 0 ≤ R.c*F+R.s*G := by
          calc
            _ = (R.c-R.s)*F+R.s*(F+G) := by ring
            _ ≥ 0 := add_nonneg term0 term1
        exact bound.trans_le (sub_nonneg.mp (by rw [identity]; exact margin))
    exact ⟨first,second⟩
  · let w := -R.s
    have wp : 0 ≤ w := by dsimp [w]; linarith only [sign]
    have wr : w ≤ R.c := by dsimp [w]; linarith only [rb.1]
    have wn : Normal R.c w := ⟨wp,wr,by dsimp [w]; nlinarith only [R.unit_normal]⟩
    have pointLower := (strict_bounds A _ _ (-R.s) R.c
      (by nlinarith only [R.unit_normal]) q).1
    have first : lower A (-R.s) R.c < -R.s*3+R.c*(1197/500) := by
      linarith only [pointLower,rc,sign]
    let d := A.c*R.c-A.s*w
    let k := A.c*w+A.s*R.c
    have dp : 0 < d := by
      have first := mul_pos rc (show 0 < A.c-A.s by linarith only [data.narrow,cn.1])
      have second := mul_nonneg cn.1 (sub_nonneg.mpr wr)
      dsimp [d]
      nlinarith only [first,second]
    have kp : 0 ≤ k := by dsimp [k]; exact add_nonneg (mul_nonneg cp.le wp) (mul_nonneg cn.1 rc.le)
    have absDot : |(-R.s)*A.c+R.c*A.s|=k := by
      rw [abs_of_nonneg (by dsimp [k,w] at kp; nlinarith only [kp])]
      dsimp [k,w]
      ring
    have absCross : |-(-R.s)*A.s+R.c*A.c|=d := by
      rw [abs_of_nonneg (by dsimp [d,w] at dp; nlinarith only [dp])]
      dsimp [d,w]
      ring
    have formula : upper A (-R.s) R.c = k*(A.loU+A.side)+d*(A.loV+A.side) := by
      dsimp [upper,supportRadius,centerX,centerY]
      rw [absDot,absCross]
      dsimp [d,k,w]
      ring
    have uWeight := mul_nonneg kp (sub_nonneg.mpr data.escape)
    have vWeight := mul_pos dp (sub_pos.mpr data.high.2.2.2)
    have strict := mul_nonneg kp (sub_nonneg.mpr ha.le)
    have bound : k*(2*(A.c+A.s)+1)+d*(3*A.c-(5/2)*A.s) < upper A (-R.s) R.c := by
      apply sub_pos.mp
      calc
        upper A (-R.s) R.c-(k*(2*(A.c+A.s)+1)+d*(3*A.c-(5/2)*A.s)) =
            k*(A.loU-2*(A.c+A.s))+
              d*(A.loV+A.side-(-A.s*(5/2)+A.c*3))+
              k*(A.side-1) := by rw [formula]; ring
        _ > 0 := add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos uWeight vWeight) strict
    let F := 1-A.s^2-A.c*A.s/2+A.s
    let G := A.c-543/500+A.s^2/2-A.c*A.s
    have sSquare : A.s^2 ≤ 1/16 := by
      nlinarith only [mul_nonneg cn.1 (sub_nonneg.mpr nb.2.1),nb.2.1,cn.1]
    have cs := mul_nonneg cn.1 (sub_nonneg.mpr cb.2.1)
    have Flo : 13/16 ≤ F := by dsimp [F]; nlinarith only [sSquare,cs,nb.2.1,cn.1]
    have sumlo : 1871/4000 ≤ F+G := by
      dsimp [F,G]
      nlinarith only [nb.1,sSquare,cs,nb.2.1,cn.1]
    have term0 := mul_nonneg (sub_nonneg.mpr wr)
      ((show (0:ℝ) ≤ 13/16 by norm_num).trans Flo)
    have term1 := mul_nonneg wp
      ((show (0:ℝ) ≤ 1871/4000 by norm_num).trans sumlo)
    have identity : k*(2*(A.c+A.s)+1)+d*(3*A.c-(5/2)*A.s)-
        (-R.s*(1543/500)+R.c*2) = R.c*F+w*G := by
      dsimp [d,k,w,F,G]
      linear_combination (3*R.c-2*R.s)*A.unit_normal
    have second : -R.s*(1543/500)+R.c*2 < upper A (-R.s) R.c := by
      have margin : 0 ≤ R.c*F+w*G := by
        calc
          _ = (R.c-w)*F+w*(F+G) := by ring
          _ ≥ 0 := add_nonneg term0 term1
      exact (sub_nonneg.mp (by rw [identity]; exact margin)).trans_lt bound
    exact ⟨first,second⟩

theorem alternatives (A R : OpenSquare) (ha : 1 < A.side) (same : A.side=R.side)
    (cn : Normal A.c A.s) (data : NarrowData A)
    (rc : 0 < R.c) (range : |R.s| ≤ R.c)
    (q : A.Inside (113/50) 2) (m : A.Inside (47/20) (47/20))
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (1197/500))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)) :
    A.loU+A.side ≤ lower R A.c A.s ∨ upper A R.c R.s ≤ R.loU := by
  have cb := normal_bounds cn
  have cp : 0 < A.c := by linarith only [cb.1]
  have rv := transverse A R cn data rc range ha q m
  have highVlo : A.loV < -A.s*3+A.c*(1197/500) := by
    linarith only [q.2.2.1,data.narrow,cp]
  have highVhi : -A.s*3+A.c*(1197/500) < A.loV+A.side := by
    linarith only [data.lowerV,cb.2.1,cn.1,ha]
  have axes := CongruentSAT.faceSeparation_of_disjoint A R same apart
  change pairRadius A R ≤ |A.c*(centerX R-centerX A)+A.s*(centerY R-centerY A)| ∨
    pairRadius A R ≤ |-A.s*(centerX R-centerX A)+A.c*(centerY R-centerY A)| ∨
    pairRadius R A ≤ |R.c*(centerX R-centerX A)+R.s*(centerY R-centerY A)| ∨
    pairRadius R A ≤ |-R.s*(centerX R-centerX A)+R.c*(centerY R-centerY A)| at axes
  have split (nx ny radius : ℝ)
      (identity : supportRadius A nx ny+supportRadius R nx ny=radius)
      (sep : radius ≤ |nx*(centerX R-centerX A)+ny*(centerY R-centerY A)|) :=
    separated A R nx ny (by rwa [identity])
  rcases axes with au | av | ru | rvAxis
  · have sep := split A.c A.s _ (parallel_radius A R) au
    rw [(ownU A).1,(ownU A).2] at sep
    rcases sep with forward | reverse
    · exact Or.inl forward
    · have bounds := strict_bounds R _ _ A.c A.s A.unit_normal marker
      exfalso
      linarith only [reverse,bounds.2,q.1,cp]
  · have sep := split (-A.s) A.c _ (transverse_radius A R) av
    rw [(ownV A).1,(ownV A).2] at sep
    have bounds := strict_bounds R _ _ (-A.s) A.c
      (by nlinarith only [A.unit_normal]) high
    rcases sep with sep | sep <;> exfalso <;>
      linarith only [sep,bounds.1,bounds.2,highVlo,highVhi]
  · have identity : supportRadius A R.c R.s+supportRadius R R.c R.s=pairRadius R A := by
      rw [add_comm]
      exact parallel_radius R A
    have sep := split R.c R.s _ identity ru
    rw [(ownU R).1,(ownU R).2] at sep
    rcases sep with forward | reverse
    · exact Or.inr forward
    · have bounds := strict_bounds A _ _ R.c R.s R.unit_normal q
      exfalso
      linarith only [reverse,bounds.1,marker.2.1,rc]
  · have identity : supportRadius A (-R.s) R.c+supportRadius R (-R.s) R.c=pairRadius R A := by
      rw [add_comm]
      exact transverse_radius R A
    have sep := split (-R.s) R.c _ identity rvAxis
    rw [(ownV R).1,(ownV R).2] at sep
    rcases sep with sep | sep <;> exfalso <;>
      linarith only [sep,rv.1,rv.2,high.2.2.2,marker.2.2.1]

#print axioms alternatives
end N12Compact.C1092ShortWallRightAxes
