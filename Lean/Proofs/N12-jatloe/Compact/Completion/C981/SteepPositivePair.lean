import Compact.Completion.C981.NegativePair
import Compact.Completion.C981.AngularScalars

/-! C981-COMMON-CYCLE Theorem 3: the actual negative central square
cannot separate from the steep positive neighboring central square. -/
namespace N12Compact.C981CompletionSteepPositivePair

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C981CompletionSupportForms C981CompletionNegativePair
open C977ChainBridge
set_option Elab.async false

theorem alternatives (C B : OpenSquare) (r : ℝ)
    (cs : C.s=-r) (cn : Normal C.c r) (bn : Normal B.c B.s) (sp : 0 < B.s)
    (side : 1 < C.side) (same : C.side=B.side)
    (cap : C.loU+C.side ≤ (47/20)*C.c-(33/20)*r)
    (center : C.Inside 2 2) (bottom : C.Inside 2 (3/2))
    (southwest : C.Inside (33/20) (33/20))
    (marker : B.Inside (33/20) (47/20)) (high : B.Inside 1 (12/5))
    (apart : ∀ x y, ¬(C.Inside x y ∧ B.Inside x y)) :
    C.loV+C.side ≤ lower B r C.c ∨ upper C (-B.s) B.c ≤ B.loV := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0 < C.c := by linarith only [cb.1]
  have bp : 0 < B.c := by linarith only [bb.1]
  have rBound : r ≤ 5/7 := by
    nlinarith only [cn.2.2,cb.1,cn.1,sq_nonneg (C.c-7/10),sq_nonneg (r-5/7)]
  have noCU (h : upper C C.c C.s ≤ lower B C.c C.s ∨
      upper B C.c C.s ≤ lower C C.c C.s) : False := by
    have own := strict_bounds C _ _ C.c C.s C.unit_normal center
    have other := strict_bounds B _ _ C.c C.s C.unit_normal marker
    have short := (short_projections C (7/10) (-(7/10)) (by norm_num)).2.1
    rw [cs] at own other short
    rcases h with forward | reverse
    · rw [cs] at forward
      nlinarith only [forward,own.2,other.1,cp,cn.1]
    · rw [(ownU C).1,cs] at reverse
      nlinarith only [reverse,other.2,cap,short,side]
  have noBU (h : upper C B.c B.s ≤ lower B B.c B.s ∨
      upper B B.c B.s ≤ lower C B.c B.s) : False := by
    rcases h with forward | reverse
    · have own := (strict_bounds C _ _ B.c B.s B.unit_normal center).2
      have other := (strict_bounds B _ _ B.c B.s B.unit_normal high).1
      nlinarith only [own,other,forward,bp,bn.2.1]
    · let alpha := B.c*C.c-B.s*r
      let k := B.c*r+B.s*C.c
      let F := 7/10-C.c-(7/20)*r^2-(3/20)*C.c*r
      let G := -(17/20)+r+(3/20)*r^2-(7/20)*C.c*r
      have ap : 0 ≤ alpha := by
        have one := mul_nonneg bp.le (sub_nonneg.mpr cn.2.1)
        have two := mul_nonneg cn.1 (sub_nonneg.mpr bn.2.1)
        dsimp [alpha]; nlinarith only [one,two]
      have kp : 0 < k := by
        dsimp [k]; nlinarith only [mul_nonneg bp.le cn.1,mul_pos sp cp]
      have support : lower C B.c B.s=alpha*C.loU+k*C.loV := by
        have raw := lower_negative_pos C r B.c B.s cs ap
          (show 0 ≤ B.c*r+B.s*C.c by dsimp [k] at kp; linarith only [kp])
        dsimp [alpha,k]; nlinarith only [raw]
      have ownV := bottom.2.2.1
      rw [cs,neg_neg] at ownV
      have first := mul_le_mul_of_nonneg_left
        (show C.loU ≤ (47/20)*C.c-(33/20)*r-1 by linarith only [cap,side]) ap
      have last := mul_lt_mul_of_pos_left
        (show C.loV < 2*r+(3/2)*C.c by linarith only [ownV]) kp
      have identity : alpha*((47/20)*C.c-(33/20)*r-1)+k*(2*r+(3/2)*C.c)-
          ((33/20)*B.c+(47/20)*B.s)=B.c*F+B.s*G := by
        dsimp [alpha,k,F,G]
        linear_combination ((47/20)*B.c+(3/2)*B.s)*cn.2.2
      have fn : F ≤ 0 := by
        dsimp [F]
        nlinarith only [cb.1,sq_nonneg r,mul_nonneg cp.le cn.1]
      have gn : G < 0 := by
        have product := mul_nonneg cn.1 (sub_nonneg.mpr cn.2.1)
        dsimp [G]
        nlinarith only [rBound,product,sq_nonneg r]
      have f := mul_nonpos_of_nonneg_of_nonpos bp.le fn
      have g := mul_neg_of_pos_of_neg sp gn
      have other := (strict_bounds B _ _ B.c B.s B.unit_normal marker).2
      rw [support] at reverse
      have endpoint : alpha*((47/20)*C.c-(33/20)*r-1)+k*(2*r+(3/2)*C.c) <
          (33/20)*B.c+(47/20)*B.s := by
        apply sub_neg.mp
        rw [identity]
        exact add_neg_of_nonpos_of_neg f g
      have supportBound := lt_trans (add_lt_add_of_le_of_lt first last) endpoint
      have markerBound : (33/20)*B.c+(47/20)*B.s < upper B B.c B.s := by
        convert other using 1 <;> ring
      exact (not_lt_of_ge (le_trans reverse supportBound.le)) markerBound
  have forward (x y : ℝ) (yp : 0 < y) (unit : x^2+y^2=1)
      (h : upper C x y ≤ lower B x y ∨ upper B x y ≤ lower C x y) :
      upper C x y ≤ lower B x y := by
    rcases h with h | h
    · exact h
    · have own := (strict_bounds C _ _ x y unit southwest).1
      have other := (strict_bounds B _ _ x y unit marker).2
      exfalso; nlinarith only [h,own,other,yp]
  have axes := CongruentSAT.faceSeparation_of_disjoint C B same apart
  change pairRadius C B ≤ |C.c*(centerX B-centerX C)+C.s*(centerY B-centerY C)| ∨
    pairRadius C B ≤ |-C.s*(centerX B-centerX C)+C.c*(centerY B-centerY C)| ∨
    pairRadius B C ≤ |B.c*(centerX B-centerX C)+B.s*(centerY B-centerY C)| ∨
    pairRadius B C ≤ |-B.s*(centerX B-centerX C)+B.c*(centerY B-centerY C)| at axes
  have sep (x y R : ℝ)
      (identity : supportRadius C x y+supportRadius B x y=R)
      (h : R ≤ |x*(centerX B-centerX C)+y*(centerY B-centerY C)|) :=
    separated C B x y (by rwa [identity])
  rcases axes with cu | cv | bu | bv
  · exact False.elim (noCU (sep _ _ _ (parallel_radius C B) cu))
  · have unit : (-C.s)^2+C.c^2=1 := by nlinarith only [C.unit_normal]
    have h : upper C (-C.s) C.c ≤ lower B (-C.s) C.c :=
      forward _ _ cp unit (sep _ _ _ (transverse_radius C B) cv)
    rw [(ownV C).2,cs,neg_neg] at h
    exact Or.inl h
  · have identity : supportRadius C B.c B.s+supportRadius B B.c B.s=pairRadius B C := by
      rw [add_comm]; exact parallel_radius B C
    exact False.elim (noBU (sep _ _ _ identity bu))
  · have identity : supportRadius C (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B C := by
      rw [add_comm]; exact transverse_radius B C
    have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
    have h := forward _ _ bp unit (sep _ _ _ identity bv)
    right; simpa only [(ownV B).1] using h

private theorem positive_v (C B : OpenSquare) (r : ℝ)
    (cs : C.s=-r) (cn : Normal C.c r) (bn : Normal B.c B.s)
    (side : 1 < B.side) (center : C.Inside 2 2) (west : C.Inside (3/2) 2)
    (low : B.Inside 1 (113/50))
    (modes : C.loV+C.side ≤ lower B r C.c ∨ upper C (-B.s) B.c ≤ B.loV) :
    3*B.c-(3/2)*B.s < B.loV+B.side := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0 < C.c := by linarith only [cb.1]
  have bp : 0 < B.c := by linarith only [bb.1]
  apply lt_of_not_ge
  intro cap
  rcases modes with cv | bv
  · let alpha := B.c*C.c-B.s*r
    let k := B.c*r+B.s*C.c
    have ap : 0 ≤ alpha := by
      have one := mul_nonneg bp.le (sub_nonneg.mpr cn.2.1)
      have two := mul_nonneg cn.1 (sub_nonneg.mpr bn.2.1)
      dsimp [alpha]; nlinarith only [one,two]
    have kp : 0 ≤ k := by dsimp [k]; exact add_nonneg (mul_nonneg bp.le cn.1) (mul_nonneg bn.1 cp.le)
    have formula := lower_pp B r C.c
      (show 0 ≤ r*B.c+C.c*B.s by dsimp [k] at kp; nlinarith only [kp])
      (show 0 ≤ -r*B.s+C.c*B.c by dsimp [alpha] at ap; nlinarith only [ap])
    rw [formula] at cv
    have first := mul_le_mul_of_nonneg_left
      (show B.loU ≤ B.c+(113/50)*B.s by linarith only [low.1]) kp
    have last := mul_le_mul_of_nonneg_left
      (show B.loV ≤ 3*B.c-(3/2)*B.s-1 by linarith only [cap,side]) ap
    have defect : 1-B.c ≤ (3/5)*B.s^2 := by
      have product := mul_nonneg (sub_nonneg.mpr bb.2.1)
        (show 0 ≤ 3*B.c-2 by linarith only [bb.1])
      nlinarith only [product,bn.2.2]
    have fn : 1-B.c-(37/50)*B.s^2-B.c*B.s/2 ≤ 0 := by
      nlinarith only [defect,sq_nonneg B.s,mul_nonneg bp.le bn.1]
    have gn : -1+B.s+B.s^2/2-(37/50)*B.c*B.s ≤ 0 := by
      have product := mul_nonneg bn.1 (sub_nonneg.mpr bn.2.1)
      nlinarith only [product,bb.2.2.2.1,sq_nonneg B.s]
    have f := mul_nonpos_of_nonneg_of_nonpos cp.le fn
    have g := mul_nonpos_of_nonneg_of_nonpos cn.1 gn
    have identity : k*(B.c+(113/50)*B.s)+alpha*(3*B.c-(3/2)*B.s-1)-2*(C.c+r)=
        C.c*(1-B.c-(37/50)*B.s^2-B.c*B.s/2)+
          r*(-1+B.s+B.s^2/2-(37/50)*B.c*B.s) := by
      dsimp [alpha,k]
      linear_combination (3*C.c+r)*bn.2.2
    have own := center.2.2.2
    rw [cs,neg_neg] at own
    have cvBound : C.loV+C.side ≤ k*B.loU+alpha*B.loV := by
      dsimp [k,alpha]; nlinarith only [cv]
    have endpoint : k*(B.c+(113/50)*B.s)+alpha*(3*B.c-(3/2)*B.s-1) ≤
        2*(C.c+r) := by
      apply sub_nonpos.mp
      rw [identity]
      exact add_nonpos f g
    have ownBound : 2*(C.c+r) < C.loV+C.side := by
      convert own using 1 <;> ring
    exact (not_lt_of_ge (le_trans cvBound (le_trans (add_le_add first last) endpoint))) ownBound
  · have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
    have own := (strict_bounds C _ _ (-B.s) B.c unit west).2
    nlinarith only [own,bv,cap,side,bb.2.1]

/-- Every support direction of the two actual squares is discharged. -/
theorem impossible (C B : OpenSquare) (r : ℝ)
    (cs : C.s=-r) (cn : Normal C.c r) (bn : Normal B.c B.s)
    (side : 1 < C.side) (same : C.side=B.side)
    (angle : 7/18 ≤ C981CompletionHalfAngle.half B.c B.s)
    (center : C.Inside 2 2) (west : C.Inside (3/2) 2) (bottom : C.Inside 2 (3/2))
    (southwest : C.Inside (33/20) (33/20))
    (missing : ¬ C.Inside (47/20) (33/20))
    (marker : B.Inside (33/20) (47/20))
    (low : B.Inside 1 (113/50)) (high : B.Inside 1 (12/5))
    (missingTop : ¬ B.Inside (3/2) 3) (missingCorner : ¬ B.Inside 1 3)
    (apart : ∀ x y, ¬(C.Inside x y ∧ B.Inside x y)) : False := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0 < C.c := by linarith only [cb.1]
  have bp : 0 < B.c := by linarith only [bb.1]
  have sp : 0 < B.s := by
    apply lt_of_not_ge
    intro no
    have zero : B.s=0 := le_antisymm no bn.1
    rw [zero] at angle
    norm_num [C981CompletionHalfAngle.half] at angle
  have sideB : 1 < B.side := by rwa [←same]
  have cap := C981CompletionNegativePair.central_cap C r cs cn center bottom missing
  have modes := alternatives C B r cs cn bn sp side same cap center bottom southwest marker high apart
  have vTop := positive_v C B r cs cn bn sideB center west low modes
  have upperU : B.loU+B.side ≤ (3/2)*B.c+3*B.s := by
    apply le_of_not_gt
    intro u
    apply missingTop
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [low.1,marker.2.2.1,u,vTop,bp,bn.1]
  have upperV : B.loV+B.side ≤ 3*B.c-B.s := by
    apply le_of_not_gt
    intro v
    apply missingCorner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high.1,high.2.2.1,marker.2.1,bn.2.1,v,bp,bn.1]
  let alpha := B.c*C.c-B.s*r
  let k := B.c*r+B.s*C.c
  have ap : 0 ≤ alpha := by
    have one := mul_nonneg bp.le (sub_nonneg.mpr cn.2.1)
    have two := mul_nonneg cn.1 (sub_nonneg.mpr bn.2.1)
    dsimp [alpha]; nlinarith only [one,two]
  have kp : 0 < k := by
    dsimp [k]; nlinarith only [mul_nonneg bp.le cn.1,mul_pos sp cp]
  rcases modes with cv | bv
  · let K := B.c+B.s-1-B.c*B.s/2
    let G := B.s-B.c-1/2-B.s^2/2
    have arcProduct := mul_nonneg (sub_nonneg.mpr bb.2.2.2.2.1)
      (sub_nonneg.mpr bb.2.2.2.2.2)
    have cross := mul_pos bp sp
    have kPositive : 0 < K := by dsimp [K]; nlinarith only [arcProduct,bn.2.2,cross]
    have gNegative : G ≤ 0 := by dsimp [G]; nlinarith only [bn.2.1,sq_nonneg B.s]
    have one := mul_neg_of_pos_of_neg cp (show -K < 0 by linarith only [kPositive])
    have two := mul_nonpos_of_nonneg_of_nonpos cn.1 gNegative
    have first := mul_le_mul_of_nonneg_left
      (show B.loU ≤ (3/2)*B.c+3*B.s-1 by linarith only [upperU,sideB]) kp.le
    have last := mul_le_mul_of_nonneg_left
      (show B.loV ≤ 3*B.c-B.s-1 by linarith only [upperV,sideB]) ap
    have identity : k*((3/2)*B.c+3*B.s-1)+alpha*(3*B.c-B.s-1)-2*(C.c+r)= -C.c*K+r*G := by
      dsimp [alpha,k,K,G]
      linear_combination (3*C.c+(3/2)*r)*bn.2.2
    have formula := lower_pp B r C.c
      (show 0 ≤ r*B.c+C.c*B.s by dsimp [k] at kp; nlinarith only [kp])
      (show 0 ≤ -r*B.s+C.c*B.c by dsimp [alpha] at ap; nlinarith only [ap])
    rw [formula] at cv
    have own := center.2.2.2
    rw [cs,neg_neg] at own
    have cvBound : C.loV+C.side ≤ k*B.loU+alpha*B.loV := by
      dsimp [k,alpha]; nlinarith only [cv]
    have endpoint : k*((3/2)*B.c+3*B.s-1)+alpha*(3*B.c-B.s-1) <
        2*(C.c+r) := by
      apply sub_neg.mp
      rw [identity]
      simpa only [mul_neg,neg_mul] using add_neg_of_neg_of_nonpos one two
    have ownBound : 2*(C.c+r) < C.loV+C.side := by
      convert own using 1 <;> ring
    exact (not_lt_of_ge (le_trans cvBound
      (le_trans (add_le_add first last) endpoint.le))) ownBound
  · let u := C.loU+C.side-2*(C.c-r)
    let v := C.loV+C.side-2*(C.c+r)
    have vp : 0 < v := by
      have own := center.2.2.2
      rw [cs,neg_neg] at own
      dsimp [v]; linarith only [own]
    have uCap : u ≤ (7/20)*(C.c+r) := by dsimp [u]; linarith only [cap]
    have support : upper C (-B.s) B.c = -k*C.loU+alpha*(C.loV+C.side) := by
      rw [upper_in_bands,cs]
      have first : (-B.s)*C.c+B.c*(-r)=-k := by dsimp [k]; ring
      have last : -(-B.s)*(-r)+B.c*C.c=alpha := by dsimp [alpha]; ring
      rw [first,last,abs_of_nonpos (neg_nonpos.mpr kp.le),abs_of_nonneg ap]
      ring
    have excess : upper C (-B.s) B.c=2*(B.c-B.s)+C.side*k-k*u+alpha*v := by
      rw [support]
      dsimp [alpha,k,u,v]
      linear_combination 2*(B.c-B.s)*cn.2.2
    have last := mul_nonneg ap vp.le
    rw [←same] at upperV
    have cut : 1 < B.c*(1-r*(1-(7/20)*(C.c+r)))+
        B.s*(1-C.c*(1-(7/20)*(C.c+r))) := by
      have lowerBound : 2*(B.c-B.s)+C.side*k-k*((7/20)*(C.c+r)) ≤
          upper C (-B.s) B.c := by
        calc
          _ ≤ 2*(B.c-B.s)+C.side*k-k*u :=
            sub_le_sub_left (mul_le_mul_of_nonneg_left uCap kp.le) _
          _ ≤ 2*(B.c-B.s)+C.side*k-k*u+alpha*v := le_add_of_nonneg_right last
          _ = upper C (-B.s) B.c := excess.symm
      have combined := le_trans (add_le_add_left (le_trans lowerBound bv) C.side) upperV
      have endpoint : C.side*(1+k) ≤ B.c+B.s+k*((7/20)*(C.c+r)) := by
        calc
          _ = (2*(B.c-B.s)+C.side*k-k*((7/20)*(C.c+r))+C.side)-
              (2*(B.c-B.s)-k*((7/20)*(C.c+r))) := by ring
          _ ≤ (3*B.c-B.s)-(2*(B.c-B.s)-k*((7/20)*(C.c+r))) :=
            sub_le_sub_right combined _
          _ = _ := by ring
      have strict : 1+k < C.side*(1+k) := by
        simpa only [one_mul] using mul_lt_mul_of_pos_right side
          (show 0 < 1+k by linarith only [kp])
      have identity : B.c*(1-r*(1-(7/20)*(C.c+r)))+
          B.s*(1-C.c*(1-(7/20)*(C.c+r))) =
          (B.c+B.s+k*((7/20)*(C.c+r)))-k := by
        dsimp [k]
        ring
      rw [identity]
      exact (lt_sub_iff_add_lt).mpr (lt_of_lt_of_le strict endpoint)
    exact C981CompletionAngularScalars.impossible C.c r B.c B.s cn bn angle cut

#print axioms impossible
end N12Compact.C981CompletionSteepPositivePair
