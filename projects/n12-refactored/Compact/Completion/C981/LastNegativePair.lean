import Compact.Completion.C981.SteepPositivePair
import Compact.Completion.C981.LastScalars

/-! The full actual two-square negative-central ending for the final two
C981 vectors. Its two new isolated foreign points strengthen the correlated
support cut exactly as in C981-LAST-TWO-CYCLES Theorem2. -/
namespace N12Compact.C981CompletionLastNegativePair
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C981CompletionSupportForms C981CompletionNegativePair C977ChainBridge
set_option Elab.async false

private theorem positive_v (C B : OpenSquare) (r : ℝ)
    (cs : C.s=-r) (cn : Normal C.c r) (bn : Normal B.c B.s)
    (side : 1 < B.side) (center : C.Inside 2 2) (west : C.Inside (3/2) 2)
    (low : B.Inside 1 (113/50))
    (modes : C.loV+C.side ≤ lower B r C.c ∨ upper C (-B.s) B.c ≤ B.loV) :
    3*B.c-(8/5)*B.s < B.loV+B.side := by
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
      (show B.loV ≤ 3*B.c-(8/5)*B.s-1 by linarith only [cap,side]) ap
    have defect : 1-B.c ≤ (3/5)*B.s^2 := by
      have product := mul_nonneg (sub_nonneg.mpr bb.2.1)
        (show 0 ≤ 3*B.c-2 by linarith only [bb.1])
      nlinarith only [product,bn.2.2]
    have fn : 1-B.c-(37/50)*B.s^2-(3/5)*B.c*B.s ≤ 0 := by
      nlinarith only [defect,sq_nonneg B.s,mul_nonneg bp.le bn.1]
    have gn : -1+B.s+(3/5)*B.s^2-(37/50)*B.c*B.s ≤ 0 := by
      have product := mul_nonneg bn.1 (sub_nonneg.mpr bn.2.1)
      nlinarith only [product,bb.2.2.2.1,sq_nonneg B.s]
    have f := mul_nonpos_of_nonneg_of_nonpos cp.le fn
    have g := mul_nonpos_of_nonneg_of_nonpos cn.1 gn
    have identity : k*(B.c+(113/50)*B.s)+alpha*(3*B.c-(8/5)*B.s-1)-2*(C.c+r)=
        C.c*(1-B.c-(37/50)*B.s^2-(3/5)*B.c*B.s)+
          r*(-1+B.s+(3/5)*B.s^2-(37/50)*B.c*B.s) := by
      dsimp [alpha,k]
      linear_combination (3*C.c+r)*bn.2.2
    have own := center.2.2.2
    rw [cs,neg_neg] at own
    have cvBound : C.loV+C.side ≤ k*B.loU+alpha*B.loV := by
      dsimp [k,alpha]; nlinarith only [cv]
    have endpoint : k*(B.c+(113/50)*B.s)+alpha*(3*B.c-(8/5)*B.s-1) ≤
        2*(C.c+r) := by
      apply sub_nonpos.mp
      rw [identity]
      exact add_nonpos f g
    have ownBound : 2*(C.c+r) < C.loV+C.side := by
      convert own using 1 <;> ring
    exact (not_lt_of_ge (le_trans cvBound (le_trans (add_le_add first last) endpoint))) ownBound
  · have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
    have own := (strict_bounds C _ _ (-B.s) B.c unit west).2
    linarith only [own,bv,cap,side,bb.2.1,bn.1]

theorem impossible (C B : OpenSquare) (r : ℝ)
    (cs : C.s=-r) (cn : Normal C.c r) (bn : Normal B.c B.s)
    (side : 1 < C.side) (same : C.side=B.side)
    (angle : 1/2 ≤ B.s)
    (center : C.Inside 2 2) (west : C.Inside (3/2) 2) (bottom : C.Inside 2 (3/2))
    (southwest : C.Inside (33/20) (33/20))
    (missing : ¬ C.Inside (47/20) (33/20))
    (marker : B.Inside (33/20) (47/20))
    (low : B.Inside 1 (113/50)) (high : B.Inside 1 (12/5))
    (missingTop : ¬ B.Inside (8/5) 3) (missingCorner : ¬ B.Inside 1 3)
    (missingD : ¬ C.Inside (113/50) 2)
    (missingJ : ¬ C.Inside (113/50) 1)
    (apart : ∀ x y, ¬(C.Inside x y ∧ B.Inside x y)) : False := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0 < C.c := by linarith only [cb.1]
  have bp : 0 < B.c := by linarith only [bb.1]
  have sp : 0 < B.s := by linarith only [angle]
  have sideB : 1 < B.side := by rwa [←same]
  have cap := C981CompletionNegativePair.central_cap C r cs cn center bottom missing
  have modes := C981CompletionSteepPositivePair.alternatives C B r cs cn bn sp side same cap center bottom southwest marker high apart
  have vTop := positive_v C B r cs cn bn sideB center west low modes
  have upperU : B.loU+B.side ≤ (8/5)*B.c+3*B.s := by
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
  · let K := B.c+B.s-1-(3/5)*B.c*B.s
    let G := B.s-B.c-2/5-(3/5)*B.s^2
    have arcProduct := mul_nonneg (sub_nonneg.mpr bb.2.2.2.2.1)
      (sub_nonneg.mpr bb.2.2.2.2.2)
    have cross := mul_pos bp sp
    have kPositive : 0 < K := by dsimp [K]; nlinarith only [arcProduct,bn.2.2,cross]
    have gNegative : G ≤ 0 := by dsimp [G]; nlinarith only [bn.2.1,sq_nonneg B.s]
    have one := mul_neg_of_pos_of_neg cp (show -K < 0 by linarith only [kPositive])
    have two := mul_nonpos_of_nonneg_of_nonpos cn.1 gNegative
    have first := mul_le_mul_of_nonneg_left
      (show B.loU ≤ (8/5)*B.c+3*B.s-1 by linarith only [upperU,sideB]) kp.le
    have last := mul_le_mul_of_nonneg_left
      (show B.loV ≤ 3*B.c-B.s-1 by linarith only [upperV,sideB]) ap
    have identity : k*((8/5)*B.c+3*B.s-1)+alpha*(3*B.c-B.s-1)-2*(C.c+r)= -C.c*K+r*G := by
      dsimp [alpha,k,K,G]
      linear_combination (3*C.c+(8/5)*r)*bn.2.2
    have formula := lower_pp B r C.c
      (show 0 ≤ r*B.c+C.c*B.s by dsimp [k] at kp; nlinarith only [kp])
      (show 0 ≤ -r*B.s+C.c*B.c by dsimp [alpha] at ap; nlinarith only [ap])
    rw [formula] at cv
    have own := center.2.2.2
    rw [cs,neg_neg] at own
    have cvBound : C.loV+C.side ≤ k*B.loU+alpha*B.loV := by
      dsimp [k,alpha]; nlinarith only [cv]
    have endpoint : k*((8/5)*B.c+3*B.s-1)+alpha*(3*B.c-B.s-1) <
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
    have cut_of_cap (q : ℝ) (uq : u ≤ q) : 1 < B.c+B.s-k+k*q := by
      have lowerBound : 2*(B.c-B.s)+C.side*k-k*q ≤ upper C (-B.s) B.c := by
        calc
          _ ≤ 2*(B.c-B.s)+C.side*k-k*u :=
            sub_le_sub_left (mul_le_mul_of_nonneg_left uq kp.le) _
          _ ≤ 2*(B.c-B.s)+C.side*k-k*u+alpha*v := le_add_of_nonneg_right last
          _ = upper C (-B.s) B.c := excess.symm
      have combined := le_trans (add_le_add_right (le_trans lowerBound bv) C.side) upperV
      have endpoint : C.side*(1+k) ≤ B.c+B.s+k*q := by
        calc
          _ = (2*(B.c-B.s)+C.side*k-k*q+C.side)-(2*(B.c-B.s)-k*q) := by ring
          _ ≤ (3*B.c-B.s)-(2*(B.c-B.s)-k*q) := sub_le_sub_right combined _
          _ = _ := by ring
      have strict : 1+k < C.side*(1+k) := by
        simpa only [one_mul] using mul_lt_mul_of_pos_right side
          (show 0 < 1+k by linarith only [kp])
      have gap : 1 < (B.c+B.s+k*q)-k :=
        (lt_sub_iff_add_lt).mpr (lt_of_lt_of_le strict endpoint)
      convert gap using 1 <;> ring
    have cut : 1 < B.c*(1-r*(1-(7/20)*(C.c+r)))+
        B.s*(1-C.c*(1-(7/20)*(C.c+r))) := by
      convert cut_of_cap ((7/20)*(C.c+r)) uCap using 1 <;> dsimp [k] <;> ring
    have pointCap : u ≤ (13/50)*C.c+r := by
      apply le_of_not_gt
      intro no
      have dLowU : C.loU < (113/50)*C.c-2*r := by
        have own := center.1
        rw [cs] at own
        linarith only [own,cp]
      have dLowV : C.loV < (113/50)*r+2*C.c := by
        have own := center.2.2.1
        rw [cs,neg_neg] at own
        linarith only [own,cn.1]
      have dHighU : (113/50)*C.c-2*r < C.loU+C.side := by
        dsimp [u] at no
        linarith only [no,cn.1]
      have dFace : C.loV+C.side ≤ (113/50)*r+2*C.c := by
        apply le_of_not_gt
        intro high
        apply missingD
        refine ⟨?_,?_,?_,?_⟩ <;> rw [cs] <;>
          linarith only [dLowU,dHighU,dLowV,high]
      have jLowU : C.loU < (113/50)*C.c-r := by
        have own := center.1
        rw [cs] at own
        linarith only [own,cp,cn.1]
      have jHighU : (113/50)*C.c-r < C.loU+C.side := by
        dsimp [u] at no
        linarith only [no]
      have jHighV : (113/50)*r+C.c < C.loV+C.side := by
        have own := center.2.2.2
        rw [cs,neg_neg] at own
        linarith only [own,cp,cn.2.1]
      have jFace : (113/50)*r+C.c ≤ C.loV := by
        apply le_of_not_gt
        intro low
        apply missingJ
        refine ⟨?_,?_,?_,?_⟩ <;> rw [cs] <;>
          linarith only [jLowU,jHighU,low,jHighV]
      linarith only [dFace,jFace,side,cb.2.1]
    have pointCut : 1 < B.c*(1-r+(13/50)*C.c*r+r^2)+
        B.s*(1-C.c+(13/50)*C.c^2+C.c*r) := by
      convert cut_of_cap ((13/50)*C.c+r) pointCap using 1 <;> dsimp [k] <;> ring
    exact C981CompletionLastScalars.negative_impossible C.c r B.c B.s cn bn angle cut pointCut

#print axioms impossible
end N12Compact.C981CompletionLastNegativePair
