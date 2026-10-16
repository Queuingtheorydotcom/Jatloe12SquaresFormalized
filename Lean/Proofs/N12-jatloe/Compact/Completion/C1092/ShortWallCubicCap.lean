import Compact.Completion.C1092.ShortWallNarrow
import Compact.Completion.C1092.ShortWallPenalty
import Compact.Completion.C1092.ShortWallAllowance

/-! The physical top wall gives a cubic cap on the same central upper
face in both surviving separating-axis comparisons. The physical wall
center cut and every first-quadrant wall orientation are retained. -/
namespace N12Compact.C1092ShortWallCubicCap
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092ShortWallScalars C1092ShortWallNarrow
set_option Elab.async false

theorem cap (A T : OpenSquare) (ha : 1 < A.side) (same : A.side=T.side)
    (cn : Normal A.c A.s) (data : NarrowData A)
    (box : InsideContainer T) (cut : 2 ≤ centerX T)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20)) (high : T.Inside (1197/500) 3)
    (apart : ∀ x y, ¬ (A.Inside x y ∧ T.Inside x y)) :
    A.loV+A.side ≤ 3*A.c-(5/2)*A.s+allowance A.c A.s := by
  classical
  have cb := normal_bounds cn
  have nb := narrow_bounds cn data.narrow.le
  have cp : 0 < A.c := by linarith only [cb.1]
  obtain ⟨W,wc,ws,side,hX,hY,inside⟩ := exists_positive_frame T
  have sameW : A.side=W.side := same.trans side.symm
  have wa : 1 < W.side := by simpa only [←sameW] using ha
  have wb : InsideContainer W := fun x y h => box x y ((inside x y).mp h)
  have wx : 2 ≤ centerX W := by simpa only [hX] using cut
  have wh := (inside _ _).mpr high
  have disjoint : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y) :=
    fun x y h => apart x y ⟨h.1,(inside x y).mp h.2⟩
  have sumpos : 0 < W.c+W.s := by nlinarith only [W.unit_normal,wc,ws]
  have wall := CentralWallEscape.right_wall (pullSwap W) (container_pullSwap W wb)
  have wallY : centerY W+W.side*(W.c+W.s)/2 ≤ 4 := by
    dsimp [pullSwap,centerY] at wall ⊢
    linarith only [wall]
  let d := A.c*W.c+A.s*W.s
  let k := A.c*W.s-A.s*W.c
  have dp : 0 < d := by
    have first := mul_pos data.sine_pos sumpos
    have second := mul_nonneg wc (sub_nonneg.mpr cn.2.1)
    dsimp [d]
    nlinarith only [first,second]
  have absDot : |(-A.s)*W.c+A.c*W.s|=|k| := by
    congr 1
    dsimp [k]
    ring
  have absCross : |-(-A.s)*W.s+A.c*W.c|=d := by
    rw [abs_of_nonneg (by dsimp [d] at dp; nlinarith only [dp] :
      0 ≤ -(-A.s)*W.s+A.c*W.c)]
    dsimp [d]
    ring
  have formula : lower W (-A.s) A.c =
      -A.s*centerX W+A.c*centerY W-W.side*(d+|k|)/2 := by
    dsimp [lower,supportRadius]
    rw [absDot,absCross]
    ring
  have centerYBound := mul_le_mul_of_nonneg_left wallY cp.le
  have centerXBound := mul_le_mul_of_nonneg_left wx cn.1
  have penalty := C1092ShortWallPenalty.penalty cn wc ws W.unit_normal
  have positive : 0 < 1+A.c^2+A.c*A.s := by
    nlinarith only [sq_nonneg A.c,mul_nonneg cp.le cn.1]
  have strict := mul_pos (sub_pos.mpr wa) positive
  have penaltyWeight := mul_nonneg W.side_pos.le (sub_nonneg.mpr penalty)
  have lowerCap : lower W (-A.s) A.c <
      3*A.c-(5/2)*A.s+allowance A.c A.s := by
    dsimp [d,k] at formula
    dsimp [allowance]
    nlinarith only [formula,centerYBound,centerXBound,strict,penaltyWeight]
  have ownVcenter := (center_coordinates W).2
  have ownYBound := mul_le_mul_of_nonneg_left wallY wc
  have ownXBound := mul_le_mul_of_nonneg_left wx ws
  have ownPositive : 0 < 1+W.c^2+W.c*W.s := by
    nlinarith only [sq_nonneg W.c,mul_nonneg wc ws]
  have ownStrict := mul_pos (sub_pos.mpr wa) ownPositive
  have ownCap : W.loV < 3*W.c-(5/2)*W.s+allowance W.c W.s := by
    dsimp [allowance]
    nlinarith only [ownVcenter,ownYBound,ownXBound,ownStrict]
  have highUlo : A.loU < A.c*(1197/500)+A.s*3 := by
    linarith only [m.1,cp,cn.1]
  have highUhi : A.c*(1197/500)+A.s*3 < A.loU+A.side := by
    linarith only [data.high.2.1,cp]
  have highVlo : A.loV < -A.s*(1197/500)+A.c*3 := by
    linarith only [q.2.2.1,cp,cn.2.1]
  have strip : ∃ x y, A.Inside x y ∧
      W.loU < W.c*x+W.s*y ∧ W.c*x+W.s*y < W.loU+W.side := by
    by_cases low : W.c*(5/2)+W.s*3 < W.loU+W.side
    · exact ⟨5/2,3,data.high,by linarith only [wh.1,wc],low⟩
    · have short := short_projections W (5/2-47/20) (3-47/20) (by norm_num)
      refine ⟨47/20,47/20,m,?_,?_⟩
      · linarith only [low,wa,short.2.1]
      · linarith only [wh.2.1,wc,ws,sumpos]
  have axes := CongruentSAT.faceSeparation_of_disjoint A W sameW disjoint
  change pairRadius A W ≤ |A.c*(centerX W-centerX A)+A.s*(centerY W-centerY A)| ∨
    pairRadius A W ≤ |-A.s*(centerX W-centerX A)+A.c*(centerY W-centerY A)| ∨
    pairRadius W A ≤ |W.c*(centerX W-centerX A)+W.s*(centerY W-centerY A)| ∨
    pairRadius W A ≤ |-W.s*(centerX W-centerX A)+W.c*(centerY W-centerY A)| at axes
  have split (nx ny radius : ℝ)
      (identity : supportRadius A nx ny+supportRadius W nx ny=radius)
      (sep : radius ≤ |nx*(centerX W-centerX A)+ny*(centerY W-centerY A)|) :=
    separated A W nx ny (by rwa [identity])
  have remaining : A.loV+A.side ≤ lower W (-A.s) A.c ∨
      upper A (-W.s) W.c ≤ W.loV := by
    rcases axes with au | av | wu | wv
    · have sep := split A.c A.s _ (parallel_radius A W) au
      rw [(ownU A).1,(ownU A).2] at sep
      have bounds := strict_bounds W _ _ A.c A.s A.unit_normal wh
      rcases sep with sep | sep <;> exfalso <;>
        linarith only [sep,bounds.1,bounds.2,highUlo,highUhi]
    · have sep := split (-A.s) A.c _ (transverse_radius A W) av
      rw [(ownV A).1,(ownV A).2] at sep
      rcases sep with forward | reverse
      · exact Or.inl forward
      · have bounds := strict_bounds W _ _ (-A.s) A.c
          (by nlinarith only [A.unit_normal]) wh
        exfalso
        linarith only [reverse,bounds.2,highVlo]
    · have identity : supportRadius A W.c W.s+supportRadius W W.c W.s=pairRadius W A := by
        rw [add_comm]
        exact parallel_radius W A
      have sep := split W.c W.s _ identity wu
      rw [(ownU W).1,(ownU W).2] at sep
      obtain ⟨x,y,owned,low,high⟩ := strip
      have bounds := strict_bounds A _ _ W.c W.s W.unit_normal owned
      rcases sep with sep | sep <;> exfalso <;>
        linarith only [sep,bounds.1,bounds.2,low,high]
    · have identity : supportRadius A (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W A := by
        rw [add_comm]
        exact transverse_radius W A
      have sep := split (-W.s) W.c _ identity wv
      rw [(ownV W).1,(ownV W).2] at sep
      rcases sep with forward | reverse
      · exact Or.inr forward
      · have bounds := strict_bounds A _ _ (-W.s) W.c
          (by nlinarith only [W.unit_normal]) data.high
        exfalso
        linarith only [reverse,bounds.1,wh.2.2.2,ws]
  rcases remaining with axis | axis
  · exact le_trans axis lowerCap.le
  · let delta := A.loV+A.side-(3*A.c-(5/2)*A.s)
    let L := (5/2)*A.c+3*A.s-A.loU
    let J := A.loU+A.side-((5/2)*A.c+3*A.s)
    have Lbound : 12/25 < L := by dsimp [L]; linarith only [p.1,nb.1,cn.1]
    have Jbound : 1/4 < J := by
      dsimp [J]
      linarith only [data.escape,ha,cb.2.1,nb.2.1]
    have upperFormula : upper A (-W.s) W.c =
        -k*(A.loU+A.side/2)+d*(A.loV+A.side/2)+A.side*(|k|+d)/2 := by
      dsimp [upper,supportRadius,centerX,centerY,d,k]
      rw [abs_of_nonneg (show 0 ≤ -(-W.s)*A.s+W.c*A.c by
        dsimp [d] at dp; nlinarith only [dp])]
      have negative : (-W.s)*A.c+W.c*A.s=-(A.c*W.s-A.s*W.c) := by ring
      rw [negative,abs_neg]
      ring
    by_cases order : 0 ≤ k
    · have comparison := C1092ShortWallAllowance.above cn data.narrow.le wc ws
        W.unit_normal order
      change allowance W.c W.s ≤ d*allowance A.c A.s+(7/20)*k at comparison
      have exactSupport : upper A (-W.s) W.c =
          3*W.c-(5/2)*W.s+d*delta+k*L := by
        rw [upperFormula,abs_of_nonneg order]
        dsimp [d,k,delta,L]
        linear_combination (3*W.c-(5/2)*W.s)*A.unit_normal
      have loss := mul_nonneg order
        (show 0 ≤ L-7/20 by linarith only [Lbound])
      have difference : delta ≤ allowance A.c A.s := by
        have scaled : d*(delta-allowance A.c A.s) ≤ 0 := by
          have gap0 : upper A (-W.s) W.c-
              (3*W.c-(5/2)*W.s+allowance W.c W.s) ≤ 0 :=
            sub_nonpos.mpr (axis.trans ownCap.le)
          have gap1 : allowance W.c W.s-(d*allowance A.c A.s+(7/20)*k) ≤ 0 :=
            sub_nonpos.mpr comparison
          calc
            d*(delta-allowance A.c A.s) =
                (upper A (-W.s) W.c-(3*W.c-(5/2)*W.s+allowance W.c W.s))+
                (allowance W.c W.s-(d*allowance A.c A.s+(7/20)*k))-
                k*(L-7/20) := by rw [exactSupport]; ring
            _ ≤ 0 := sub_nonpos.mpr ((add_nonpos gap0 gap1).trans loss)
        have nonpos : delta-allowance A.c A.s ≤ 0 :=
          (mul_le_mul_iff_right₀ dp).mp (by simpa only [mul_zero] using scaled)
        linarith only [nonpos]
      dsimp [delta] at difference
      linarith only [difference]
    · have reversed : k ≤ 0 := (lt_of_not_ge order).le
      have comparison := C1092ShortWallAllowance.below cn data.narrow.le wc ws
        W.unit_normal reversed
      change allowance W.c W.s ≤ d*allowance A.c A.s-k/200 at comparison
      have exactSupport : upper A (-W.s) W.c =
          3*W.c-(5/2)*W.s+d*delta-k*J := by
        rw [upperFormula,abs_of_nonpos reversed]
        dsimp [d,k,delta,J]
        linear_combination (3*W.c-(5/2)*W.s)*A.unit_normal
      have loss := mul_nonneg (show 0 ≤ -k by linarith only [reversed])
        (show 0 ≤ J-1/200 by linarith only [Jbound])
      have difference : delta ≤ allowance A.c A.s := by
        have scaled : d*(delta-allowance A.c A.s) ≤ 0 := by
          have gap0 : upper A (-W.s) W.c-
              (3*W.c-(5/2)*W.s+allowance W.c W.s) ≤ 0 :=
            sub_nonpos.mpr (axis.trans ownCap.le)
          have gap1 : allowance W.c W.s-(d*allowance A.c A.s-k/200) ≤ 0 :=
            sub_nonpos.mpr comparison
          calc
            d*(delta-allowance A.c A.s) =
                (upper A (-W.s) W.c-(3*W.c-(5/2)*W.s+allowance W.c W.s))+
                (allowance W.c W.s-(d*allowance A.c A.s-k/200))-
                (-k)*(J-1/200) := by rw [exactSupport]; ring
            _ ≤ 0 := sub_nonpos.mpr ((add_nonpos gap0 gap1).trans loss)
        have nonpos : delta-allowance A.c A.s ≤ 0 :=
          (mul_le_mul_iff_right₀ dp).mp (by simpa only [mul_zero] using scaled)
        linarith only [nonpos]
      dsimp [delta] at difference
      linarith only [difference]

#print axioms cap
end N12Compact.C1092ShortWallCubicCap
