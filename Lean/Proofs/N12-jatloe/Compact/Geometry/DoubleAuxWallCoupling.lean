import Compact.Geometry.CentralWallEscape
import Compact.Geometry.DoubleAuxWallMargins
import Compact.Geometry.ABTransverse

/-! A wall owning both auxiliary heights cannot be replaced by a universal
stronger point. Instead its full square support excludes that point from
an escaping central elbow. Both squares and the exact outer exclusion
are retained; there is no angle grid or numerical geometric premise. -/
namespace N12Compact.DoubleAuxWallCoupling
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
set_option Elab.async false

private theorem faces (T : OpenSquare) (ha : 1 < T.side)
    (hc : 0 < T.c) (hs : 0 ≤ T.s)
    (marker : T.Inside 2 (1543/500)) (high : T.Inside (12/5) 3)
    (low : T.Inside (87/50) 3)
    (missingLow : ¬ T.Inside (8/5) 3)
    (missingInward : ¬ T.Inside 2 (113/50))
    (missingStrong : ¬ T.Inside (5/2) 3) :
    (8/5)*T.c+3*T.s ≤ T.loU ∧
      -(5/2)*T.s+3*T.c ≤ T.loV ∧
      T.loU < (5/2)*T.c+3*T.s ∧
      (5/2)*T.c+3*T.s < T.loU+T.side := by
  have wUhi : (8/5)*T.c+3*T.s < T.loU+T.side := by
    linarith only [low.2.1,hc]
  have wVlo : T.loV < -(8/5)*T.s+3*T.c := by
    linarith only [low.2.2.1,hs]
  have dUhi : 2*T.c+(113/50)*T.s < T.loU+T.side := by
    linarith only [high.2.1,hc,hs]
  have dVhi : -2*T.s+(113/50)*T.c < T.loV+T.side := by
    linarith only [marker.2.2.2,hc]
  have pUlo : T.loU < (5/2)*T.c+3*T.s := by
    linarith only [high.1,hc]
  have pVhi : -(5/2)*T.s+3*T.c < T.loV+T.side := by
    linarith only [low.2.2.2,hs]
  have wu : (8/5)*T.c+3*T.s ≤ T.loU := by
    apply le_of_not_gt
    intro below
    have wv : T.loV+T.side ≤ -(8/5)*T.s+3*T.c :=
      le_of_not_gt (fun h => missingLow ⟨by nlinarith only [below],
        by nlinarith only [wUhi],by nlinarith only [wVlo],by nlinarith only [h]⟩)
    have du : 2*T.c+(113/50)*T.s ≤ T.loU := by
      apply le_of_not_gt
      intro lower
      have dv : -2*T.s+(113/50)*T.c ≤ T.loV :=
        le_of_not_gt (fun h => missingInward ⟨by nlinarith only [lower],
          by nlinarith only [dUhi],by nlinarith only [h],by nlinarith only [dVhi]⟩)
      have gap := (short_projections T (-2/5) (37/50) (by norm_num)).2.2.2
      linarith only [dv,wv,gap,ha]
    have pu := (short_projections T (1/2) (37/50) (by norm_num)).2.1
    have pv := (short_projections T (9/10) 0 (by norm_num)).2.2.1
    exact missingStrong ⟨by nlinarith only [pUlo],
      by nlinarith only [du,pu,ha],by nlinarith only [wv,pv,ha],
      by nlinarith only [pVhi]⟩
  have pUhi : (5/2)*T.c+3*T.s < T.loU+T.side := by
    have gap := (short_projections T (9/10) 0 (by norm_num)).2.1
    linarith only [wu,gap,ha]
  have pv : -(5/2)*T.s+3*T.c ≤ T.loV :=
    le_of_not_gt (fun h => missingStrong ⟨by nlinarith only [pUlo],
      by nlinarith only [pUhi],by nlinarith only [h],by nlinarith only [pVhi]⟩)
  exact ⟨wu,pv,pUlo,pUhi⟩

/-- The missing strong point is proved on the central square, using the
actual neighboring wall square rather than asserting that wall owns it. -/
theorem missing_strong (A T : OpenSquare) (ha : 1 < A.side)
    (same : A.side=T.side) (box : InsideContainer T)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (narrow : 4*A.s ≤ A.c)
    (p : A.Inside 2 (113/50)) (m : A.Inside (47/20) (47/20))
    (lowerBound : 2*A.c+2*A.s ≤ A.loU)
    (marker : T.Inside 2 (1543/500)) (high : T.Inside (12/5) 3)
    (low : T.Inside (87/50) 3) (missingLow : ¬ T.Inside (8/5) 3)
    (apart : ∀ x y, ¬ (A.Inside x y ∧ T.Inside x y)) :
    ¬ A.Inside (5/2) 3 := by
  intro owned
  obtain ⟨W,wc,ws,side,inside,_⟩ := ClosedFrames.positive_frame T
  have hW : 1 < W.side := by simpa only [side,←same] using ha
  have sameW : A.side=W.side := same.trans side.symm
  have wm := (inside _ _).mpr marker
  have wh := (inside _ _).mpr high
  have wl := (inside _ _).mpr low
  have disjoint : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y) :=
    fun x y h => apart x y ⟨h.1,(inside x y).mp h.2⟩
  have f := faces W hW wc ws wm wh wl
    (fun h => missingLow ((inside _ _).mp h))
    (fun h => disjoint _ _ ⟨p,h⟩) (fun h => disjoint _ _ ⟨owned,h⟩)
  have wall : W.s*(W.loU+W.side)+W.c*(W.loV+W.side) ≤ 4 := by
    have wb : InsideContainer W := fun x y h => box x y ((inside x y).mp h)
    have bound := CentralWallEscape.right_wall (pullSwap W) (container_pullSwap W wb)
    dsimp [pullSwap] at bound
    linarith only [bound]
  have positiveSum : 0 < W.c+W.s := by linarith only [wc,ws]
  have weightedU := mul_le_mul_of_nonneg_left f.1 ws
  have weightedV := mul_le_mul_of_nonneg_left f.2.1 wc.le
  have strictSide := mul_pos (sub_pos.mpr hW) positiveSum
  have delta : 0 < 1+(9/10)*W.c*W.s-W.c-W.s := by
    nlinarith only [weightedU,weightedV,wall,strictSide,W.unit_normal]
  have margins := DoubleAuxWallMargins.bounds A.c A.s W.c W.s hc hs
    A.unit_normal narrow wc ws W.unit_normal delta
  let d := A.c*W.c+A.s*W.s
  let k := A.c*W.s-A.s*W.c
  have dp : 0 < d := add_pos_of_pos_of_nonneg (mul_pos hc wc) (mul_nonneg hs ws)
  have kp : 0 < k := margins.1
  have minFormula : lower W (-A.s) A.c=k*W.loU+d*W.loV := by
    dsimp [lower,supportRadius,centerX,centerY]
    rw [abs_of_nonneg (show 0 ≤ -A.s*W.c+A.c*W.s by dsimp [k] at kp; linarith only [kp]),
      abs_of_nonneg (show 0 ≤ -(-A.s)*W.s+A.c*W.c by dsimp [d] at dp; linarith only [dp])]
    dsimp [d,k]; ring
  have maxFormula : upper A (-W.s) W.c= -k*A.loU+d*(A.loV+A.side) := by
    dsimp [upper,supportRadius,centerX,centerY]
    rw [abs_of_nonpos (show -W.s*A.c+W.c*A.s ≤ 0 by dsimp [k] at kp; linarith only [kp]),
      abs_of_nonneg (show 0 ≤ -(-W.s)*A.s+W.c*A.c by dsimp [d] at dp; linarith only [dp])]
    dsimp [d,k]; ring
  have minUpper : lower W (-A.s) A.c ≤ -(5/2)*A.s+3*A.c := by
    have hwall := mul_le_mul_of_nonneg_left wall dp.le
    have hlu := mul_le_mul_of_nonneg_left f.1 hs
    have hside := mul_pos (sub_pos.mpr hW) (mul_pos dp positiveSum)
    have identity : W.c*(k*W.loU+d*W.loV) =
        d*(W.s*(W.loU+W.side)+W.c*(W.loV+W.side))-
          A.s*W.loU-W.side*d*(W.c+W.s) := by
      calc
        _ = d*(W.s*(W.loU+W.side)+W.c*(W.loV+W.side))-
            A.s*(W.c^2+W.s^2)*W.loU-W.side*d*(W.c+W.s) := by
              dsimp [d,k]; ring
        _ = _ := by rw [W.unit_normal]; ring
    rw [minFormula]
    apply (mul_le_mul_iff_right₀ wc).mp
    dsimp [d] at hwall hside
    dsimp [d,k] at identity
    nlinarith only [hwall,hlu,hside,identity,margins.2.1]
  have maxLower : W.loV < upper A (-W.s) W.c := by
    have up := mul_lt_mul_of_pos_left p.1 kp
    have vp := mul_lt_mul_of_pos_left owned.2.2.2 dp
    have pointIdentity : -k*(2*A.c+(113/50)*A.s)+d*(-(5/2)*A.s+3*A.c) =
        -(5/2)*W.s+3*W.c+k*((1/2)*A.c+(37/50)*A.s) := by
      calc
        _ = (A.c^2+A.s^2)*(-(5/2)*W.s+3*W.c)+
            k*((1/2)*A.c+(37/50)*A.s) := by dsimp [d,k]; ring
        _ = _ := by rw [A.unit_normal,one_mul]
    have ownLower : -(5/2)*W.s+3*W.c+k*((1/2)*A.c+(37/50)*A.s) <
        upper A (-W.s) W.c := by
      rw [maxFormula]
      nlinarith only [up,vp,pointIdentity]
    have cap : W.c*W.loV ≤ W.c*(-(5/2)*W.s+3*W.c)+
        (1+(9/10)*W.c*W.s-W.c-W.s) := by
      nlinarith only [wall,weightedU,strictSide,W.unit_normal]
    have supportMargin := margins.2.2
    change 0 ≤ W.c*k*((1/2)*A.c+(37/50)*A.s)-
      (1+(9/10)*W.c*W.s-W.c-W.s) at supportMargin
    have product := mul_lt_mul_of_pos_left ownLower wc
    exact (mul_lt_mul_iff_right₀ wc).mp (by nlinarith only [cap,supportMargin,product])
  have cu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,hc]
  have highUlo : A.loU < (12/5)*A.c+3*A.s := by
    linarith only [m.1,hc,hs]
  have highUhi : (12/5)*A.c+3*A.s < A.loU+A.side := by
    linarith only [lowerBound,narrow,cu,ha]
  have axes := CongruentSAT.faceSeparation_of_disjoint A W sameW disjoint
  change pairRadius A W ≤ |A.c*(centerX W-centerX A)+A.s*(centerY W-centerY A)| ∨
    pairRadius A W ≤ |-A.s*(centerX W-centerX A)+A.c*(centerY W-centerY A)| ∨
    pairRadius W A ≤ |W.c*(centerX W-centerX A)+W.s*(centerY W-centerY A)| ∨
    pairRadius W A ≤ |-W.s*(centerX W-centerX A)+W.c*(centerY W-centerY A)| at axes
  have split (nx ny radius : ℝ)
      (identity : supportRadius A nx ny+supportRadius W nx ny=radius)
      (sep : radius ≤ |nx*(centerX W-centerX A)+ny*(centerY W-centerY A)|) :=
    separated A W nx ny (by rwa [identity])
  rcases axes with au | av | wu | wv
  · have sep := split A.c A.s _ (parallel_radius A W) au
    rw [(ownU A).1,(ownU A).2] at sep
    have bounds := strict_bounds W _ _ A.c A.s A.unit_normal wh
    rcases sep with h | h <;> linarith only [h,bounds.1,bounds.2,highUlo,highUhi]
  · have sep := split (-A.s) A.c _ (transverse_radius A W) av
    rw [(ownV A).1,(ownV A).2] at sep
    have bounds := strict_bounds W _ _ (-A.s) A.c
      (by nlinarith only [A.unit_normal]) wh
    rcases sep with h | h
    · linarith only [h,minUpper,owned.2.2.2]
    · linarith only [h,bounds.2,owned.2.2.1,hs]
  · have identity : supportRadius A W.c W.s+supportRadius W W.c W.s=pairRadius W A := by
      rw [add_comm]; exact parallel_radius W A
    have sep := split W.c W.s _ identity wu
    rw [(ownU W).1,(ownU W).2] at sep
    have bounds := strict_bounds A _ _ W.c W.s W.unit_normal owned
    rcases sep with h | h <;> linarith only [h,bounds.1,bounds.2,f.2.2.1,f.2.2.2]
  · have identity : supportRadius A (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W A := by
      rw [add_comm]; exact transverse_radius W A
    have sep := split (-W.s) W.c _ identity wv
    rw [(ownV W).1,(ownV W).2] at sep
    have bounds := strict_bounds A _ _ (-W.s) W.c
      (by nlinarith only [W.unit_normal]) owned
    rcases sep with h | h
    · linarith only [h,maxLower]
    · linarith only [h,bounds.1,f.2.1,W.side_pos]

#print axioms missing_strong
end N12Compact.DoubleAuxWallCoupling
