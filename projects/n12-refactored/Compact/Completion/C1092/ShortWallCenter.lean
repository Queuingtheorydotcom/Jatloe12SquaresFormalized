import Compact.Completion.C1092.ShortWallCubicCap
import Compact.Completion.C1092.ShortWallRightAxes
import Compact.Completion.C1092.ShortWallRightMargin

/-! The complete physical two-wall center theorem. The exact short
endpoints, all central orientations, all signed wall orientations and
weak support contacts are retained. No auxiliary assignment is assumed. -/
namespace N12Compact.C1092ShortWallCenter
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C977CornerSectorBounds C1092ShortWallScalars C1092ShortWallNarrow
set_option Elab.async false

private theorem supports (A R : OpenSquare)
    (dot : 0 ≤ A.c*R.c+A.s*R.s) :
    upper A R.c R.s =
      (A.c*R.c+A.s*R.s)*(A.loU+A.side/2)+
      (A.c*R.s-A.s*R.c)*(A.loV+A.side/2)+
      A.side*((A.c*R.c+A.s*R.s)+|A.c*R.s-A.s*R.c|)/2 ∧
    lower R A.c A.s =
      (A.c*R.c+A.s*R.s)*(R.loU+R.side/2)-
      (A.c*R.s-A.s*R.c)*(R.loV+R.side/2)-
      R.side*((A.c*R.c+A.s*R.s)+|A.c*R.s-A.s*R.c|)/2 := by
  have dotA : |R.c*A.c+R.s*A.s|=A.c*R.c+A.s*R.s := by
    rw [abs_of_nonneg (by nlinarith only [dot])]
    ring
  have dotR : |A.c*R.c+A.s*R.s|=A.c*R.c+A.s*R.s := abs_of_nonneg dot
  have crossA : |-R.c*A.s+R.s*A.c|=|A.c*R.s-A.s*R.c| := by congr 1; ring
  have crossR : |-A.c*R.s+A.s*R.c|=|A.c*R.s-A.s*R.c| := by
    rw [show -A.c*R.s+A.s*R.c=-(A.c*R.s-A.s*R.c) by ring,abs_neg]
  constructor
  · dsimp [upper,supportRadius,centerX,centerY]
    rw [dotA,crossA]
    ring
  · dsimp [lower,supportRadius,centerX,centerY]
    rw [dotR,crossR]
    ring

private theorem canonical_impossible (A R T : OpenSquare)
    (ha : 1 < A.side) (sameR : A.side=R.side) (sameT : A.side=T.side)
    (boxR : InsideContainer R) (boxT : InsideContainer T) (cutT : 2 ≤ centerX T)
    (cn : Normal A.c A.s)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (missingB : ¬ A.Inside (33/20) (47/20))
    (rMarker : R.Inside (1543/500) 2) (rHigh : R.Inside 3 (1197/500))
    (tHigh : T.Inside (1197/500) 3)
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y))
    (apartTop : ∀ x y, ¬ (A.Inside x y ∧ T.Inside x y))
    (missing : ¬ A.Inside 2 2) : False := by
  classical
  have data := C1092ShortWallNarrow.of_missing A R ha sameR boxR cn p q m missingG missingB
    (fun h => apartTop _ _ ⟨h,tHigh⟩) rMarker rHigh ar missing
  have cap := C1092ShortWallCubicCap.cap A T ha sameT cn data boxT cutT p q m tHigh apartTop
  have cb := normal_bounds cn
  have cp : 0 < A.c := by linarith only [cb.1]
  have escape : 2*A.c+2*A.s≤A.loU := by simpa only [mul_add] using data.escape
  have narrow : 12*A.s ≤ 5*A.c := by linarith only [data.narrow,cp]
  have outer := C1092ShortWallCrossing.outer_point A ha cn q m data.lowerV data.topcap missingB
  obtain ⟨W,wc,range,side,inside,_⟩ := ClosedFrames.canonical_frame R
  have same : A.side=W.side := sameR.trans side.symm
  have wb : InsideContainer W := fun x y h => boxR x y ((inside x y).mp h)
  have wm := (inside _ _).mpr rMarker
  have wh := (inside _ _).mpr rHigh
  have apart : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y) :=
    fun x y h => ar x y ⟨h.1,(inside x y).mp h.2⟩
  have axes := C1092ShortWallRightAxes.alternatives A W ha same cn data wc range q m wm wh apart
  by_cases sign : 0 ≤ W.s
  · have wn : Normal W.c W.s := ⟨sign,(abs_le.mp range).2,W.unit_normal⟩
    let d := A.c*W.c+A.s*W.s
    let k := A.c*W.s-A.s*W.c
    have dp : 0 < d := add_pos_of_pos_of_nonneg (mul_pos cp wc) (mul_nonneg cn.1 sign)
    by_cases turn : 0 ≤ k
    · rcases axes with axis | axis
      · exact C1092ShortWallCrossing.central_axis_impossible A W ha same wb cp cn.1 wc sign
          narrow turn escape wm wh axis
      · exact CentralWallPairSupport.wall_axis_impossible A W ha same wb cp cn.1 wc sign
          narrow turn escape data.lowerV outer wm axis
    · have kn : k ≤ 0 := (lt_of_not_ge turn).le
      have ordered : W.s ≤ A.s := sine_order cn wn kn
      have raw := supports A W dp.le
      have upperFormula : upper A W.c W.s=d*(A.loU+A.side)+k*A.loV := by
        have formula := raw.1
        change upper A W.c W.s=d*(A.loU+A.side/2)+k*(A.loV+A.side/2)+A.side*(d+|k|)/2 at formula
        rw [abs_of_nonpos kn] at formula
        rw [formula]
        ring
      have lowerFormula : lower W A.c A.s=d*W.loU-k*W.loV := by
        have formula := raw.2
        change lower W A.c A.s=d*(W.loU+W.side/2)-k*(W.loV+W.side/2)-W.side*(d+|k|)/2 at formula
        rw [abs_of_nonpos kn] at formula
        rw [formula]
        ring
      have wall := CentralWallEscape.right_wall W wb
      have markerBound := mul_le_mul_of_nonneg_left wm.2.2.1.le sign
      have wallBound : W.c*W.loU+W.side*W.c+(1543/500)*W.s^2-2*W.c*W.s ≤ 4 := by
        nlinarith only [wall,markerBound]
      rcases axes with axis | axis
      · have wallScaled := mul_le_mul_of_nonneg_left wall dp.le
        have markerScaled := mul_le_mul_of_nonneg_left wm.2.2.1.le cn.1
        have cancellation : d*W.s-W.c*k=A.s := by
          dsimp [d,k]
          linear_combination A.s*W.unit_normal
        have supportBound : W.c*lower W A.c A.s ≤
            W.c*(4*A.c+2*A.s)+(457/500)*A.s*W.s-W.side*W.c*d := by
          have identity : W.c*lower W A.c A.s =
              d*(W.c*(W.loU+W.side)-W.s*W.loV)+A.s*W.loV-W.side*W.c*d := by
            rw [lowerFormula]
            nlinarith only [congrArg (fun x : ℝ => x*W.loV) cancellation]
          dsimp [d] at identity wallScaled ⊢
          nlinarith only [identity,wallScaled,markerScaled]
        have margin := central_positive_below cn wn data.narrow.le ordered
        have strict := mul_pos (sub_pos.mpr ha)
          (mul_pos wc (show 0 < 1+d by linarith only [dp]))
        have axisScaled := mul_le_mul_of_nonneg_left axis wc.le
        have lowerScaled := mul_le_mul_of_nonneg_left data.escape wc.le
        rw [←same] at supportBound
        dsimp [d] at strict
        nlinarith only [supportBound,axisScaled,lowerScaled,margin,strict]
      · let B := 3*A.c-(5/2)*A.s+allowance A.c A.s
        have uWeight := mul_nonneg dp.le (sub_nonneg.mpr data.escape)
        have vWeight := mul_nonneg (show 0 ≤ -k by linarith only [kn])
          (show 0 ≤ B-A.side-A.loV by dsimp [B]; linarith only [cap])
        have compose : d*(2*(A.c+A.s))+k*B =
            W.c*C1092ShortWallRightMargin.X A.c A.s+W.s*C1092ShortWallRightMargin.Y A.c A.s := by
          dsimp [d,k,B,C1092ShortWallRightMargin.X,C1092ShortWallRightMargin.Y]
          linear_combination (2*W.c+3*W.s)*A.unit_normal
        have supportBound : W.c*C1092ShortWallRightMargin.X A.c A.s+
            W.s*C1092ShortWallRightMargin.Y A.c A.s+A.side*(d-k) ≤ upper A W.c W.s := by
          nlinarith only [upperFormula,uWeight,vWeight,compose]
        have margin := C1092ShortWallRightMargin.ordered cn wn data.narrow.le ordered
        have strict := mul_pos (sub_pos.mpr ha)
          (mul_pos wc (show 0 < d-k+1 by linarith only [dp,kn]))
        have necessary := mul_le_mul_of_nonneg_left (le_trans supportBound axis) wc.le
        rw [←same] at wallBound
        dsimp [d,k] at necessary strict
        nlinarith only [necessary,wallBound,margin,strict]
  · let w := -W.s
    have wp : 0 ≤ w := by dsimp [w]; linarith only [sign]
    have wr : w ≤ W.c := by dsimp [w]; linarith only [(abs_le.mp range).1]
    have wn : Normal W.c w := ⟨wp,wr,by dsimp [w]; nlinarith only [W.unit_normal]⟩
    let d := A.c*W.c-A.s*w
    let k := A.c*w+A.s*W.c
    have dp : 0 < d := by
      have first := mul_pos wc (show 0 < A.c-A.s by linarith only [data.narrow,cn.1])
      have second := mul_nonneg cn.1 (sub_nonneg.mpr wr)
      dsimp [d]
      nlinarith only [first,second]
    have kp : 0 ≤ k := add_nonneg (mul_nonneg cp.le wp) (mul_nonneg cn.1 wc.le)
    have dot : 0 ≤ A.c*W.c+A.s*W.s := by dsimp [d,w] at dp; nlinarith only [dp]
    have cross : A.c*W.s-A.s*W.c ≤ 0 := by dsimp [k,w] at kp; nlinarith only [kp]
    have raw := supports A W dot
    have upperFormula : upper A W.c W.s=d*(A.loU+A.side)-k*A.loV := by
      have formula := raw.1
      rw [abs_of_nonpos cross] at formula
      dsimp [d,k,w]
      nlinarith only [formula]
    have lowerFormula : lower W A.c A.s=d*W.loU+k*W.loV := by
      have formula := raw.2
      rw [abs_of_nonpos cross] at formula
      dsimp [d,k,w]
      nlinarith only [formula]
    have boxTurn : InsideContainer (turnFrame W) := fun x y h =>
      wb x y ((turnFrame_inside W x y).mp h)
    have wall := CentralWallEscape.right_wall (turnFrame W) boxTurn
    have wallBound : W.c*(W.loU+W.side)+w*(W.loV+W.side) ≤ 4 := by
      dsimp [turnFrame,w] at wall ⊢
      linarith only [wall]
    rcases axes with axis | axis
    · have wallScaled := mul_le_mul_of_nonneg_left wallBound dp.le
      have markerScaled := mul_le_mul_of_nonneg_left wm.2.2.1.le cn.1
      have cancellation : W.c*k-d*w=A.s := by
        dsimp [d,k]
        linear_combination A.s*wn.2.2
      have supportBound : W.c*lower W A.c A.s ≤
          W.c*(4*A.c+2*A.s)-(457/500)*A.s*w-W.side*d*(W.c+w) := by
        have identity : W.c*lower W A.c A.s =
            d*(W.c*(W.loU+W.side)+w*(W.loV+W.side))+A.s*W.loV-W.side*d*(W.c+w) := by
          rw [lowerFormula]
          nlinarith only [congrArg (fun x : ℝ => x*W.loV) cancellation]
        dsimp [d,w] at identity wallScaled ⊢
        nlinarith only [identity,wallScaled,markerScaled]
      have margin := central_negative_below cn wn data.narrow.le
      have strict := mul_pos (sub_pos.mpr ha)
        (show 0 < W.c+d*(W.c+w) by
          have product := mul_nonneg dp.le (by linarith only [wc,wp] : 0 ≤ W.c+w)
          linarith only [wc,product])
      have axisScaled := mul_le_mul_of_nonneg_left axis wc.le
      have lowerScaled := mul_le_mul_of_nonneg_left data.escape wc.le
      rw [←same] at supportBound
      change 0≤W.c+d*(W.c+w)-2*A.c*W.c+(457/500)*A.s*w at margin
      have escapeGap := mul_nonneg wc.le (sub_nonneg.mpr data.escape)
      have supportGap := sub_nonneg.mpr supportBound
      have positive : 0<W.c*(A.loU+A.side)-W.c*lower W A.c A.s := by
        calc
          _ = W.c*(A.loU-2*(A.c+A.s))+
              (W.c*(4*A.c+2*A.s)-(457/500)*A.s*w-A.side*d*(W.c+w)-
                W.c*lower W A.c A.s)+
              (W.c+d*(W.c+w)-2*A.c*W.c+(457/500)*A.s*w)+
              (A.side-1)*(W.c+d*(W.c+w)) := by ring
          _ > 0 := add_pos_of_nonneg_of_pos
            (add_nonneg (add_nonneg escapeGap supportGap) margin) strict
      exact (not_lt_of_ge (sub_nonpos.mpr axisScaled)) positive
    · let B := 3*A.c-(5/2)*A.s+allowance A.c A.s
      have uWeight := mul_nonneg dp.le (sub_nonneg.mpr data.escape)
      have vWeight := mul_nonneg kp
        (show 0 ≤ B-A.side-A.loV by dsimp [B]; linarith only [cap])
      have compose : d*(2*(A.c+A.s))-k*B =
          W.c*C1092ShortWallRightMargin.X A.c A.s-w*C1092ShortWallRightMargin.Y A.c A.s := by
        dsimp [d,k,B,C1092ShortWallRightMargin.X,C1092ShortWallRightMargin.Y]
        linear_combination (2*W.c-3*w)*A.unit_normal
      have supportBound : W.c*C1092ShortWallRightMargin.X A.c A.s-
          w*C1092ShortWallRightMargin.Y A.c A.s+A.side*(d+k) ≤ upper A W.c W.s := by
        nlinarith only [upperFormula,uWeight,vWeight,compose]
      have necessary : W.c*C1092ShortWallRightMargin.X A.c A.s-
          w*C1092ShortWallRightMargin.Y A.c A.s+A.side*(d+k) < 3*W.c-(1197/500)*w := by
        have highUpper : W.loU<3*W.c-(1197/500)*w := by
          calc
            W.loU < W.c*3+W.s*(1197/500) := wh.1
            _ = 3*W.c-(1197/500)*w := by dsimp [w]; ring
        exact supportBound.trans_lt (axis.trans_lt highUpper)
      have baseline := cubic_baseline cn data.narrow.le
      have wallBaseline := negative_wall_baseline cn data.narrow.le
      have weighted0 := mul_nonneg wc.le (show 0 ≤
          A.s^2/2-(1-A.c)*(1-A.s)-A.s*allowance A.c A.s by
        nlinarith only [baseline,pow_nonneg cn.1 3])
      have weighted1 := mul_nonneg wp (show 0 ≤
          A.c-A.s-303/500+A.s^2+A.c*A.s/2-A.c*allowance A.c A.s by
        linarith only [wallBaseline])
      have strict := mul_pos (sub_pos.mpr ha) (show 0 < d+k by linarith only [dp,kp])
      have identity : W.c*C1092ShortWallRightMargin.X A.c A.s-
          w*C1092ShortWallRightMargin.Y A.c A.s+(d+k)-3*W.c+(1197/500)*w =
          W.c*(A.s^2/2-(1-A.c)*(1-A.s)-A.s*allowance A.c A.s)+
          w*(A.c-A.s-303/500+A.s^2+A.c*A.s/2-A.c*allowance A.c A.s) := by
        dsimp [d,k,C1092ShortWallRightMargin.X,C1092ShortWallRightMargin.Y]
        ring
      have positive : 0<W.c*C1092ShortWallRightMargin.X A.c A.s-
          w*C1092ShortWallRightMargin.Y A.c A.s+A.side*(d+k)-
          (3*W.c-(1197/500)*w) := by
        calc
          _ = (W.c*C1092ShortWallRightMargin.X A.c A.s-
                w*C1092ShortWallRightMargin.Y A.c A.s+(d+k)-3*W.c+(1197/500)*w)+
              (A.side-1)*(d+k) := by ring
          _ > 0 := add_pos_of_nonneg_of_pos
            (by rw [identity]; exact add_nonneg weighted0 weighted1) strict
      exact (not_lt_of_ge positive.le) (sub_neg.mpr necessary)

/-- Every orientation of A,R,T is covered. The physical center cuts on
both walls are transported when the central coordinates are interchanged. -/
theorem point (A R T : OpenSquare)
    (ha : 1 < A.side) (sameR : A.side=R.side) (sameT : A.side=T.side)
    (boxR : InsideContainer R) (boxT : InsideContainer T)
    (cutR : 2 ≤ centerY R) (cutT : 2 ≤ centerX T)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (missingB : ¬ A.Inside (33/20) (47/20))
    (rMarker : R.Inside (1543/500) 2) (rHigh : R.Inside 3 (1197/500))
    (tMarker : T.Inside 2 (1543/500)) (tHigh : T.Inside (1197/500) 3)
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y))
    (apartTop : ∀ x y, ¬ (A.Inside x y ∧ T.Inside x y)) : A.Inside 2 2 := by
  classical
  obtain ⟨a,hc,hs,side,inside,_⟩ := ClosedFrames.positive_frame A
  have ha' : 1 < a.side := by simpa only [side] using ha
  have sameR' : a.side=R.side := side.trans sameR
  have sameT' : a.side=T.side := side.trans sameT
  have p' := (inside _ _).mpr p
  have q' := (inside _ _).mpr q
  have m' := (inside _ _).mpr m
  have g' : ¬ a.Inside (47/20) (33/20) := fun h => missingG ((inside _ _).mp h)
  have b' : ¬ a.Inside (33/20) (47/20) := fun h => missingB ((inside _ _).mp h)
  have ar' : ∀ x y, ¬ (a.Inside x y ∧ R.Inside x y) :=
    fun x y h => ar x y ⟨(inside x y).mp h.1,h.2⟩
  have at' : ∀ x y, ¬ (a.Inside x y ∧ T.Inside x y) :=
    fun x y h => apartTop x y ⟨(inside x y).mp h.1,h.2⟩
  apply (inside _ _).mp
  by_contra missing
  by_cases order : a.s ≤ a.c
  · exact canonical_impossible a R T ha' sameR' sameT' boxR boxT cutT
      ⟨hs,order,a.unit_normal⟩ p' q' m' g' b' rMarker rHigh tHigh ar' at' missing
  · have swapped := canonical_impossible (pullSwap a) (pullSwap T) (pullSwap R) ha'
      sameT' sameR' (container_pullSwap T boxT) (container_pullSwap R boxR)
      (by simpa only [center_pullSwap_x] using cutR)
      (by exact ⟨hc.le,(lt_of_not_ge order).le,(pullSwap a).unit_normal⟩)
      ((inside_pullSwap a _ _).mpr q') ((inside_pullSwap a _ _).mpr p')
      ((inside_pullSwap a _ _).mpr m')
      (fun h => b' ((inside_pullSwap a _ _).mp h))
      (fun h => g' ((inside_pullSwap a _ _).mp h))
      ((inside_pullSwap T _ _).mpr tMarker) ((inside_pullSwap T _ _).mpr tHigh)
      ((inside_pullSwap R _ _).mpr rHigh)
      (fun x y h => at' y x ⟨(inside_pullSwap a x y).mp h.1,(inside_pullSwap T x y).mp h.2⟩)
      (fun x y h => ar' y x ⟨(inside_pullSwap a x y).mp h.1,(inside_pullSwap R x y).mp h.2⟩)
      (fun h => missing ((inside_pullSwap a _ _).mp h))
    exact swapped

#print axioms point
end N12Compact.C1092ShortWallCenter
