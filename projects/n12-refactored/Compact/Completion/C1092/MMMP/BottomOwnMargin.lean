import Compact.Completion.C1092.MMMP.BottomBoundaryMargin

/-! DOUBLE-RIGHT-BOTTOM-ORIGIN section 2. The interval bounds in the
completed prose are encoded algebraically. The entire boundary quadrant
is covered, with the switching points b=.914 and b=t retained. -/
namespace N12Compact.C1092MMMPBottomOwnMargin
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977CornerCubic
open C1092WholeSupports C1092MixedCornerSupports C1092MMMPBottomBoundaryOrder
set_option Elab.async false

private theorem large_cosine {c s b t : ℝ} (cn : Normal c s)
    (bp : 0<b) (tp : 0<t) (unit : b^2+t^2=1)
    (order : 0<t*c-b*s) (large : 457/500≤b) :
    c*b*(2-b-t)+s*(b^2-b*t+(457/500)*t)<b := by
  let K := 2-b-t
  let J := b^2-b*t+(457/500)*t
  let alpha := b*c+t*s
  let delta := t*c-b*s
  let base := b^2*K+t*J
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have bSmall : b<1 := by
    nlinarith only [unit,mul_pos tp tp,bp,sq_nonneg (b-1)]
  have tSmall : t<203/500 := by
    have first := mul_nonneg (sub_nonneg.mpr large)
      (show 0≤b+457/500 by linarith only [bp])
    apply lt_of_not_ge
    intro bad
    have last := mul_nonneg (show 0≤t-203/500 by linarith only [bad])
      (show 0≤t+203/500 by linarith only [tp])
    nlinarith only [first,last,unit]
  have kp : 0<K := by dsimp [K]; linarith only [bSmall,tSmall]
  have jn : 0≤J := by
    have first := mul_nonneg bp.le (show 0≤b-t by linarith only [large,tSmall])
    dsimp [J]
    nlinarith only [first,tp]
  have baseNonnegative : 0≤base :=
    add_nonneg (mul_nonneg (sq_nonneg b) kp.le) (mul_nonneg tp.le jn)
  have baseCap : base<b := by
    have negative := mul_neg_of_neg_of_pos (sub_neg.mpr bSmall)
      (show 0<(543/500)*b-457/500 by linarith only [large])
    have identity : base-b=(b-1)*((543/500)*b-457/500) := by
      dsimp [base,K,J]
      linear_combination (457/500-b)*unit
    linarith only [negative,identity]
  have derivative : 0<J-t*K := by
    have identity : J-t*K=1-(543/500)*t := by
      dsimp [J,K]
      linear_combination unit
    linarith only [identity,tSmall]
  have ap : 0<alpha := add_pos_of_pos_of_nonneg (mul_pos bp cp) (mul_nonneg tp.le cn.1)
  have relative : alpha^2+delta^2=1 := by
    calc
      _ = (b^2+t^2)*(c^2+s^2) := by dsimp [alpha,delta]; ring
      _ = 1 := by rw [unit,cn.2.2]; norm_num
  have acap : alpha≤1 := by nlinarith only [relative,sq_nonneg delta,sq_nonneg (alpha-1)]
  have first := mul_le_mul_of_nonneg_right acap baseNonnegative
  have last := mul_pos (mul_pos bp order) derivative
  have identity : c*b*K+s*J=alpha*base-b*delta*(J-t*K) := by
    dsimp [alpha,base,delta]
    linear_combination -(c*b*K+s*J)*unit
  calc
    _ = alpha*base-b*delta*(J-t*K) := identity
    _ < alpha*base := by nlinarith only [last]
    _ ≤ base := by simpa using first
    _ < b := baseCap

private theorem small_cosine {c s b t : ℝ} (cn : Normal c s)
    (cosine : 500/543<c) (bp : 0<b) (tp : 0<t)
    (unit : b^2+t^2=1) (small : b≤457/500) :
    c*t*(2-b-t)+s*b*(b+t-457/500)<t := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cosine]
  have sine : s<391/1000 := by
    have first := mul_pos (sub_pos.mpr cosine)
      (show 0<c+500/543 by linarith only [cp])
    apply lt_of_not_ge
    intro bad
    have last := mul_nonneg (show 0≤s-391/1000 by linarith only [bad])
      (show 0≤s+391/1000 by linarith only [cn.1])
    nlinarith only [first,last,cn.2.2]
  by_cases canonical : t≤b
  · have sumLower : 1≤b+t := by
      apply le_of_not_gt
      intro bad
      have gap := mul_pos (show 0<1-b-t by linarith only [bad])
        (show 0<1+b+t by linarith only [bp,tp])
      have product := mul_nonneg bp.le tp.le
      nlinarith only [unit,product,gap]
    have sum : 1319/1000<b+t := by
      apply lt_of_not_ge
      intro bad
      have product := mul_nonneg (show 0≤457/500-b by linarith only [small])
        (show 0≤457/500-t by linarith only [canonical,small])
      have chord := mul_nonneg (show 0≤b+t-1 by linarith only [sumLower])
        (show 0≤1319/1000-b-t by linarith only [bad])
      nlinarith only [unit,product,chord,bad]
    have kCap : 2-b-t<681/1000 := by linarith only [sum]
    have jCap : b*(b+t-457/500)≤(457/500)*t := by
      have product := mul_nonpos_of_nonpos_of_nonneg
        (show b-457/500≤0 by linarith only [small])
        (show 0≤b+t by linarith only [bp,tp])
      nlinarith only [product]
    have tangent : (23/25)*c+(2/5)*s<251/250 := by
      have identity : ((23/25)*c+(2/5)*s)^2+((2/5)*c-(23/25)*s)^2=
          (629/625)*(c^2+s^2) := by ring
      apply lt_of_not_ge
      intro bad
      have product := mul_nonneg
        (show 0≤(23/25)*c+(2/5)*s-251/250 by linarith only [bad])
        (show 0≤(23/25)*c+(2/5)*s+251/250 by linarith only [cp,cn.1])
      nlinarith only [identity,product,cn.2.2,sq_nonneg ((2/5)*c-(23/25)*s)]
    have margin : (681/1000)*c+(457/500)*s<1 := by linarith only [tangent,sine]
    have first := mul_lt_mul_of_pos_left kCap (mul_pos cp tp)
    have last := mul_le_mul_of_nonneg_left jCap cn.1
    have scaled := mul_lt_mul_of_pos_left margin tp
    nlinarith only [first,last,scaled]
  · have order : b≤t := le_of_not_ge canonical
    have bCap : b≤1 := by nlinarith only [unit,sq_nonneg t,sq_nonneg (b-1)]
    have chord := mul_nonneg bp.le
      (show 0≤(1+t)/2-b by linarith only [bCap,order])
    have identity : (1+t)*(b/2-1+t)=b*((1+t)/2-b) := by
      linear_combination unit
    have h : 0≤b/2-1+t :=
      nonneg_of_mul_nonneg_right (by rw [identity]; exact chord)
        (by linarith only [tp])
    have kCap : 2-b-t≤1-b/2 := by linarith only [h]
    have jCap : b*(b+t-457/500)≤b*t := by
      have product := mul_nonpos_of_nonneg_of_nonpos bp.le
        (show b-457/500≤0 by linarith only [small])
      nlinarith only [product]
    have first := mul_le_mul_of_nonneg_left kCap (mul_nonneg cp.le tp.le)
    have last := mul_le_mul_of_nonneg_left jCap cn.1
    have strict := mul_pos (mul_pos bp tp)
      (show 0<c/2-s by linarith only [cosine,sine])
    have cap := mul_le_mul_of_nonneg_right cb.2.1 tp.le
    nlinarith only [first,last,strict,cap]

/-- Section 2 excludes the inward square's own upward normal using
the full support of the same actual boundary square. -/
theorem own_normal_impossible (C R : OpenSquare) (side : 1<C.side)
    (same : C.side=R.side) (cn : Normal C.c C.s) (sp : 0<C.s)
    (lowerFace : 0≤C.loU) (S : R.Inside (543/500) 0)
    (data : Data C R) (separation : C.loU+C.side≤lower R C.c C.s) : False := by
  let c := C.c
  let s := C.s
  let b := R.c
  let t := R.s
  let a := R.side
  let alpha := b*c+t*s
  let delta := t*c-b*s
  let K := 2-b-t
  have cp : 0<c := by dsimp [c]; linarith only [(normal_bounds cn).1]
  have bp : 0<b := data.cosine
  have tp : 0<t := data.sine
  have ap : 0<alpha := add_pos_of_pos_of_nonneg (mul_pos bp cp) (mul_nonneg tp.le cn.1)
  have dp : 0<delta := data.angle
  have sideR : 1<a := by dsimp [a]; rwa [←same]
  have formula := lower_pn R c s alpha (-delta)
    (by dsimp [c,s,b,t,alpha]; ring) (by dsimp [c,s,b,t,delta]; ring)
    ap.le (by linarith only [dp])
  have wallScaled := mul_le_mul_of_nonneg_left data.wall dp.le
  have identity : t*lower R c s=
      s*R.loU-a*delta*(t+b)+delta*(b*(R.loU+a)-t*R.loV) := by
    rw [formula]
    dsimp [alpha,delta,b,t,a]
    linear_combination C.s*R.loU*R.unit_normal
  have wallBound : t*lower R c s≤s*R.loU-a*delta*(t+b)+2*delta := by
    dsimp [b,t,a] at identity
    nlinarith only [identity,wallScaled]
  have excess := mul_pos (sub_pos.mpr sideR)
    (mul_pos dp (show 0<t+b by linarith only [bp,tp]))
  have coarse : t*lower R c s<s*R.loU+delta*K := by
    dsimp [K]
    nlinarith only [wallBound,excess]
  have support : lower R c s<1 := by
    by_cases large : 457/500≤b
    · have markerScaled := mul_lt_mul_of_pos_left data.markerV tp
      have sideScaled := mul_pos bp (sub_pos.mpr sideR)
      have lCap : b*R.loU<2-(543/500)*t^2-b := by
        dsimp [b,t,a] at sideScaled ⊢
        nlinarith only [data.wall,markerScaled,sideScaled]
      have first := mul_lt_mul_of_pos_left coarse bp
      have last := mul_lt_mul_of_pos_left lCap sp
      have combined : b*t*lower R c s<
          s*(2-(543/500)*t^2-b)+b*delta*K := by nlinarith only [first,last]
      have identity : s*(2-(543/500)*t^2-b)+b*delta*K=
          t*(c*b*K+s*(b^2-b*t+(457/500)*t)) := by
        dsimp [delta,K,b,t]
        linear_combination C.s*(R.c-2)*R.unit_normal
      rw [identity] at combined
      have scalar := large_cosine cn bp tp R.unit_normal data.angle large
      have scaled := mul_lt_mul_of_pos_left scalar tp
      apply (mul_lt_mul_left (mul_pos bp tp)).mp
      nlinarith only [combined,scaled]
    · have small : b≤457/500 := le_of_not_ge large
      by_cases cosine : c≤500/543
      · have bound := (strict_bounds R _ _ C.c C.s C.unit_normal S).1
        dsimp [c,s]
        linarith only [bound,cosine]
      · have cosine' : 500/543<c := lt_of_not_ge cosine
        have markerScaled := mul_lt_mul_of_pos_left data.markerU sp
        have bound : t*lower R c s<c*t*K+s*b*(b+t-457/500) := by
          dsimp [b] at markerScaled
          dsimp [K,delta] at coarse ⊢
          nlinarith only [coarse,markerScaled]
        have scalar := small_cosine cn cosine' bp tp R.unit_normal small
        apply (mul_lt_mul_left tp).mp
        nlinarith only [bound,scalar]
  dsimp [c,s] at support
  linarith only [lowerFace,side,separation,support]

#print axioms own_normal_impossible
end N12Compact.C1092MMMPBottomOwnMargin
