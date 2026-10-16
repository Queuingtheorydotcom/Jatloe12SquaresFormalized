import Compact.Completion.C1092.MMMMFirstPair

/-! The second standardized MMMM pair uses the small angle already proved
by the first pair. Both adjacent signs and all actual support axes are covered. -/
namespace N12Compact.C1092MMMMSecondPair
open S12 S12Pilot ABTransverse C977CornerCubic C1092WholeSupports C1092ShortChordTable
set_option Elab.async false

private theorem negative_impossible (C B : OpenSquare) (ha : 1 < C.side)
    (same : C.side=B.side) (dn : Normal C.c C.s) (bn : Normal B.c (-B.s))
    (small : C.s < 7/50) (close : 99/100 < C.c)
    (origin : C.Inside 0 0) (central : C.Inside (-7/20) (-7/20))
    (marker : B.Inside (-7/20) (7/20)) (ordinary : B.Inside (-1) (2/5))
    (faces : NegativeFaces B.c (-B.s) B.loU B.loV B.side)
    (cap : C.loU+C.side ≤ (7/20)*(C.c-C.s))
    (high : C.s/2 < C.loV+C.side)
    (apart : ∀ x y, ¬ (C.Inside x y ∧ B.Inside x y)) : False := by
  let d := C.c
  let r := C.s
  let b := B.c
  let t := -B.s
  let u := C.loU+C.side
  let v := C.loV+C.side
  let alpha := b*d-t*r
  let k := b*r+t*d
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0 < d := by dsimp [d]; linarith only [db.1]
  have bp : 0 < b := by dsimp [b]; linarith only [bb.1]
  have pcap : B.loU+B.side ≤ -(39/100)*b := faces.2.1
  have qcap : B.loV+B.side ≤ b-(39/100)*t := faces.2.2.2
  have plow : -b-t ≤ B.loU := faces.1
  have haB : 1 < B.side := by rwa [←same]
  have tp : 0 < t := by
    have width : B.side ≤ t+(61/100)*b := by linarith only [plow,pcap]
    dsimp [b,t] at width ⊢
    linarith only [width,haB,bb.2.1]
  have kp : 0 < k := by
    have first := mul_nonneg bp.le dn.1
    have last := mul_pos tp dp
    dsimp [k]; linarith only [first,last]
  have ap : 0 < alpha := by
    have first := mul_nonneg (sub_nonneg.mpr bn.2.1)
      (show 0≤d-r by dsimp [d,r]; linarith only [close,small])
    have last := mul_pos bp (show 0<d-r by dsimp [d,r]; linarith only [close,small])
    dsimp [alpha]
    have order := mul_nonneg (sub_nonneg.mpr bn.2.1) dn.1
    nlinarith only [last,order]
  have axes := C1092MMMMPairAxes.alternatives C B ha same dp dn.2.1 bp
    (by linarith only [bp,tp])
    (by linarith only [db.2.2.2.2.2,dn.1])
    origin central marker ordinary cap apart
  rcases axes with longitudinal | transverse | ownTransverse
  · have longitudinal : B.loU+B.side ≤ lower C b (-t) := by
      simpa only [b,t,neg_neg] using longitudinal
    have support := lower_pn C b (-t) alpha (-k)
      (by dsimp [alpha,b,t,d,r] <;> ring) (by dsimp [k,b,t,d,r] <;> ring) ap.le
      (by linarith only [kp])
    rw [←same] at longitudinal
    have first := mul_nonneg ap.le (sub_nonneg.mpr cap)
    have last := mul_pos kp (show 0<v-r/2 by dsimp [v,r]; linarith only [high])
    have strict := mul_pos (sub_pos.mpr ha) (show 0<1+alpha by linarith only [ap])
    have identity : b+t-alpha+alpha*(7/20)*(d-r)-k*r/2=
        b*(27/20-d-(7/20)*d*r-(17/20)*r^2)+
          t*(1+r-(17/20)*d*r+(7/20)*r^2) := by
      dsimp [alpha,k]
      linear_combination ((7/20)*b)*dn.2.2
    have necessary : 1 < b*(27/20-d-(7/20)*d*r-(17/20)*r^2)+
        t*(1+r-(17/20)*d*r+(7/20)*r^2) := by
      rw [←identity]
      dsimp [u,v,d,r] at first last
      nlinarith only [longitudinal,support,plow,first,last,strict]
    have margin := C1092MMMMPairScalars.small_negative_longitudinal dn bn small close
    linarith only [necessary,margin]
  · change v ≤ lower B (-r) d at transverse
    have support := lower_np B (-r) d (-k) alpha
      (by dsimp [k,b,t,d,r]; ring) (by dsimp [alpha,b,t,d,r]; ring)
      (by linarith only [kp]) ap.le
    have ppoint : -(7/20)*(b+t) < B.loU+B.side := by
      dsimp [b,t]; linarith only [marker.2.1]
    have first := mul_lt_mul_of_neg_left ppoint (show -k<0 by linarith only [kp])
    have qstrict : B.loV < b-(39/100)*t-1 := by linarith only [qcap,haB]
    have last := mul_lt_mul_of_pos_left qstrict ap
    have identity : (7/20)*k*(b+t)+alpha*(b-(39/100)*t-1)=
        d*(1-b-(13/20)*t^2-(1/25)*b*t)+
          r*(7/20+(1/25)*t^2-(13/20)*b*t+t) := by
      dsimp [k,alpha]
      linear_combination (d+(7/20)*r)*bn.2.2
    have margin := C1092MMMMPairScalars.small_negative_transverse dn bn small close tp
    rw [←identity] at margin
    dsimp [v,r] at transverse
    nlinarith only [transverse,support,first,last,margin,high]
  · change upper C t b ≤ B.loV at ownTransverse
    have unit : t^2+b^2=1 := by dsimp [b,t]; nlinarith only [B.unit_normal]
    have zero := (strict_bounds C 0 0 t b unit origin).2
    have qnegative : B.loV < 0 := by
      dsimp [b,t] at qcap ⊢
      linarith only [qcap,haB,bb.2.1,bn.1]
    linarith only [zero,qnegative,ownTransverse]

structure Result (C B : OpenSquare) : Prop where
  positive : 0 < B.s
  sine : (9/20 : ℝ) < B.s
  cosine : B.c < 9/10
  support : C.side*(1+B.s*C.c-B.c*C.s) ≤ B.c+B.s+
    (B.s*C.c-B.c*C.s)*(C.loU+C.side)-
    (B.c*C.c+B.s*C.s)*(C.loV+C.side)

theorem result (C B : OpenSquare) (ha : 1 < C.side) (same : C.side=B.side)
    (dn : Normal C.c C.s) (small : C.s < 7/50) (close : 99/100 < C.c)
    (bp : 0 < B.c) (canonical : |B.s| ≤ B.c)
    (origin : C.Inside 0 0) (bottom : C.Inside 0 (-1/2)) (left : C.Inside (-1/2) 0)
    (central : C.Inside (-7/20) (-7/20))
    (missingG : ¬ C.Inside (7/20) (-7/20)) (missingM : ¬ C.Inside (-7/20) (7/20))
    (marker : B.Inside (-7/20) (7/20))
    (H1 : B.Inside (-1) (13/50)) (H2 : B.Inside (-1) (2/5))
    (L0 : ¬ B.Inside (-1) 0) (L1 : ¬ B.Inside (-1) 1)
    (R0 : ¬ B.Inside (-39/100) 0) (R1 : ¬ B.Inside (-39/100) 1)
    (apart : ∀ x y, ¬ (C.Inside x y ∧ B.Inside x y)) : Result C B := by
  classical
  have db := normal_bounds dn
  have dp : 0 < C.c := by linarith only [db.1]
  have ucap : C.loU+C.side ≤ (7/20)*(C.c-C.s) := by
    apply le_of_not_gt; intro upper; apply missingG
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [upper,origin.1,origin.2.2.2,bottom.2.2.1,dp,dn.1,dn.2.1,small,close]
  have vcap : C.loV+C.side ≤ (7/20)*(C.c+C.s) := by
    apply le_of_not_gt; intro upper; apply missingM
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [upper,origin.2.1,origin.2.2.1,left.1,dp,dn.1,dn.2.1]
  have high : C.s/2 < C.loV+C.side := by linarith only [left.2.2.2]
  have haB : 1 < B.side := by rwa [←same]
  have pos : 0 < B.s := by
    apply lt_of_not_ge; intro sign
    have bn : Normal B.c (-B.s) := ⟨by linarith only [sign],
      by simpa only [abs_of_nonpos sign] using canonical,
      by nlinarith only [B.unit_normal]⟩
    have faces := (negative B haB bn marker H1 H2 L0 L1 R0 R1).1
    exact negative_impossible C B ha same dn bn small close origin central marker H2
      faces ucap high apart
  have bn : Normal B.c B.s := ⟨pos.le,
    by simpa only [abs_of_pos pos] using canonical,B.unit_normal⟩
  obtain ⟨faces,steepness⟩ := positive B haB bn marker H1 H2 L0 L1 R0 R1
  let d := C.c
  let r := C.s
  let b := B.c
  let t := B.s
  let u := C.loU+C.side
  let v := C.loV+C.side
  let alpha := b*d+t*r
  let k := t*d-b*r
  have bb := normal_bounds bn
  have ap : 0 < alpha := by
    have first := mul_pos bp dp
    have last := mul_nonneg bn.1 dn.1
    dsimp [alpha,b,t,d,r]; linarith only [first,last]
  have kp : 0 < k := by
    have first := mul_lt_mul_of_pos_left close pos
    have last := mul_nonneg dn.1 (show 0≤9/10-B.c by linarith only [steepness.2])
    dsimp [k,b,t,d,r]
    nlinarith only [first,last,steepness.1,small]
  have axes := C1092MMMMPairAxes.alternatives C B ha same dp dn.2.1 bp bn.2.1
    (by linarith only [db.2.2.2.2.2,dn.1]) origin central marker H2 ucap apart
  have pcap : B.loU+B.side ≤ t-(39/100)*b := faces.2.1
  have qcap : B.loV+B.side ≤ b+t := faces.2.2.2
  have ownSupport : C.side*(1+k) ≤ b+t+k*u-alpha*v := by
    rcases axes with longitudinal | transverse | ownTransverse
    · exfalso
      change B.loU+B.side ≤ lower C b t at longitudinal
      have support := lower_nn C b t alpha k
        (by dsimp [alpha,b,t,d,r] <;> ring) (by dsimp [k,b,t,d,r] <;> ring) ap.le kp.le
      have strictU : C.loU < (7/20)*(d-r)-1 := by linarith only [ucap,ha]
      have strictV : C.loV < -d/2 := by dsimp [d]; linarith only [bottom.2.2.1]
      have first := mul_lt_mul_of_pos_left strictU ap
      have last := mul_lt_mul_of_pos_left strictV kp
      have identity : alpha*((7/20)*(d-r)-1)-k*d/2+(7/20)*b-(7/20)*t=
          b*(7/10-d-(7/20)*r^2+(3/20)*d*r)+
            t*(-17/20-r+(3/20)*r^2+(7/20)*d*r) := by
        dsimp [alpha,k]
        linear_combination ((7/20)*b-t/2)*dn.2.2
      have margin := C1092MMMMPairScalars.small_positive_longitudinal dn small close
      have firstMargin := mul_neg_of_pos_of_neg bp margin.1
      have lastMargin := mul_neg_of_pos_of_neg pos margin.2
      have bound : alpha*((7/20)*(d-r)-1)-k*d/2+(7/20)*b-(7/20)*t<0 := by
        rw [identity]; linarith only [firstMargin,lastMargin]
      have point : -(7/20)*b+(7/20)*t < B.loU+B.side := by
        dsimp [b,t]; linarith only [marker.2.1]
      nlinarith only [longitudinal,support,first,last,bound,point]
    · exfalso
      change v ≤ lower B (-r) d at transverse
      have support := lower_nn B (-r) d k alpha
        (by dsimp [k,b,t,d,r]; ring) (by dsimp [alpha,b,t,d,r]; ring) kp.le ap.le
      have pstrict : B.loU < t-(39/100)*b-1 := by linarith only [pcap,haB]
      have qstrict : B.loV < b+t-1 := by linarith only [qcap,haB]
      have first := mul_lt_mul_of_pos_left pstrict kp
      have last := mul_lt_mul_of_pos_left qstrict ap
      have identity : k*(t-(39/100)*b-1)+alpha*(b+t-1)=
          -d*(b+t-1-(61/100)*b*t)+r*(b-t+39/100+(61/100)*t^2) := by
        dsimp [k,alpha]
        linear_combination (d+(39/100)*r)*bn.2.2
      have margin := C1092MMMMPairScalars.small_positive_transverse dn bn small close
        steepness.1 steepness.2
      dsimp [v,r] at transverse
      nlinarith only [transverse,support,first,last,identity,margin,high]
    · change upper C (-t) b ≤ B.loV at ownTransverse
      have support := upper_np C (-t) b (-k) alpha
        (by dsimp [k,b,t,d,r]; ring) (by dsimp [alpha,b,t,d,r]; ring)
        (by linarith only [kp]) ap.le
      rw [←same] at qcap
      dsimp [u,v]
      nlinarith only [ownTransverse,support,qcap]
  refine ⟨pos,steepness.1,steepness.2,?_⟩
  convert ownSupport using 1 <;> dsimp [k,alpha,b,t,d,r,u,v] <;> ring

#print axioms result
end N12Compact.C1092MMMMSecondPair
