import Compact.Completion.C1092.MMMMNegativeNeighbor

/-! The first actual MMMM pair forces a positive adjacent sign and a small
central angle. Its retained inequality uses the same two original C faces. -/
namespace N12Compact.C1092MMMMFirstPair
open S12 S12Pilot ABTransverse C977CornerCubic C1092WholeSupports C1092ShortChordTable
set_option Elab.async false

structure Result (C B : OpenSquare) : Prop where
  positive : 0 < B.s
  faces : PositiveFaces B.c B.s B.loU B.loV B.side
  sine : (9/20 : ℝ) < B.s
  cosine : B.c < 9/10
  centralSine : -C.s < 7/50
  centralCosine : 99/100 < C.c
  support : C.side*(1+B.c*(-C.s)+B.s*C.c) ≤ B.c+B.s+
    (B.c*(-C.s)+B.s*C.c)*(C.loU+C.side)-
    (B.c*C.c-B.s*(-C.s))*(C.loV+C.side)

/-- The positive-neighbor support calculation uses these two actual upper
faces only. Its conclusion keeps both upper faces of the same central square. -/
theorem positive_support (C B : OpenSquare) (ha : 1<C.side) (same : C.side=B.side)
    (dn : Normal C.c (-C.s)) (bn : Normal B.c B.s) (positive : 0<B.s)
    (origin : C.Inside 0 0) (bottom : C.Inside 0 (-1/2))
    (central : C.Inside (-7/20) (-7/20)) (missing : ¬C.Inside (7/20) (-7/20))
    (marker : B.Inside (-7/20) (7/20)) (H2 : B.Inside (-1) (2/5))
    (faceUpperU : B.loU+B.side≤B.s-(39/100)*B.c)
    (faceUpperV : B.loV+B.side≤B.c+B.s)
    (apart : ∀ x y, ¬(C.Inside x y ∧ B.Inside x y)) :
    C.side*(1+B.c*(-C.s)+B.s*C.c)≤B.c+B.s+
      (B.c*(-C.s)+B.s*C.c)*(C.loU+C.side)-
      (B.c*C.c-B.s*(-C.s))*(C.loV+C.side) := by
  have haB : 1<B.side := by rwa [←same]
  have bp : 0<B.c := by linarith only [(normal_bounds bn).1]
  let d := C.c
  let r := -C.s
  let b := B.c
  let t := B.s
  let u := C.loU+C.side
  let v := C.loV+C.side
  let alpha := b*d-t*r
  let k := b*r+t*d
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0 < d := by dsimp [d]; linarith only [db.1]
  have rn : 0 ≤ r := dn.1
  have an : 0 ≤ alpha := by
    have first := mul_nonneg (sub_nonneg.mpr bn.2.1) dp.le
    have last := mul_nonneg bn.1 (sub_nonneg.mpr dn.2.1)
    dsimp [alpha]; nlinarith only [first,last]
  have kp : 0 < k := by
    have first := mul_nonneg bp.le rn
    have last := mul_pos positive dp
    dsimp [k,b,t]; linarith only [first,last]
  have up : 0 < u := by dsimp [u]; linarith only [origin.2.1]
  have vp : 0 < v := by dsimp [v]; linarith only [origin.2.2.2]
  have cap : u ≤ (7/20)*(d+r) := by
    apply le_of_not_gt; intro upper; apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      dsimp [u,d,r] at upper dp rn ⊢ <;>
      linarith only [upper,origin.1,origin.2.2.2,bottom.2.2.1,dp,rn,dn.2.1]
  have axes := C1092MMMMPairAxes.alternatives C B ha same dp
    (by dsimp [d,r] at dp rn; linarith only [dp,rn]) bp bn.2.1
    db.2.2.2.2.2 origin central marker H2 cap apart
  have pcap : B.loU+B.side ≤ t-(39/100)*b := faceUpperU
  have qcap : B.loV+B.side ≤ b+t := faceUpperV
  have ownSupport : C.side*(1+k) ≤ b+t+k*u-alpha*v := by
    rcases axes with longitudinal | transverse | ownTransverse
    · exfalso
      change B.loU+B.side ≤ lower C b t at longitudinal
      have support := lower_nn C b t alpha k
        (by dsimp [alpha,b,t,d,r]; ring) (by dsimp [k,b,t,d,r]; ring) an kp.le
      have strictU : C.loU < (7/20)*(d+r)-1 := by dsimp [u] at cap; linarith only [cap,ha]
      have strictV : C.loV < -d/2 := by dsimp [d]; linarith only [bottom.2.2.1]
      have first := mul_le_mul_of_nonneg_left strictU.le an
      have last := mul_lt_mul_of_pos_left strictV kp
      have identity : alpha*((7/20)*(d+r)-1)-k*d/2+(7/20)*b-(7/20)*t=
          b*(7/10-d-(7/20)*r^2-(3/20)*d*r)+
            t*(-17/20+r+(3/20)*r^2-(7/20)*d*r) := by
        dsimp [alpha,k]
        linear_combination ((7/20)*b-t/2)*dn.2.2
      have margins := C1092MMMMPairScalars.positive_longitudinal dn
      have firstMargin := mul_nonpos_of_nonneg_of_nonpos bp.le margins.1
      have lastMargin := mul_neg_of_pos_of_neg positive margins.2
      have margin : alpha*((7/20)*(d+r)-1)-k*d/2+(7/20)*b-(7/20)*t<0 := by
        rw [identity]; linarith only [firstMargin,lastMargin]
      have point : -(7/20)*b+(7/20)*t < B.loU+B.side := by
        dsimp [b,t]; linarith only [marker.2.1]
      nlinarith only [longitudinal,support,first,last,margin,point]
    · exfalso
      change v ≤ lower B r d at transverse
      have support := lower_nn B r d k alpha
        (by dsimp [k,b,t,d,r]; ring) (by dsimp [alpha,b,t,d,r]; ring) kp.le an
      have pstrict : B.loU < t-(39/100)*b-1 := by linarith only [pcap,haB]
      have qweak : B.loV ≤ b+t-1 := by linarith only [qcap,haB]
      have first := mul_lt_mul_of_pos_left pstrict kp
      have last := mul_le_mul_of_nonneg_left qweak an
      have identity : k*(t-(39/100)*b-1)+alpha*(b+t-1)=
          -d*(b+t-1-(61/100)*b*t)+r*(t-b-39/100-(61/100)*t^2) := by
        dsimp [k,alpha]
        linear_combination (d-(39/100)*r)*bn.2.2
      have margin := C1092MMMMPairScalars.positive_transverse dn bn positive
      rw [←identity] at margin
      nlinarith only [transverse,support,first,last,margin,vp]
    · change upper C (-t) b ≤ B.loV at ownTransverse
      have support := upper_np C (-t) b (-k) alpha
        (by dsimp [k,b,t,d,r]; ring) (by dsimp [alpha,b,t,d,r]; ring)
        (by linarith only [kp]) an
      rw [←same] at qcap
      dsimp [u,v]
      nlinarith only [ownTransverse,support,qcap]
  convert ownSupport using 1 <;> dsimp [d,r,b,t,u,v,alpha,k] <;> ring

theorem result (C B : OpenSquare) (ha : 1 < C.side) (same : C.side=B.side)
    (dn : Normal C.c (-C.s)) (bp : 0 < B.c) (canonical : |B.s| ≤ B.c)
    (origin : C.Inside 0 0) (bottom : C.Inside 0 (-1/2))
    (central : C.Inside (-7/20) (-7/20)) (missing : ¬ C.Inside (7/20) (-7/20))
    (marker : B.Inside (-7/20) (7/20))
    (H1 : B.Inside (-1) (13/50)) (H2 : B.Inside (-1) (2/5))
    (L0 : ¬ B.Inside (-1) 0) (L1 : ¬ B.Inside (-1) 1)
    (R0 : ¬ B.Inside (-39/100) 0) (R1 : ¬ B.Inside (-39/100) 1)
    (apart : ∀ x y, ¬ (C.Inside x y ∧ B.Inside x y)) : Result C B := by
  classical
  have haB : 1 < B.side := by rwa [←same]
  have positive : 0 < B.s := by
    apply lt_of_not_ge
    intro sign
    have bn : Normal B.c (-B.s) := ⟨by linarith only [sign],
      by simpa only [abs_of_nonpos sign] using canonical,
      by nlinarith only [B.unit_normal]⟩
    have faces := (negative B haB bn marker H1 H2 L0 L1 R0 R1).1
    exact C1092MMMMNegativeNeighbor.impossible C B ha same dn bn origin bottom central
      missing marker H2 faces apart
  have bn : Normal B.c B.s := ⟨positive.le,
    by simpa only [abs_of_pos positive] using canonical,B.unit_normal⟩
  obtain ⟨faces,steepness⟩ := C1092ShortChordTable.positive B haB bn marker H1 H2 L0 L1 R0 R1
  have ownSupport := positive_support C B ha same dn bn positive origin bottom central missing
    marker H2 faces.2.1 faces.2.2.2 apart
  have db := normal_bounds dn
  have dp : 0<C.c := by linarith only [db.1]
  have up : 0<C.loU+C.side := by linarith only [origin.2.1]
  have vp : 0<C.loV+C.side := by linarith only [origin.2.2.2]
  have cap : C.loU+C.side≤(7/20)*(C.c+(-C.s)) := by
    apply le_of_not_gt
    intro upper
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [upper,origin.1,origin.2.2.2,bottom.2.2.1,dp,dn.1,dn.2.1]
  have small := C1092MMMMPairScalars.small_of_support dn bn ha up vp cap ownSupport
  exact ⟨positive,faces,steepness.1,steepness.2,small.1,small.2,ownSupport⟩

#print axioms positive_support
#print axioms result
end N12Compact.C1092MMMMFirstPair
