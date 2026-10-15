import Compact.Completion.C1092.MMMMPairAxes
import Compact.Completion.C1092.MMMMPairScalars
import Compact.Completion.C1092.ShortChordTable
import Compact.Completion.C1092.WholeSupports

/-! A nonpositive standardized central angle excludes the entire negative
neighbor sign. The three actual surviving axes are all discharged, including
both orders of the relative transverse angle and equality. -/
namespace N12Compact.C1092MMMMNegativeNeighbor
open S12 S12Pilot ABTransverse C977CornerCubic C1092WholeSupports C1092ShortChordTable
set_option Elab.async false

theorem impossible_faces (C B : OpenSquare) (ha : 1 < C.side) (same : C.side=B.side)
    (dn : Normal C.c (-C.s)) (bn : Normal B.c (-B.s))
    (origin : C.Inside 0 0) (bottom : C.Inside 0 (-1/2))
    (central : C.Inside (-7/20) (-7/20))
    (missing : ¬ C.Inside (7/20) (-7/20))
    (marker : B.Inside (-7/20) (7/20)) (ordinary : B.Inside (-1) (2/5))
    (faceLower : -B.c-(-B.s) ≤ B.loU)
    (faceUpperU : B.loU+B.side ≤ -(39/100)*B.c)
    (faceUpperV : B.loV+B.side ≤ B.c-(39/100)*(-B.s))
    (apart : ∀ x y, ¬ (C.Inside x y ∧ B.Inside x y)) : False := by
  let d := C.c
  let r := -C.s
  let b := B.c
  let t := -B.s
  let u := C.loU+C.side
  let v := C.loV+C.side
  let alpha := b*d+t*r
  let h := b*r-t*d
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0 < d := by dsimp [d]; linarith only [db.1]
  have bp : 0 < b := by dsimp [b]; linarith only [bb.1]
  have rn : 0 ≤ r := dn.1
  have tn : 0 ≤ t := bn.1
  have ap : 0 < alpha := by
    have first := mul_pos bp dp
    have last := mul_nonneg tn rn
    dsimp [alpha]; linarith only [first,last]
  have up : 0 < u := by dsimp [u]; linarith only [origin.2.1]
  have vp : 0 < v := by dsimp [v]; linarith only [origin.2.2.2]
  have cap : u ≤ (7/20)*(d+r) := by
    apply le_of_not_gt; intro upper; apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      dsimp [u,d,r] at upper dp rn ⊢ <;>
      linarith only [upper,origin.1,origin.2.2.2,bottom.2.2.1,dp,rn,dn.2.1]
  have haB : 1 < B.side := by rwa [←same]
  have axes := C1092MMMMPairAxes.alternatives C B ha same dp
    (by dsimp [d,r] at dp rn; linarith only [dp,rn]) bp
    (by dsimp [b,t] at bp tn; linarith only [bp,tn])
    db.2.2.2.2.2 origin central marker ordinary cap apart
  have pcap : B.loU+B.side ≤ -(39/100)*b := faceUpperU
  have qcap : B.loV+B.side ≤ b-(39/100)*t := faceUpperV
  have plow : -b-t ≤ B.loU := faceLower
  have relativeU : b*C.c+(-t)*C.s=alpha := by dsimp [b,t,alpha,d,r]; ring
  have relativeV : -b*C.s+(-t)*C.c=h := by dsimp [b,t,h,d,r]; ring
  have otherU : r*B.c+d*B.s=h := by dsimp [b,t,h,d,r]; ring
  have otherV : -r*B.s+d*B.c=alpha := by dsimp [b,t,alpha,d,r]; ring
  rcases axes with longitudinal | transverse | ownTransverse
  · have signed : B.s = -t := by dsimp [t]; ring
    rw [signed] at longitudinal
    change B.loU+B.side ≤ lower C b (-t) at longitudinal
    by_cases positive : 0 ≤ h
    · have support := lower_nn C b (-t) alpha h relativeU relativeV ap.le positive
      have strictU : C.loU < (7/20)*(d+r)-1 := by dsimp [u] at cap; linarith only [cap,ha]
      have strictV : C.loV < -d/2 := by dsimp [d]; linarith only [bottom.2.2.1]
      have first := mul_lt_mul_of_pos_left strictU ap
      have last := mul_le_mul_of_nonneg_left strictV.le positive
      have identity : alpha*((7/20)*(d+r)-1)-h*d/2+(7/20)*(b+t)=
          b*(7/10-d-(7/20)*r^2-(3/20)*d*r)+
            t*(17/20-r-(3/20)*r^2+(7/20)*d*r) := by
        dsimp [alpha,h]
        linear_combination ((7/20)*b+t/2)*dn.2.2
      have margin := C1092MMMMPairScalars.negative_longitudinal_ge dn bn positive
      have point : -(7/20)*(b+t) < B.loU+B.side := by
        dsimp [b,t]; linarith only [marker.2.1]
      rw [←identity] at margin
      nlinarith only [longitudinal,support,first,last,margin,point]
    · have hn : h ≤ 0 := (lt_of_not_ge positive).le
      have support := lower_pn C b (-t) alpha h relativeU relativeV ap.le hn
      rw [←same] at longitudinal
      have first := mul_nonneg ap.le (sub_nonneg.mpr cap)
      have last := mul_nonpos_of_nonneg_of_nonpos vp.le hn
      have strict := mul_pos (sub_pos.mpr ha) (show 0<1+alpha by linarith only [ap])
      have necessary : 1 < b+t-alpha*(1-(7/20)*(d+r)) := by
        dsimp [u,v] at first last
        nlinarith only [longitudinal,support,plow,first,last,strict]
      have margin := C1092MMMMPairScalars.negative_longitudinal_le dn bn
      dsimp [alpha] at necessary
      linarith only [necessary,margin]
  · change v ≤ lower B r d at transverse
    have qstrict : B.loV < b-(39/100)*t-1 := by linarith only [qcap,haB]
    have last := mul_lt_mul_of_pos_left qstrict ap
    by_cases positive : 0 ≤ h
    · have support := lower_nn B r d h alpha otherU otherV positive ap.le
      have pweak : B.loU ≤ -(39/100)*b-1 := by linarith only [pcap,haB]
      have first := mul_le_mul_of_nonneg_left pweak positive
      have identity : h*(-(39/100)*b-1)+alpha*(b-(39/100)*t-1)=
          d*(1-b+t-t^2)+r*(-39/100-b-t+b*t) := by
        dsimp [h,alpha]
        linear_combination (d-(39/100)*r)*bn.2.2
      have margin := C1092MMMMPairScalars.negative_transverse_ge dn bn positive
      rw [←identity] at margin
      have negative : lower B r d < 0 := by
        calc
          _ = h*B.loU+alpha*B.loV := support
          _ < h*(-(39/100)*b-1)+alpha*(b-(39/100)*t-1) :=
            add_lt_add_of_le_of_lt first last
          _ ≤ 0 := margin
      exact (not_lt_of_ge (le_trans vp.le transverse)) negative
    · have hn : h ≤ 0 := (lt_of_not_ge positive).le
      have support := lower_np B r d h alpha otherU otherV hn ap.le
      have ppoint : -(7/20)*(b+t) < B.loU+B.side := by
        dsimp [b,t]; linarith only [marker.2.1]
      have first := mul_le_mul_of_nonpos_left ppoint.le hn
      have tp : 0 < t := by
        have width : B.side ≤ t+(61/100)*b := by
          calc
            _ = (B.loU+B.side)-B.loU := by ring
            _ ≤ -(39/100)*b-(-b-t) := sub_le_sub pcap plow
            _ = _ := by ring
        dsimp [b,t] at width ⊢
        linarith only [width,haB,bb.2.1]
      have identity : -(7/20)*h*(b+t)+alpha*(b-(39/100)*t-1)=
          d*(1-b-(13/20)*t^2-(1/25)*b*t)+
            r*(-7/20-(1/25)*t^2+(13/20)*b*t-t) := by
        dsimp [h,alpha]
        linear_combination (d-(7/20)*r)*bn.2.2
      have margin := C1092MMMMPairScalars.negative_transverse_le dn bn tp
      rw [←identity] at margin
      have negative : lower B r d < 0 := by
        calc
          _ = h*(B.loU+B.side)+alpha*B.loV := support
          _ < h*(-(7/20)*(b+t))+alpha*(b-(39/100)*t-1) :=
            add_lt_add_of_le_of_lt first last
          _ = -(7/20)*h*(b+t)+alpha*(b-(39/100)*t-1) := by ring
          _ < 0 := margin
      exact (not_lt_of_ge (le_trans vp.le transverse)) negative
  · change upper C t b ≤ B.loV at ownTransverse
    have unit : t^2+b^2=1 := by dsimp [b,t]; nlinarith only [B.unit_normal]
    have zero := (strict_bounds C 0 0 t b unit origin).2
    have qnegative : B.loV < 0 := by
      dsimp [b,t] at qcap ⊢
      linarith only [qcap,haB,bb.2.1,bn.1]
    linarith only [zero,qnegative,ownTransverse]

theorem impossible (C B : OpenSquare) (ha : 1 < C.side) (same : C.side=B.side)
    (dn : Normal C.c (-C.s)) (bn : Normal B.c (-B.s))
    (origin : C.Inside 0 0) (bottom : C.Inside 0 (-1/2))
    (central : C.Inside (-7/20) (-7/20))
    (missing : ¬ C.Inside (7/20) (-7/20))
    (marker : B.Inside (-7/20) (7/20)) (ordinary : B.Inside (-1) (2/5))
    (faces : NegativeFaces B.c (-B.s) B.loU B.loV B.side)
    (apart : ∀ x y, ¬ (C.Inside x y ∧ B.Inside x y)) : False :=
  impossible_faces C B ha same dn bn origin bottom central missing marker ordinary
    faces.1 faces.2.1 faces.2.2.2 apart

#print axioms impossible_faces
#print axioms impossible
end N12Compact.C1092MMMMNegativeNeighbor
