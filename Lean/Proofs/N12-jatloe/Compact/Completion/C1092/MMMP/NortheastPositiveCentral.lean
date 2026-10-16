import Compact.Completion.C1092.MMMP.NortheastNegativeFaces
import Compact.Completion.C1092.MMMP.NortheastSignScalars
import Compact.Completion.C1092.MMMMPairAxes
import Compact.Completion.C1092.WholeSupports

/-! A positive central square excludes the whole nonpositive northeast
sign. The actual left-wall endpoint and all complete support orders remain
in the hypotheses; no top origin is presumed. -/
namespace N12Compact.C1092MMMPNortheastPositiveCentral
open S12 S12Pilot ABTransverse C977CornerCubic C1092WholeSupports
set_option Elab.async false

theorem impossible (C B : OpenSquare) (side : 1<C.side) (same : C.side=B.side)
    (dn : Normal C.c C.s) (bn : Normal B.c (-B.s))
    (origin : C.Inside 0 0) (left : C.Inside (-1/2) 0)
    (central : C.Inside (-7/20) (-7/20))
    (missingG : ¬C.Inside (7/20) (-7/20)) (missingM : ¬C.Inside (-7/20) (7/20))
    (missingF : ¬C.Inside (-39/100) (-1))
    (marker : B.Inside (-7/20) (7/20)) (ordinary : B.Inside (-1) (2/5))
    (faces : C1092MMMPNortheastNegativeFaces.Faces B)
    (apart : ∀ x y, ¬(C.Inside x y ∧ B.Inside x y)) : False := by
  classical
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0<C.c := by linarith only [db.1]
  have bp : 0<B.c := by linarith only [bb.1]
  have capV : C.loV+C.side≤(7/20)*(C.c+C.s) := by
    apply le_of_not_gt
    intro failure
    apply missingM
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,left.1,origin.2.1,central.2.2.1,dp,dn.1,dn.2.1]
  have capU : C.loU+C.side≤(7/20)*(C.c-C.s) := by
    apply le_of_not_gt
    intro failure
    have lowerV : C.loV < -(7/20)*(C.c+C.s) := by
      linarith only [capV,side,db.2.2.2.2.2]
    apply missingG
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,lowerV,origin.1,central.2.2.2,dp,dn.1,dn.2.1]
  have short : (37/50)*C.c+(13/20)*C.s<1 := by
    nlinarith only [C.unit_normal,sq_nonneg ((13/20)*C.c-(37/50)*C.s),
      sq_nonneg ((37/50)*C.c+(13/20)*C.s-1)]
  have floorV : C.side+(39/100)*C.s-C.c≤C.loV+C.side := by
    apply le_of_not_gt
    intro failure
    have lowerU : C.loU< -(39/100)*C.c-C.s := by linarith only [capU,side,short]
    apply missingF
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,lowerU,central.2.1,central.2.2.2,dp,dn.1,dn.2.1]
  have all := C1092MMMMPairAxes.alternatives C B side same dp dn.2.1 bp
    (by linarith only [bp,bn.1]) (by linarith only [db.2.1,dn.1])
    origin central marker ordinary capU apart
  let d := C.c
  let r := C.s
  let b := B.c
  let t := -B.s
  let u := C.loU+C.side
  let v := C.loV+C.side
  let alpha := b*d-t*r
  let k := b*r+t*d
  have an : 0≤alpha := by
    have first := mul_nonneg (sub_nonneg.mpr bn.2.1) dp.le
    have last := mul_nonneg bn.1 (sub_nonneg.mpr dn.2.1)
    dsimp [alpha,b,d,t,r]
    nlinarith only [first,last]
  have kp : 0<k := by
    have first := mul_nonneg bp.le dn.1
    have last := mul_pos (show 0< -B.s by linarith only [faces.sine]) dp
    dsimp [k,b,r,t,d]
    nlinarith only [first,last,dp]
  have haB : 1<B.side := by rwa [←same]
  rcases all with longitudinal|transverse|ownTransverse
  · have longitudinal : B.loU+B.side≤lower C b (-t) := by
      simpa only [b,t,neg_neg] using longitudinal
    have support := lower_pn C b (-t) alpha (-k)
      (by dsimp [alpha,b,t,d,r]; ring) (by dsimp [k,b,t,d,r]; ring)
      an (by linarith only [kp])
    have first := mul_nonneg an (sub_nonneg.mpr capU)
    have last := mul_nonneg kp.le (sub_nonneg.mpr floorV)
    have strict := mul_pos (sub_pos.mpr side)
      (show 0<1+alpha+k by linarith only [an,kp])
    have necessary : 1<b+t+alpha*(7/20)*(d-r)+k*(d-(39/100)*r)-alpha-k := by
      have plow := faces.lowerU
      rw [←same] at longitudinal
      dsimp [d,r,b,t] at first last ⊢
      nlinarith only [longitudinal,support,first,last,strict,plow]
    have identity : b+t+alpha*(7/20)*(d-r)+k*(d-(39/100)*r)-alpha-k=
        b*(27/20-d-r+(13/20)*d*r-(37/50)*r^2)+
          t*(2+r-d-(37/50)*d*r-(13/20)*r^2) := by
      dsimp [alpha,k]
      linear_combination ((7/20)*b+t)*dn.2.2
    have margin := C1092MMMPNortheastSignScalars.longitudinal dn bn
    rw [identity] at necessary
    linarith only [necessary,margin]
  · change v≤lower B (-r) d at transverse
    have support := lower_np B (-r) d (-k) alpha
      (by dsimp [k,b,t,d,r]; ring) (by dsimp [alpha,b,t,d,r]; ring)
      (by linarith only [kp]) an
    have first := mul_nonneg kp.le (sub_nonneg.mpr faces.lowerU)
    have last := mul_nonneg an (sub_nonneg.mpr faces.upperV)
    have strict := mul_pos (sub_pos.mpr haB)
      (show 0<k+alpha by linarith only [kp,an])
    have bound : lower B (-r) d<k*(b+t-1)+alpha*(b-(39/100)*t-1) := by
      nlinarith only [support,first,last,strict]
    have identity : k*(b+t-1)+alpha*(b-(39/100)*t-1)=
        -d*(b+t-1-(61/100)*b*t)+r*(1-b+t-(61/100)*t^2) := by
      dsimp [k,alpha]
      linear_combination (d+r)*bn.2.2
    have margin := C1092MMMPNortheastSignScalars.transverse dn bn faces.sine faces.cosine
    rw [identity] at bound
    dsimp [v,d,r] at transverse
    linarith only [transverse,bound,margin,floorV,side]
  · change upper C (-B.s) B.c≤B.loV at ownTransverse
    have point := (strict_bounds C 0 0 (-B.s) B.c
      (by nlinarith only [B.unit_normal]) origin).2
    have qnegative : B.loV<0 := by linarith only [faces.upperV,haB,bb.2.1,bn.1]
    linarith only [ownTransverse,point,qnegative]

#print axioms impossible
end N12Compact.C1092MMMPNortheastPositiveCentral
