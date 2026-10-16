import Compact.Completion.C1092.MPPMNorthwestSignScalars
import Compact.Completion.C1092.MPPMUpperSign
import Compact.Completion.C1092.MMMMFirstPair

/-! The actual mixed-left square excludes the nonpositive northwest angle.
The center inequality is retained in its genuine direction. Every support
below belongs to the same three squares and permits contact. -/
namespace N12Compact.C1092MPPMNorthwestSign
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse C977CornerCubic C1092WholeSupports
open C1092RigidCharts C1092MMMPEndingAxes
set_option Elab.async false

private theorem axes (W L : OpenSquare) (same : W.side=L.side)
    (dn : Normal W.c (-W.s)) (small : -W.s<7/50) (close : 99/100<W.c)
    (ln : Normal L.c L.s)
    (origin : W.Inside 0 0) (marker : W.Inside (-7/20) (7/20))
    (G : L.Inside (-1) (2/5)) (Q : L.Inside (-1) (7/20))
    (P : L.Inside (-1) (-39/100))
    (apart : ∀ x y, ¬(W.Inside x y ∧ L.Inside x y)) :
    upper L W.c W.s≤W.loU ∨ L.loU+L.side≤lower W L.c L.s := by
  have db := normal_bounds dn
  have lb := normal_bounds ln
  have wp : 0<W.c := by linarith only [close]
  have lp : 0<L.c := by linarith only [lb.1]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper L nx ny≤lower W nx ny) :
      0<nx ∧ 0<(13/20)*nx+(37/50)*ny ∧ 0<nx-(2/5)*ny := by
    have first := strict_bounds L _ _ nx ny unit Q
    have last := strict_bounds W _ _ nx ny unit marker
    have bottom := strict_bounds L _ _ nx ny unit P
    have top := strict_bounds L _ _ nx ny unit G
    have zero := strict_bounds W 0 0 nx ny unit origin
    refine ⟨?_,?_,?_⟩ <;> linarith only [first.2,last.1,bottom.2,top.2,zero.1,sep]
  have all := CongruentSAT.faceSeparation_of_disjoint L W same.symm
    (fun x y own => apart x y ⟨own.2,own.1⟩)
  change pairRadius L W≤|L.c*(centerX W-centerX L)+L.s*(centerY W-centerY L)| ∨
    pairRadius L W≤|-L.s*(centerX W-centerX L)+L.c*(centerY W-centerY L)| ∨
    pairRadius W L≤|W.c*(centerX W-centerX L)+W.s*(centerY W-centerY L)| ∨
    pairRadius W L≤|-W.s*(centerX W-centerX L)+W.c*(centerY W-centerY L)| at all
  have split (nx ny radius : ℝ)
      (identity : supportRadius L nx ny+supportRadius W nx ny=radius)
      (sep : radius≤|nx*(centerX W-centerX L)+ny*(centerY W-centerY L)|) :=
    separated L W nx ny (by rwa [identity])
  have reverse (nx ny : ℝ) (sep : upper W nx ny≤lower L nx ny) :
      upper L (-nx) (-ny)≤lower W (-nx) (-ny) := by
    rw [(C1092MixedCornerSupports.negative_support L nx ny).2,
      (C1092MixedCornerSupports.negative_support W nx ny).1]
    linarith only [sep]
  rcases all with lu|lv|wu|wv
  · rcases split L.c L.s _ (parallel_radius L W) lu with forward|back
    · exact Or.inr (by simpa only [(ownU L).2] using forward)
    · have h := cone (-L.c) (-L.s) (by nlinarith only [L.unit_normal]) (reverse _ _ back)
      exfalso; linarith only [h.1,lp]
  · rcases split (-L.s) L.c _ (transverse_radius L W) lv with forward|back
    · have h := cone (-L.s) L.c (by nlinarith only [L.unit_normal]) forward
      exfalso; linarith only [h.1,ln.1]
    · have h := cone L.s (-L.c) (by nlinarith only [L.unit_normal])
        (by simpa only [neg_neg] using reverse _ _ back)
      exfalso; linarith only [h.2.1,ln.2.1,lp]
  · have identity : supportRadius L W.c W.s+supportRadius W W.c W.s=pairRadius W L := by
      rw [add_comm]; exact parallel_radius W L
    rcases split W.c W.s _ identity wu with forward|back
    · exact Or.inl (by simpa only [(ownU W).1] using forward)
    · have h := cone (-W.c) (-W.s) (by nlinarith only [W.unit_normal]) (reverse _ _ back)
      exfalso; linarith only [h.1,wp]
  · have identity : supportRadius L (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W L := by
      rw [add_comm]; exact transverse_radius W L
    rcases split (-W.s) W.c _ identity wv with forward|back
    · have h := cone (-W.s) W.c (by nlinarith only [W.unit_normal]) forward
      exfalso; linarith only [h.2.2,small,close]
    · have h := cone W.s (-W.c) (by nlinarith only [W.unit_normal])
        (by simpa only [neg_neg] using reverse _ _ back)
      exfalso; linarith only [h.1,dn.1]

theorem nonpositive_impossible (W N L : OpenSquare)
    (side : 1<W.side) (sameN : W.side=N.side) (sameL : W.side=L.side)
    (dn : Normal W.c (-W.s)) (nn : Normal N.c N.s) (positiveN : 0<N.s)
    (faces : C1092MPPMUpperSign.Faces N)
    (origin : W.Inside 0 0) (left : W.Inside (-1/2) 0)
    (diagonal : W.Inside (-1/2) (1/2)) (marker : W.Inside (-7/20) (7/20))
    (missingS : ¬W.Inside (-7/20) (-7/20)) (missingN : ¬W.Inside (7/20) (7/20))
    (markerN : N.Inside (7/20) (7/20)) (topN : N.Inside (2/5) 1)
    (ln : Normal L.c L.s) (sumL : 5/4<L.c+L.s) (centerL : centerY L≤0)
    (G : L.Inside (-1) (2/5)) (Q : L.Inside (-1) (7/20))
    (P : L.Inside (-1) (-39/100))
    (apartN : ∀ x y, ¬(W.Inside x y ∧ N.Inside x y))
    (apartL : ∀ x y, ¬(W.Inside x y ∧ L.Inside x y)) : False := by
  classical
  let C := clockwise W
  let B := clockwise N
  let d := W.c
  let r := -W.s
  let b := N.c
  let t := N.s
  let A := W.loU+W.side
  let H := W.loV+W.side
  let alpha := b*d-t*r
  let k := b*r+t*d
  have db := normal_bounds dn
  have nb := normal_bounds nn
  have dp : 0<d := by dsimp [d]; linarith only [db.1]
  have bp : 0<b := by dsimp [b]; linarith only [nb.1]
  have tp : 0<t := positiveN
  have ap : 0≤alpha := by
    have first := mul_nonneg (sub_nonneg.mpr nn.2.1) dp.le
    have last := mul_nonneg nn.1 (sub_nonneg.mpr dn.2.1)
    dsimp [alpha,b,t,d,r]; nlinarith only [first,last]
  have kp : 0<k := by
    have first := mul_nonneg bp.le dn.1
    have last := mul_pos tp dp
    dsimp [k,b,r,t,d]; linarith only [first,last]
  have cOrigin : C.Inside 0 0 := by norm_num [C,inside_clockwise]; exact origin
  have cBottom : C.Inside 0 (-1/2) := by norm_num [C,inside_clockwise]; simpa only [neg_div] using left
  have cMarker : C.Inside (-7/20) (-7/20) := by norm_num [C,inside_clockwise]; simpa only [neg_div] using marker
  have cMissing : ¬C.Inside (7/20) (-7/20) := by norm_num [C,inside_clockwise]; simpa only [neg_div] using missingS
  have support0 := C1092MMMMFirstPair.positive_support C B side sameN dn nn positiveN
    cOrigin cBottom cMarker cMissing
    (by norm_num [B,inside_clockwise]; exact markerN)
    (by norm_num [B,inside_clockwise]; exact topN)
    (by dsimp [B,clockwise]; linarith only [faces.lowerV,nb.1])
    (by dsimp [B,clockwise]; exact faces.upperU)
    (fun x y own => apartN _ _
      ⟨(inside_clockwise _ _ _).mp own.1,(inside_clockwise _ _ _).mp own.2⟩)
  have support : W.side≤b+t-alpha*A-k*H := by
    dsimp [C,B,clockwise] at support0
    dsimp [b,t,alpha,k,A,H,d,r]
    nlinarith only [support0]
  have cp : 0<C.loU+C.side := by dsimp [C,clockwise]; linarith only [origin.2.2.1]
  have av : 0<A := by dsimp [A]; linarith only [origin.2.1]
  have hv : 0<H := by dsimp [H]; linarith only [origin.2.2.2]
  have capC : C.loU+C.side≤(7/20)*(d+r) := by
    apply le_of_not_gt
    intro failure
    apply cMissing
    refine ⟨?_,?_,?_,?_⟩ <;> dsimp [C,clockwise,d,r] at failure ⊢ <;>
      linarith only [failure,origin.2.1,origin.2.2.2,origin.1,left.1,dp,dn.1,dn.2.1]
  have small0 := C1092MMMMPairScalars.small_of_support dn nn side cp av capC support0
  have small : r<7/50 := small0.1
  have close : 99/100<d := small0.2
  have capA : A≤(7/20)*(d-r) := by
    apply le_of_not_gt
    intro failure
    apply missingN
    refine ⟨?_,?_,?_,?_⟩ <;> dsimp [A,H,d,r] at failure small close ⊢ <;>
      linarith only [failure,origin.1,origin.2.2.1,diagonal.2.2.2,small,close,dn.1,dn.2.1]
  have floorH : 1-(7/20)*(d+r)≤H := by
    dsimp [C,clockwise] at capC
    dsimp [H]
    linarith only [capC,side]
  have angleSpan : b+t-1<(3/4)*t := C1092MPPMNorthwestSignScalars.upper_span nn faces.angle
  have kLower : t≤k := by
    have first := mul_nonneg tp.le (sub_nonneg.mpr dn.2.1)
    have last := mul_nonneg tp.le (show 0≤d+r-1 by dsimp [d,r]; linarith only [db.2.2.2.2.1])
    have exactGap := mul_nonneg (show 0≤b-t by dsimp [b,t]; linarith only [nn.2.1]) dn.1
    dsimp [k]
    nlinarith only [last,exactGap]
  have hCap : H<41/50 := by
    apply lt_of_not_ge
    intro bad
    have first := mul_nonneg ap av.le
    have last := mul_nonneg kp.le (show 0≤H-41/50 by linarith only [bad])
    nlinarith only [support,side,angleSpan,first,last,kLower,tp]
  let F := 1-d*A-r*H
  let K := 1-d*H+r*A
  have projection : 1<b*F+t*K := by dsimp [F,K,alpha,k]; nlinarith only [support,side]
  have projectionSquare := mul_pos (sub_pos.mpr projection)
    (show 0<b*F+t*K+1 by linarith only [projection])
  have cauchy : (b*F+t*K)^2+(t*F-b*K)^2=F^2+K^2 := by
    dsimp [b,t]; linear_combination (F^2+K^2)*nn.2.2
  have normIdentity : F^2+K^2-1=A^2+H^2-2*(d-r)*A-2*(d+r)*H+1 := by
    dsimp [F,K,d,r]; linear_combination (A^2+H^2)*dn.2.2
  have norm : 0<A^2+H^2-2*(d-r)*A-2*(d+r)*H+1 := by
    nlinarith only [cauchy,projectionSquare,sq_nonneg (t*F-b*K),normIdentity]
  have aCap := C1092MPPMNorthwestSignScalars.cap dn small close capA floorH hCap norm
  have all := axes W L sameL dn small close ln origin marker G Q P apartL
  let e := L.c
  let v := L.s
  let J := L.loU+L.side
  let V := L.loV
  let beta := d*e-r*v
  let weight := d*v+r*e
  have lb := normal_bounds ln
  have ep : 0<e := by dsimp [e]; linarith only [lb.1]
  have vt := C1092MPPMNorthwestSignScalars.wall_sine ln sumL
  have vp : 0<v := by dsimp [v]; linarith only [vt]
  have betaPos : 0<beta := by
    have first := mul_pos ep (show 0<d-r by linarith only [close,small])
    have last := mul_nonneg dn.1 (sub_nonneg.mpr ln.2.1)
    dsimp [beta,e,v]; nlinarith only [first,last]
  have weightPos : 0<weight := by
    have first := mul_pos dp vp
    have last := mul_nonneg dn.1 ep.le
    dsimp [weight]; linarith only [first,last]
  have jLow : -e+(2/5)*v<J := by dsimp [J,e,v]; linarith only [G.2.1]
  rcases all with centralAxis|leftAxis
  · have upperFormula : upper L W.c W.s=beta*J-weight*V := by
      rw [(formulas L W.c W.s).2,
        show W.c*L.c+W.s*L.s=beta by dsimp [beta,d,r,e,v]; ring,
        show -W.c*L.s+W.s*L.c=-weight by dsimp [weight,d,r,e,v]; ring,
        max_eq_left betaPos.le,max_eq_right (by linarith only [weightPos] : -weight≤0)]
      dsimp [J,V]; ring
    have center : v*J+e*V≤0 := by
      have product := mul_nonneg L.side_pos.le (sub_nonneg.mpr ln.2.1)
      change L.s*(L.loU+L.side/2)+L.c*(L.loV+L.side/2)≤0 at centerL
      dsimp [v,e,J,V]
      linarith only [centerL,product]
    have weighted := mul_nonpos_of_nonneg_of_nonpos weightPos.le center
    have lower := mul_lt_mul_of_pos_left jLow dp
    have identity : e*(beta*J-weight*V)=d*J-weight*(v*J+e*V) := by
      dsimp [beta,weight,e,v]; linear_combination (d*J)*ln.2.2
    have axis := mul_le_mul_of_nonneg_left centralAxis ep.le
    have positive := mul_pos ep (show 0<W.side-d by linarith only [side,db.2.1])
    have delta := mul_nonneg av.le (show 0≤1-e by dsimp [e]; linarith only [lb.2.1])
    have dt1 := mul_pos (show 0<d-99/100 by linarith only [close]) vp
    have dt2 := mul_pos (by norm_num : (0:ℝ)<99/100)
      (show 0<v-9/32 by dsimp [v]; linarith only [vt])
    rw [upperFormula] at axis
    rw [show W.loU=A-W.side by dsimp [A]; ring] at axis
    nlinarith only [identity,weighted,lower,axis,positive,delta,dt1,dt2,aCap]
  · have lowerFormula := lower_nn W L.c L.s beta weight
      (by dsimp [beta,d,r,e,v]; ring) (by dsimp [weight,d,r,e,v]; ring)
      betaPos.le weightPos.le
    have first := mul_lt_mul_of_pos_left
      (show W.loU< -(9/10) by dsimp [A] at aCap; linarith only [aCap,side]) betaPos
    have last := mul_lt_mul_of_pos_left
      (show W.loV< -(9/50) by dsimp [H] at hCap; linarith only [hCap,side]) weightPos
    have margin : 0<e*((9/10)*d+(9/50)*r-1)+v*(2/5-(9/10)*r+(9/50)*d) :=
      C1092MPPMNorthwestSignScalars.wall_margin dn ln small close sumL
    have identity : -e+(2/5)*v+(9/10)*beta+(9/50)*weight=
        e*((9/10)*d+(9/50)*r-1)+v*(2/5-(9/10)*r+(9/50)*d) := by
      dsimp [beta,weight]; ring
    change J≤lower W L.c L.s at leftAxis
    nlinarith only [leftAxis,lowerFormula,first,last,jLow,identity,margin]

#print axioms nonpositive_impossible
end N12Compact.C1092MPPMNorthwestSign
