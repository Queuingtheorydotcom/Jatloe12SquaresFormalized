import Compact.Geometry.CornerWallMarkerShared
import Compact.Geometry.CornerWallMarkerOtherMixedBounds

/-! The complete positive-L L-axis / W-axis separator with the genuine
foreign marker. The full O support width is kept in the scalar theorem. -/
namespace N12Compact.CornerWallMarkerOtherMixed
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner

theorem sector (O L W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c L.s) (wn : Normal W.c t)
    (ws : W.s=-t) (side : 1<L.side)
    (sameOL : O.side=L.side) (sameLW : L.side=W.side)
    (oBox : InsideContainer O) (lBox : InsideContainer L)
    (oCap : O.loU+O.side≤2*O.c+(457/500)*O.s)
    (wCap : W.loV+W.side≤(457/500)*t+3*W.c)
    (order : O.s≤t) (small : t≤3/5) (wide : 4/5≤W.c)
    (ol : upper O (-L.s) L.c≤L.loV)
    (lw : upper L t W.c≤W.loV) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0<O.c := by linarith only [ob.1]
  have hd : 0<W.c := by linarith only [wide]
  have hl : 0<L.c := by linarith only [lb.1]
  let D := O.s*L.c-O.c*L.s
  let extra := (D+|D|)/2
  have extra0 : 0≤extra := by dsimp [extra]; clear_value D; linarith only [neg_le_abs D]
  have extraD : D≤extra := by dsimp [extra]; clear_value D; linarith only [le_abs_self D]
  have lower := CornerWallMarkerShared.bottom_support O L.c L.s
    (2*O.c+(457/500)*O.s) on hl.le ln.1 oBox oCap
  rw [sameOL] at lower
  let p := t*L.c+W.c*L.s
  let q := W.c*L.c-t*L.s
  have pp : 0≤p := by
    dsimp [p]; exact add_nonneg (mul_nonneg wn.1 hl.le) (mul_nonneg hd.le ln.1)
  have qp : 0≤q := by
    have first := mul_nonneg hd.le (sub_nonneg.mpr ln.2.1)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr wn.2.1)
    dsimp [q]; nlinarith only [first,second]
  have form : upper L t W.c=p*(L.loU+L.side)+q*(L.loV+L.side) := by
    rw [upper_in_bands]
    rw [show t*L.c+W.c*L.s=p by rfl,
      show -t*L.s+W.c*L.c=q by dsimp [q]; ring]
    rw [abs_of_nonneg pp,abs_of_nonneg qp]
    ring
  have wall0 := FourSquareBLBridge.left_wall L hl.le lBox
  rw [abs_of_nonneg ln.1] at wall0
  dsimp [centerX] at wall0
  have wall : 0≤L.c*L.loU-L.s*(L.loV+L.side) := by nlinarith only [wall0]
  have wallWeighted := mul_nonneg pp wall
  have formIdentity :
      L.c*upper L t W.c-W.c*(L.loV+L.side)-L.side*L.c*p=
        p*(L.c*L.loU-L.s*(L.loV+L.side)) := by
    rw [form]
    dsimp [p,q]
    linear_combination W.c*(L.loV+L.side)*ln.2.2
  have lowerL : W.c*(L.loV+L.side)+L.side*L.c*p≤L.c*upper L t W.c := by
    nlinarith only [formIdentity,wallWeighted]
  have olWeighted := mul_nonneg (mul_nonneg hc.le hd.le) (sub_nonneg.mpr ol)
  have lwWeighted := mul_nonneg (mul_nonneg hc.le hl.le) (sub_nonneg.mpr lw)
  have lWeighted := mul_nonneg hc.le (sub_nonneg.mpr lowerL)
  have oWeighted := mul_nonneg hd.le (sub_nonneg.mpr lower)
  have top := mul_nonneg (mul_nonneg hc.le hl.le) (sub_nonneg.mpr wCap)
  rw [←sameLW] at top
  let Q := W.c*(O.c*(O.c*L.c+O.s*L.s)+L.s+O.c*extra)+
    O.c*W.c+O.c*L.c*p+O.c*L.c
  let R := W.c*L.s*(2*O.c+(457/500)*O.s)+
    O.c*L.c*((457/500)*t+3*W.c)
  have positive : 0<Q := by
    have inner := add_nonneg (mul_nonneg hc.le hl.le) (mul_nonneg on.1 ln.1)
    have first := mul_nonneg hd.le (add_nonneg
      (add_nonneg (mul_nonneg hc.le inner) ln.1) (mul_nonneg hc.le extra0))
    have second := mul_pos hc hd
    have third := mul_nonneg (mul_nonneg hc.le hl.le) pp
    have fourth := mul_pos hc hl
    dsimp [Q]
    nlinarith only [first,second,third,fourth]
  have combined : L.side*Q≤R := by
    dsimp [Q,R,extra,D] at *
    clear_value p q
    nlinarith only [olWeighted,lwWeighted,lWeighted,oWeighted,top]
  have scalar := CornerWallMarkerOtherMixedBounds.margin on wn ln
    order small wide extra0 extraD
  have scaled := mul_nonneg (mul_nonneg hc.le hl.le) scalar
  have identity :
      (O.c*L.c)*(1+W.c*O.c+t*L.c+W.c*L.s+W.c/L.c+
        (W.c*L.s/L.c)*(O.s-2+(1-(457/500)*O.s)/O.c)-
        (457/500)*t-3*W.c+(W.c/L.c)*extra)=Q-R := by
    dsimp [Q,R,p]
    field_simp [hc.ne',hl.ne']
    ring
  have width := mul_pos (sub_pos.mpr side) positive
  clear_value Q R extra D p q
  nlinarith only [combined,scaled,identity,width]

#print axioms sector
end N12Compact.CornerWallMarkerOtherMixed
