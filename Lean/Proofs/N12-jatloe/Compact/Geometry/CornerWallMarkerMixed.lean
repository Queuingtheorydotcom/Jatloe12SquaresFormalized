import Compact.Geometry.CornerWallMarkerMixedBounds
import Compact.Geometry.CornerWallMarkerShared

/-! The full positive-L O-v / L-v selector, using genuine marker faces.
The lower-angle branch uses L's actual left container wall; the higher
branch uses its original strict marker. No virtual wall or top seed is
assumed. -/
namespace N12Compact.CornerWallMarkerMixed

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic hiding boundary
open C977CornerSectorBounds C977NegativeCorner
open CornerWallMarkerMixedBounds

theorem low_sector (O L W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c L.s) (wn : Normal W.c t)
    (ws : W.s=-t) (side : 1<L.side) (same : L.side=W.side)
    (lBox : InsideContainer L) (wBox : InsideContainer W)
    (bottomFace : boundary O.c O.s<O.loV+O.side)
    (top : W.loV+W.side≤t+3*W.c)
    (order : O.s≤t) (leftOrder : L.s≤O.s)
    (small : t≤3/5) (wide : 4/5≤W.c)
    (ol : O.loV+O.side≤lower L (-O.s) O.c)
    (lw : L.loV+L.side≤lower W (-L.s) L.c) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0<O.c := by linarith only [ob.1]
  have hd : 0<W.c := by linarith only [wide]
  have lc : 0<L.c := by linarith only [lb.1]
  let D := O.c*L.s-O.s*L.c
  let K := O.c*L.c+O.s*L.s
  have cosine := cosine_order on ln leftOrder
  have cp0 := mul_nonneg hc.le (sub_nonneg.mpr leftOrder)
  have cp1 := mul_nonneg on.1 (sub_nonneg.mpr cosine)
  have dn : D≤0 := by dsimp [D]; nlinarith only [cp0,cp1]
  have kp : 0≤K := by
    dsimp [K]
    exact add_nonneg (mul_nonneg hc.le lc.le) (mul_nonneg on.1 ln.1)
  have form : lower L (-O.s) O.c=D*(L.loU+L.side)+K*L.loV := by
    rw [lower_in_bands]
    rw [show (-O.s)*L.c+O.c*L.s=D by dsimp [D]; ring,
      show -(-O.s)*L.s+O.c*L.c=K by dsimp [K]; ring]
    rw [abs_of_nonpos dn,abs_of_nonneg kp]
    ring
  have wall0 := FourSquareBLBridge.left_wall L lc.le lBox
  rw [abs_of_nonneg ln.1] at wall0
  dsimp [centerX] at wall0
  have wall : 0≤L.c*L.loU-L.s*(L.loV+L.side) := by nlinarith only [wall0]
  have wallWeighted := mul_nonneg (neg_nonneg.mpr dn) wall
  have separated := mul_nonneg lc.le (sub_nonneg.mpr ol)
  have identity :
      O.c*L.loV-L.c*(O.loV+O.side)+L.side*D*(L.c+L.s) =
        -D*(L.c*L.loU-L.s*(L.loV+L.side))+
          L.c*(lower L (-O.s) O.c-(O.loV+O.side)) := by
    rw [form]
    dsimp [D,K]
    linear_combination -O.c*L.loV*ln.2.2
  have lower : L.c*(O.loV+O.side)-L.side*D*(L.c+L.s)≤O.c*L.loV := by
    nlinarith only [identity,wallWeighted,separated]
  have upper := CornerWallMarkerShared.wall_support W t L.c L.s (t+3*W.c)
    wn ln ws wBox top
  rw [←same] at upper
  have lwWeighted := mul_nonneg hd.le (sub_nonneg.mpr lw)
  have lowerWeighted := mul_nonneg hd.le (sub_nonneg.mpr lower)
  have upperWeighted := mul_nonneg hc.le (sub_nonneg.mpr upper)
  have lwScaled := mul_nonneg hc.le lwWeighted
  let Q := O.c*W.c-W.c*D*(L.c+L.s)+O.c*(W.c*(L.s*W.c+L.c*t)+L.c)
  have qp : 0<Q := by
    have p0 := mul_pos hc hd
    have p1 := mul_nonneg hd.le
      (mul_nonneg (neg_nonneg.mpr dn) (add_nonneg lc.le ln.1))
    have p2 := mul_nonneg ln.1 hd.le
    have p3 := mul_nonneg lc.le wn.1
    have p4 := mul_nonneg hc.le
      (add_nonneg (mul_nonneg hd.le (add_nonneg p2 p3)) lc.le)
    dsimp [Q]
    nlinarith only [p0,p1,p4]
  have combined :
      W.c*L.c*(O.loV+O.side)+L.side*Q≤O.c*L.c*(t+3*W.c) := by
    dsimp [Q]
    nlinarith only [lowerWeighted,upperWeighted,lwScaled]
  have scalar := low_margin on wn ln order leftOrder small wide
  have scaled := mul_nonneg (mul_nonneg hc.le hd.le) scalar
  have scalarIdentity :
      (O.c*W.c)*(1+(L.c/O.c)*boundary O.c O.s-D*(L.c+L.s)/O.c+
        L.s*W.c+L.c*t+L.c/W.c-3*L.c-L.c*t/W.c) =
      W.c*L.c*boundary O.c O.s+Q-O.c*L.c*(t+3*W.c) := by
    dsimp [Q]
    field_simp [ne_of_gt hc,ne_of_gt hd]
    ring
  have face := mul_pos (mul_pos hd lc) (sub_pos.mpr bottomFace)
  have width := mul_pos (sub_pos.mpr side) qp
  dsimp [D] at scalarIdentity
  clear_value Q D K
  ring_nf at scalarIdentity scaled
  nlinarith only [combined,scaled,scalarIdentity,face,width]

theorem high_sector (O L W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c L.s) (wn : Normal W.c t)
    (ws : W.s=-t) (side : 1<L.side) (same : L.side=W.side)
    (wBox : InsideContainer W) (marker : L.Inside (457/500) 1)
    (bottomFace : boundary O.c O.s<O.loV+O.side)
    (top : W.loV+W.side≤t+3*W.c)
    (order : O.s≤t) (leftOrder : O.s≤L.s)
    (small : t≤3/5) (wide : 4/5≤W.c)
    (ol : O.loV+O.side≤lower L (-O.s) O.c)
    (lw : L.loV+L.side≤lower W (-L.s) L.c) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0<O.c := by linarith only [ob.1]
  have hd : 0<W.c := by linarith only [wide]
  have lc : 0<L.c := by linarith only [lb.1]
  let D := O.c*L.s-O.s*L.c
  let K := O.c*L.c+O.s*L.s
  let U := (457/500)*L.c+L.s
  have cosine := cosine_order ln on leftOrder
  have cp0 := mul_nonneg hc.le (sub_nonneg.mpr leftOrder)
  have cp1 := mul_nonneg on.1 (sub_nonneg.mpr cosine)
  have dn : 0≤D := by dsimp [D]; nlinarith only [cp0,cp1]
  have kp : 0<K := by
    have p0 := mul_pos hc lc
    have p1 := mul_nonneg on.1 ln.1
    dsimp [K]
    linarith only [p0,p1]
  have form : lower L (-O.s) O.c=D*L.loU+K*L.loV := by
    rw [lower_in_bands]
    rw [show (-O.s)*L.c+O.c*L.s=D by dsimp [D]; ring,
      show -(-O.s)*L.s+O.c*L.c=K by dsimp [K]; ring]
    rw [abs_of_nonneg dn,abs_of_nonneg kp.le]
    ring
  have markerBound : L.loU<U := by
    dsimp [U]
    linarith only [marker.1]
  have markerWeighted := mul_nonneg dn (sub_nonneg.mpr markerBound.le)
  have lower : O.loV+O.side-D*U≤K*L.loV := by
    rw [form] at ol
    nlinarith only [ol,markerWeighted]
  have upper := CornerWallMarkerShared.wall_support W t L.c L.s (t+3*W.c)
    wn ln ws wBox top
  rw [←same] at upper
  have lwWeighted := mul_nonneg hd.le (sub_nonneg.mpr lw)
  have lowerWeighted := mul_nonneg hd.le (sub_nonneg.mpr lower)
  have upperWeighted := mul_nonneg kp.le (sub_nonneg.mpr upper)
  have lwScaled := mul_nonneg kp.le lwWeighted
  let Q := K*(W.c+W.c*(L.s*W.c+L.c*t)+L.c)
  have qp : 0<Q := by
    have p0 := mul_nonneg ln.1 hd.le
    have p1 := mul_nonneg lc.le wn.1
    have p2 := mul_nonneg hd.le (add_nonneg p0 p1)
    have inner : 0<W.c+W.c*(L.s*W.c+L.c*t)+L.c := by
      linarith only [hd,p2,lc]
    exact mul_pos kp inner
  have combined :
      W.c*(O.loV+O.side-D*U)+L.side*Q≤K*L.c*(t+3*W.c) := by
    dsimp [Q]
    nlinarith only [lowerWeighted,upperWeighted,lwScaled]
  have scalar := high_margin on wn ln order leftOrder small wide
  have scaled := mul_nonneg (mul_nonneg hd.le kp.le) scalar
  have scalarIdentity :
      (W.c*K)*((boundary O.c O.s-D*U)/K+
        1+L.s*W.c+L.c*t+L.c/W.c-3*L.c-L.c*t/W.c) =
      W.c*(boundary O.c O.s-D*U)+Q-K*L.c*(t+3*W.c) := by
    dsimp [Q]
    field_simp [ne_of_gt hd,ne_of_gt kp]
    ring
  have face := mul_pos hd (sub_pos.mpr bottomFace)
  have width := mul_pos (sub_pos.mpr side) qp
  dsimp [D,K,U] at scalarIdentity
  dsimp [D,K,U] at combined scaled
  clear_value Q D K U
  nlinarith only [combined,scaled,scalarIdentity,face,width]

theorem sector (O L W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c L.s) (wn : Normal W.c t)
    (ws : W.s=-t) (side : 1<L.side) (same : L.side=W.side)
    (lBox : InsideContainer L) (wBox : InsideContainer W)
    (marker : L.Inside (457/500) 1)
    (bottomFace : boundary O.c O.s<O.loV+O.side)
    (top : W.loV+W.side≤t+3*W.c)
    (order : O.s≤t) (small : t≤3/5) (wide : 4/5≤W.c)
    (ol : O.loV+O.side≤lower L (-O.s) O.c)
    (lw : L.loV+L.side≤lower W (-L.s) L.c) : False := by
  rcases le_total L.s O.s with low | high
  · exact low_sector O L W t on ln wn ws side same lBox wBox bottomFace top
      order low small wide ol lw
  · exact high_sector O L W t on ln wn ws side same wBox marker bottomFace top
      order high small wide ol lw

end N12Compact.CornerWallMarkerMixed
