import Compact.Geometry.CornerWallCycleBounds
import Compact.Geometry.C696PositiveCorner
import Compact.Geometry.LeftWallNegativeFaces

/-! A complete support-selector sector for three actual squares. O's
positive transverse axis separates O/L, and W's negative transverse axis
separates L/W. The left singleton may have either canonical orientation.
The true left wall and the full side of L enter the support identity. -/
namespace N12Compact.CornerWallCycle

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner
open CornerWallCycleBounds

private theorem relative_nonnegative {c s l r : ℝ}
    (on : Normal c s) (ln : Normal l r) : 0≤c*l-s*r := by
  have first := mul_nonneg (le_trans ln.1 ln.2.1) (sub_nonneg.mpr on.2.1)
  have second := mul_nonneg on.1 (sub_nonneg.mpr ln.2.1)
  nlinarith only [first,second]

private theorem cross_order {c s l r : ℝ}
    (on : Normal c s) (ln : Normal l r) (order : r≤s) : c*r≤s*l := by
  have ob := normal_bounds on
  have cosine := cosine_order on ln order
  have first := mul_nonneg (show 0≤c by linarith only [ob.1])
    (sub_nonneg.mpr order)
  have second := mul_nonneg on.1 (sub_nonneg.mpr cosine)
  nlinarith only [first,second]

/-- With the two indicated actual support separators, W cannot tilt at
least as far as O. The face bounds are deliberately weakened to marker
coordinate 1; the original 457/500 bounds imply them. -/
theorem transverse_sector (O L W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (wn : Normal W.c t) (ws : W.s=-t)
    (lc : 0<L.c) (canonical : |L.s|≤L.c)
    (side : 1<L.side) (same : L.side=W.side) (box : InsideContainer L)
    (order : O.s≤t)
    (bottomFace : bottom O.c O.s<O.loV+O.side)
    (wallFace : W.loV+W.side≤t+3*W.c)
    (ol : O.loV+O.side≤lower L (-O.s) O.c)
    (lw : upper L t W.c≤W.loV) : False := by
  let c := O.c
  let s := O.s
  let d := W.c
  let H := O.loV+O.side
  let h := c*t+d*s
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have hc : 0<c := by dsimp [c]; linarith only [ob.1]
  have hd : 0<d := by dsimp [d]; linarith only [wb.1]
  have hp : 0≤h := by
    dsimp [h,c,s,d]
    exact add_nonneg (mul_nonneg hc.le wn.1) (mul_nonneg hd.le on.1)
  have close (P wall : ℝ) (positive : 0≤P) (wallNonnegative : 0≤wall)
      (scalar : 0≤(d/c)*bottom c s+1+P-t-3*d)
      (identity : c*upper L t d-d*H-L.side*c*P =
        h*wall+d*(lower L (-s) c-H)) : False := by
    have wp := mul_nonneg hp wallNonnegative
    have sp := mul_nonneg hd.le (sub_nonneg.mpr ol)
    have support : d*H+L.side*c*P≤c*upper L t d := by
      dsimp only [c,s,d,H,h] at *
      nlinarith only [wp,sp,identity]
    have top0 := mul_nonneg hc.le (sub_nonneg.mpr lw)
    have top1 := mul_nonneg hc.le (sub_nonneg.mpr wallFace)
    rw [←same] at top1
    have scaled := mul_nonneg hc.le scalar
    have scalarIdentity :
        c*((d/c)*bottom c s+1+P-t-3*d)=
          d*bottom c s+c+c*P-c*(t+3*d) := by
      field_simp [ne_of_gt hc]
      ring
    have face := mul_pos hd (sub_pos.mpr bottomFace)
    have width := mul_pos (mul_pos hc (sub_pos.mpr side))
      (show 0<1+P by linarith only [positive])
    dsimp only [c,s,d,H,h] at *
    nlinarith only [support,top0,top1,scaled,scalarIdentity,face,width]
  by_cases sign : 0≤L.s
  · have ln : Normal L.c L.s :=
      ⟨sign,(abs_le.mp canonical).2,L.unit_normal⟩
    let D := c*L.s-s*L.c
    let K := c*L.c+s*L.s
    let p := t*L.c+d*L.s
    let q := d*L.c-t*L.s
    have kp : 0≤K := by
      dsimp [K]; exact add_nonneg (mul_nonneg hc.le lc.le) (mul_nonneg on.1 sign)
    have pp : 0≤p := by
      dsimp [p]; exact add_nonneg (mul_nonneg wn.1 lc.le) (mul_nonneg hd.le sign)
    have qp : 0≤q := relative_nonnegative wn ln
    have up : upper L t d=p*(L.loU+L.side)+q*(L.loV+L.side) := by
      rw [upper_in_bands]
      rw [show t*L.c+d*L.s=p by rfl,show -t*L.s+d*L.c=q by dsimp [q]; ring]
      rw [abs_of_nonneg pp,abs_of_nonneg qp]
      ring
    have wall0 := FourSquareBLBridge.left_wall L lc.le box
    rw [abs_of_nonneg sign] at wall0
    dsimp [centerX] at wall0
    have wall : 0≤L.c*L.loU-L.s*(L.loV+L.side) := by nlinarith only [wall0]
    by_cases leftOrder : L.s≤s
    · have dn : D≤0 := by
        have cross := cross_order on ln leftOrder
        dsimp [D]; linarith only [cross]
      have low : lower L (-s) c=D*(L.loU+L.side)+K*L.loV := by
        rw [lower_in_bands]
        rw [show (-s)*L.c+c*L.s=D by dsimp [D]; ring,
          show -(-s)*L.s+c*L.c=K by dsimp [K]; ring]
        rw [abs_of_nonpos dn,abs_of_nonneg kp]
        ring
      let P := L.c*(t+d)+(d*s/c)*(L.c+L.s)
      have positive : 0≤P := by
        dsimp [P]
        exact add_nonneg (mul_nonneg lc.le (add_nonneg wn.1 hd.le))
          (mul_nonneg (div_nonneg (mul_nonneg hd.le on.1) hc.le) (add_nonneg lc.le sign))
      apply close P _ positive wall (positive_coefficient on wn ln order leftOrder)
      rw [up,low]
      dsimp [P,D,K,p,q,h]
      field_simp [ne_of_gt hc]
      ring
    · have leftOrder : s≤L.s := le_of_lt (lt_of_not_ge leftOrder)
      have dp : 0≤D := by
        have cross := cross_order ln on leftOrder
        dsimp [D]; linarith only [cross]
      have low : lower L (-s) c=D*L.loU+K*L.loV := by
        rw [lower_in_bands]
        rw [show (-s)*L.c+c*L.s=D by dsimp [D]; ring,
          show -(-s)*L.s+c*L.c=K by dsimp [K]; ring]
        rw [abs_of_nonneg dp,abs_of_nonneg kp]
        ring
      let P := L.c*(t+d)+d*L.s*(1+s/c)
      have positive : 0≤P := by
        dsimp [P]
        exact add_nonneg (mul_nonneg lc.le (add_nonneg wn.1 hd.le))
          (mul_nonneg (mul_nonneg hd.le sign)
            (add_nonneg zero_le_one (div_nonneg on.1 hc.le)))
      apply close P _ positive wall (positive_large_coefficient on wn ln order leftOrder)
      rw [up,low]
      dsimp [P,D,K,p,q,h]
      field_simp [ne_of_gt hc]
      ring
  · let r := -L.s
    have rp : 0≤r := by dsimp [r]; linarith only [sign]
    have ls : L.s=-r := by dsimp [r]; ring
    have ln : Normal L.c r := by
      refine ⟨rp,?_,?_⟩
      · dsimp [r]; linarith only [(abs_le.mp canonical).1]
      · dsimp [r]; nlinarith only [L.unit_normal]
    let D := s*L.c+c*r
    let K := c*L.c-s*r
    let p := t*L.c-d*r
    let q := t*r+d*L.c
    have dp : 0≤D := by
      dsimp [D]; exact add_nonneg (mul_nonneg on.1 lc.le) (mul_nonneg hc.le rp)
    have kp : 0≤K := relative_nonnegative on ln
    have qp : 0≤q := by
      dsimp [q]; exact add_nonneg (mul_nonneg wn.1 rp) (mul_nonneg hd.le lc.le)
    have low : lower L (-s) c=-D*(L.loU+L.side)+K*L.loV := by
      have raw := lower_negative_nonpos L r (-s) c ls
        (show (-s)*L.c-c*r≤0 by dsimp [D] at dp; linarith only [dp])
        (show 0≤(-s)*r+c*L.c by dsimp [K] at kp; linarith only [kp])
      rw [raw]
      dsimp [D,K]; ring
    have wall0 := FourSquareBLBridge.left_wall L lc.le box
    rw [ls,abs_neg,abs_of_nonneg rp] at wall0
    dsimp [centerX] at wall0
    rw [ls] at wall0
    have wall : 0≤L.c*L.loU+r*L.loV := by clear_value r; nlinarith only [wall0]
    by_cases leftOrder : r≤t
    · have pp : 0≤p := by
        have cross := cross_order wn ln leftOrder
        dsimp [p]; linarith only [cross]
      have up : upper L t d=p*(L.loU+L.side)+q*(L.loV+L.side) := by
        exact upper_negative_pos L r t d ls pp qp
      let P := L.c*(t+d+d*s/c)+t*r
      have positive : 0≤P := by
        dsimp [P]
        exact add_nonneg
          (mul_nonneg lc.le (add_nonneg (add_nonneg wn.1 hd.le)
            (div_nonneg (mul_nonneg hd.le on.1) hc.le)))
          (mul_nonneg wn.1 rp)
      apply close P _ positive wall (negative_coefficient on wn ln order leftOrder)
      rw [up,low]
      dsimp [P,D,K,p,q,h]
      field_simp [ne_of_gt hc]
      ring
    · have leftOrder : t≤r := le_of_lt (lt_of_not_ge leftOrder)
      have pn : p≤0 := by
        have cross := cross_order ln wn leftOrder
        dsimp [p]; linarith only [cross]
      have up : upper L t d=p*L.loU+q*(L.loV+L.side) := by
        exact upper_negative_nonpos L r t d ls pn qp
      let P := d*L.c*(1+s/c)+r*(t+d)
      have positive : 0≤P := by
        dsimp [P]
        exact add_nonneg
          (mul_nonneg (mul_nonneg hd.le lc.le)
            (add_nonneg zero_le_one (div_nonneg on.1 hc.le)))
          (mul_nonneg rp (add_nonneg wn.1 hd.le))
      apply close P _ positive wall (negative_large_coefficient on wn ln order leftOrder)
      rw [up,low]
      dsimp [P,D,K,p,q,h]
      field_simp [ne_of_gt hc]
      ring

/-- All face inputs of `transverse_sector` follow from original local
ownership, missing markers and container walls. The two selected axes
and the angle order are the only surviving geometric choices. -/
theorem original_transverse_sector (O L W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (wn : Normal W.c t) (ws : W.s=-t)
    (lc : 0<L.c) (canonical : |L.s|≤L.c)
    (side : 1<L.side) (sameOL : O.side=L.side) (sameLW : L.side=W.side)
    (oBox : InsideContainer O) (lBox : InsideContainer L) (wBox : InsideContainer W)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oMissing : ¬O.Inside 1 1) (oMissingMarker : ¬O.Inside 2 (457/500))
    (wMarker : W.Inside (457/500) 2) (wPoint : W.Inside 1 (113/50))
    (wMissing : ¬W.Inside 1 2) (wMissingTop : ¬W.Inside (457/500) 3)
    (order : O.s≤t)
    (ol : O.loV+O.side≤lower L (-O.s) O.c)
    (lw : upper L t W.c≤W.loV) : False := by
  have oside : 1<O.side := by rwa [sameOL]
  have wside : 1<W.side := by rwa [←sameLW]
  have face := (C696PositiveCorner.corner_faces O on oside oBox
    oMarker oNear oMissing oMissingMarker).2.2.2.2
  have top := (LeftWallNegativeFaces.faces W t ws wn wside wBox
    wMarker wPoint wMissing wMissingTop).2.1
  have ob := normal_bounds on
  have hc : 0<O.c := by linarith only [ob.1]
  have nonnegative := div_nonneg (sq_nonneg O.s) hc.le
  have bottomComparison : bottom O.c O.s≤C696CornerMargins.boundary O.c O.s := by
    unfold bottom C696CornerMargins.boundary
    simp only [mul_div_assoc]
    nlinarith only [nonnegative]
  have bottomFace : bottom O.c O.s<O.loV+O.side := lt_of_le_of_lt bottomComparison face
  have wallFace : W.loV+W.side≤t+3*W.c := by nlinarith only [top,wn.1]
  exact transverse_sector O L W t on wn ws lc canonical side sameLW lBox
    order bottomFace wallFace ol lw

end N12Compact.CornerWallCycle
