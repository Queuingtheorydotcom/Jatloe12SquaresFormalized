import Compact.Geometry.C977CornerSectorBounds

/-! Exact endpoint inequalities for a genuine O/L/W support cycle.
The marker coordinate 457/500 is weakened to 1 in both boundary faces.
This removes numerical angle bounds from the entire scalar argument. -/
namespace N12Compact.CornerWallCycleBounds

open C977CornerCubic C977CornerSectorBounds

noncomputable def bottom (c s : ℝ) : ℝ := 1+s/c-2*s-s^2/c

private theorem bottom_mul {c s : ℝ} (hc : 0<c) :
    c*bottom c s=c+s-2*c*s-s^2 := by
  unfold bottom
  field_simp [ne_of_gt hc]

/-- A positive linear functional on this unit arc lies above the smaller
endpoint value. The proof uses the exact sine-coordinate chord. -/
theorem arc_nonnegative {c s l r b p q : ℝ}
    (normal : Normal c s) (point : Normal l r) (order : r≤s)
    (hp : 0≤p) (first : 0≤b+p) (last : 0≤b+p*c+q*s) :
    0≤b+p*l+q*r := by
  have cb := normal_bounds normal
  have lb := normal_bounds point
  have hc : 0<c := by linarith only [cb.1]
  by_cases zero : s=0
  · have rz : r=0 := by linarith only [order,point.1,zero]
    have leq : l=1 := by nlinarith only [point.2.2,rz,lb.1]
    simpa only [rz,leq,mul_one,mul_zero,add_zero] using first
  · have sp : 0<s := lt_of_le_of_ne normal.1 (Ne.symm zero)
    have raw := arc_chord normal point order (show (0:ℝ)≤0 by norm_num)
    have identity :
        s*((1-0*r)*(c*l+s*r))-((s-r)*c+r*(1-0*s)) =
          c*(s*l-s+r*(1-c)) := by
      linear_combination r*normal.2.2
    have scaled : 0≤c*(s*l-s+r*(1-c)) := by linarith only [raw,identity]
    have chord := nonneg_of_mul_nonneg_right scaled hc
    have h0 := mul_nonneg (sub_nonneg.mpr order) first
    have h1 := mul_nonneg point.1 last
    have correction := mul_nonneg hp chord
    have weighted : 0≤s*(b+p*l+q*r) := by
      nlinarith only [h0,h1,correction]
    exact nonneg_of_mul_nonneg_right weighted sp

/-- The horizontal singleton endpoint of the cycle. -/
theorem endpoint_zero {c s d t : ℝ} (on : Normal c s) (wn : Normal d t)
    (order : s≤t) :
    0≤(d/c)*bottom c s+1+(t+d+d*s/c)-t-3*d := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have hc : 0<c := by linarith only [ob.1]
  have dc : d≤c := cosine_order wn on order
  have defect := mul_nonneg (sub_nonneg.mpr ob.2.1)
    (sub_nonneg.mpr ob.2.2.2.1)
  have coefficient : 0≤c^2+(1-c)*(1-s) := by
    nlinarith only [sq_nonneg c,defect]
  have monotone := mul_nonneg (sub_nonneg.mpr dc) coefficient
  have endpoint := mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr ob.2.1))
    (show 0≤c+s-1 by linarith only [ob.2.2.2.2.1])
  have identity :
      c^2*((d/c)*bottom c s+1+(t+d+d*s/c)-t-3*d) =
        c^2-d*(c^2+(1-c)*(1-s)) := by
    calc
      _ = c^2-d*(c^2+(1-c)*(1-s))+d*(1-(c^2+s^2)) := by
        unfold bottom
        field_simp [ne_of_gt hc]
        ; ring
      _ = _ := by rw [on.2.2]; ring
  have numerator : 0≤c^2*((d/c)*bottom c s+1+(t+d+d*s/c)-t-3*d) := by
    nlinarith only [identity,monotone,endpoint]
  exact nonneg_of_mul_nonneg_right numerator (sq_pos_of_pos hc)

/-- The singleton with the same positive tilt as O is the second endpoint.
Its motion with W's tilt uses only the unit-vector dot-product bound. -/
theorem endpoint_self {c s d t : ℝ} (on : Normal c s) (wn : Normal d t)
    (order : s≤t) :
    0≤(d/c)*bottom c s+1+(c*t+d*s+d/c)-t-3*d := by
  have ob := normal_bounds on
  have hc : 0<c := by linarith only [ob.1]
  have dc : d≤c := cosine_order wn on order
  let Q := 2/c+s-3-2*s/c+s*(1-s)/c^2
  have qIdentity : c^2*(Q+c)=-(1-c)*(c^2+(1-c)*(1-s)) := by
    calc
      _ = -(1-c)*(c^2+(1-c)*(1-s))+(1-(c^2+s^2)) := by
        dsimp [Q]
        field_simp [ne_of_gt hc]
        ; ring
      _ = _ := by rw [on.2.2]; ring
  have defect := mul_nonneg (sub_nonneg.mpr ob.2.1)
    (sub_nonneg.mpr ob.2.2.2.1)
  have coefficient : 0≤c^2+(1-c)*(1-s) := by
    nlinarith only [sq_nonneg c,defect]
  have product := mul_nonneg (sub_nonneg.mpr ob.2.1) coefficient
  have qbound : Q≤-c := by
    have nonpositive : c^2*(Q+c)≤0 := by nlinarith only [qIdentity,product]
    have negative := nonpos_of_mul_nonpos_right nonpositive (sq_pos_of_pos hc)
    linarith only [negative]
  have qOrder := mul_nonneg (sub_nonneg.mpr dc)
    (show 0≤-c-Q by linarith only [qbound])
  have dot := dot_le_one on wn
  have sum := mul_nonneg (show 0≤c+s-1 by linarith only [ob.2.2.2.2.1])
    (sub_nonneg.mpr order)
  have moving : 1+c*Q+(c-1)*s≤1+d*Q+(c-1)*t := by
    nlinarith only [qOrder,dot,on.2.2,sum]
  have endpoint := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr ob.2.2.2.1) (sub_nonneg.mpr ob.2.1))
    (show 0≤2*c-1 by linarith only [ob.1])
  have endpointIdentity :
      c*(1+c*Q+(c-1)*s)=(1-s)*(1-c)*(2*c-1) := by
    calc
      _ = (1-s)*(1-c)*(2*c-1)+(1-(c^2+s^2)) := by
        dsimp [Q]
        field_simp [ne_of_gt hc]
        ; ring
      _ = _ := by rw [on.2.2]; ring
  have endpointNonnegative : 0≤1+c*Q+(c-1)*s := by
    have weighted : 0≤c*(1+c*Q+(c-1)*s) := by
      nlinarith only [endpoint,endpointIdentity]
    exact nonneg_of_mul_nonneg_right weighted hc
  have form :
      (d/c)*bottom c s+1+(c*t+d*s+d/c)-t-3*d=1+d*Q+(c-1)*t := by
    unfold bottom
    dsimp [Q]
    field_simp [ne_of_gt hc]
    ; ring
  rw [form]
  linarith only [moving,endpointNonnegative]

theorem positive_coefficient {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (wallOrder : s≤t) (leftOrder : r≤s) :
    0≤(d/c)*bottom c s+1+(l*(t+d)+(d*s/c)*(l+r))-t-3*d := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have hc : 0<c := by linarith only [ob.1]
  have dc : 0≤d := by linarith only [wb.1]
  let b := (d/c)*bottom c s+1-t-3*d
  let p := t+d+d*s/c
  let q := d*s/c
  have ratio : 0≤d*s/c := div_nonneg (mul_nonneg dc on.1) hc.le
  have hp : 0≤p := by dsimp [p]; linarith only [wn.1,dc,ratio]
  have h0 : 0≤b+p := by
    have h := endpoint_zero on wn wallOrder
    dsimp [b,p]
    nlinarith only [h]
  have h1 : 0≤b+p*c+q*s := by
    have h := endpoint_self on wn wallOrder
    have identity : p*c+q*s=c*t+d*s+d/c := by
      calc
        _ = c*t+d*s+d/c+(d/c)*(c^2+s^2-1) := by
          dsimp [p,q]
          field_simp [ne_of_gt hc]
          ; ring
        _ = _ := by rw [on.2.2]; ring
    dsimp [b]
    rw [add_assoc, identity]
    nlinarith only [h]
  have h := arc_nonnegative on ln leftOrder hp h0 h1
  dsimp [b,p,q] at h
  nlinarith only [h]

theorem negative_coefficient {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (wallOrder : s≤t) (leftOrder : r≤t) :
    0≤(d/c)*bottom c s+1+(l*(t+d+d*s/c)+t*r)-t-3*d := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have hc : 0<c := by linarith only [ob.1]
  have dc : 0≤d := by linarith only [wb.1]
  have cd : d≤c := cosine_order wn on wallOrder
  let b := (d/c)*bottom c s+1-t-3*d
  let p := t+d+d*s/c
  have ratio : 0≤d*s/c := div_nonneg (mul_nonneg dc on.1) hc.le
  have hp : 0≤p := by dsimp [p]; linarith only [wn.1,dc,ratio]
  have h0 : 0≤b+p := by
    have h := endpoint_zero on wn wallOrder
    dsimp [b,p]
    nlinarith only [h]
  have h1 : 0≤b+p*d+t*t := by
    have h := endpoint_self on wn wallOrder
    have cross : c*t+d*s≤1 := by
      nlinarith only [on.2.2,wn.2.2,sq_nonneg (c-t),sq_nonneg (s-d)]
    have margin := mul_nonneg (div_nonneg (sub_nonneg.mpr cd) hc.le)
      (sub_nonneg.mpr cross)
    have identity : p*d+t*t-(c*t+d*s+d/c)=((c-d)/c)*(1-c*t-d*s) := by
      calc
        _ = ((c-d)/c)*(1-c*t-d*s)+(d^2+t^2-1) := by
          dsimp [p]
          field_simp [ne_of_gt hc]
          ; ring
        _ = _ := by rw [wn.2.2]; ring
    dsimp [b]
    nlinarith only [h,margin,identity]
  have h := arc_nonnegative wn ln leftOrder hp h0 h1
  dsimp [b,p] at h
  nlinarith only [h]

private theorem cross_bound {c s l r : ℝ} (on : Normal c s) (ln : Normal l r) :
    r≤c := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have osquares := mul_nonneg (sub_nonneg.mpr on.2.1)
    (show 0≤c+s by linarith only [ob.1,on.1])
  have lsquares := mul_nonneg (sub_nonneg.mpr ln.2.1)
    (show 0≤l+r by linarith only [lb.1,ln.1])
  by_contra no
  have bad := mul_pos (show 0<r-c by linarith only [no])
    (show 0<r+c by linarith only [ob.1,ln.1])
  nlinarith only [bad,osquares,lsquares,on.2.2,ln.2.2]

/-- When L tilts beyond O, the support corner changes and contributes
an additional full-width term. The resulting coefficient is larger than
the equal-O-angle endpoint. -/
theorem positive_large_coefficient {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (wallOrder : s≤t) (leftOrder : s≤r) :
    0≤(d/c)*bottom c s+1+(l*(t+d)+d*r*(1+s/c))-t-3*d := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  have hc : 0<c := by linarith only [ob.1]
  have hd : 0≤d := by linarith only [wb.1]
  have lc : l≤c := cosine_order ln on leftOrder
  have rc := cross_bound on ln
  have first := mul_nonneg (show 0≤c+s by linarith only [ob.1,on.1])
    (sub_nonneg.mpr ln.2.1)
  have second := mul_nonneg (sub_nonneg.mpr on.2.1) (sub_nonneg.mpr rc)
  have margin : 0≤(c+s)*(c+l)-2*c*(r+s) := by
    nlinarith only [first,second]
  have weighted := mul_nonneg (sub_nonneg.mpr leftOrder) margin
  have identity :
      (c+l)*((c+s)*(r-s)-2*c*(c-l)) =
        (r-s)*((c+s)*(c+l)-2*c*(r+s)) := by
    linear_combination 2*c*ln.2.2-2*c*on.2.2
  have chord : 0≤(c+s)*(r-s)-2*c*(c-l) := by
    have scaled : 0≤(c+l)*((c+s)*(r-s)-2*c*(c-l)) := by
      nlinarith only [identity,weighted]
    exact nonneg_of_mul_nonneg_right scaled (by linarith only [ob.1,lb.1])
  have h0 := mul_nonneg hd chord
  have h1 := mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr wn.2.1))
    (sub_nonneg.mpr lc)
  have differenceIdentity :
      c*((l*(t+d)+d*r*(1+s/c))-(c*t+d*s+d/c)) =
        d*((c+s)*(r-s)-2*c*(c-l))+c*(d-t)*(c-l) := by
    calc
      _ = d*((c+s)*(r-s)-2*c*(c-l))+c*(d-t)*(c-l)+
          d*(c^2+s^2-1) := by
        field_simp [ne_of_gt hc]
        ; ring
      _ = _ := by rw [on.2.2]; ring
  have difference : c*t+d*s+d/c≤l*(t+d)+d*r*(1+s/c) := by
    have weighted : 0≤c*((l*(t+d)+d*r*(1+s/c))-(c*t+d*s+d/c)) := by
      nlinarith only [differenceIdentity,h0,h1]
    have unscaled := nonneg_of_mul_nonneg_right weighted hc
    linarith only [unscaled]
  have endpoint := endpoint_self on wn wallOrder
  linarith only [endpoint,difference]

/-- When negative L tilts beyond W, its upper support corner changes.
The new width coefficient increases from the equal-W-angle endpoint. -/
theorem negative_large_coefficient {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (wallOrder : s≤t) (leftOrder : t≤r) :
    0≤(d/c)*bottom c s+1+(d*l*(1+s/c)+r*(t+d))-t-3*d := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  have hc : 0<c := by linarith only [ob.1]
  have hd : 0≤d := by linarith only [wb.1]
  have dc : d≤c := cosine_order wn on wallOrder
  have ld : l≤d := cosine_order ln wn leftOrder
  have chordProduct := mul_nonneg (sub_nonneg.mpr leftOrder)
    (show 0≤d+l-r-t by linarith only [wn.2.1,ln.2.1])
  have chordIdentity : (d+l)*(r-t-d+l)=(r-t)*(d+l-r-t) := by
    linear_combination ln.2.2-wn.2.2
  have chord : 0≤r-t-d+l := by
    have weighted : 0≤(d+l)*(r-t-d+l) := by
      nlinarith only [chordIdentity,chordProduct]
    exact nonneg_of_mul_nonneg_right weighted (by linarith only [wb.1,lb.1])
  have cross0 := mul_nonneg hc.le (sub_nonneg.mpr wallOrder)
  have cross1 := mul_nonneg on.1 (sub_nonneg.mpr dc)
  have ratio : 0≤t-d*s/c := by
    have identity : c*(t-d*s/c)=c*t-d*s := by
      field_simp [ne_of_gt hc]
    have weighted : 0≤c*(t-d*s/c) := by
      nlinarith only [identity,cross0,cross1]
    exact nonneg_of_mul_nonneg_right weighted hc
  have coefficient : 0≤d*(1+s/c) :=
    mul_nonneg hd (add_nonneg zero_le_one (div_nonneg on.1 hc.le))
  have p0 := mul_nonneg coefficient chord
  have p1 := mul_nonneg ratio (sub_nonneg.mpr leftOrder)
  have differenceIdentity :
      (d*l*(1+s/c)+r*(t+d))-(d*(t+d+d*s/c)+t*t) =
        d*(1+s/c)*(r-t-d+l)+(t-d*s/c)*(r-t) := by ring
  have difference : d*(t+d+d*s/c)+t*t≤d*l*(1+s/c)+r*(t+d) := by
    nlinarith only [differenceIdentity,p0,p1]
  have endpoint := negative_coefficient on wn wn wallOrder (le_refl t)
  linarith only [endpoint,difference]

end N12Compact.CornerWallCycleBounds
