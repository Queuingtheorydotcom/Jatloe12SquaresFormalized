import Compact.Geometry.PositiveCornerSmallBottom
import Compact.Geometry.CornerSingletonPair
import Compact.Geometry.LeftSingletonWallSeparation

/-! The full positive-left-singleton sector of the remaining positive-wall
upper-U escape. The bottom square is genuinely negative, with its two
original face bounds. All four L/W separating axes are ruled out; the
negative-L sector is not asserted here. -/
namespace N12Compact.PositiveWallUpperUPositiveLeft

open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem left_wall (q : OpenSquare) (normal : Normal q.c q.s)
    (box : InsideContainer q) : 0≤q.c*q.loU-q.s*(q.loV+q.side) := by
  have wall := FourSquareBLBridge.left_wall q (le_trans normal.1 normal.2.1) box
  rw [abs_of_nonneg normal.1] at wall
  dsimp [centerX] at wall
  linarith only [wall]

private theorem corner (q : OpenSquare) (u v : ℝ)
    (hu : q.loU≤u ∧ u≤q.loU+q.side)
    (hv : q.loV≤v ∧ v≤q.loV+q.side) :
    ClosedInside q (q.c*u-q.s*v) (q.s*u+q.c*v) := by
  have first : q.c*(q.c*u-q.s*v)+q.s*(q.s*u+q.c*v)=u := by
    linear_combination u*q.unit_normal
  have second : -q.s*(q.c*u-q.s*v)+q.c*(q.s*u+q.c*v)=v := by
    linear_combination v*q.unit_normal
  change q.loU≤_ ∧ _≤q.loU+q.side ∧ q.loV≤_ ∧ _≤q.loV+q.side
  rw [first,second]
  exact ⟨hu.1,hu.2,hv.1,hv.2⟩

private theorem half_defect {l r : ℝ} (normal : Normal l r) : 2*(1-l)≤r := by
  have b := normal_bounds normal
  have product := mul_nonneg (sub_nonneg.mpr b.2.1)
    (show 0≤5*l-3 by linarith only [b.1])
  nlinarith only [product,normal.2.2,normal.1,b.2.1]

private theorem bottom_cosine {c t : ℝ} (normal : Normal c t)
    (small : t≤1/5) : 9/10≤c := by
  have b := normal_bounds normal
  have square := mul_nonneg normal.1 (sub_nonneg.mpr small)
  nlinarith only [square,normal.2.2,small,b.1,sq_nonneg (c-9/10)]

private theorem relative_positive {c t l r : ℝ}
    (on : Normal c t) (ln : Normal l r) (small : t≤1/5) : 0<c*l-t*r := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have first := mul_pos (show 0<c-t by linarith only [ob.1,small])
    (show 0<l by linarith only [lb.1])
  have second := mul_nonneg on.1 (sub_nonneg.mpr ln.2.1)
  nlinarith only [first,second]

/-- The positive singleton's own transverse axis cannot separate it from
the actual small negative bottom square. Both complete squares are used. -/
theorem not_left_axis (O L : OpenSquare) (t : ℝ) (os : O.s=-t)
    (on : Normal O.c t) (ln : Normal L.c L.s) (small : t≤1/5)
    (side : 1<O.side)
    (bottom : t*(O.loU+O.side)≤O.c*O.loV)
    (cap : O.loU+O.side≤2*O.c-(457/500)*t)
    (owned : L.Inside 1 1)
    (sep : upper O (-L.s) L.c≤L.loV) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have oc : 0<O.c := by linarith only [ob.1]
  let K := L.c*O.c-L.s*t
  let D := L.s*O.c+L.c*t
  have kp : 0<K := by
    have positive := relative_positive on ln small
    dsimp [K]
    nlinarith only [positive]
  have dp : 0≤D := by
    dsimp [D]
    exact add_nonneg (mul_nonneg ln.1 oc.le)
      (mul_nonneg (by linarith only [lb.1]) on.1)
  have form : upper O (-L.s) L.c= -D*O.loU+K*(O.loV+O.side) := by
    rw [upper_in_bands,os]
    rw [show (-L.s)*O.c+L.c*(-t)= -D by dsimp [D]; ring,
      show -(-L.s)*(-t)+L.c*O.c=K by dsimp [K]; ring]
    rw [abs_neg,abs_of_nonneg dp,abs_of_nonneg kp.le]
    ring
  have gap0 := mul_nonneg kp.le (sub_nonneg.mpr bottom)
  have gap1 := mul_nonneg ln.1 (sub_nonneg.mpr cap)
  have coefficient : 0<L.s+K*(O.c+t) := by
    have p := mul_pos kp (show 0<O.c+t by linarith only [oc,on.1])
    linarith only [ln.1,p]
  have gap2 := mul_pos (sub_pos.mpr side) coefficient
  have gap3 := mul_nonneg (mul_nonneg oc.le (sub_nonneg.mpr ln.2.1))
    (show 0≤O.c+t-1 by linarith only [ob.2.2.2.2.1])
  have square := mul_nonneg on.1 (sub_nonneg.mpr small)
  have defect : 0≤(457/500)*t-2*O.c*(1-O.c) := by
    nlinarith only [square,small,on.1,on.2.2,ob.2.1]
  have gap4 := mul_nonneg ln.1 defect
  have identity :
      O.c*(upper O (-L.s) L.c-(L.c-L.s)) =
      K*(O.c*O.loV-t*(O.loU+O.side))+
      L.s*(2*O.c-(457/500)*t-O.loU-O.side)+
      (O.side-1)*(L.s+K*(O.c+t))+
      O.c*(L.c-L.s)*(O.c+t-1)+
      L.s*((457/500)*t-2*O.c*(1-O.c)) := by
    rw [form]
    dsimp [K,D]
    linear_combination (-L.s*(O.loU+1))*on.2.2
  have positive : 0<O.c*(upper O (-L.s) L.c-(L.c-L.s)) := by
    linarith only [identity,gap0,gap1,gap2,gap3,gap4]
  have projection := pos_of_mul_pos_right positive oc.le
  nlinarith only [projection,sep,owned.2.2.1]

/-- The remaining O-axis separator lifts the entire upper V face of L.
This is a face estimate, not an assertion that L owns a fixed wall point. -/
theorem left_upper_face (O L : OpenSquare) (t : ℝ)
    (on : Normal O.c t) (ln : Normal L.c L.s) (small : t≤1/5)
    (same : O.side=L.side) (side : 1<L.side) (box : InsideContainer L)
    (cap : O.loU+O.side≤2*O.c-(457/500)*t)
    (sep : upper L O.c (-t)≤O.loU) : (957/500)*L.c<L.loV+L.side := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have lc : 0<L.c := by linarith only [lb.1]
  have cosine := bottom_cosine on small
  have chord := half_defect ln
  let K := O.c*L.c-t*L.s
  have kp : 0<K := relative_positive on ln small
  have wall := left_wall L ln box
  have southeast := corner L (L.loU+L.side) L.loV
    ⟨by linarith only [side],le_rfl⟩ ⟨le_rfl,by linarith only [side]⟩
  have projection := (closed_bounds L _ _ O.c (-t) southeast).2
  have projected : O.c*(L.c*(L.loU+L.side)-L.s*L.loV)-
      t*(L.s*(L.loU+L.side)+L.c*L.loV)≤O.loU := by
    nlinarith only [projection,sep]
  have gap0 := mul_nonneg kp.le wall
  have gap1 := mul_nonneg lc.le (sub_nonneg.mpr projected)
  have cap' : O.loU+L.side≤2*O.c-(457/500)*t := by rwa [same] at cap
  have gap2 := mul_nonneg lc.le (sub_nonneg.mpr cap')
  have coefficient : 0<K*(L.c+L.s)+t+L.c := by
    have p := mul_nonneg kp.le (show 0≤L.c+L.s by linarith only [lc,ln.1])
    linarith only [p,on.1,lc]
  have gap3 := mul_pos (sub_pos.mpr side) coefficient
  have first := mul_nonneg (show 0≤O.c-9/10 by linarith only [cosine]) lc.le
  have second := mul_nonneg on.1
    (show 0≤10/7-(L.c+L.s) by linarith only [lb.2.2.2.2.2])
  have scalar : 0≤O.c*L.c/2-t*(L.c+L.s) := by
    nlinarith only [first,second,lb.1,small]
  have s0 := mul_nonneg (mul_nonneg (by linarith only [ob.1]) lc.le)
    (show 0≤L.c+L.s-1-L.s/2 by linarith only [chord])
  have s1 := mul_nonneg lc.le (sub_nonneg.mpr ob.2.1)
  have s2 := mul_nonneg on.1 (sub_nonneg.mpr lb.2.1)
  have s3 := mul_nonneg ln.1 scalar
  have remainder : 0≤K*(L.c+L.s)+t+L.c-2*O.c*L.c-L.c*t := by
    dsimp [K]
    nlinarith only [s0,s1,s2,s3]
  have identity : t*(L.loV+L.side-(957/500)*L.c) =
      K*(L.c*L.loU-L.s*(L.loV+L.side))+
      L.c*(O.loU-(O.c*(L.c*(L.loU+L.side)-L.s*L.loV)-
        t*(L.s*(L.loU+L.side)+L.c*L.loV)))+
      L.c*(2*O.c-(457/500)*t-O.loU-L.side)+
      (L.side-1)*(K*(L.c+L.s)+t+L.c)+
      (K*(L.c+L.s)+t+L.c-2*O.c*L.c-L.c*t) := by
    dsimp [K]
    linear_combination (-t*L.loV)*ln.2.2
  have positive : 0<t*(L.loV+L.side-(957/500)*L.c) := by
    linarith only [identity,gap0,gap1,gap2,gap3,remainder]
  have height := pos_of_mul_pos_right positive on.1
  linarith only [height]

private theorem not_longitudinal (L W : OpenSquare)
    (ln : Normal L.c L.s) (side : 1<L.side) (box : InsideContainer L)
    (high : (957/500)*L.c<L.loV+L.side)
    (marker : W.Inside (457/500) 2)
    (sep : L.loU+L.side≤lower W L.c L.s) : False := by
  have lb := normal_bounds ln
  have lc : 0<L.c := by linarith only [lb.1]
  have wall := left_wall L ln box
  have gap := mul_nonneg ln.1 (sub_nonneg.mpr high.le)
  have width := mul_pos lc (sub_pos.mpr side)
  have coefficient : 0≤1-(457/500)*L.c-(43/500)*L.s := by
    linarith only [lb.2.1,lb.2.2.2.1]
  have bound := mul_nonneg lc.le coefficient
  have projection := (strict_bounds W _ _ L.c L.s L.unit_normal marker).1
  have separation := mul_nonneg lc.le (sub_nonneg.mpr sep)
  have strict := mul_pos lc (sub_pos.mpr projection)
  nlinarith only [wall,gap,width,bound,separation,strict]

private theorem not_left_transverse (L W : OpenSquare)
    (ln : Normal L.c L.s) (wn : Normal W.c W.s)
    (same : L.side=W.side) (side : 1<L.side) (box : InsideContainer W)
    (high : (957/500)*L.c<L.loV+L.side)
    (cap : W.loU+W.side≤W.c+(1457/500)*W.s)
    (sep : L.loV+L.side≤lower W (-L.s) L.c) : False := by
  have lb := normal_bounds ln
  have wb := normal_bounds wn
  have lc : 0<L.c := by linarith only [lb.1]
  have wc : 0<W.c := by linarith only [wb.1]
  have width : 1<W.side := by rwa [←same]
  let K := L.c*W.c+L.s*W.s
  let H := L.c*W.s-L.s*W.c
  have kp : 0≤K := add_nonneg (mul_nonneg lc.le wc.le) (mul_nonneg ln.1 wn.1)
  have southwest := corner W W.loU W.loV
    ⟨le_rfl,by linarith only [width]⟩ ⟨le_rfl,by linarith only [width]⟩
  have projected := (closed_bounds W _ _ (-L.s) L.c southwest).1
  have bound : L.loV+L.side≤H*W.loU+K*W.loV := by
    dsimp [H,K]
    nlinarith only [sep,projected]
  have gap0 := mul_nonneg lc.le (sub_nonneg.mpr cap)
  have gap1 := mul_nonneg kp (left_wall W wn box)
  have gap2 := mul_nonneg wn.1 (sub_nonneg.mpr bound)
  have balance : W.side*(L.c+K*W.s)+W.s*(L.loV+L.side)≤
      L.c*(W.c+(1457/500)*W.s) := by
    have identity :
        L.c*(W.c+(1457/500)*W.s)-W.side*(L.c+K*W.s)-W.s*(L.loV+L.side) =
        L.c*(W.c+(1457/500)*W.s-W.loU-W.side)+
        K*(W.c*W.loU-W.s*(W.loV+W.side))+
        W.s*(H*W.loU+K*W.loV-(L.loV+L.side)) := by
      dsimp [K,H]
      linear_combination (-L.c*W.loU)*wn.2.2
    linarith only [identity,gap0,gap1,gap2]
  have coefficient : 0<L.c+K*W.s := by
    have p := mul_nonneg kp wn.1
    linarith only [lc,p]
  have excess := mul_pos (sub_pos.mpr width) coefficient
  have height := mul_nonneg wn.1 (sub_nonneg.mpr high.le)
  have wallDefect := mul_nonneg (mul_nonneg lc.le (sub_nonneg.mpr wb.2.1))
    (show 0≤1-W.s by linarith only [wb.2.2.2.1])
  have linear := mul_nonneg lc.le wn.1
  have quadratic := mul_nonneg ln.1 (sq_nonneg W.s)
  dsimp [K] at excess balance
  nlinarith only [balance,excess,height,wallDefect,linear,quadratic]

private theorem not_wall_transverse (O L W : OpenSquare) (t : ℝ)
    (on : Normal O.c t) (ln : Normal L.c L.s) (wn : Normal W.c W.s)
    (small : t≤1/5) (sameOL : O.side=L.side) (sameLW : L.side=W.side)
    (side : 1<L.side) (lBox : InsideContainer L) (wBox : InsideContainer W)
    (oCap : O.loU+O.side≤2*O.c-(457/500)*t)
    (wCap : W.loU+W.side≤W.c+(1457/500)*W.s)
    (ol : upper L O.c (-t)≤O.loU)
    (lw : upper L (-W.s) W.c≤W.loV) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have wb := normal_bounds wn
  have oc : 0<O.c := by linarith only [ob.1]
  have lc : 0<L.c := by linarith only [lb.1]
  have wc : 0<W.c := by linarith only [wb.1]
  let x := L.c*L.loU-L.s*(L.loV+L.side)
  let y := L.s*(L.loU+L.side)+L.c*L.loV
  have wall : 0≤x := left_wall L ln lBox
  have southeast := corner L (L.loU+L.side) L.loV
    ⟨by linarith only [side],le_rfl⟩ ⟨le_rfl,by linarith only [side]⟩
  have northwest := corner L L.loU (L.loV+L.side)
    ⟨le_rfl,by linarith only [side]⟩ ⟨by linarith only [side],le_rfl⟩
  have se := (closed_bounds L _ _ O.c (-t) southeast).2
  have nw := (closed_bounds L _ _ (-W.s) W.c northwest).2
  have seBound : O.c*(x+L.side*(L.c+L.s))-t*y≤O.loU := by
    dsimp [x,y]
    nlinarith only [se,ol]
  have nwBound : -W.s*x+W.c*(y+L.side*(L.c-L.s))≤W.loV := by
    dsimp [x,y]
    nlinarith only [nw,lw]
  have relative : 0≤W.c*O.c-W.s*t := by
    have p := mul_nonneg wc.le (sub_nonneg.mpr on.2.1)
    have q := mul_nonneg on.1 (sub_nonneg.mpr wn.2.1)
    nlinarith only [p,q]
  have weightedWall := mul_nonneg relative wall
  have bottomWeight := mul_nonneg wc.le (sub_nonneg.mpr seBound)
  have wallWeight := mul_nonneg on.1 (sub_nonneg.mpr nwBound)
  have cap' : O.loU+L.side≤2*O.c-(457/500)*t := by rwa [sameOL] at oCap
  have capWeight := mul_nonneg wc.le (sub_nonneg.mpr cap')
  let Q := O.c*(L.c+L.s)+t*(L.c-L.s)
  have qp : 0≤Q := by
    dsimp [Q]
    exact add_nonneg (mul_nonneg oc.le (add_nonneg lc.le ln.1))
      (mul_nonneg on.1 (sub_nonneg.mpr ln.2.1))
  have excess := mul_pos (mul_pos wc (sub_pos.mpr side))
    (show 0<Q+1 by linarith only [qp])
  have chord := half_defect ln
  have e0 := mul_nonneg
    (show 0≤(O.c+t)/2 by linarith only [oc,on.1]) (sub_nonneg.mpr chord)
  have e1 := mul_nonneg
    (show 0≤(O.c-3*t)/2 by linarith only [ob.1,small]) ln.1
  have endpoint : 0≤Q+1-2*O.c-t := by
    dsimp [Q]
    nlinarith only [e0,e1,ob.2.1]
  have endpointWeight := mul_nonneg wc.le endpoint
  have identity : t*(W.loV-(957/500)*W.c) =
      (W.c*O.c-W.s*t)*x+
      W.c*(O.loU-(O.c*(x+L.side*(L.c+L.s))-t*y))+
      t*(W.loV-(-W.s*x+W.c*(y+L.side*(L.c-L.s))))+
      W.c*(2*O.c-(457/500)*t-O.loU-L.side)+
      W.c*(L.side-1)*(Q+1)+W.c*(Q+1-2*O.c-t) := by
    dsimp [Q]
    ring
  have positive : 0<t*(W.loV-(957/500)*W.c) := by
    linarith only [identity,weightedWall,bottomWeight,wallWeight,capWeight,excess,endpointWeight]
  have height := pos_of_mul_pos_right positive on.1
  have wSide : 1<W.side := by rwa [←sameLW]
  have actualWall := left_wall W wn wBox
  have actualCap := mul_nonneg wc.le (sub_nonneg.mpr wCap)
  have actualHeight := mul_nonneg wn.1 height.le
  have actualWidth := mul_pos (sub_pos.mpr wSide)
    (show 0<W.c+W.s by linarith only [wc,wn.1])
  have defect := mul_nonneg (sub_nonneg.mpr wb.2.1)
    (show 0≤W.c+W.s by linarith only [wc,wn.1])
  have cross := mul_nonneg wc.le wn.1
  nlinarith only [actualWall,actualCap,actualHeight,actualWidth,defect,cross]

/-- A complete continuous orientation family under a single upper-face
bound. The coefficient 2.914 includes the genuine marker escape
`.914*d+3*s`, since the positive canonical frame has `s≤d`. The strict
side excess supplies the contradiction even when the scalar slack is zero. -/
theorem impossible_relaxed (O L W : OpenSquare) (t : ℝ) (os : O.s=-t)
    (on : Normal O.c t) (ln : Normal L.c L.s) (wn : Normal W.c W.s)
    (positive : 0<t) (small : t≤1/5)
    (sameOL : O.side=L.side) (sameLW : L.side=W.side) (side : 1<L.side)
    (lBox : InsideContainer L) (wBox : InsideContainer W)
    (bottom : t*(O.loU+O.side)≤O.c*O.loV)
    (oCap : O.loU+O.side≤2*O.c-(457/500)*t)
    (wCap : W.loU+W.side≤W.c+(1457/500)*W.s)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oFar : O.Inside (187/100) (19/25))
    (lMarker : L.Inside (457/500) 1) (lCorner : L.Inside 1 1)
    (lFar : L.Inside (19/25) (187/100)) (wMarker : W.Inside (457/500) 2)
    (apartOL : ∀ x y, ¬(O.Inside x y ∧ L.Inside x y))
    (apartLW : ∀ x y, ¬(L.Inside x y ∧ W.Inside x y)) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have wb := normal_bounds wn
  have oc : 0<O.c := by linarith only [ob.1]
  have lc : 0<L.c := by linarith only [lb.1]
  have wc : 0<W.c := by linarith only [wb.1]
  have oSide : 1<O.side := by rwa [sameOL]
  have ol : upper L O.c (-t)≤O.loU := by
    rcases CornerSingletonPair.alternatives O L oc lc sameOL oMarker oNear oFar lCorner apartOL with h | h
    · rcases h with h | h
      · rw [os] at h; exfalso; linarith only [h.1,positive]
      · have h' := h.2
        rw [(ownU O).1,os] at h'
        exact h'
    · rcases h with h | h
      · have sep : upper O (-L.s) L.c≤L.loV := by simpa only [(ownV L).1] using h.2
        exact False.elim (not_left_axis O L t os on ln small oSide bottom oCap lCorner sep)
      · exact False.elim ((not_lt_of_ge ln.1) h.1)
  have high := left_upper_face O L t on ln small sameOL side lBox oCap ol
  rcases LeftSingletonWallSeparation.alternatives L W lc ln.1 wc wn.1 sameLW lMarker wMarker apartLW with h | h | h | h
  · exact not_longitudinal L W ln side lBox high wMarker h
  · exact not_left_transverse L W ln wn sameLW side wBox high wCap h
  · have far := (strict_bounds L _ _ W.c W.s W.unit_normal lFar).2
    have short : (6/25)*W.c+(261/250)*W.s<1 := by
      linarith only [wn.2.1,wb.2.2.2.2.2]
    have width : 1<W.side := by rwa [←sameLW]
    nlinarith only [far,h,short,wCap,width]
  · exact not_wall_transverse O L W t on ln wn small sameOL sameLW side lBox wBox oCap wCap ol h

/-- The actual excluded upper marker supplies the relaxed face bound
whenever it escapes W through its upper-U face. No singleton near-seed
or additional wall-angle bound is required. -/
theorem marker_cap (W : OpenSquare) (normal : Normal W.c W.s)
    (cap : W.loU+W.side≤(457/500)*W.c+3*W.s) :
    W.loU+W.side≤W.c+(1457/500)*W.s := by
  linarith only [cap,normal.2.1]

/-- Compatibility wrapper for the earlier explicit 2.88 premise.
Its proof is shared with the genuine-marker upper-U branch above. -/
theorem impossible (O L W : OpenSquare) (t : ℝ) (os : O.s=-t)
    (on : Normal O.c t) (ln : Normal L.c L.s) (wn : Normal W.c W.s)
    (positive : 0<t) (small : t≤1/5)
    (sameOL : O.side=L.side) (sameLW : L.side=W.side) (side : 1<L.side)
    (lBox : InsideContainer L) (wBox : InsideContainer W)
    (bottom : t*(O.loU+O.side)≤O.c*O.loV)
    (oCap : O.loU+O.side≤2*O.c-(457/500)*t)
    (wCap : W.loU+W.side≤W.c+(72/25)*W.s)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oFar : O.Inside (187/100) (19/25))
    (lMarker : L.Inside (457/500) 1) (lCorner : L.Inside 1 1)
    (lFar : L.Inside (19/25) (187/100)) (wMarker : W.Inside (457/500) 2)
    (apartOL : ∀ x y, ¬(O.Inside x y ∧ L.Inside x y))
    (apartLW : ∀ x y, ¬(L.Inside x y ∧ W.Inside x y)) : False :=
  impossible_relaxed O L W t os on ln wn positive small sameOL sameLW side
    lBox wBox bottom oCap (by linarith only [wCap,wn.1]) oMarker oNear oFar
    lMarker lCorner lFar wMarker apartOL apartLW

end N12Compact.PositiveWallUpperUPositiveLeft
