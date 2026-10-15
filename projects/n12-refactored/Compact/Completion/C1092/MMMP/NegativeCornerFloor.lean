import Compact.Completion.C1092.MMMP.NegativeCenterSupports

/-! The actual negative left-wall square forces the corner's scaled
lower transverse face. All separating-axis alternatives are retained. -/
namespace N12Compact.C1092MMMPNegativeCornerFloor
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092MixedCornerSupports
set_option Elab.async false

private theorem positive_pair_scalar {d r c s : ℝ}
    (dn : Normal d r) (cn : Normal c s) :
    r*((1/5)*c^2+(1/2)*c*s-c)+
      d*(1/2+(1/2)*s^2-s+(1/5)*c*s)≤d/2-(3/5)*r := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have bounds := C1092MixedCornerScalars.elementary cn
  have product := mul_nonneg (sub_nonneg.mpr cb.2.2.2.2.1)
    (sub_nonneg.mpr cb.2.2.2.2.2)
  have cross := mul_nonneg cp.le cn.1
  have arc : 1+(4/5)*c*s≤c+s := by
    nlinarith only [product,cn.2.2,cross]
  have ordered := mul_nonneg cn.1 (sub_nonneg.mpr cn.2.1)
  have first : (1/2)*s^2-s+(1/5)*c*s≤0 := by
    have h := mul_nonneg cn.1
      (show 0≤1-s/2-c/5 by linarith only [cb.2.1,cb.2.2.2.1])
    nlinarith only [h]
  have last : (1/5)*c^2+(1/2)*c*s-c+
      (1/2+(1/2)*s^2-s+(1/5)*c*s)+1/10≤0 := by
    nlinarith only [arc,ordered,bounds.2.1,cn.2.2]
  have a := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr dn.2.1) first
  have b := mul_nonpos_of_nonneg_of_nonpos dn.1 last
  nlinarith only [a,b]

/-- A nonnegative canonical corner sign cannot be disjoint from the
negative left square with these actual anchors and container bounds. -/
theorem nonnegative_impossible (L K : OpenSquare) (side : 1<L.side)
    (same : L.side=K.side) (dn : Normal L.c (-L.s)) (negative : L.s<0)
    (left : centerX L≤0) (cut : 0≤centerY L)
    (wall : ∀ x y, L.Inside x y → -1≤x)
    (cn : Normal K.c K.s) (G : L.Inside 0 (2/5))
    (H : K.Inside 0 (1/2)) (P : K.Inside 0 1) (missing : ¬K.Inside (1/5) 1)
    (apart : ∀ x y, ¬(L.Inside x y ∧ K.Inside x y)) : False := by
  let d := L.c
  let r := -L.s
  let c := K.c
  let s := K.s
  let alpha := r*c+d*s
  let beta := d*c-r*s
  have db := normal_bounds dn
  have cb := normal_bounds cn
  have dp : 0<d := by dsimp [d]; linarith only [db.1]
  have rp : 0<r := by dsimp [r]; linarith only [negative]
  have cp : 0<c := by dsimp [c]; linarith only [cb.1]
  have ap : 0<alpha := add_pos_of_pos_of_nonneg (mul_pos rp cp) (mul_nonneg dp.le cn.1)
  have bn : 0≤beta := by
    calc
      beta = d*(c-s)+s*(d-r) := by dsimp [beta]; ring
      _ ≥ 0 := add_nonneg (mul_nonneg dp.le (sub_nonneg.mpr cn.2.1))
        (mul_nonneg cn.1 (sub_nonneg.mpr dn.2.1))
  have sideK : 1<K.side := by rwa [←same]
  have capU : K.loU+K.side≤(1/5)*c+s := by
    apply le_of_not_gt
    intro failure
    apply missing
    dsimp [c,s] at failure
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [P.1,P.2.2.2,H.2.2.1,failure,cp,cn.1,cn.2.1]
  have upperU : K.loU<(1/5)*c+s-1 := by linarith only [capU,sideK]
  have lowerV : K.loV<c/2 := by dsimp [c]; linarith only [H.2.2.1]
  have axes := C1092MMMPNegativeCenterSupports.alternatives L K side same dn cp left cut G H apart
  rcases axes with axis | axis | axis
  · have support := lower_nn K r d alpha beta
      (by dsimp [r,d,c,s,alpha]; ring) (by dsimp [r,d,c,s,beta]; ring) ap.le bn
    have first := mul_lt_mul_of_pos_left upperU ap
    have last := mul_le_mul_of_nonneg_left lowerV.le bn
    have bound : lower K r d<alpha*((1/5)*c+s-1)+beta*(c/2) := by
      rw [support]
      exact add_lt_add_of_lt_of_le first last
    have identity : alpha*((1/5)*c+s-1)+beta*(c/2)=
        r*((1/5)*c^2+(1/2)*c*s-c)+d*(1/2+(1/2)*s^2-s+(1/5)*c*s) := by
      dsimp [alpha,beta,c,s]
      linear_combination (1/2)*d*cn.2.2
    rw [identity] at bound
    have scalar := positive_pair_scalar dn cn
    have floor := C1092MMMPNegativeCenterSupports.up_right L dn wall cut L.c (-L.s) dn
    rw [(ownV L).2] at floor
    have excess := mul_nonneg (sub_nonneg.mpr side.le)
      (show 0≤d+r by linarith only [dp,rp])
    dsimp [d,r,c,s] at bound excess
    nlinarith only [bound,scalar,floor,axis,excess,dn.1]
  · have bound := (strict_bounds L _ _ K.c K.s K.unit_normal G).2
    dsimp [c,s] at upperU
    linarith only [bound,axis,upperU,cb.2.1,cb.2.2.2.1]
  · have bound := C1092MMMPCenterCorner.up_left L side left cut (-K.s) K.c
      (by nlinarith only [K.unit_normal]) (by linarith only [cn.1]) cp.le
    dsimp [c] at lowerV
    linarith only [axis,bound,lowerV]

private theorem upper_u (L K : OpenSquare) (side : 1<L.side)
    (same : L.side=K.side) (dn : Normal L.c (-L.s))
    (left : centerX L≤0) (cut : 0≤centerY L)
    (cn : Normal K.c (-K.s)) (G : L.Inside 0 (2/5))
    (H : K.Inside 0 (1/2)) (P : K.Inside 0 1) (missing : ¬K.Inside (1/5) 1)
    (apart : ∀ x y, ¬(L.Inside x y ∧ K.Inside x y)) :
    K.loU+K.side≤K.c/5+K.s := by
  let d := L.c
  let r := -L.s
  let c := K.c
  let s := -K.s
  let delta := r*c-d*s
  let beta := r*s+d*c
  have cb := normal_bounds cn
  have dp : 0<d := by dsimp [d]; linarith only [(normal_bounds dn).1]
  have cp : 0<c := by dsimp [c]; linarith only [cb.1]
  have bp : 0<beta := add_pos_of_nonneg_of_pos (mul_nonneg dn.1 cn.1) (mul_pos dp cp)
  have sideK : 1<K.side := by rwa [←same]
  have lowU : K.loU< -s := by dsimp [s]; linarith only [P.1]
  have highU : -s<K.loU+K.side := by dsimp [s]; linarith only [P.2.1]
  have lowV : K.loV<c/2 := by dsimp [c]; linarith only [H.2.2.1]
  by_contra first
  have capV : K.loV+K.side≤c+s/5 := by
    apply le_of_not_gt
    intro second
    apply missing
    dsimp [c,s] at lowU lowV second
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [first,second,lowU,lowV,cp,cn.1]
  have upperV : K.loV<c+s/5-1 := by linarith only [capV,sideK]
  have axes := C1092MMMPNegativeCenterSupports.alternatives L K side same dn cp left cut G H apart
  rcases axes with axis | axis | axis
  · have du : r*K.c+d*K.s=delta := by dsimp [r,d,c,s,delta]; ring
    have dv : -r*K.s+d*K.c=beta := by dsimp [r,d,c,s,beta]; ring
    have bound : lower K r d<delta*(-s)+beta*(c+s/5-1) := by
      have last := mul_lt_mul_of_pos_left upperV bp
      by_cases sign : 0≤delta
      · rw [lower_nn K r d delta beta du dv sign bp.le]
        exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left lowU.le sign) last
      · have an : delta≤0 := le_of_not_ge sign
        rw [lower_np K r d delta beta du dv an bp.le]
        exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonpos_left highU.le an) last
    have identity : delta*(-s)+beta*(c+s/5-1)=
        r*(s^2/5-s)+d*(1-c+c*s/5) := by
      dsimp [delta,beta,c,s]
      linear_combination d*cn.2.2
    rw [identity] at bound
    have firstWeight := mul_nonneg cn.1
      (show 0≤1-s/5 by dsimp [s]; linarith only [cb.2.2.2.1])
    have firstNonpositive : s^2/5-s≤0 := by nlinarith only [firstWeight]
    have firstScaled := mul_nonpos_of_nonneg_of_nonpos dn.1 firstNonpositive
    have elementary := C1092MixedCornerScalars.elementary cn
    have last := mul_pos dp (show 0<c-c*s/5-3/5 by
      dsimp [c,s]; linarith only [elementary.1,elementary.2.2])
    have anchor : (2/5)*d<L.loV+L.side := by dsimp [d]; linarith only [G.2.2.2]
    dsimp [r,d] at bound firstScaled last anchor
    nlinarith only [bound,firstScaled,last,axis,anchor]
  · have yp := upward L K K.c K.s K.unit_normal G H
      (by simpa only [(ownU K).1] using axis)
    linarith only [yp,cn.1]
  · have anchor := (strict_bounds L _ _ (-K.s) K.c
      (by nlinarith only [K.unit_normal]) G).2
    dsimp [c,s] at upperV
    linarith only [anchor,axis,upperV,cb.2.1,cb.2.2.2.1]

/-- The negative corner's scaled face follows from actual disjointness;
the face is not an extra branch premise. -/
theorem floor (L K : OpenSquare) (side : 1<L.side) (sideCap : L.side≤2)
    (same : L.side=K.side) (dn : Normal L.c (-L.s))
    (left : centerX L≤0) (cut : 0≤centerY L)
    (wall : ∀ x y, L.Inside x y → -1≤x)
    (cn : Normal K.c (-K.s)) (G : L.Inside 0 (2/5))
    (H : K.Inside 0 (1/2)) (P : K.Inside 0 1) (missing : ¬K.Inside (1/5) 1)
    (apart : ∀ x y, ¬(L.Inside x y ∧ K.Inside x y)) :
    K.side*(K.c+(-K.s))/2-(-K.s)≤K.loV := by
  let d := L.c
  let r := -L.s
  let c := K.c
  let s := -K.s
  let a := K.side
  let delta := r*c-d*s
  let beta := r*s+d*c
  have cb := normal_bounds cn
  have dp : 0<d := by dsimp [d]; linarith only [(normal_bounds dn).1]
  have cp : 0<c := by dsimp [c]; linarith only [cb.1]
  have bp : 0<beta := add_pos_of_nonneg_of_pos (mul_nonneg dn.1 cn.1) (mul_pos dp cp)
  have aLarge : 1<a := by dsimp [a]; rwa [←same]
  have aSmall : a≤2 := by dsimp [a]; rwa [←same]
  have capU := upper_u L K side same dn left cut cn G H P missing apart
  have lowU : K.loU≤c/5-s-a := by dsimp [c,s,a]; linarith only [capU]
  have highU : -s/2<K.loU+K.side := by dsimp [s]; linarith only [H.2.1]
  have ownFloor := C1092MMMPNegativeCenterSupports.up_right L dn wall cut L.c (-L.s) dn
  rw [(ownV L).2,same] at ownFloor
  have axes := C1092MMMPNegativeCenterSupports.alternatives L K side same dn cp left cut G H apart
  rcases axes with axis | axis | axis
  · apply le_of_not_gt
    intro low
    have du : r*K.c+d*K.s=delta := by dsimp [r,d,c,s,delta]; ring
    have dv : -r*K.s+d*K.c=beta := by dsimp [r,d,c,s,beta]; ring
    have last := mul_lt_mul_of_pos_left low bp
    by_cases sign : 0≤delta
    · have support := lower_nn K r d delta beta du dv sign bp.le
      have first := mul_le_mul_of_nonneg_left lowU sign
      have bound : lower K r d<delta*(c/5-s-a)+beta*(a*(c+s)/2-s) := by
        rw [support]
        exact add_lt_add_of_le_of_lt first last
      have identity : delta*(c/5-s-a)+beta*(a*(c+s)/2-s)-(a*(d+r)/2-r)=
          delta*(c/5-a+(1-a/2)*(c-s)) := by
        dsimp [delta,beta,c,s]
        linear_combination (a*(r+d)/2-r)*cn.2.2
      have extra := mul_nonneg (sub_nonneg.mpr aLarge.le)
        (show 0≤1+(c-s)/2 by linarith only [cn.2.1])
      have scalar : c/5-a+(1-a/2)*(c-s)≤0 := by
        nlinarith only [extra,cb.2.1,cn.1]
      have product := mul_nonpos_of_nonneg_of_nonpos sign scalar
      rw [←identity] at product
      dsimp [r,d,c,s,a] at bound product
      linarith only [bound,product,ownFloor,axis]
    · have an : delta≤0 := le_of_not_ge sign
      have support := lower_np K r d delta beta du dv an bp.le
      have first := mul_le_mul_of_nonpos_left highU.le an
      have bound : lower K r d<delta*(-s/2)+beta*(a*(c+s)/2-s) := by
        rw [support]
        exact add_lt_add_of_le_of_lt first last
      have identity : delta*(-s/2)+beta*(a*(c+s)/2-s)-(a*(d+r)/2-r)=
          delta*(c-s/2-a*(c-s)/2) := by
        dsimp [delta,beta,c,s]
        linear_combination (a*(r+d)/2-r)*cn.2.2
      have extra := mul_nonneg (sub_nonneg.mpr aSmall) (sub_nonneg.mpr cn.2.1)
      have scalar : 0≤c-s/2-a*(c-s)/2 := by nlinarith only [extra,cn.1]
      have product := mul_nonpos_of_nonpos_of_nonneg an scalar
      rw [←identity] at product
      dsimp [r,d,c,s,a] at bound product
      linarith only [bound,product,ownFloor,axis]
  · have yp := upward L K K.c K.s K.unit_normal G H
      (by simpa only [(ownU K).1] using axis)
    linarith only [yp,cn.1]
  · exact (by simpa only [same] using
      C1092MMMPNegativeCenterSupports.up_right L dn wall cut K.c (-K.s) cn).trans axis

#print axioms nonnegative_impossible
#print axioms floor
end N12Compact.C1092MMMPNegativeCornerFloor
