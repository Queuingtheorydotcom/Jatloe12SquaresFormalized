import Compact.Geometry.CentralWallEscape
import Compact.Geometry.C977NegativeCorner
import Compact.Geometry.CornerWallLowerSupportMargin
import Mathlib.Tactic.LinearCombination

/-! A right wall's complete lower support is bounded by its actual upper
corner exclusion. The two upper-face escapes are both retained. This is
a continuous signed sector and uses no side upper bound or center box. -/
namespace N12Compact.CentralRightCornerSupport
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem upper_u_margin {c s d t : ℝ}
    (bn : Normal c s) (rn : Normal d t) :
    0≤1-c*((1-d)+d*t+(43/500)*t^2)+s*(t-t^2+(43/500)*d*t) := by
  have cb := normal_bounds bn
  have db := normal_bounds rn
  have cp : 0≤c := by linarith only [cb.1]
  have dp : 0≤d := by linarith only [db.1]
  have dt : 0≤d*t := mul_nonneg dp rn.1
  have product : d*t≤1/2 := by nlinarith only [rn.2.2,sq_nonneg (d-t)]
  have squares := mul_nonneg (sub_nonneg.mpr rn.2.1) (add_nonneg dp rn.1)
  have tsq : t^2≤1/2 := by nlinarith only [squares,rn.2.2]
  let A := (1-d)+d*t+(43/500)*t^2
  let B := t-t^2+(43/500)*d*t
  have ap : 0≤A := by dsimp [A]; nlinarith only [db.2.1,dt,sq_nonneg t]
  have bound : A≤843/1000 := by dsimp [A]; nlinarith only [db.1,product,tsq]
  have bp : 0≤B := by
    have h := mul_nonneg rn.1 (sub_nonneg.mpr db.2.2.2.1)
    dsimp [B]; nlinarith only [h,dt]
  have first := mul_nonneg (sub_nonneg.mpr cb.2.1) ap
  have second := mul_nonneg bn.1 bp
  change 0≤1-c*A+s*B
  clear_value A B
  nlinarith only [first,second,bound]

/-- The full band support bound after the actual missing corner has
selected one of its upper faces. All translations remain explicit. -/
private theorem band_bound {c s d t a u v : ℝ}
    (bn : Normal c s) (rn : Normal d t) (positive : 0<t) (side : 1≤a)
    (wall : d*(u+a)-t*v≤4) (marker : v≤2*d-(1543/500)*t)
    (faces : u+a≤3*(d+t) ∨ v+a≤3*(d-t)) :
    (c*d+s*t)*u+(s*d-c*t)*v-a*max (c*t-s*d) 0≤2*(c+s)+1 := by
  have cb := normal_bounds bn
  have db := normal_bounds rn
  have cp : 0≤c := by linarith only [cb.1]
  have dp : 0<d := by linarith only [db.1]
  let K := c*d+s*t
  let H := s*d-c*t
  let G := max (c*t-s*d) 0
  let F := CornerWallLowerSupportMargin.F c s d t
  have kp : 0≤K := add_nonneg (mul_nonneg cp dp.le) (mul_nonneg bn.1 rn.1)
  have gp : 0≤G := le_max_right _ _
  have fp : 0≤F := CornerWallLowerSupportMargin.margin bn rn
  have fd : d*F=d*(1-2*c-s)+s*(1-t)+d*(K+G) := by
    dsimp [F,CornerWallLowerSupportMargin.F,K,G]
    field_simp [ne_of_gt dp]
    ring
  change K*u+H*v-a*G≤2*(c+s)+1
  rcases faces with cap | cap
  · by_cases hs : 0≤H
    · have gz : G=0 := by
        dsimp [G,H] at *
        exact max_eq_right (by linarith only [hs])
      let M := 1-c*((1-d)+d*t+(43/500)*t^2)+s*(t-t^2+(43/500)*d*t)
      have mp : 0≤M := upper_u_margin bn rn
      have first := mul_nonneg kp (sub_nonneg.mpr cap)
      have second := mul_nonneg hs (sub_nonneg.mpr marker)
      have third := mul_nonneg (sub_nonneg.mpr side) kp
      have identity : 2*(c+s)+1-(K*u+H*v)=
          K*(3*(d+t)-(u+a))+H*(2*d-(1543/500)*t-v)+(a-1)*K+M := by
        dsimp [K,H,M]
        linear_combination -(3*c+2*s)*rn.2.2
      rw [gz,mul_zero,sub_zero]
      clear_value K H G F M
      linarith only [identity,first,second,third,mp]
    · have hn : H≤0 := (lt_of_not_ge hs).le
      have ge : G=-H := by
        dsimp [G,H]
        rw [max_eq_left (by dsimp [H] at hn; linarith only [hn])]
        ring
      have first := mul_nonneg bn.1 (sub_nonneg.mpr cap)
      have second := mul_nonneg (neg_nonneg.mpr hn) (sub_nonneg.mpr wall)
      have third := mul_nonneg (sub_nonneg.mpr side)
        (mul_nonneg positive.le (show 0≤K-H by linarith only [kp,hn]))
      have fourth := mul_nonneg positive.le fp
      have correction : 0≤s*(1-t)/d := div_nonneg
        (mul_nonneg bn.1 (sub_nonneg.mpr db.2.2.2.1)) dp.le
      have identity : t*(2*(c+s)+1-(K*u+H*v+a*H))=
          s*(3*(d+t)-(u+a))-H*(4-d*(u+a)+t*v)+
          (a-1)*t*(K-H)+t*F+s*(1-t)/d := by
        dsimp [F,CornerWallLowerSupportMargin.F,K,H,G] at *
        rw [max_eq_left (by linarith only [hn])]
        field_simp [ne_of_gt dp]
        linear_combination -s*(d*(u+a)-1)*rn.2.2
      have nonnegative : 0≤t*(2*(c+s)+1-(K*u+H*v+a*H)) := by
        clear_value K H G F
        linarith only [identity,first,second,third,fourth,correction]
      have bound := nonneg_of_mul_nonneg_right nonnegative positive
      rw [ge]
      linarith only [bound]
  · have first := mul_nonneg kp (sub_nonneg.mpr wall)
    have second := mul_nonneg bn.1 (sub_nonneg.mpr cap)
    have third := mul_nonneg (sub_nonneg.mpr side)
      (show 0≤s+d*(K+G) from add_nonneg bn.1 (mul_nonneg dp.le (add_nonneg kp gp)))
    have fourth := mul_nonneg dp.le fp
    have identity : d*(2*(c+s)+1-(K*u+H*v-a*G))=
        K*(4-d*(u+a)+t*v)+s*(3*(d-t)-(v+a))+
        (a-1)*(s+d*(K+G))+d*F := by
      rw [fd]
      dsimp [K,H]
      linear_combination -(s*v)*rn.2.2
    have nonnegative : 0≤d*(2*(c+s)+1-(K*u+H*v-a*G)) := by
      clear_value K H G F
      linarith only [identity,first,second,third,fourth]
    exact le_of_sub_nonneg (nonneg_of_mul_nonneg_right nonnegative dp)

/-- A right-wall square with a positive canonical frame and a foreign
actual upper corner has this lower-support bound in every positive
canonical direction. The strict marker and the full right container
wall remove the two lower-face escapes. -/
theorem lower_support (R : OpenSquare) {c s : ℝ}
    (bn : Normal c s) (rn : Normal R.c R.s) (side : 1≤R.side)
    (box : InsideContainer R) (marker : R.Inside (1543/500) 2)
    (missing : ¬R.Inside 3 3) : lower R c s≤2*(c+s)+1 := by
  have cb := normal_bounds bn
  have rb := normal_bounds rn
  have cp : 0≤c := by linarith only [cb.1]
  have dp : 0<R.c := by linarith only [rb.1]
  have wall := CentralWallEscape.right_wall R box
  by_cases zero : R.s=0
  · have dc : R.c=1 := by nlinarith only [R.unit_normal,zero,dp]
    have support : lower R c s=c*R.loU+s*R.loV := by
      rw [lower_in_bands,zero,dc]
      simp only [mul_one,mul_zero,add_zero,neg_mul,zero_add,
        abs_of_nonneg cp,abs_of_nonneg bn.1]
      ring
    have first := mul_nonneg cp (show 0≤3-R.loU by
      rw [zero,dc] at wall; linarith only [wall,side])
    have second := mul_nonneg bn.1 (show 0≤2-R.loV by
      have m := marker.2.2.1; rw [zero,dc] at m; linarith only [m])
    rw [support]
    linarith only [first,second,cb.2.1]
  have positive : 0<R.s := lt_of_le_of_ne rn.1 (Ne.symm zero)
  have reach : 1≤R.c+R.c*R.s := by
    have product := mul_nonneg rn.1
      (show 0≤R.c*(1+R.c)-R.s by nlinarith only [rn.2.1,sq_nonneg R.c])
    have identity : (1+R.c)*(R.c+R.c*R.s-1)=
        R.s*(R.c*(1+R.c)-R.s) := by
      linear_combination R.unit_normal
    have denominator : 0<1+R.c := by linarith only [dp]
    have nonnegative : 0≤(1+R.c)*(R.c+R.c*R.s-1) := by
      linarith only [identity,product]
    have result := nonneg_of_mul_nonneg_right nonnegative denominator
    linarith only [result]
  have lowerU : R.loU<3*(R.c+R.s) := by
    apply lt_of_not_ge
    intro high
    have first := mul_nonneg dp.le (sub_nonneg.mpr high)
    have second := mul_nonneg dp.le (sub_nonneg.mpr side)
    have third := mul_lt_mul_of_pos_left marker.2.2.1 positive
    nlinarith only [wall,first,second,third,reach,R.unit_normal,sq_nonneg R.s]
  have lowerV : R.loV<3*(R.c-R.s) := by
    linarith only [marker.2.2.1,dp,rn.1]
  have faces : R.loU+R.side≤3*(R.c+R.s) ∨
      R.loV+R.side≤3*(R.c-R.s) := by
    by_cases cap : R.loU+R.side≤3*(R.c+R.s)
    · exact Or.inl cap
    · right
      apply le_of_not_gt
      intro upperV
      apply missing
      exact ⟨by linarith only [lowerU],by linarith only [cap],
        by linarith only [lowerV],by linarith only [upperV]⟩
  have support : lower R c s=(c*R.c+s*R.s)*R.loU+
      (s*R.c-c*R.s)*R.loV-R.side*max (c*R.s-s*R.c) 0 := by
    rw [lower_in_bands]
    have kp : 0≤c*R.c+s*R.s :=
      add_nonneg (mul_nonneg cp dp.le) (mul_nonneg bn.1 rn.1)
    rw [abs_of_nonneg kp]
    by_cases sign : 0≤s*R.c-c*R.s
    · rw [abs_of_nonneg (by linarith only [sign]),max_eq_right (by linarith only [sign])]
      ring
    · rw [abs_of_nonpos (by linarith only [sign]),max_eq_left (by linarith only [sign])]
      ring
  rw [support]
  exact band_bound bn rn positive side wall (by linarith only [marker.2.2.1]) faces

/-- The negative wall sector is simpler: the right container wall and
the actual marker already suffice. In particular, no upper-corner face
or missing point is needed in this signed sector. -/
theorem negative_lower_support (R : OpenSquare) {c s t : ℝ}
    (bn : Normal c s) (rn : Normal R.c t) (signed : R.s=-t)
    (side : 1≤R.side) (box : InsideContainer R)
    (marker : R.Inside (1543/500) 2) : lower R c s≤2*(c+s)+1 := by
  have cb := normal_bounds bn
  have rb := normal_bounds rn
  have cp : 0≤c := by linarith only [cb.1]
  have dp : 0<R.c := by linarith only [rb.1]
  have wall : R.c*(R.loU+R.side)+t*(R.loV+R.side)≤4 := by
    have h := CentralWallEscape.right_wall (turnFrame R)
      (fun x y h => box x y ((turnFrame_inside R x y).mp h))
    dsimp [turnFrame] at h
    rw [signed] at h
    linarith only [h]
  have mv : R.loV≤(1543/500)*t+2*R.c := by
    have h := marker.2.2.1
    rw [signed] at h
    linarith only [h]
  let K := c*R.c-s*t
  let H := c*t+s*R.c
  have kp : 0≤K := by
    have first := mul_nonneg dp.le (sub_nonneg.mpr bn.2.1)
    have second := mul_nonneg bn.1 (sub_nonneg.mpr rn.2.1)
    dsimp [K]; nlinarith only [first,second]
  have hp : 0≤H := add_nonneg (mul_nonneg cp rn.1) (mul_nonneg bn.1 dp.le)
  have support : lower R c s=K*R.loU+H*R.loV := by
    rw [lower_in_bands,signed]
    have first : c*R.c+s*(-t)=K := by dsimp [K]; ring
    have second : -c*(-t)+s*R.c=H := by dsimp [H]; ring
    rw [first,second,abs_of_nonneg kp,abs_of_nonneg hp]
    ring
  have reach : 2≤2*R.c+t := by
    have product := mul_nonneg rn.1
      (show 0≤1+R.c-2*t by linarith only [rn.2.1,rb.2.2.2.1])
    have identity : (1+R.c)*(2*R.c+t-2)=t*(1+R.c-2*t) := by
      linear_combination 2*rn.2.2
    have nonnegative : 0≤(1+R.c)*(2*R.c+t-2) := by
      linarith only [identity,product]
    have result := nonneg_of_mul_nonneg_right nonnegative
      (show 0<1+R.c by linarith only [dp])
    linarith only [result]
  let P := 2-R.c-t
  let Q := t*(R.c+t-457/500)/R.c
  have qd : R.c*Q=t*(R.c+t-457/500) := by
    dsimp [Q]
    field_simp [ne_of_gt dp]
  have pc : P≤R.c := by dsimp [P]; linarith only [reach]
  have qt : Q≤t := by
    have small : t≤457/500 := by
      linarith only [rn.2.1,rb.2.2.2.2.2]
    have weighted := mul_nonneg rn.1 (sub_nonneg.mpr small)
    dsimp [Q]
    apply (div_le_iff₀ dp).mpr
    nlinarith only [weighted]
  have first := mul_nonneg cp (sub_nonneg.mpr pc)
  have second := mul_nonneg bn.1 (sub_nonneg.mpr qt)
  have dot : c*R.c+s*t≤1 := by
    nlinarith only [bn.2.2,rn.2.2,sq_nonneg (c-R.c),sq_nonneg (s-t)]
  have margin : 0≤1-P*c-Q*s := by nlinarith only [first,second,dot]
  have wallWeight := mul_nonneg kp (sub_nonneg.mpr wall)
  have markerWeight := mul_nonneg bn.1 (sub_nonneg.mpr mv)
  have width := mul_nonneg (sub_nonneg.mpr side)
    (mul_nonneg kp (show 0≤R.c+t by linarith only [dp,rn.1]))
  have marginWeight := mul_nonneg dp.le margin
  have identity : R.c*(2*(c+s)+1-(K*R.loU+H*R.loV))=
      K*(4-R.c*(R.loU+R.side)-t*(R.loV+R.side))+
      s*((1543/500)*t+2*R.c-R.loV)+
      (R.side-1)*K*(R.c+t)+R.c*(1-P*c-Q*s) := by
    dsimp [P,K,H]
    linear_combination -(s*R.loV)*rn.2.2+s*qd
  have nonnegative : 0≤R.c*(2*(c+s)+1-(K*R.loU+H*R.loV)) := by
    clear_value K H P Q
    linarith only [identity,wallWeight,markerWeight,width,marginWeight]
  rw [support]
  exact le_of_sub_nonneg (nonneg_of_mul_nonneg_right nonnegative dp)

/-- Both canonical signs of the right square satisfy the same support
bound. The corner exclusion is used only in its nonnegative sector. -/
theorem canonical_lower_support (R : OpenSquare) {c s : ℝ}
    (bn : Normal c s) (canonical : |R.s|≤R.c) (side : 1≤R.side)
    (box : InsideContainer R) (marker : R.Inside (1543/500) 2)
    (missing : ¬R.Inside 3 3) : lower R c s≤2*(c+s)+1 := by
  by_cases sign : 0≤R.s
  · exact lower_support R bn
      ⟨sign,by simpa only [abs_of_nonneg sign] using canonical,R.unit_normal⟩
      side box marker missing
  · have negative : R.s<0 := lt_of_not_ge sign
    exact negative_lower_support R (t := -R.s) bn
      ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using canonical,
        by nlinarith only [R.unit_normal]⟩
      (by ring) side box marker

theorem lower_pullY (R : OpenSquare) (c s : ℝ) :
    lower (pullY R) c (-s)=lower R c s-4*s := by
  have radius : supportRadius (pullY R) c (-s)=supportRadius R c s := by
    dsimp [supportRadius,pullY]
    rw [show c*R.c+(-s)*(-R.s)=c*R.c+s*R.s by ring,
      show -c*(-R.s)+(-s)*R.c=-(-c*R.s+s*R.c) by ring,abs_neg]
  dsimp only [lower]
  rw [center_pullY_x,center_pullY_y,radius]
  ring

/-- With both real adjacent corners foreign, the support bound also
covers both signs of the test direction. Reflection is applied only to
the one square and its actual points, not to an ownership branch. -/
theorem signed_direction_support (R : OpenSquare) {c s : ℝ}
    (direction : |s|≤c) (unit : c^2+s^2=1) (canonical : |R.s|≤R.c)
    (side : 1≤R.side) (box : InsideContainer R)
    (marker : R.Inside (1543/500) 2)
    (missingTop : ¬R.Inside 3 3) (missingBottom : ¬R.Inside 3 1) :
    lower R c s≤2*(c+s)+1 := by
  by_cases sign : 0≤s
  · exact canonical_lower_support R
      ⟨sign,by simpa only [abs_of_nonneg sign] using direction,unit⟩
      canonical side box marker missingTop
  · have negative : s<0 := lt_of_not_ge sign
    have normal : Normal c (-s) :=
      ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using direction,
        by nlinarith only [unit]⟩
    have canonicalY : |(pullY R).s|≤(pullY R).c := by
      simpa only [pullY,abs_neg] using canonical
    have markerY : (pullY R).Inside (1543/500) 2 := by
      rw [inside_pullY]
      norm_num only
      exact marker
    have missingY : ¬(pullY R).Inside 3 3 := by
      rw [inside_pullY]
      norm_num only
      exact missingBottom
    have bound := canonical_lower_support (pullY R) normal canonicalY side
      (container_pullY R box) markerY missingY
    rw [lower_pullY] at bound
    linarith only [bound]

/-- A complete support-chain obstruction: a preceding square cannot
start beyond the center on this axis and then end before the right wall. -/
theorem forward_impossible (B R : OpenSquare)
    (bn : Normal B.c B.s) (rn : Normal R.c R.s)
    (side : 1<B.side) (rSide : 1≤R.side) (box : InsideContainer R)
    (marker : R.Inside (1543/500) 2) (missing : ¬R.Inside 3 3)
    (start : 2*(B.c+B.s)≤B.loU)
    (axis : B.loU+B.side≤lower R B.c B.s) : False := by
  have bound := lower_support R bn rn rSide box marker missing
  linarith only [bound,start,side,axis]

#print axioms lower_support
#print axioms negative_lower_support
#print axioms canonical_lower_support
#print axioms signed_direction_support
#print axioms forward_impossible
end N12Compact.CentralRightCornerSupport
