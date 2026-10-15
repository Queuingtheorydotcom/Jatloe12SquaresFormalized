import Compact.Geometry.C977CornerSectorBounds

/-! The actual foreign top seed gives a strict margin for the shared
singleton axis. Two broad continuous ranges suffice; no sampled angle or
enumeration is used. The coefficient vector lies strictly inside the unit
disk, so the conclusion holds for every direction of the singleton. -/
namespace N12Compact.CornerWallSharedMargin

open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

noncomputable def first (c d t : ℝ) : ℝ :=
  c+t-72/25+(1-t)/d

noncomputable def second (c s d : ℝ) : ℝ :=
  s+d-2+(1-s)/c

private theorem first_mul {c d t : ℝ} (hd : 0<d) :
    d*first c d t=c*d+d*t-(72/25)*d+1-t := by
  unfold first
  field_simp [ne_of_gt hd]
  <;> ring

private theorem second_mul {c s d : ℝ} (hc : 0<c) :
    c*second c s d=c*s+c*d-2*c+1-s := by
  unfold second
  field_simp [ne_of_gt hc]
  <;> ring

private theorem bounds {c s d t : ℝ} (on : Normal c s) (wn : Normal d t)
    (order : s≤t) (small : t≤3/5) (wide : 4/5≤d) :
    -(49/50)≤first c d t ∧ first c d t≤0 ∧
      -(1/5)≤second c s d ∧ second c s d≤0 := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have hc : 0<c := by linarith only [ob.1]
  have hd : 0<d := by linarith only [wide]
  have dc : d≤c := cosine_order wn on order
  have ai := first_mul (c:=c) (t:=t) hd
  have bi := second_mul (s:=s) (d:=d) hc
  have p0 := mul_nonneg (sub_nonneg.mpr wide)
    (show 0≤d-1/2 by linarith only [wide])
  have p1 := mul_nonneg (sub_nonneg.mpr wb.2.1) (sub_nonneg.mpr small)
  have p2 := mul_nonneg hd.le (sub_nonneg.mpr dc)
  have lowerFirst : -(49/50)≤first c d t := by
    have scaled : 0≤d*(first c d t+49/50) := by
      nlinarith only [ai,p0,p1,p2]
    have unscaled := nonneg_of_mul_nonneg_right scaled hd
    linarith only [unscaled]
  have p3 := mul_nonneg (sub_nonneg.mpr wide)
    (show 0≤47/25-t by linarith only [small])
  have p4 := mul_nonneg hd.le (sub_nonneg.mpr ob.2.1)
  have upperFirst : first c d t≤0 := by
    have scaled : d*first c d t≤0 := by nlinarith only [ai,p3,p4,wn.1]
    exact nonpos_of_mul_nonpos_right scaled hd
  have p5 := mul_nonneg (sub_nonneg.mpr ob.2.2.2.1)
    (sub_nonneg.mpr ob.2.1)
  have p6 := mul_nonneg hc.le (sub_nonneg.mpr wide)
  have lowerSecond : -(1/5)≤second c s d := by
    have scaled : 0≤c*(second c s d+1/5) := by nlinarith only [bi,p5,p6]
    have unscaled := nonneg_of_mul_nonneg_right scaled hc
    linarith only [unscaled]
  have p7 := mul_nonneg (sub_nonneg.mpr ob.2.1)
    (show 0≤c+s-1 by linarith only [ob.2.2.2.2.1])
  have p8 := mul_nonneg hc.le (sub_nonneg.mpr dc)
  have upperSecond : second c s d≤0 := by
    have scaled : c*second c s d≤0 := by nlinarith only [bi,p7,p8]
    exact nonpos_of_mul_nonpos_right scaled hc
  exact ⟨lowerFirst,upperFirst,lowerSecond,upperSecond⟩

/-- The stronger top-seed coefficient vector has squared norm at most
249901/250000. This uniform positive margin covers all singleton angles. -/
theorem norm_sq {c s d t : ℝ} (on : Normal c s) (wn : Normal d t)
    (order : s≤t) (small : t≤3/5) (wide : 4/5≤d) :
    (first c d t)^2+(second c s d)^2≤249901/250000 := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have hc : 0<c := by linarith only [ob.1]
  have hd : 0<d := by linarith only [wide]
  have dc : d≤c := cosine_order wn on order
  have limits := bounds on wn order small wide
  have ai := first_mul (c:=c) (t:=t) hd
  have bi := second_mul (s:=s) (d:=d) hc
  by_cases tiny : s≤1/10
  · have ss := mul_nonneg on.1 (sub_nonneg.mpr tiny)
    have cosine : 49/50≤c := by
      by_contra no
      have product := mul_nonneg
        (show 0≤49/50-c by linarith only [no])
        (show 0≤49/50+c by linarith only [ob.1])
      nlinarith only [on.2.2,ss,tiny,product]
    have defect := mul_nonneg (sub_nonneg.mpr wb.2.1)
      (show 0≤1-t by linarith only [small])
    have scaled : 0≤d*(first c d t+9/10) := by
      have moving := mul_nonneg hd.le (sub_nonneg.mpr cosine)
      nlinarith only [ai,defect,moving]
    have lower := nonneg_of_mul_nonneg_right scaled hd
    have asq := mul_nonneg lower
      (show 0≤9/10-first c d t by linarith only [limits.2.1])
    have bsq := mul_nonneg
      (show 0≤second c s d+1/5 by linarith only [limits.2.2.1])
      (show 0≤1/5-second c s d by linarith only [limits.2.2.2])
    nlinarith only [asq,bsq]
  · have large : 1/10≤s := (lt_of_not_ge tiny).le
    have ss := mul_nonneg (sub_nonneg.mpr large)
      (show 0≤s+1/10 by linarith only [on.1])
    have defect : 1/200≤1-c := by
      nlinarith only [ss,on.2.2,sq_nonneg (1-c)]
    have product := mul_nonneg
      (show 0≤3/5-s by linarith only [order,small])
      (show 0≤1-c by linarith only [ob.2.1])
    have lowerProduct : 1/500≤(1-s)*(1-c) := by
      nlinarith only [product,defect]
    have moving := mul_nonneg hc.le (sub_nonneg.mpr wide)
    have scaled : 0≤c*(second c s d+99/500) := by
      nlinarith only [bi,moving,lowerProduct,ob.2.1]
    have lower := nonneg_of_mul_nonneg_right scaled hc
    have asq := mul_nonneg
      (show 0≤first c d t+49/50 by linarith only [limits.1])
      (show 0≤49/50-first c d t by linarith only [limits.2.1])
    have bsq := mul_nonneg lower
      (show 0≤99/500-second c s d by linarith only [limits.2.2.2])
    nlinarith only [asq,bsq]

/-- The shared-axis margin is positive even before its nonnegative
support-corner correction is included. -/
theorem shared_axis {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (small : t≤3/5) (wide : 4/5≤d) :
    0<1+l*(c+t-72/25+(1-t)/d)+r*(s+d-2+(1-s)/c) := by
  let A := first c d t
  let B := second c s d
  have norm : A^2+B^2≤249901/250000 := norm_sq on wn order small wide
  have identity : (l*A+r*B)^2+(l*B-r*A)^2=A^2+B^2 := by
    linear_combination (A^2+B^2)*ln.2.2
  have square : (l*A+r*B)^2<1 := by
    nlinarith only [norm,identity,sq_nonneg (l*B-r*A)]
  have strict : 0<1+l*A+r*B := by nlinarith only [square]
  exact strict

#print axioms norm_sq
#print axioms shared_axis
end N12Compact.CornerWallSharedMargin
