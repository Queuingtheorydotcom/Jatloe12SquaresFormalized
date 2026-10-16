import Compact.Geometry.CentralWallPairSupport
import Compact.Geometry.FullAuxWallRightMargin

/-! Actual right-neighbor SAT reduction without an assumed crossing
point. Both signs of the right square's canonical frame are retained. -/
namespace N12Compact.FullAuxWallRightAxes
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

private theorem positive_lower (A R : OpenSquare)
    (an : Normal A.c A.s) (rn : Normal R.c R.s)
    (ha : 1<A.side) (narrow : 4*A.s≤A.c)
    (escape : 2*(A.c+A.s)≤A.loU)
    (q : A.Inside (113/50) 2)
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s) :
    lower A (-R.s) R.c<(12/5)*R.c-3*R.s := by
  have ab := normal_bounds an
  have rb := normal_bounds rn
  have cp : 0<A.c := by linarith only [ab.1]
  have rp : 0<R.c := by linarith only [rb.1]
  have aNonneg := an.1
  have rt := rn.1
  by_cases below : A.c*R.s≤A.s*R.c
  · have weighted := mul_nonneg rp.le (sub_nonneg.mpr narrow)
    have slope : 4*R.s≤R.c := by nlinarith only [below,weighted,cp]
    have bound := (strict_bounds A _ _ (-R.s) R.c
      (by nlinarith only [R.unit_normal]) q).1
    nlinarith only [bound,slope,rp]
  · let k := A.c*R.s-A.s*R.c
    let d := A.c*R.c+A.s*R.s
    have kp : 0≤k := by dsimp [k]; linarith only [lt_of_not_ge below]
    have dp : 0<d := by dsimp [d]; positivity
    have coefficientU : -R.s*A.c+R.c*A.s≤0 := by dsimp [k] at kp; nlinarith only [kp]
    have coefficientV : 0≤-(-R.s)*A.s+R.c*A.c := by dsimp [d] at dp; nlinarith only [dp]
    have formula : lower A (-R.s) R.c=(-k)*(A.loU+A.side)+d*A.loV := by
      dsimp [lower,supportRadius,centerX,centerY]
      rw [abs_of_nonpos coefficientU,abs_of_nonneg coefficientV]
      dsimp [k,d]
      ring
    have lowU : 2*(A.c+A.s)+1<A.loU+A.side := by linarith only [escape,ha]
    have highV : A.loV<3*A.c-(12/5)*A.s-1 := by linarith only [top,ha]
    have first := mul_nonneg kp (sub_nonneg.mpr lowU.le)
    have second := mul_pos dp (sub_pos.mpr highV)
    let F := A.c-A.s-3/5+A.s^2+(2/5)*A.c*A.s
    let G := A.c+A.s-1+(2/5)*A.s^2-A.c*A.s
    have bounds := FullAuxWallRightMargin.central_bounds an narrow
    have fp : 0≤F := by dsimp [F]; linarith only [bounds.2.2.2.2]
    have crossBound := mul_nonneg aNonneg (sub_nonneg.mpr ab.2.1)
    have sum : 0≤F+G := by
      dsimp [F,G]
      nlinarith only [bounds.1,bounds.2.1,crossBound,sq_nonneg A.s]
    have endpoint1 := mul_nonneg (sub_nonneg.mpr rn.2.1) fp
    have endpoint2 := mul_nonneg rt sum
    have identity : (12/5)*R.c-3*R.s-
        ((-k)*(2*(A.c+A.s)+1)+d*(3*A.c-(12/5)*A.s-1))=R.c*F+R.s*G := by
      dsimp [k,d,F,G]
      linear_combination (-3*R.c+2*R.s)*an.2.2
    nlinarith only [formula,first,second,identity,endpoint1,endpoint2]

private theorem negative_upper (A R : OpenSquare) (t : ℝ)
    (an : Normal A.c A.s) (rn : Normal R.c t) (rs : R.s=-t)
    (ha : 1<A.side) (narrow : 4*A.s≤A.c)
    (escape : 2*(A.c+A.s)≤A.loU) (high : A.Inside (5/2) 3) :
    (1543/500)*t+2*R.c<upper A t R.c := by
  have ab := normal_bounds an
  have rb := normal_bounds rn
  have bounds := FullAuxWallRightMargin.central_bounds an narrow
  have cp : 0<A.c := by linarith only [ab.1]
  have rp : 0<R.c := by linarith only [rb.1]
  let k := A.c*t+A.s*R.c
  let d := A.c*R.c-A.s*t
  have kp : 0≤k := by
    exact add_nonneg (mul_nonneg cp.le rn.1) (mul_nonneg an.1 rp.le)
  have dp : 0<d := by
    have first := mul_nonneg an.1 (sub_nonneg.mpr rn.2.1)
    have second := mul_pos rp (show 0<A.c-A.s by linarith only [bounds.1,bounds.2.1])
    dsimp [d]
    nlinarith only [first,second]
  have coefficientU : 0≤t*A.c+R.c*A.s := by dsimp [k] at kp; nlinarith only [kp]
  have coefficientV : 0≤-t*A.s+R.c*A.c := by dsimp [d] at dp; nlinarith only [dp]
  have formula : upper A t R.c=k*(A.loU+A.side)+d*(A.loV+A.side) := by
    dsimp [upper,supportRadius,centerX,centerY]
    rw [abs_of_nonneg coefficientU,abs_of_nonneg coefficientV]
    dsimp [k,d]
    ring
  have lowU : 2*(A.c+A.s)+1<A.loU+A.side := by linarith only [escape,ha]
  have first := mul_nonneg kp (sub_nonneg.mpr lowU.le)
  have second := mul_pos dp (sub_pos.mpr high.2.2.2)
  let F := 1-A.s^2-(1/2)*A.c*A.s+A.s
  let G := A.c-543/500+(1/2)*A.s^2-A.c*A.s
  have crossBound := mul_nonneg an.1 (sub_nonneg.mpr ab.2.1)
  have smallSquare := mul_nonneg (sub_nonneg.mpr bounds.2.1)
    (show 0≤A.s+(1/4 : ℝ) by linarith only [an.1])
  have fp : 0≤F := by dsimp [F]; nlinarith only [crossBound,smallSquare,an.1]
  have sum : 0≤F+G := by
    dsimp [F,G]
    nlinarith only [bounds.1,bounds.2.1,crossBound,smallSquare]
  have endpoint1 := mul_nonneg (sub_nonneg.mpr rn.2.1) fp
  have endpoint2 := mul_nonneg rn.1 sum
  have identity :
      k*(2*(A.c+A.s)+1)+d*(3*A.c-(5/2)*A.s)-
        ((1543/500)*t+2*R.c)=R.c*F+t*G := by
    dsimp [k,d,F,G]
    linear_combination (3*R.c+2*t)*an.2.2
  nlinarith only [formula,first,second,identity,endpoint1,endpoint2]

/-- Every signed canonical right square leaves only the two forward
longitudinal alternatives. No assumption on the relative angle is made. -/
theorem alternatives (A R : OpenSquare)
    (an : Normal A.c A.s) (rc : 0<R.c)
    (rlo : -R.c≤R.s) (rhi : R.s≤R.c)
    (ha : 1<A.side) (same : A.side=R.side) (narrow : 4*A.s≤A.c)
    (escape : 2*(A.c+A.s)≤A.loU)
    (gv : -(47/20)*A.s+(33/20)*A.c≤A.loV)
    (q : A.Inside (113/50) 2) (m : A.Inside (47/20) (47/20))
    (highA : A.Inside (5/2) 3)
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (apart : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y)) :
    A.loU+A.side≤lower R A.c A.s ∨ upper A R.c R.s≤R.loU := by
  have ab := normal_bounds an
  have cp : 0<A.c := by linarith only [ab.1]
  have avlo : A.loV < -(3:ℝ)*A.s+(12/5)*A.c := by
    linarith only [q.2.2.1,narrow,cp]
  have avhi : -(3:ℝ)*A.s+(12/5)*A.c<A.loV+A.side := by
    linarith only [gv,ha,ab.2.1,an.1]
  have noRV (h : upper A (-R.s) R.c≤lower R (-R.s) R.c ∨
      upper R (-R.s) R.c≤lower A (-R.s) R.c) : False := by
    have unit : (-R.s)^2+R.c^2=1 := by nlinarith only [R.unit_normal]
    have bm := strict_bounds R _ _ (-R.s) R.c unit marker
    have bh := strict_bounds R _ _ (-R.s) R.c unit high
    by_cases sign : 0≤R.s
    · have rn : Normal R.c R.s := ⟨sign,rhi,R.unit_normal⟩
      have am := (strict_bounds A _ _ (-R.s) R.c unit m).2
      have lower := positive_lower A R an rn ha narrow escape q top
      rcases h with h | h <;> nlinarith only [h,am,bm.1,bh.2,lower,rc,sign]
    · let t := -R.s
      have rs : R.s=-t := by dsimp [t]; ring
      have rn : Normal R.c t := by
        refine ⟨?_,?_,?_⟩
        · dsimp [t]; linarith only [lt_of_not_ge sign]
        · dsimp [t]; linarith only [rlo]
        · dsimp [t]; nlinarith only [R.unit_normal]
      have aq := (strict_bounds A _ _ (-R.s) R.c unit q).1
      have upper := negative_upper A R t an rn rs ha narrow escape highA
      rw [rs,neg_neg] at h bm bh aq
      rcases h with h | h <;> nlinarith only [h,upper,bm.1,bh.2,aq,rc,rn.1]
  have axes := CongruentSAT.faceSeparation_of_disjoint A R same apart
  change pairRadius A R≤|A.c*(centerX R-centerX A)+A.s*(centerY R-centerY A)| ∨
    pairRadius A R≤|-A.s*(centerX R-centerX A)+A.c*(centerY R-centerY A)| ∨
    pairRadius R A≤|R.c*(centerX R-centerX A)+R.s*(centerY R-centerY A)| ∨
    pairRadius R A≤|-R.s*(centerX R-centerX A)+R.c*(centerY R-centerY A)| at axes
  have separateAxis (x y P : ℝ)
      (identity : supportRadius A x y+supportRadius R x y=P)
      (h : P≤|x*(centerX R-centerX A)+y*(centerY R-centerY A)|) :=
    separated A R x y (by rwa [identity])
  rcases axes with au | av | ru | rv
  · have h := separateAxis _ _ _ (parallel_radius A R) au
    rw [(ownU A).1,(ownU A).2] at h
    rcases h with yes | no
    · exact Or.inl yes
    · have b := (strict_bounds R _ _ A.c A.s A.unit_normal marker).2
      exact False.elim (by linarith only [no,b,q.1,cp])
  · have h := separateAxis _ _ _ (transverse_radius A R) av
    rw [(ownV A).1,(ownV A).2] at h
    have b := strict_bounds R _ _ (-A.s) A.c
      (by nlinarith only [A.unit_normal]) high
    rcases h with h | h <;> exact False.elim (by linarith only [h,b.1,b.2,avlo,avhi])
  · have identity : supportRadius A R.c R.s+supportRadius R R.c R.s=pairRadius R A := by
      rw [add_comm]
      exact parallel_radius R A
    have h := separateAxis _ _ _ identity ru
    rw [(ownU R).1,(ownU R).2] at h
    rcases h with yes | no
    · exact Or.inr yes
    · have a := (strict_bounds A _ _ R.c R.s R.unit_normal q).1
      exact False.elim (by linarith only [no,a,marker.2.1,rc])
  · have identity : supportRadius A (-R.s) R.c+supportRadius R (-R.s) R.c=pairRadius R A := by
      rw [add_comm]
      exact transverse_radius R A
    exact False.elim (noRV (separateAxis _ _ _ identity rv))

#print axioms alternatives
end N12Compact.FullAuxWallRightAxes
