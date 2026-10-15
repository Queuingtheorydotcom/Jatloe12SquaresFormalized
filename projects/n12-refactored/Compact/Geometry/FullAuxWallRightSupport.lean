import Compact.Geometry.FullAuxWallRightAxes
import Compact.Geometry.ClosedFrames
import Compact.Geometry.FullAuxWallEscape
import Compact.Geometry.CentralOuterReach

/-! The actual right-hand square controls the escaping central square's
excess over the center face quadratically. Both signs of the neighbor's
frame are retained. The enclosing wall is used on a genuine vertex of
that square, never on a replacement point or virtual rectangle. -/
namespace N12Compact.FullAuxWallRightSupport
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

private theorem upper_corner_wall (R : OpenSquare) (box : InsideContainer R) :
    R.c*(R.loU+R.side)-R.s*(R.loV+R.side)≤4 := by
  have bound : 0≤4-R.c*(R.loU+R.side)+R.s*(R.loV+R.side) := by
    apply affine_endpoint_nonnegative R.side (R.c-R.s) _ R.side_pos
    intro e he0 he1
    let u := R.loU+R.side-e
    let v := R.loV+R.side-e
    have point : R.Inside (R.c*u-R.s*v) (R.s*u+R.c*v) := by
      apply (inside_iff_rotated_box R _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp [u,v,InBands]
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    have x := (box _ _ point).2.1
    dsimp [u,v] at x
    nlinarith only [x]
  linarith only [bound]

private theorem positive_below (A R : OpenSquare)
    (an : Normal A.c A.s) (rn : Normal R.c R.s)
    (ha : 1<A.side) (same : A.side=R.side) (box : InsideContainer R)
    (narrow : 4*A.s≤A.c) (escape : 2*(A.c+A.s)≤A.loU)
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (marker : R.Inside (1543/500) 2)
    (cross : A.c*R.s≤A.s*R.c)
    (axes : A.loU+A.side≤lower R A.c A.s ∨ upper A R.c R.s≤R.loU) :
    A.loU-2*(A.c+A.s)<(1/5)*A.s^2 ∧
      A.c*(A.loU-2*(A.c+A.s))+(2/5)*A.s^2-(1-A.c)*(1-A.s)<0 := by
  have ab := normal_bounds an
  have rb := normal_bounds rn
  have cp : 0<A.c := by linarith only [ab.1]
  have rp : 0<R.c := by linarith only [rb.1]
  have order : R.s≤A.s := sine_order an rn (by nlinarith only [cross])
  let d := A.c*R.c+A.s*R.s
  let k := A.c*R.s-A.s*R.c
  let e := A.loU-2*(A.c+A.s)
  have dp : 0<d := by
    exact add_pos_of_pos_of_nonneg (mul_pos cp rp) (mul_nonneg an.1 rn.1)
  have kn : k≤0 := by dsimp [k]; linarith only [cross]
  have en : 0≤e := by dsimp [e]; linarith only [escape]
  have lowerFormula : lower R A.c A.s=d*R.loU-k*R.loV := by
    dsimp [lower,supportRadius,centerX,centerY]
    rw [abs_of_nonneg (show 0≤A.c*R.c+A.s*R.s from dp.le),
      abs_of_nonneg (show 0≤-A.c*R.s+A.s*R.c by dsimp [k] at kn; linarith)]
    dsimp [d,k]
    ring
  have upperFormula : upper A R.c R.s=d*(A.loU+A.side)+k*A.loV := by
    have dot : 0≤R.c*A.c+R.s*A.s := by dsimp [d] at dp; nlinarith only [dp]
    have transverse : -R.c*A.s+R.s*A.c≤0 := by dsimp [k] at kn; nlinarith only [kn]
    dsimp [upper,supportRadius,centerX,centerY]
    rw [abs_of_nonneg dot,abs_of_nonpos transverse]
    dsimp [d,k]
    ring
  have wall := CentralWallEscape.right_wall R box
  rcases axes with central | neighbor
  · have wallScaled := mul_le_mul_of_nonneg_left wall dp.le
    have markerScaled := mul_le_mul_of_nonneg_left marker.2.2.1.le an.1
    have cancellation : d*R.s-R.c*k=A.s := by
      dsimp [d,k]
      linear_combination A.s*rn.2.2
    have supportIdentity : R.c*lower R A.c A.s=
        d*(R.c*(R.loU+R.side)-R.s*R.loV)+A.s*R.loV-R.side*R.c*d := by
      rw [lowerFormula]
      nlinarith only [congrArg (fun z : ℝ => z*R.loV) cancellation]
    have bound : R.c*lower R A.c A.s≤
        4*A.c*R.c+2*A.s*R.c+(457/500)*A.s*R.s-R.side*R.c*d := by
      dsimp [d] at supportIdentity wallScaled ⊢
      nlinarith only [supportIdentity,wallScaled,markerScaled]
    have axis := mul_le_mul_of_nonneg_left central rp.le
    have entry := mul_nonneg rp.le (sub_nonneg.mpr escape)
    have scalar := FullAuxWallRightMargin.positive_u_margin an rn narrow order
    have strict := mul_pos (sub_pos.mpr ha)
      (mul_pos rp (show 0<1+d by linarith only [dp]))
    rw [←same] at bound
    dsimp [d] at bound strict
    exact False.elim (by nlinarith only [bound,axis,entry,scalar,strict])
  · have face := mul_nonneg (neg_nonneg.mpr kn) (sub_nonneg.mpr top)
    let X := 2+(2/5)*A.s^2-A.c*A.s
    let Y := 3-A.s^2-(2/5)*A.c*A.s
    have identity : d*(2*(A.c+A.s))+k*(3*A.c-(12/5)*A.s)=R.c*X+R.s*Y := by
      dsimp [d,k,X,Y]
      linear_combination (2*R.c+3*R.s)*an.2.2
    have support : R.c*X+R.s*Y+d*e+A.side*(d-k)≤upper A R.c R.s := by
      dsimp [e] at ⊢
      nlinarith only [upperFormula,face,identity]
    have markerScaled := mul_le_mul_of_nonneg_left marker.2.2.1.le rn.1
    have wallBound : R.c*R.loU+R.side*R.c+(1543/500)*R.s^2-2*R.c*R.s≤4 := by
      nlinarith only [wall,markerScaled]
    have axis := mul_le_mul_of_nonneg_left (le_trans support neighbor) rp.le
    let M := R.c^2*X+R.c*R.s*(Y-2)+R.c*(d-k+1)+(1543/500)*R.s^2-4
    have necessary : R.c*d*e+M+(A.side-1)*R.c*(d-k+1)≤0 := by
      rw [←same] at wallBound
      dsimp [M]
      nlinarith only [axis,wallBound]
    have strict := mul_pos (sub_pos.mpr ha)
      (mul_pos rp (show 0<d-k+1 by linarith only [dp,kn]))
    have scalar := FullAuxWallRightMargin.margin an rn narrow order
    have margin : 0≤M+(1/5)*R.c*d*A.s^2 := by
      dsimp [M,X,Y,d,k]
      convert scalar using 1 <;> ring
    have sharp : e<(1/5)*A.s^2 := by
      by_contra failure
      have large : (1/5)*A.s^2≤e := le_of_not_gt failure
      have weighted := mul_nonneg (mul_pos rp dp).le (sub_nonneg.mpr large)
      nlinarith only [necessary,strict,margin,weighted]
    refine ⟨sharp,?_⟩
    have baselineScalar := FullAuxWallRightMargin.baseline_margin an rn narrow order
    have baseline : (2/5)*A.s^2-(1-A.c)*(1-A.s)≤M := by
      dsimp [M,X,Y,d,k]
      convert baselineScalar using 1 <;> ring
    have coefficient : R.c*d-A.c=-R.s*k := by
      dsimp [d,k]
      linear_combination A.c*rn.2.2
    have sign := mul_nonpos_of_nonneg_of_nonpos rn.1 kn
    have weighted := mul_nonneg (show 0≤R.c*d-A.c by linarith only [coefficient,sign]) en
    change A.c*e+(2/5)*A.s^2-(1-A.c)*(1-A.s)<0
    nlinarith only [necessary,strict,baseline,weighted]

private theorem negative (A R : OpenSquare) (t : ℝ)
    (an : Normal A.c A.s) (rn : Normal R.c t) (rs : R.s=-t)
    (ha : 1<A.side) (same : A.side=R.side) (box : InsideContainer R)
    (narrow : 4*A.s≤A.c) (escape : 2*(A.c+A.s)≤A.loU)
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (axes : A.loU+A.side≤lower R A.c A.s ∨ upper A R.c R.s≤R.loU) :
    A.loU-2*(A.c+A.s)<(1/5)*A.s^2 ∧
      A.c*(A.loU-2*(A.c+A.s))+(2/5)*A.s^2-(1-A.c)*(1-A.s)<0 := by
  have ab := normal_bounds an
  have rb := normal_bounds rn
  have bounds := FullAuxWallRightMargin.central_bounds an narrow
  have cp : 0<A.c := by linarith only [ab.1]
  have rp : 0<R.c := by linarith only [rb.1]
  let d := A.c*R.c-A.s*t
  let k := A.c*t+A.s*R.c
  let e := A.loU-2*(A.c+A.s)
  have kn : 0≤k := by
    exact add_nonneg (mul_nonneg cp.le rn.1) (mul_nonneg an.1 rp.le)
  have dLower : (7/10)*R.c≤d := by
    have first := mul_nonneg an.1 (sub_nonneg.mpr rn.2.1)
    have second := mul_nonneg rp.le
      (show 0≤A.c-A.s-7/10 by linarith only [bounds.1,bounds.2.1])
    dsimp [d]
    nlinarith only [first,second]
  have dp : 0<d := by nlinarith only [dLower,rp]
  have en : 0≤e := by dsimp [e]; linarith only [escape]
  have lowerFormula : lower R A.c A.s=d*R.loU+k*R.loV := by
    have dot : 0≤A.c*R.c+A.s*R.s := by rw [rs]; dsimp [d] at dp; nlinarith only [dp]
    have transverse : 0≤-A.c*R.s+A.s*R.c := by rw [rs]; dsimp [k] at kn; nlinarith only [kn]
    dsimp [lower,supportRadius,centerX,centerY]
    rw [abs_of_nonneg dot,abs_of_nonneg transverse,rs]
    dsimp [d,k]
    ring
  have upperFormula : upper A R.c R.s=d*(A.loU+A.side)-k*A.loV := by
    have dot : 0≤R.c*A.c+R.s*A.s := by rw [rs]; dsimp [d] at dp; nlinarith only [dp]
    have transverse : -R.c*A.s+R.s*A.c≤0 := by rw [rs]; dsimp [k] at kn; nlinarith only [kn]
    dsimp [upper,supportRadius,centerX,centerY]
    rw [abs_of_nonneg dot,abs_of_nonpos transverse,rs]
    dsimp [d,k]
    ring
  rcases axes with central | neighbor
  · have wall := upper_corner_wall R box
    rw [rs] at wall
    have wallScaled := mul_le_mul_of_nonneg_left wall dp.le
    have markerV := marker.2.2.1
    rw [rs] at markerV
    have markerScaled := mul_le_mul_of_nonneg_left markerV.le an.1
    have cancellation : R.c*k-d*t=A.s := by
      dsimp [d,k]
      linear_combination A.s*rn.2.2
    have supportIdentity : R.c*lower R A.c A.s=
        d*(R.c*(R.loU+R.side)+t*(R.loV+R.side))+
          A.s*R.loV-R.side*d*(R.c+t) := by
      rw [lowerFormula]
      nlinarith only [congrArg (fun z : ℝ => z*R.loV) cancellation]
    have bound : R.c*lower R A.c A.s≤
        4*A.c*R.c+2*A.s*R.c-(457/500)*A.s*t-R.side*d*(R.c+t) := by
      dsimp [d] at supportIdentity wallScaled ⊢
      nlinarith only [supportIdentity,wallScaled,markerScaled]
    have axis := mul_le_mul_of_nonneg_left central rp.le
    have entry := mul_nonneg rp.le (sub_nonneg.mpr escape)
    have scalar := FullAuxWallRightMargin.negative_u_margin an rn narrow
    have strict := mul_pos (sub_pos.mpr ha)
      (add_pos rp (mul_pos dp (add_pos_of_pos_of_nonneg rp rn.1)))
    rw [←same] at bound
    dsimp [d] at bound strict
    exact False.elim (by nlinarith only [bound,axis,entry,scalar,strict])
  · have face := mul_nonneg kn (sub_nonneg.mpr top)
    let X := 2+(2/5)*A.s^2-A.c*A.s
    let Y := 3-A.s^2-(2/5)*A.c*A.s
    have identity : d*(2*(A.c+A.s))-k*(3*A.c-(12/5)*A.s)=R.c*X-t*Y := by
      dsimp [d,k,X,Y]
      linear_combination (2*R.c-3*t)*an.2.2
    have support : R.c*X-t*Y+d*e+A.side*(d+k)≤upper A R.c R.s := by
      dsimp [e] at ⊢
      nlinarith only [upperFormula,face,identity]
    have highU := high.1
    rw [rs] at highU
    let M0 := (2/5)*A.s^2-(1-A.c)*(1-A.s)
    let B := A.c-A.s-3/5+A.s^2+(2/5)*A.c*A.s
    have necessary : d*e+R.c*M0+t*B+(A.side-1)*(d+k)<0 := by
      dsimp [M0,B,X,Y,d,k] at support ⊢
      nlinarith only [support,neighbor,highU]
    have baseline := mul_nonneg rp.le (sub_nonneg.mpr bounds.2.2.2.1)
    have bp : 0≤B := by dsimp [B]; linarith only [bounds.2.2.2.2]
    have term := mul_nonneg rn.1 bp
    have strict := mul_pos (sub_pos.mpr ha) (show 0<d+k by linarith only [dp,kn])
    have sharp : e<(1/5)*A.s^2 := by
      by_contra failure
      have large : (1/5)*A.s^2≤e := le_of_not_gt failure
      have weighted := mul_nonneg dp.le (sub_nonneg.mpr large)
      have projection := mul_nonneg (sq_nonneg A.s) (sub_nonneg.mpr dLower)
      have square := mul_nonneg rp.le (sq_nonneg A.s)
      dsimp [M0] at necessary
      nlinarith only [necessary,baseline,term,strict,weighted,projection,square]
    refine ⟨sharp,?_⟩
    have smallSquare : A.s^2≤1/16 := by
      have product := mul_nonneg (sub_nonneg.mpr bounds.2.1)
        (show 0≤1/4+A.s by linarith only [an.1])
      nlinarith only [product]
    have ecap : e≤1/80 := by nlinarith only [sharp,smallSquare]
    have se := mul_le_mul bounds.2.1 ecap en (by norm_num : (0:ℝ)≤1/4)
    have rem : 0≤B-A.s*e := by
      dsimp [B]
      nlinarith only [se,bounds.2.2.2.2]
    have rest := mul_nonneg rn.1 rem
    have scaled : R.c*(A.c*e+M0)<0 := by
      dsimp [d] at necessary
      nlinarith only [necessary,strict,rest]
    have result := (mul_neg_iff_of_pos_left rp).mp scaled
    dsimp [M0,e] at result
    exact result

/-- An original right neighbor, in any signed canonical frame, forces a
quadratic upper bound on the central lower-U face. -/
theorem canonical_bounds (A R : OpenSquare)
    (an : Normal A.c A.s) (rc : 0<R.c) (rlo : -R.c≤R.s) (rhi : R.s≤R.c)
    (ha : 1<A.side) (same : A.side=R.side) (box : InsideContainer R)
    (narrow : 4*A.s≤A.c) (escape : 2*(A.c+A.s)≤A.loU)
    (gv : -(47/20)*A.s+(33/20)*A.c≤A.loV)
    (q : A.Inside (113/50) 2) (m : A.Inside (47/20) (47/20))
    (highA : A.Inside (5/2) 3) (outer : A.Inside (47/20) (53/20))
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (apart : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y)) :
    A.loU-2*(A.c+A.s)<(1/5)*A.s^2 ∧
      A.c*(A.loU-2*(A.c+A.s))+(2/5)*A.s^2-(1-A.c)*(1-A.s)<0 := by
  have axes := FullAuxWallRightAxes.alternatives A R an rc rlo rhi ha same narrow
    escape gv q m highA top marker high apart
  by_cases sign : 0≤R.s
  · have rn : Normal R.c R.s := ⟨sign,rhi,R.unit_normal⟩
    by_cases cross : 0≤A.c*R.s-A.s*R.c
    · have ab := normal_bounds an
      have cp : 0<A.c := by linarith only [ab.1]
      have shallow : 12*A.s≤5*A.c := by linarith only [narrow,cp]
      have lower : 2*A.c+2*A.s≤A.loU := by linarith only [escape]
      rcases axes with central | neighbor
      · exact False.elim (CentralWallPairSupport.central_axis_impossible A R ha same box
          cp an.1 rc sign shallow cross lower marker high central)
      · exact False.elim (CentralWallPairSupport.wall_axis_impossible A R ha same box
          cp an.1 rc sign shallow cross lower gv outer marker neighbor)
    · exact positive_below A R an rn ha same box narrow escape top marker
        (by linarith only [lt_of_not_ge cross]) axes
  · let t := -R.s
    have rs : R.s=-t := by dsimp [t]; ring
    have rn : Normal R.c t := by
      refine ⟨?_,?_,?_⟩
      · dsimp [t]; linarith only [lt_of_not_ge sign]
      · dsimp [t]; linarith only [rlo]
      · dsimp [t]; nlinarith only [R.unit_normal]
    exact negative A R t an rn rs ha same box narrow escape top marker high axes

theorem canonical (A R : OpenSquare)
    (an : Normal A.c A.s) (rc : 0<R.c) (rlo : -R.c≤R.s) (rhi : R.s≤R.c)
    (ha : 1<A.side) (same : A.side=R.side) (box : InsideContainer R)
    (narrow : 4*A.s≤A.c) (escape : 2*(A.c+A.s)≤A.loU)
    (gv : -(47/20)*A.s+(33/20)*A.c≤A.loV)
    (q : A.Inside (113/50) 2) (m : A.Inside (47/20) (47/20))
    (highA : A.Inside (5/2) 3) (outer : A.Inside (47/20) (53/20))
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (apart : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y)) :
    A.loU-2*(A.c+A.s)<(1/5)*A.s^2 :=
  (canonical_bounds A R an rc rlo rhi ha same box narrow escape gv q m highA
    outer top marker high apart).1

/-- A convenient weaker scalar form of the exact retained clearance. -/
theorem quadratic_of_clearance {c s e : ℝ} (an : Normal c s)
    (narrow : 4*s≤c)
    (clearance : c*e+(2/5)*s^2-(1-c)*(1-s)<0) : e<s^2/10 := by
  have ab := normal_bounds an
  have cp : 0<c := by linarith only [ab.1]
  have small : s≤1/4 := by linarith only [narrow,ab.2.1]
  have defectProduct := mul_nonneg cp.le (sub_nonneg.mpr ab.2.1)
  have defect : 1-c≤s^2 := by nlinarith only [defectProduct,an.2.2]
  let H := ((2/5)+(1/10)*c)*(1+c)-(1-s)
  have identityH : H=s-(1/10)*s^2-(1/2)*(1-c) := by
    dsimp [H]
    linear_combination (1/10)*an.2.2
  have smallProduct := mul_nonneg an.1
    (show 0≤1-(3/5)*s by linarith only [small])
  have hn : 0≤H := by nlinarith only [identityH,defect,smallProduct]
  have product := mul_nonneg (sub_nonneg.mpr ab.2.1) hn
  have identity : (1/10)*c*s^2+(2/5)*s^2-(1-c)*(1-s)=(1-c)*H := by
    dsimp [H]
    linear_combination ((2/5)+(1/10)*c)*an.2.2
  have scaled : c*e<c*(s^2/10) := by nlinarith only [clearance,identity,product]
  exact (mul_lt_mul_left cp).mp scaled

/-- Face reindexing does not alter the right square or any packing premise. -/
theorem bounds (A R : OpenSquare)
    (an : Normal A.c A.s) (ha : 1<A.side)
    (same : A.side=R.side) (box : InsideContainer R)
    (narrow : 4*A.s≤A.c) (escape : 2*(A.c+A.s)≤A.loU)
    (gv : -(47/20)*A.s+(33/20)*A.c≤A.loV)
    (q : A.Inside (113/50) 2) (m : A.Inside (47/20) (47/20))
    (highA : A.Inside (5/2) 3) (outer : A.Inside (47/20) (53/20))
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (apart : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y)) :
    A.loU-2*(A.c+A.s)<(1/5)*A.s^2 ∧
      A.c*(A.loU-2*(A.c+A.s))+(2/5)*A.s^2-(1-A.c)*(1-A.s)<0 := by
  obtain ⟨r,rc,range,side,inside,_⟩ := ClosedFrames.canonical_frame R
  have bound := abs_le.mp range
  apply canonical_bounds A r an rc bound.1 bound.2 ha (same.trans side.symm)
    (fun x y h => box x y ((inside x y).mp h)) narrow escape gv q m highA outer top
    ((inside _ _).mpr marker) ((inside _ _).mpr high)
  intro x y h
  exact apart x y ⟨h.1,(inside x y).mp h.2⟩

theorem excess (A R : OpenSquare)
    (an : Normal A.c A.s) (ha : 1<A.side)
    (same : A.side=R.side) (box : InsideContainer R)
    (narrow : 4*A.s≤A.c) (escape : 2*(A.c+A.s)≤A.loU)
    (gv : -(47/20)*A.s+(33/20)*A.c≤A.loV)
    (q : A.Inside (113/50) 2) (m : A.Inside (47/20) (47/20))
    (highA : A.Inside (5/2) 3) (outer : A.Inside (47/20) (53/20))
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (apart : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y)) :
    A.loU-2*(A.c+A.s)<(1/5)*A.s^2 :=
  (bounds A R an ha same box narrow escape gv q m highA outer top marker high apart).1

/-- All additional face and outer-point facts are consequences of the
original three-square entrance. The result has no saved enclosure premise. -/
theorem original_bounds_of_missing (A R : OpenSquare) (ha : 1<A.side)
    (sameR : A.side=R.side) (boxR : InsideContainer R)
    (hc : 0<A.c) (hs : 0≤A.s) (order : A.s≤A.c)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬A.Inside (47/20) (33/20))
    (missingB : ¬A.Inside (33/20) (47/20))
    (rMarker : R.Inside (1543/500) 2) (rHigh : R.Inside 3 (12/5))
    (missingTop : ¬A.Inside (12/5) 3)
    (ar : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y))
    (missing : ¬A.Inside 2 2) :
    A.loU-2*(A.c+A.s)<(1/5)*A.s^2 ∧
      A.c*(A.loU-2*(A.c+A.s))+(2/5)*A.s^2-(1-A.c)*(1-A.s)<0 := by
  have faces := FullAuxWallEscape.narrow_faces_of_missing A R ha sameR boxR hc hs order
    p q m missingG missingB rMarker rHigh missingTop ar missing
  have lower := CentralWallPairAxes.central_lower_faces A hc hs
    (by linarith only [faces.2.1,hc]) p q m missing missingG
  have outer := CentralOuterReach.points A ha p q m missingG missingB
    (fun h => ar _ _ ⟨h,rHigh⟩) missingTop
  exact bounds A R ⟨hs,order,A.unit_normal⟩ ha sameR boxR faces.2.1.le
    (by linarith only [faces.2.2.1]) lower.2 q m faces.2.2.2.2.2.2
    outer.1 faces.2.2.2.2.2.1 rMarker rHigh ar

theorem original_bounds (A R T : OpenSquare) (ha : 1<A.side)
    (sameR : A.side=R.side) (boxR : InsideContainer R)
    (hc : 0<A.c) (hs : 0≤A.s) (order : A.s≤A.c)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬A.Inside (47/20) (33/20))
    (missingB : ¬A.Inside (33/20) (47/20))
    (rMarker : R.Inside (1543/500) 2)
    (rHigh : R.Inside 3 (12/5)) (tHigh : T.Inside (12/5) 3)
    (ar : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y))
    (apartTop : ∀ x y, ¬(A.Inside x y ∧ T.Inside x y))
    (missing : ¬A.Inside 2 2) :
    A.loU-2*(A.c+A.s)<(1/5)*A.s^2 ∧
      A.c*(A.loU-2*(A.c+A.s))+(2/5)*A.s^2-(1-A.c)*(1-A.s)<0 :=
  original_bounds_of_missing A R ha sameR boxR hc hs order p q m missingG missingB
    rMarker rHigh (fun h => apartTop _ _ ⟨h,tHigh⟩) ar missing

theorem from_original (A R T : OpenSquare) (ha : 1<A.side)
    (sameR : A.side=R.side) (boxR : InsideContainer R)
    (hc : 0<A.c) (hs : 0≤A.s) (order : A.s≤A.c)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬A.Inside (47/20) (33/20))
    (missingB : ¬A.Inside (33/20) (47/20))
    (rMarker : R.Inside (1543/500) 2) (rHigh : R.Inside 3 (12/5))
    (tHigh : T.Inside (12/5) 3)
    (ar : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y))
    (apartTop : ∀ x y, ¬(A.Inside x y ∧ T.Inside x y))
    (missing : ¬A.Inside 2 2) :
    A.loU-2*(A.c+A.s)<(1/5)*A.s^2 :=
  (original_bounds A R T ha sameR boxR hc hs order p q m missingG missingB
    rMarker rHigh tHigh ar apartTop missing).1

#print axioms from_original
#print axioms original_bounds
end N12Compact.FullAuxWallRightSupport
