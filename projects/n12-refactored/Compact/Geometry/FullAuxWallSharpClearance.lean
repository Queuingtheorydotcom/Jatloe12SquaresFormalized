import Compact.Geometry.FullAuxWallRightSupport
import Compact.Geometry.FullAuxWallPositiveAngleOrder

/-! Retaining the exact right-wall clearance gives uniform bounds far
stronger than its coarse quadratic consequence. The only maximization
used below is a cubic identity with a nonnegative remainder. Both actual
A/C longitudinal support selectors are retained. -/
namespace N12Compact.FullAuxWallSharpClearance
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic FullAuxWallTopEndpoint
set_option Elab.async false

/-- A single cubic square bounds the actual displacement, with no
angle subdivision or numerical optimization premise. -/
theorem excess {c s e : ℝ} (an : Normal c s) (narrow : 4*s≤c)
    (clearance : c*e+(2/5)*s^2-(1-c)*(1-s)<0) : e<1/1250 := by
  have bounds := FullAuxWallRightMargin.central_bounds an narrow
  have weighted := mul_nonneg (sub_nonneg.mpr bounds.2.2.1)
    (show 0≤1-s by linarith only [bounds.2.1])
  have square := mul_nonneg (sq_nonneg (s-18/125))
    (show 0≤125*s+9 by linarith only [an.1])
  have identity : 2916/15625-s^2*(27-125*s)=
      (s-18/125)^2*(125*s+9) := by ring
  have cubic : 245*c*e<2916/15625 := by
    nlinarith only [clearance,weighted,square,identity]
  apply lt_of_not_ge
  intro large
  have lower := mul_nonneg
    (show 0≤c by linarith only [bounds.1]) (sub_nonneg.mpr large)
  nlinarith only [cubic,lower,bounds.1]

/-- Positivity of the actual displacement makes the escaping frame
strictly narrower than the original quarter-slope reduction. -/
theorem angle {c s e : ℝ} (an : Normal c s) (narrow : 4*s≤c)
    (entry : 0≤e)
    (clearance : c*e+(2/5)*s^2-(1-c)*(1-s)<0) :
    977/1000≤c ∧ s<21/100 := by
  have ab := normal_bounds an
  have cp : 0<c := by linarith only [ab.1]
  have defect : 0≤1-c := sub_nonneg.mpr ab.2.1
  have product := mul_nonneg (sub_nonneg.mpr narrow)
    (show 0≤c+4*s by linarith only [cp,an.1])
  have first : 97/100≤c := by
    apply le_of_not_gt
    intro small
    have square := mul_pos (sub_pos.mpr small)
      (show 0<97/100+c by linarith only [cp])
    nlinarith only [square,product,an.2.2]
  have ep := mul_nonneg cp.le entry
  have identity : (2/5)*s^2-(1-c)*(1-s)=
      (1-c)*(s+(2/5)*c-3/5) := by
    linear_combination (2/5)*an.2.2
  have arc : s+(2/5)*c<3/5 := by
    apply lt_of_not_ge
    intro wrong
    have term := mul_nonneg defect (sub_nonneg.mpr wrong)
    nlinarith only [clearance,ep,identity,term]
  have small : s<53/250 := by linarith only [first,arc]
  have sSquare := mul_pos (sub_pos.mpr small)
    (show 0<53/250+s by linarith only [an.1])
  have second : 977/1000≤c := by
    apply le_of_not_gt
    intro wrong
    have cSquare := mul_pos (sub_pos.mpr wrong)
      (show 0<977/1000+c by linarith only [cp])
    nlinarith only [cSquare,sSquare,an.2.2]
  exact ⟨second,by linarith only [second,arc]⟩

private theorem angular_margin {c s : ℝ} (an : Normal c s)
    (cosine : 977/1000≤c) (small : s≤21/100) :
    50*c*(1-c)≤11*((1-c)*(1-s)+(2/5)*s) := by
  have ab := normal_bounds an
  let K := 11*s*(1-s)+(22/5)*(1+c)-50*c*s
  have cs := mul_nonneg an.1 (sub_nonneg.mpr ab.2.1)
  have linear := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤39+11*(s+21/100) by linarith only [an.1])
  have kp : 0≤K := by
    dsimp [K]
    nlinarith only [cosine,cs,linear]
  have remainder := mul_nonneg an.1 kp
  have identity :
      (1+c)*(11*((1-c)*(1-s)+(2/5)*s)-50*c*(1-c))=s*K := by
    dsimp [K]
    linear_combination (50*c-11*(1-s))*an.2.2
  have scaled : 0≤(1+c)*(11*((1-c)*(1-s)+(2/5)*s)-50*c*(1-c)) := by
    linarith only [identity,remainder]
  have bound := nonneg_of_mul_nonneg_right scaled
    (show 0<1+c by linarith only [ab.1])
  linarith only [bound]

private theorem upper_pn (q : OpenSquare) (x y : ℝ)
    (hu : 0≤x*q.c+y*q.s) (hv : -x*q.s+y*q.c≤0) :
    upper q x y=(x*q.c+y*q.s)*(q.loU+q.side)+
      (-x*q.s+y*q.c)*q.loV := by
  dsimp [upper,supportRadius,centerX,centerY]
  rw [abs_of_nonneg hu,abs_of_nonpos hv]
  ring

/-- Both genuine A/C separators force the opposite central frame below
slope 11/50. Its position is not replaced by an independently chosen box. -/
theorem opposite_slope (A D : OpenSquare)
    (an : Normal A.c A.s) (dn : Normal D.c D.s)
    (ha : 1<A.side) (narrow : 4*A.s≤A.c)
    (escape : 2*(A.c+A.s)≤A.loU)
    (clearance : A.c*(A.loU-2*(A.c+A.s))+
      (2/5)*A.s^2-(1-A.c)*(1-A.s)<0)
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (center : D.Inside 2 2) (bottom : D.Inside 2 (3/2))
    (axes : upper D A.c A.s≤A.loU ∨
      D.loU+D.side≤lower A D.c D.s) : 50*D.s<11*D.c := by
  let e := A.loU-2*(A.c+A.s)
  let u := D.loU+D.side-2*(D.c+D.s)
  let v := A.loV-2*(A.c-A.s)
  let alpha := A.c*D.c+A.s*D.s
  let gamma := A.c*D.s-A.s*D.c
  have ab := normal_bounds an
  have db := normal_bounds dn
  have cp : 0<A.c := by linarith only [ab.1]
  have dp : 0<D.c := by linarith only [db.1]
  have ep : 0≤e := sub_nonneg.mpr escape
  have aBounds := angle an narrow ep clearance
  have ecap := excess an narrow clearance
  have ap : 0<alpha := by dsimp [alpha]; positivity
  have up : 0<u := by dsimp [u]; linarith only [center.2.1]
  apply lt_of_not_ge
  intro large
  have first := mul_nonneg cp.le (sub_nonneg.mpr large)
  have second := mul_nonneg dp.le
    (show 0≤(11/50)*A.c-A.s-1/250 by linarith only [aBounds.1,aBounds.2])
  have gammaLower : D.c/250≤gamma := by
    dsimp [gamma]
    nlinarith only [first,second]
  have gp : 0<gamma := by linarith only [gammaLower,dp]
  rcases axes with own | other
  · have support := upper_pn D A.c A.s ap.le
      (by dsimp [gamma] at gp; linarith only [gp])
    have identity : upper D A.c A.s-2*(A.c+A.s)=
        alpha*u+gamma*(2*(D.c-D.s)-D.loV) := by
      rw [support]
      dsimp [alpha,gamma,u]
      linear_combination (2*(A.c+A.s))*D.unit_normal
    have lower : D.c/2<2*(D.c-D.s)-D.loV := by
      nlinarith only [bottom.2.2.1]
    have weighted := mul_pos gp (sub_pos.mpr lower)
    have extra := mul_pos ap up
    have gap := mul_nonneg dp.le (sub_nonneg.mpr gammaLower)
    have square := mul_nonneg (sub_nonneg.mpr db.1)
      (show 0≤D.c+7/10 by linarith only [dp])
    dsimp [e] at ecap
    nlinarith only [own,identity,weighted,extra,gap,square,ecap]
  · have support := lower_pp A D.c D.s
      (by dsimp [alpha] at ap; nlinarith only [ap])
      (by dsimp [gamma] at gp; nlinarith only [gp])
    have identity : lower A D.c D.s-2*(D.c+D.s)=alpha*e+gamma*v := by
      rw [support]
      dsimp [alpha,gamma,e,v]
      linear_combination (2*(D.c+D.s))*A.unit_normal
    have height : v<A.c-1-(2/5)*A.s := by
      dsimp [v]; linarith only [top,ha]
    have cut : 0<alpha*e+gamma*v := by
      dsimp [u] at up
      nlinarith only [up,other,identity]
    have ccut := mul_pos cp cut
    have eTerm := mul_pos ap (show 0<(1-A.c)*(1-A.s)-(2/5)*A.s^2-A.c*e by
      dsimp [e]; linarith only [clearance])
    have vTerm := mul_pos (mul_pos cp gp) (sub_pos.mpr height)
    have exactIdentity :
        alpha*((1-A.c)*(1-A.s)-(2/5)*A.s^2)+
          A.c*gamma*(A.c-1-(2/5)*A.s)=
        D.c*A.c*(1-A.c)-D.s*((1-A.c)*(1-A.s)+(2/5)*A.s) := by
      dsimp [alpha,gamma]
      linear_combination (-D.s*(1-A.c+(2/5)*A.s))*an.2.2
    have margin := angular_margin an aBounds.1 aBounds.2.le
    have W : 0≤(1-A.c)*(1-A.s)+(2/5)*A.s := by
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr ab.2.1)
        (by linarith only [aBounds.2])) (mul_nonneg (by norm_num) an.1)
    have scaled := mul_nonneg dp.le (sub_nonneg.mpr margin)
    have ordered := mul_nonneg W (sub_nonneg.mpr large)
    nlinarith only [ccut,eTerm,vTerm,exactIdentity,scaled,ordered]

#print axioms excess
#print axioms angle
#print axioms opposite_slope
end N12Compact.FullAuxWallSharpClearance
