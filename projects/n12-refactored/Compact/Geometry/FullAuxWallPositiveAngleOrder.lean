import Compact.Geometry.FullAuxWallPositiveOpposite
import Compact.Geometry.FullAuxWallPositiveTop

/-! The genuine quadratic A/R clearance orders the two opposite central
frames strictly below the upper outer frame. Both surviving A/C support
selectors are retained; no relative-angle selector is assumed. -/
namespace N12Compact.FullAuxWallPositiveAngleOrder

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic FullAuxWallTopEndpoint
set_option Elab.async false

private theorem bands_closed (q : OpenSquare) (U V : ℝ)
    (hu : q.loU≤U ∧ U≤q.loU+q.side) (hv : q.loV≤V ∧ V≤q.loV+q.side) :
    ClosedInside q (q.c*U-q.s*V) (q.s*U+q.c*V) := by
  have first : q.c*(q.c*U-q.s*V)+q.s*(q.s*U+q.c*V)=U := by
    linear_combination U*q.unit_normal
  have second : -q.s*(q.c*U-q.s*V)+q.c*(q.s*U+q.c*V)=V := by
    linear_combination V*q.unit_normal
  change q.loU≤_ ∧ _≤q.loU+q.side ∧ q.loV≤_ ∧ _≤q.loV+q.side
  rw [first,second]
  exact ⟨hu.1,hu.2,hv.1,hv.2⟩

/-- Keep the actual clearance in both U-axis alternatives. The central
V-coordinate belongs to both closed bands, so no angle order is needed. -/
theorem projected_excess (A D : OpenSquare)
    (an : Normal A.c A.s) (dn : Normal D.c D.s)
    (ha : 1<A.side) (sp : 0<A.s) (narrow : 4*A.s≤A.c)
    (escape : 2*(A.c+A.s)≤A.loU)
    (high : A.Inside (5/2) 3)
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (center : D.Inside 2 2)
    (axes : upper D A.c A.s≤A.loU ∨
      D.loU+D.side≤lower A D.c D.s) :
    (A.c*D.c+A.s*D.s)*(D.loU+D.side-2*(D.c+D.s))≤
      A.loU-2*(A.c+A.s) := by
  have cp : 0<A.c := by linarith only [(normal_bounds an).1]
  have dp : 0<D.c := by linarith only [(normal_bounds dn).1]
  let alpha := A.c*D.c+A.s*D.s
  let e := A.loU-2*(A.c+A.s)
  let u := D.loU+D.side-2*(D.c+D.s)
  have ap : 0<alpha := by dsimp [alpha]; positivity
  have cap : alpha≤1 := C977CornerSectorBounds.dot_le_one an dn
  have ep : 0≤e := sub_nonneg.mpr escape
  change alpha*u≤e
  rcases axes with own | other
  · have face := bands_closed D (D.loU+D.side) (2*(D.c-D.s))
      ⟨by linarith only [D.side_pos],le_rfl⟩
      ⟨by linarith only [center.2.2.1],by linarith only [center.2.2.2]⟩
    have bound := (closed_bounds D _ _ A.c A.s face).2
    have identity :
        A.c*(D.c*(D.loU+D.side)-D.s*(2*(D.c-D.s)))+
          A.s*(D.s*(D.loU+D.side)+D.c*(2*(D.c-D.s)))-2*(A.c+A.s)=alpha*u := by
      dsimp [alpha,u]
      linear_combination (2*(A.c+A.s))*D.unit_normal
    dsimp [e]
    nlinarith only [bound,own,identity]
  · have v := FullAuxWallPositiveOpposite.central_v_band A ha cp sp narrow high top
    have face := bands_closed A A.loU (2*(A.c-A.s))
      ⟨le_rfl,by linarith only [A.side_pos]⟩ ⟨v.1.le,v.2.le⟩
    have bound := (closed_bounds A _ _ D.c D.s face).1
    have identity :
        D.c*(A.c*A.loU-A.s*(2*(A.c-A.s)))+
          D.s*(A.s*A.loU+A.c*(2*(A.c-A.s)))-2*(D.c+D.s)=alpha*e := by
      dsimp [alpha,e]
      linear_combination (2*(D.c+D.s))*A.unit_normal
    have cut : u≤alpha*e := by dsimp [u]; nlinarith only [bound,other,identity]
    have first := mul_nonneg ap.le (sub_nonneg.mpr cut)
    have second := mul_nonneg ep
      (mul_nonneg (sub_nonneg.mpr cap) (show 0≤1+alpha by linarith only [ap]))
    nlinarith only [first,second]

theorem small_excess (A D : OpenSquare)
    (an : Normal A.c A.s) (dn : Normal D.c D.s)
    (ha : 1<A.side) (sp : 0<A.s) (narrow : 4*A.s≤A.c)
    (escape : 2*(A.c+A.s)≤A.loU)
    (sharp : A.loU-2*(A.c+A.s)<A.s^2/10)
    (high : A.Inside (5/2) 3)
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (center : D.Inside 2 2)
    (axes : upper D A.c A.s≤A.loU ∨
      D.loU+D.side≤lower A D.c D.s) :
    D.loU+D.side-2*(D.c+D.s)<1/112 := by
  have ab := normal_bounds an
  have db := normal_bounds dn
  have cp : 0<A.c := by linarith only [ab.1]
  let alpha := A.c*D.c+A.s*D.s
  let u := D.loU+D.side-2*(D.c+D.s)
  have projected := projected_excess A D an dn ha sp narrow escape high top center axes
  change alpha*u≤A.loU-2*(A.c+A.s) at projected
  have small : A.s≤1/4 := by linarith only [narrow,ab.2.1]
  have lower0 := mul_nonneg cp.le (sub_nonneg.mpr db.1)
  have lower1 := mul_nonneg sp.le dn.1
  have alphaLower : (7/10)*A.c≤alpha := by
    dsimp [alpha]; nlinarith only [lower0,lower1]
  have square0 := mul_nonneg (sub_nonneg.mpr narrow) sp.le
  have square1 := mul_nonneg cp.le
    (show 0≤1-4*A.s by linarith only [small])
  apply lt_of_not_ge
  intro large
  change (1/112 : ℝ)≤u at large
  have weighted := mul_nonneg (sub_nonneg.mpr alphaLower)
    (show 0≤u by linarith only [large])
  have lower := mul_nonneg cp.le (sub_nonneg.mpr large)
  nlinarith only [projected,sharp,square0,square1,weighted,lower]

private theorem slope_scalar {c s C S : ℝ}
    (an : Normal c s) (dn : Normal C S) (sp : 0<s)
    (narrow : 4*s≤c)
    (cut : C*(c*S-s*C)/2<s^2/5 ∨
      0<(c*C+s*S)*(s^2/5)+(c*S-s*C)*(c-1-(2/5)*s)) :
    82*S<29*C := by
  apply lt_of_not_ge
  intro large
  have ab := normal_bounds an
  have db := normal_bounds dn
  have cp : 0<c := by linarith only [ab.1]
  have dp : 0<C := by linarith only [db.1]
  have small : s≤1/4 := by linarith only [narrow,ab.2.1]
  let alpha := c*C+s*S
  let gamma := c*S-s*C
  have ap : 0<alpha := by dsimp [alpha]; positivity
  have first := mul_nonneg (sub_nonneg.mpr narrow)
    (show 0≤21*C+2*S by linarith only [dp,dn.1])
  have second := mul_nonneg cp.le
    (show 0≤82*S-29*C by linarith only [large])
  have identity : 84*gamma-8*alpha=
      (c-4*s)*(21*C+2*S)+c*(82*S-29*C) := by
    dsimp [gamma,alpha]; ring
  have ratio : (2/21)*alpha≤gamma := by
    nlinarith only [first,second,identity]
  have gp : 0≤gamma := by linarith only [ratio,ap]
  rcases cut with firstCut | secondCut
  · have lowerTerm := mul_nonneg cp.le (sub_nonneg.mpr db.1)
    have otherTerm := mul_nonneg sp.le dn.1
    have alphaLower : (7/10)*c≤alpha := by
      dsimp [alpha]; nlinarith only [lowerTerm,otherTerm]
    have gammaLower : c/15≤gamma := by linarith only [ratio,alphaLower]
    have product := mul_nonneg (sub_nonneg.mpr db.1) gp
    have square0 := mul_nonneg (sub_nonneg.mpr narrow) sp.le
    have square1 := mul_nonneg cp.le
      (show 0≤1-4*s by linarith only [small])
    change C*gamma/2<s^2/5 at firstCut
    nlinarith only [firstCut,gammaLower,product,square0,square1,cp]
  · have defect : c-1≤-s^2/2 := by
      nlinarith only [an.2.2,sq_nonneg (c-1)]
    have defectTerm := mul_nonpos_of_nonneg_of_nonpos gp
      (show c-1+s^2/2≤0 by linarith only [defect])
    have term0 := mul_nonneg (sub_nonneg.mpr ratio)
      (show 0≤(2/5)*s+s^2/2 by positivity)
    have term1 := mul_nonneg (mul_nonneg ap.le sp.le)
      (show 0≤1-4*s by linarith only [small])
    have equation :
        gamma*((2/5)*s+s^2/2)-alpha*s^2/5=
        (gamma-(2/21)*alpha)*((2/5)*s+s^2/2)+
          (4/105)*alpha*s*(1-4*s) := by ring
    change 0<alpha*(s^2/5)+gamma*(c-1-(2/5)*s) at secondCut
    nlinarith only [secondCut,defectTerm,term0,term1,equation]

private theorem upper_pn (q : OpenSquare) (x y : ℝ)
    (hu : 0≤x*q.c+y*q.s) (hv : -x*q.s+y*q.c≤0) :
    upper q x y=(x*q.c+y*q.s)*(q.loU+q.side)+
      (-x*q.s+y*q.c)*q.loV := by
  dsimp [upper,supportRadius,centerX,centerY]
  rw [abs_of_nonneg hu,abs_of_nonpos hv]
  ring

/-- The actual two-square support disjunction and genuine quadratic
right-wall clearance imply a uniform strict opposite-angle bound. -/
theorem opposite_slope_strong (A D : OpenSquare)
    (an : Normal A.c A.s) (dn : Normal D.c D.s)
    (ha : 1<A.side) (sp : 0<A.s) (narrow : 4*A.s≤A.c)
    (sharp : A.loU-2*(A.c+A.s)<A.s^2/5)
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (center : D.Inside 2 2) (bottom : D.Inside 2 (3/2))
    (axes : upper D A.c A.s≤A.loU ∨
      D.loU+D.side≤lower A D.c D.s) : 82*D.s<29*D.c := by
  have ab := normal_bounds an
  have db := normal_bounds dn
  have cp : 0<A.c := by linarith only [ab.1]
  have dp : 0<D.c := by linarith only [db.1]
  by_cases order : A.c*D.s≤A.s*D.c
  · have product := mul_nonneg dp.le (sub_nonneg.mpr narrow)
    have scaled : A.c*(4*D.s-D.c)≤0 := by
      nlinarith only [order,product]
    have small : 4*D.s≤D.c := by
      exact (mul_nonpos_iff_of_pos_left cp).mp scaled
    linarith only [small,dp]
  have gp : 0<A.c*D.s-A.s*D.c := by linarith only [order]
  let alpha := A.c*D.c+A.s*D.s
  let gamma := A.c*D.s-A.s*D.c
  let e := A.loU-2*(A.c+A.s)
  let u := D.loU+D.side-2*(D.c+D.s)
  let v := A.loV-2*(A.c-A.s)
  have ap : 0<alpha := by dsimp [alpha]; positivity
  have up : 0<u := by dsimp [u]; linarith only [center.2.1]
  have gpos : 0<gamma := gp
  apply slope_scalar an dn sp narrow
  rcases axes with own | other
  · left
    have support := upper_pn D A.c A.s ap.le (by linarith only [gp])
    have equation : upper D A.c A.s-2*(A.c+A.s)=
        alpha*u+gamma*(2*(D.c-D.s)-D.loV) := by
      rw [support]
      dsimp [alpha,gamma,u]
      linear_combination (2*(A.c+A.s))*D.unit_normal
    have lower : D.c/2<2*(D.c-D.s)-D.loV := by
      nlinarith only [bottom.2.2.1]
    have weighted := mul_pos gpos (sub_pos.mpr lower)
    have extra := mul_pos ap up
    nlinarith only [own,equation,weighted,extra,sharp]
  · right
    have support := lower_pp A D.c D.s
      (by dsimp [alpha] at ap; nlinarith only [ap])
      (by dsimp [gamma] at gpos; nlinarith only [gpos])
    have equation : lower A D.c D.s-2*(D.c+D.s)=alpha*e+gamma*v := by
      rw [support]
      dsimp [alpha,gamma,e,v]
      linear_combination (2*(D.c+D.s))*A.unit_normal
    have height : v<A.c-1-(2/5)*A.s := by dsimp [v]; linarith only [top,ha]
    have weightedE := mul_pos ap (sub_pos.mpr sharp)
    have weightedV := mul_pos gpos (sub_pos.mpr height)
    have cut : 0<alpha*e+gamma*v := by
      dsimp [u] at up
      nlinarith only [up,other,equation]
    dsimp [alpha,gamma,e] at cut weightedE weightedV ⊢
    nlinarith only [cut,weightedE,weightedV]

/-- The width between B's actual foreign left-marker and top-endpoint
faces is larger than one, so B lies strictly above slope 9/25. -/
theorem outer_slope_strong {b t : ℝ} (bn : Normal b t)
    (width : 1<(343/500)*b+t) : 77*b<200*t := by
  apply lt_of_not_ge
  intro small
  have bounds := normal_bounds bn
  have bp : 0<b := by linarith only [bounds.1]
  have weighted := mul_nonneg bp.le
    (show 0≤77*b-200*t by linarith only [small])
  have square := mul_pos (sub_pos.mpr width)
    (show 0<(343/500)*b+t+1 by linarith only [width])
  nlinarith only [weighted,square,bn.2.2,sq_nonneg b]

theorem outer_slope {b t : ℝ} (bn : Normal b t)
    (width : 1<(343/500)*b+t) : 9*b<25*t := by
  have bp : 0<b := by linarith only [(normal_bounds bn).1]
  linarith only [outer_slope_strong bn width,bp]

theorem ordered {C S b t : ℝ} (dn : Normal C S) (bn : Normal b t)
    (opposite : 25*S<9*C) (width : 1<(343/500)*b+t) : b*S<t*C := by
  have dc : 0<C := by linarith only [(normal_bounds dn).1]
  have bc : 0<b := by linarith only [(normal_bounds bn).1]
  have first := mul_pos bc (sub_pos.mpr opposite)
  have second := mul_pos dc (sub_pos.mpr (outer_slope bn width))
  nlinarith only [first,second]

#print axioms opposite_slope_strong
#print axioms outer_slope
#print axioms ordered
#print axioms projected_excess
#print axioms small_excess
end N12Compact.FullAuxWallPositiveAngleOrder
