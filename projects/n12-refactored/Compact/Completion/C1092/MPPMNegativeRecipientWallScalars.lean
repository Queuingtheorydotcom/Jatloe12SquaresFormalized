import Compact.Completion.C1092.MPPMCrosspointBoundaryHalf
import Compact.Completion.CommonCases.UnitCircleChord

/-! Exact scalar comparisons for NEGATIVE-MISSING-POSITIVE-ENDING,
Theorem 1. The delicate quarter-slope endpoint is replaced by a finite
half-angle cubic on [0,77/625]. This rational interval contains the whole
required arc and retains a positive endpoint value. Source only. -/
namespace N12Compact.C1092MPPMNegativeRecipientWall.Scalars
open C977CornerCubic
set_option Elab.async false
noncomputable section

theorem weak_bounds {d t : ℝ} (en : Normal d t)
    (angle : 237/763<C1092WallProfileScalars.half d t) :
    7/10<d ∧ d<33/40 ∧ 283/500<t ∧ t<71/100 ∧ 139/100<d+t := by
  have eb := normal_bounds en
  have dp : 0<d := by linarith only [eb.1]
  have endpoint : Normal (263000/319169:ℝ) (180831/319169) := by norm_num [Normal]
  have lower : 180831/319169<t := by
    apply lt_of_not_ge
    intro low
    have order := C1092MPPMCrosspointSupport.half_order en endpoint low
    have high : C1092WallProfileScalars.half d t≤237/763 := by
      change t/(1+d)≤237/763
      norm_num [C1092MPPMCrosspointSupport.half] at order
      exact order
    linarith only [angle,high]
  have cosine := C977CornerSectorBounds.cosine_order en endpoint lower.le
  have order := mul_nonneg (sub_nonneg.mpr en.2.1) (show 0≤d+t by linarith only [dp,en.1])
  have sum := CommonCases.UnitCircleChord.increasing
    (c:=d) (s:=t) (d:=263000/319169) (t:=180831/319169) (A:=1) (B:=1)
    dp (by norm_num) en.2.2 endpoint.2.2 en.1 endpoint.1 lower.le
    (by norm_num) (by norm_num) (by linarith only [en.2.1])
  refine ⟨?_,by linarith only [cosine],by linarith only [lower],?_,by linarith only [sum]⟩
  · nlinarith only [eb.1,order,en.2.2]
  · nlinarith only [order,en.2.2,en.1,sq_nonneg (t-71/100)]

private def poly (x : ℝ) : ℝ := 43-250*x-957*x^2+1250*x^3

private theorem poly_positive (x : ℝ) (xn : 0≤x) (cap : x^2+8*x≤1) : 0<poly x := by
  have xu : x≤77/625 := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (show 0<x-77/625 by linarith only [bad])
      (show 0<x+77/625+8 by linarith only [xn])
    nlinarith only [cap,product]
  have small : x≤1/8 := by linarith only [xu]
  have square := mul_le_mul small small xn (by norm_num : (0:ℝ)≤1/8)
  have coefficient : 0≤250+957*(77/625+x)-1250*((77/625)^2+(77/625)*x+x^2) := by
    nlinarith only [square,small,xn]
  have product := mul_nonneg (sub_nonneg.mpr xu) coefficient
  have identity : poly x-poly (77/625)=
      (77/625-x)*(250+957*(77/625+x)-1250*((77/625)^2+(77/625)*x+x^2)) := by
    dsimp [poly]; ring
  have endpoint : 0<poly (77/625) := by norm_num [poly]
  nlinarith only [product,identity,endpoint]

/-- Division-free form of the manuscript's g(beta,v)>0. The whole
closed quarter-slope interval is handled by one exact cubic comparison. -/
theorem upward_margin {d t b r : ℝ} (en : Normal d t) (bn : Normal b r)
    (rp : 0<r) (slope : 4*r≤b) (recipient : 2*d≤3*t) :
    0<b*(d*b+t*r)+t-2*(d*b+t*r)-b*t+(543/500)*t*r+b*d := by
  have eb := normal_bounds en
  have bb := normal_bounds bn
  have dp : 0<d := by linarith only [eb.1]
  have bp : 0<b := by linarith only [bb.1]
  have near : 97/100<b := by
    apply lt_of_not_ge
    intro low
    have square := mul_nonneg (show 0≤b-4*r by linarith only [slope])
      (show 0≤b+4*r by linarith only [bp,rp])
    have bound := mul_nonneg (show 0≤97/100-b by linarith only [low])
      (show 0≤97/100+b by linarith only [bp])
    nlinarith only [square,bound,bn.2.2]
  let x := C1092WallProfileScalars.half b r
  have data := C1092WallProfileScalars.quarter_data b r bp.le bn.1 bn.2.2
  have xn : 0≤x := data.1
  have den : 0<1+x^2 := by positivity
  have cosine : (1+x^2)*b=1-x^2 := data.2.2.2.1
  have sine : (1+x^2)*r=2*x := data.2.2.2.2
  have cap : x^2+8*x≤1 := by
    have weight := mul_nonneg (show 0≤b-4*r by linarith only [slope]) den.le
    nlinarith only [weight,cosine,sine]
  have pp := poly_positive x xn cap
  let base := (2/3)*(b-457/500)+x*(2/3-b)
  have identity : (1+x^2)*base=poly x/750 := by
    dsimp [base,poly]
    linear_combination (2/3-x)*cosine
  have basep : 0<base := by
    have product : 0<(1+x^2)*base := by nlinarith only [identity,pp]
    exact pos_of_mul_pos_right product den.le
  have coefficient : 0<b-457/500+x := by linarith only [near,xn]
  have comparison := mul_nonneg (show 0≤t-(2/3)*d by linarith only [recipient]) coefficient.le
  have lower := mul_pos dp basep
  have margin : 0<t*(b-457/500)+x*(t-b*d) := by
    dsimp [base] at lower
    nlinarith only [comparison,lower]
  have relation : x*(1+b)=r := data.2.2.1
  have chord : x*r=1-b := by
    have weighted := congrArg (fun z : ℝ => z*r) relation
    dsimp at weighted
    have factor : (1+b)*(x*r-(1-b))=0 := by nlinarith only [weighted,bn.2.2]
    exact sub_eq_zero.mp ((mul_eq_zero.mp factor).resolve_left (by linarith only [bp]))
  have product := mul_pos rp margin
  have formula : b*(d*b+t*r)+t-2*(d*b+t*r)-b*t+(543/500)*t*r+b*d=
      r*(t*(b-457/500)+x*(t-b*d)) := by
    linear_combination -(t-b*d)*chord
  rwa [←formula] at product

theorem boundary_margin {d t b r : ℝ} (en : Normal d t) (bn : Normal b r)
    (rp : 0<r) (slope : 4*r≤b)
    (dh : d<33/40) (tl : 283/500<t) (th : t<71/100) (sum : 139/100<d+t) :
    0<(d*b+t*r)+(t*b-d*r)-(543/500)*b+
      (13/50)*(t*b-d*r)*t-(d*b+t*r)*(t-(14/25)*d) := by
  have bb := normal_bounds bn
  have eb := normal_bounds en
  have bp : 0<b := by linarith only [bb.1]
  have dp : 0<d := by linarith only [eb.1]
  have dot : d*t≤1/2 := by nlinarith only [en.2.2,sq_nonneg (d-t)]
  have order := mul_nonneg (sub_nonneg.mpr en.2.1) (show 0≤d+t by linarith only [dp,en.1])
  have square : t^2≤1/2 := by nlinarith only [order,en.2.2]
  let P := d+t-263/500-d*t-(3/10)*t^2
  let Q := t-d-t^2+(3/10)*d*t
  have pp : 107/500<P := by dsimp [P]; linarith only [sum,dot,square]
  have first := mul_nonneg (show 0≤71/100-t by linarith only [th])
    (show 0≤71/100+t-1 by linarith only [tl])
  have last := mul_pos (show 0<33/40-d by linarith only [dh])
    (show 0<1-(3/10)*t by linarith only [th])
  have qq : -(12/25)<Q := by dsimp [Q]; nlinarith only [first,last,tl]
  have pweight := mul_pos bp (show 0<P-107/500 by linarith only [pp])
  have qweight := mul_pos rp (show 0<Q+12/25 by linarith only [qq])
  have identity : (d*b+t*r)+(t*b-d*r)-(543/500)*b+
      (13/50)*(t*b-d*r)*t-(d*b+t*r)*(t-(14/25)*d)=b*P+r*Q := by
    dsimp [P,Q]
    linear_combination ((14/25)*b)*en.2.2
  rw [identity]
  nlinarith only [pweight,qweight,slope,bp]

end
#print axioms upward_margin
#print axioms boundary_margin
end N12Compact.C1092MPPMNegativeRecipientWall.Scalars
