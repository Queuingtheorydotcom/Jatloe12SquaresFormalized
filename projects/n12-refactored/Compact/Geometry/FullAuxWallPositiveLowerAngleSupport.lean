import Compact.Geometry.FullAuxWallPositiveTop
import Compact.Geometry.FullAuxWallPositiveLowerAngle

/-! Both genuine transverse C/B separators imply a scalar obstruction
when the opposite central square approaches an axis. All translations
are eliminated with its real lower face and the outer square's two real
upper faces; the common side remains strictly larger than one. -/
namespace N12Compact.FullAuxWallPositiveLowerAngleSupport
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic FullAuxWallTopEndpoint
set_option Elab.async false

/-- Exact necessary inequalities for the two remaining actual selectors. -/
theorem cuts (D B : OpenSquare)
    (dn : Normal D.c D.s) (bn : Normal B.c B.s)
    (ha : 1<D.side) (same : D.side=B.side)
    (bottom : D.c-(8/5)*D.s≤D.loV)
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (upperV : B.loV+B.side≤3*B.c-B.s)
    (ordered : D.s*B.c≤D.c*B.s)
    (modes : D.loV+D.side≤lower B (-D.s) D.c ∨ upper D (-B.s) B.c≤B.loV) :
    1<D.c*(2-B.c-B.s+(3/5)*B.c*B.s)+
        D.s*(B.c-B.s+(3/5)*B.s^2) ∨
      1+B.c*(D.c-D.s+D.s^2+(2/5)*D.c*D.s-2)+
        B.s*(D.c+D.s+(2/5)*D.s^2-D.c*D.s-1)-
        (D.c*B.s-D.s*B.c)*(D.loU+D.side-2*(D.c+D.s))<0 := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dc : 0<D.c := by linarith only [db.1]
  have bc : 0<B.c := by linarith only [bb.1]
  let alpha := D.c*B.c+D.s*B.s
  let beta := D.c*B.s-D.s*B.c
  let u := D.loU+D.side-2*(D.c+D.s)
  have ap : 0<alpha := by
    exact add_pos_of_pos_of_nonneg (mul_pos dc bc) (mul_nonneg dn.1 bn.1)
  have bp : 0≤beta := by dsimp [beta]; linarith only [ordered]
  have strict := mul_pos (sub_pos.mpr ha)
    (show 0<1+alpha+beta by linarith only [ap,bp])
  rcases modes with own | neighbor
  · left
    have support := lower_pp B (-D.s) D.c
      (by dsimp [beta] at bp; nlinarith only [bp])
      (by dsimp [alpha] at ap; nlinarith only [ap])
    have formula : lower B (-D.s) D.c=beta*B.loU+alpha*B.loV := by
      rw [support]
      dsimp [alpha,beta]
      ring
    have first := mul_nonneg bp (sub_nonneg.mpr upperU)
    have second := mul_nonneg ap.le (sub_nonneg.mpr upperV)
    have identity :
        beta*((8/5)*B.c+3*B.s)+alpha*(3*B.c-B.s)-
          (D.c-(8/5)*D.s)-(1+alpha+beta)=
        D.c*(2-B.c-B.s+(3/5)*B.c*B.s)+
          D.s*(B.c-B.s+(3/5)*B.s^2)-1 := by
      dsimp [alpha,beta]
      linear_combination (3*D.c-(8/5)*D.s)*bn.2.2
    rw [←same] at first second
    nlinarith only [own,formula,first,second,bottom,strict,identity]
  · right
    have hu : -B.s*D.c+B.c*D.s≤0 := by dsimp [beta] at bp; nlinarith only [bp]
    have hv : 0≤-(-B.s)*D.s+B.c*D.c := by dsimp [alpha] at ap; nlinarith only [ap]
    have formula : upper D (-B.s) B.c=(-beta)*D.loU+alpha*(D.loV+D.side) := by
      dsimp [upper,supportRadius,centerX,centerY]
      rw [abs_of_nonpos hu,abs_of_nonneg hv]
      dsimp [alpha,beta]
      ring
    have low := mul_nonneg ap.le (sub_nonneg.mpr bottom)
    have identity :
        (1+alpha+beta)-beta*(2*(D.c+D.s)+u)+
          alpha*(D.c-(8/5)*D.s)-(3*B.c-B.s)=
        1+B.c*(D.c-D.s+D.s^2+(2/5)*D.c*D.s-2)+
          B.s*(D.c+D.s+(2/5)*D.s^2-D.c*D.s-1)-beta*u := by
      dsimp [alpha,beta]
      linear_combination (B.c-2*B.s)*dn.2.2
    rw [←same] at upperV
    change 1+B.c*(D.c-D.s+D.s^2+(2/5)*D.c*D.s-2)+
      B.s*(D.c+D.s+(2/5)*D.s^2-D.c*D.s-1)-beta*u<0
    dsimp [u] at identity ⊢
    nlinarith only [neighbor,formula,low,upperV,strict,identity]

#print axioms cuts

/-- Neither full-square separating axis permits the opposite central
frame to lie within sine 1/20 of the horizontal. -/
theorem sine (D B : OpenSquare)
    (dn : Normal D.c D.s) (bn : Normal B.c B.s)
    (ha : 1<D.side) (same : D.side=B.side)
    (bottom : D.c-(8/5)*D.s≤D.loV)
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (upperV : B.loV+B.side≤3*B.c-B.s)
    (steep : 3/10<B.s)
    (offset : D.loU+D.side-2*(D.c+D.s)≤1/112)
    (ordered : D.s*B.c≤D.c*B.s)
    (modes : D.loV+D.side≤lower B (-D.s) D.c ∨ upper D (-B.s) B.c≤B.loV) :
    1/20<D.s := by
  apply lt_of_not_ge
  intro small
  have necessary := cuts D B dn bn ha same bottom upperU upperV ordered modes
  rcases necessary with own | neighbor
  · have bound := FullAuxWallPositiveLowerAngle.c_axis dn bn small steep
    linarith only [own,bound]
  · have bound := FullAuxWallPositiveLowerAngle.b_axis dn bn small steep offset
      (by linarith only [ordered])
    linarith only [neighbor,bound]

#print axioms sine
end N12Compact.FullAuxWallPositiveLowerAngleSupport
