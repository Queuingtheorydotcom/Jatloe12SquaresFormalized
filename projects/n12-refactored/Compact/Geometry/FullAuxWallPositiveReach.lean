import Compact.Geometry.FullAuxWallPositiveOpposite
import Compact.Geometry.FullAuxWallPositiveMargins

/-! A true shifted left point of the positive opposite central square.
The bottom-face bound uses the actual A/C separating axis; the coarse
upper-U excess alone would not imply this point. -/
namespace N12Compact.FullAuxWallPositiveReach

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic
set_option Elab.async false

private theorem face (q : OpenSquare) (U V : ℝ)
    (hu : q.loU≤U ∧ U≤q.loU+q.side) (hv : q.loV≤V ∧ V≤q.loV+q.side) :
    ClosedInside q (q.c*U-q.s*V) (q.s*U+q.c*V) := by
  have first : q.c*(q.c*U-q.s*V)+q.s*(q.s*U+q.c*V)=U := by
    linear_combination U*q.unit_normal
  have second : -q.s*(q.c*U-q.s*V)+q.c*(q.s*U+q.c*V)=V := by
    linear_combination V*q.unit_normal
  change q.loU≤_ ∧ _≤q.loU+q.side ∧ q.loV≤_ ∧ _≤q.loV+q.side
  rw [first,second]
  exact ⟨hu.1,hu.2,hv.1,hv.2⟩

private theorem own_margin {c s C S : ℝ}
    (an : Normal c s) (dn : Normal C S) (narrow : 4*s≤c) :
    (13/50)*s≤(c*C+s*S)*(1-(2/5)*C-S)+(1/2)*C*(c*S-s*C) := by
  have ab := normal_bounds an
  have db := normal_bounds dn
  have cp : 0<c := by linarith only [ab.1]
  have dp : 0<C := by linarith only [db.1]
  let H := 1-(2/5)*C-(1/2)*S
  have cross : C*S≤1/2 := by nlinarith only [dn.2.2,sq_nonneg (C-S)]
  have product := mul_nonneg (sub_nonneg.mpr db.1)
    (show 0≤(18/25 : ℝ)-(2/5)*C by linarith only [db.2.1])
  have bound : (1/4 : ℝ)≤C*H := by
    dsimp [H]
    nlinarith only [product,cross]
  have hp : 0≤H := by nlinarith only [bound,dp]
  have first := mul_nonneg cp.le (sub_nonneg.mpr bound)
  have second := mul_nonneg (mul_nonneg an.1 dn.1) hp
  have identity : (c*C+s*S)*(1-(2/5)*C-S)+(1/2)*C*(c*S-s*C)=
      (c*C+s*S)*H-(1/2)*s := by
    dsimp [H]
    linear_combination (-(1/2)*s)*dn.2.2
  nlinarith only [first,second,identity,narrow,an.1]

/-- Each genuine longitudinal A/C separator puts the foreign bottom
auxiliary strictly above C's lower U face. -/
theorem bottom_u (A D : OpenSquare)
    (ha : 1<A.side) (hd : 1<D.side)
    (an : Normal A.c A.s) (dn : Normal D.c D.s)
    (sp : 0<A.s) (narrow : 4*A.s≤A.c)
    (p : A.Inside 2 (113/50)) (high : A.Inside (5/2) 3)
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (low : D.Inside 2 (3/2))
    (axes : upper D A.c A.s≤A.loU ∨ D.loU+D.side≤lower A D.c D.s) :
    D.loU<(8/5)*D.c+D.s := by
  have ab := normal_bounds an
  have db := normal_bounds dn
  have cp : 0<A.c := by linarith only [ab.1]
  have dp : 0<D.c := by linarith only [db.1]
  let alpha := A.c*D.c+A.s*D.s
  let gamma := A.c*D.s-A.s*D.c
  let u := D.loU+D.side-2*(D.c+D.s)
  let e := A.loU-2*(A.c+A.s)
  have alpha_pos : 0<alpha := by dsimp [alpha]; positivity
  have e_small : e<(13/50)*A.s := by dsimp [e]; linarith only [p.1]
  rcases axes with own | other
  · apply lt_of_not_ge
    intro bad
    have lower : 1-(2/5)*D.c-D.s<u := by
      dsimp [u]
      linarith only [bad,hd]
    have point := face D (D.loU+D.side) (-(2:ℝ)*D.s+(3/2)*D.c)
      ⟨by linarith only [D.side_pos],le_rfl⟩
      ⟨by linarith only [low.2.2.1],by linarith only [low.2.2.2]⟩
    have bound := (closed_bounds D _ _ A.c A.s point).2
    have identity :
        A.c*(D.c*(D.loU+D.side)-D.s*(-2*D.s+(3/2)*D.c))+
          A.s*(D.s*(D.loU+D.side)+D.c*(-2*D.s+(3/2)*D.c))-
          2*(A.c+A.s)=alpha*u+(1/2)*D.c*gamma := by
      dsimp [alpha,gamma,u]
      linear_combination (2*(A.c+A.s))*D.unit_normal
    have weighted := mul_pos alpha_pos (sub_pos.mpr lower)
    have margin := own_margin an dn narrow
    change (13/50)*A.s≤alpha*(1-(2/5)*D.c-D.s)+(1/2)*D.c*gamma at margin
    dsimp [e] at e_small
    nlinarith only [bound,own,identity,weighted,margin,e_small]
  · let V := 3*A.c-(12/5)*A.s-1
    have vlo : A.loV≤V := by dsimp [V]; linarith only [top,ha]
    have vhi : V≤A.loV+A.side := by
      dsimp [V]
      linarith only [high.2.2.2,narrow,ab.2.1]
    have point := face A A.loU V
      ⟨le_rfl,by linarith only [A.side_pos]⟩ ⟨vlo,vhi⟩
    have bound := (closed_bounds A _ _ D.c D.s point).1
    have identity :
        D.c*(A.c*A.loU-A.s*V)+D.s*(A.s*A.loU+A.c*V)-2*(D.c+D.s)=
        alpha*e+gamma*(A.c-1-(2/5)*A.s) := by
      dsimp [alpha,gamma,e,V]
      linear_combination (2*(D.c+D.s))*A.unit_normal
    have weighted := mul_pos alpha_pos (sub_pos.mpr e_small)
    have coefficient :
        (2/5)*D.c+D.s+alpha*((13/50)*A.s)+gamma*(A.c-1-(2/5)*A.s)=
        D.c*FullAuxWallPositiveMargins.F A.c A.s+
          D.s*FullAuxWallPositiveMargins.G A.c A.s := by
      dsimp [alpha,gamma,FullAuxWallPositiveMargins.F,FullAuxWallPositiveMargins.G]
      linear_combination D.s*A.unit_normal
    have margin := FullAuxWallPositiveMargins.margin an dn narrow
    dsimp [e] at identity weighted
    nlinarith only [bound,other,identity,weighted,coefficient,margin,hd]

/-- The actual missing bottom auxiliary therefore selects the lower V
face, with its original coordinate 8/5 retained. -/
theorem bottom_face (D : OpenSquare) (dn : Normal D.c D.s)
    (center : D.Inside 2 2) (u : D.loU<(8/5)*D.c+D.s)
    (missing : ¬D.Inside (8/5) 1) : D.c-(8/5)*D.s≤D.loV := by
  have db := normal_bounds dn
  have dp : 0<D.c := by linarith only [db.1]
  apply le_of_not_gt
  intro bad
  apply missing
  refine ⟨u,?_,?_,?_⟩
  · nlinarith only [center.2.1,dp,dn.1]
  · linarith only [bad]
  · nlinarith only [center.2.2.2,dp,dn.2.1]

/-- This shifted point is forced by the two genuine face bounds. Unlike
(11/10,2), its upper-V band has a uniform strict margin on the whole arc. -/
theorem point (D : OpenSquare) (dn : Normal D.c D.s)
    (hd : 1<D.side) (center : D.Inside 2 2) (low : D.Inside 2 (3/2))
    (excess : D.loU+D.side-2*(D.c+D.s)<1/10)
    (bottom : D.c-(8/5)*D.s≤D.loV) : D.Inside (6/5) (19/10) := by
  have db := normal_bounds dn
  have dp : 0<D.c := by linarith only [db.1]
  have u_projection : (4/5)*D.c+(1/10)*D.s≤9/10 := by
    linarith only [db.2.1,db.2.2.2.1]
  have v_projection : (9/10)*D.c+(2/5)*D.s≤1 := by
    have identity : ((9/10)*D.c+(2/5)*D.s)^2+
        ((2/5)*D.c-(9/10)*D.s)^2=97/100 := by
      nlinarith only [dn.2.2]
    nlinarith only [identity,sq_nonneg ((2/5)*D.c-(9/10)*D.s)]
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [excess,hd,u_projection]
  · nlinarith only [center.2.1,dp,dn.1]
  · nlinarith only [low.2.2.1,dp,dn.1]
  · nlinarith only [bottom,hd,v_projection]

#print axioms bottom_u
#print axioms bottom_face
#print axioms point
end N12Compact.FullAuxWallPositiveReach
