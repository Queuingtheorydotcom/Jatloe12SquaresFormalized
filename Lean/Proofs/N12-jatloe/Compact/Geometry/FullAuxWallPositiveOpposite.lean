import Compact.Geometry.FullAuxWallOppositeAxes
import Compact.Geometry.C977CornerSectorBounds

/-! The positive canonical opposite square in the full-wall residual.
Both genuine longitudinal SAT selectors survive. They imply the same
small upper-U excess and a definite lower-V escape at the actual foreign
bottom auxiliary point. This file does not assert a pair-only exclusion. -/
namespace N12Compact.FullAuxWallPositiveOpposite

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977ChainBridge
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

/-- The central V-coordinate lies strictly inside the escaping square's
vertical face interval, although its U-coordinate is excluded. -/
theorem central_v_band (A : OpenSquare) (ha : 1<A.side)
    (hc : 0<A.c) (hs : 0<A.s) (narrow : 4*A.s≤A.c)
    (high : A.Inside (5/2) 3)
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s) :
    A.loV<2*(A.c-A.s) ∧ 2*(A.c-A.s)<A.loV+A.side := by
  have cosine : A.c≤1 := by
    nlinarith only [A.unit_normal,sq_nonneg A.s,hc]
  constructor
  · nlinarith only [top,ha,cosine,hs]
  · nlinarith only [high.2.2.2,narrow,hc,hs]

private theorem opposite_v_impossible (A D : OpenSquare)
    (ha : 1<A.side) (an : Normal A.c A.s) (dn : Normal D.c D.s)
    (sp : 0<A.s) (narrow : 4*A.s≤A.c)
    (escape : 2*(A.c+A.s)≤A.loU) (p : A.Inside 2 (113/50))
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (center : D.Inside 2 2)
    (sep : D.loV+D.side≤lower A (-D.s) D.c) : False := by
  have ab := normal_bounds an
  have db := normal_bounds dn
  have cp : 0<A.c := by linarith only [ab.1]
  have dp : 0<D.c := by linarith only [db.1]
  let e := A.loU-2*(A.c+A.s)
  let v := A.loV-2*(A.c-A.s)
  let dx := A.c*e-A.s*v
  let dy := A.s*e+A.c*v
  have ep : 0≤e := sub_nonneg.mpr escape
  have offset : e<(13/50)*A.s := by dsimp [e]; linarith only [p.1]
  have height : v<A.c-1-(2/5)*A.s := by dsimp [v]; linarith only [top,ha]
  have vp : v<0 := by linarith only [height,ab.2.1,sp]
  have xp : 0≤dx := by
    have first := mul_nonneg cp.le ep
    have second := mul_nonpos_of_nonneg_of_nonpos sp.le vp.le
    dsimp [dx]
    linarith only [first,second]
  have yp : dy<0 :=
    (FullAuxWallLowerCorner.scalar A.c A.s e v cp sp A.unit_normal narrow offset height).1
  have corner := bands_closed A A.loU A.loV
    ⟨le_rfl,by linarith only [A.side_pos]⟩
    ⟨le_rfl,by linarith only [A.side_pos]⟩
  have bound := (closed_bounds A _ _ (-D.s) D.c corner).1
  have identity :
      (-D.s)*(A.c*A.loU-A.s*A.loV)+D.c*(A.s*A.loU+A.c*A.loV)-
        2*(D.c-D.s)=(-D.s)*dx+D.c*dy := by
    dsimp [dx,dy,e,v]
    linear_combination (2*(D.c-D.s))*A.unit_normal
  have first := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr dn.1) xp
  have second := mul_neg_of_pos_of_neg dp yp
  nlinarith only [sep,bound,center.2.2.2,identity,first,second]

/-- Actual A/C disjointness leaves both forward U-axis alternatives.
No relative-angle order is assumed or silently selected. -/
theorem alternatives (A D : OpenSquare)
    (ha : 1<A.side) (same : A.side=D.side)
    (an : Normal A.c A.s) (dn : Normal D.c D.s)
    (sp : 0<A.s) (narrow : 4*A.s≤A.c)
    (escape : 2*(A.c+A.s)≤A.loU)
    (p : A.Inside 2 (113/50)) (m : A.Inside (47/20) (47/20))
    (high : A.Inside (5/2) 3)
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (marker : D.Inside (33/20) (33/20)) (center : D.Inside 2 2)
    (apart : ∀ x y, ¬(A.Inside x y ∧ D.Inside x y)) :
    upper D A.c A.s≤A.loU ∨ D.loU+D.side≤lower A D.c D.s := by
  have ab := normal_bounds an
  have db := normal_bounds dn
  have cp : 0<A.c := by linarith only [ab.1]
  have dp : 0<D.c := by linarith only [db.1]
  have av : (-A.s)^2+A.c^2=1 := by nlinarith only [A.unit_normal]
  have dv : (-D.s)^2+D.c^2=1 := by nlinarith only [D.unit_normal]
  have forward (nx ny : ℝ) (unit : nx^2+ny^2=1) (direction : 0≤nx+ny)
      (sep : upper D nx ny≤lower A nx ny ∨ upper A nx ny≤lower D nx ny) :
      upper D nx ny≤lower A nx ny := by
    rcases sep with yes | no
    · exact yes
    · have low := (strict_bounds D _ _ nx ny unit marker).1
      have upper := (strict_bounds A _ _ nx ny unit m).2
      exfalso
      nlinarith only [low,upper,no,direction]
  have axes := CongruentSAT.faceSeparation_of_disjoint D A same.symm
    (fun x y h => apart x y ⟨h.2,h.1⟩)
  change pairRadius D A≤|D.c*(centerX A-centerX D)+D.s*(centerY A-centerY D)| ∨
    pairRadius D A≤|-D.s*(centerX A-centerX D)+D.c*(centerY A-centerY D)| ∨
    pairRadius A D≤|A.c*(centerX A-centerX D)+A.s*(centerY A-centerY D)| ∨
    pairRadius A D≤|-A.s*(centerX A-centerX D)+A.c*(centerY A-centerY D)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius D nx ny+supportRadius A nx ny=R)
      (sep : R≤|nx*(centerX A-centerX D)+ny*(centerY A-centerY D)|) :=
    separated D A nx ny (by rwa [identity])
  rcases axes with du | dV | au | aV
  · right
    have selected := forward D.c D.s D.unit_normal
      (by linarith only [dp,dn.1]) (separateAxis _ _ _ (parallel_radius D A) du)
    simpa only [(ownU D).2] using selected
  · have selected := forward (-D.s) D.c dv
      (by linarith only [dn.2.1]) (separateAxis _ _ _ (transverse_radius D A) dV)
    have own : D.loV+D.side≤lower A (-D.s) D.c := by
      simpa only [(ownV D).2] using selected
    exact False.elim (opposite_v_impossible A D ha an dn sp narrow escape p top center own)
  · left
    have identity : supportRadius D A.c A.s+supportRadius A A.c A.s=
        pairRadius A D := by rw [add_comm]; exact parallel_radius A D
    have selected := forward A.c A.s A.unit_normal
      (by linarith only [cp,sp]) (separateAxis _ _ _ identity au)
    simpa only [(ownU A).1] using selected
  · have identity : supportRadius D (-A.s) A.c+supportRadius A (-A.s) A.c=
        pairRadius A D := by rw [add_comm]; exact transverse_radius A D
    have selected := forward (-A.s) A.c av
      (by linarith only [an.2.1]) (separateAxis _ _ _ identity aV)
    have own : upper D (-A.s) A.c≤A.loV := by
      simpa only [(ownV A).1] using selected
    have lower := (central_v_band A ha cp sp narrow high top).1
    have upper := (strict_bounds D _ _ (-A.s) A.c av center).2
    exact False.elim (by nlinarith only [own,lower,upper])

/-- Either surviving selector bounds the same actual face excess.
Closed face points remove the need for relative-angle case expansion. -/
theorem upper_u_offset (A D : OpenSquare)
    (ha : 1<A.side) (an : Normal A.c A.s) (dn : Normal D.c D.s)
    (sp : 0<A.s) (narrow : 4*A.s≤A.c)
    (escape : 2*(A.c+A.s)≤A.loU) (p : A.Inside 2 (113/50))
    (high : A.Inside (5/2) 3) (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (center : D.Inside 2 2)
    (axes : upper D A.c A.s≤A.loU ∨ D.loU+D.side≤lower A D.c D.s) :
    0<D.loU+D.side-2*(D.c+D.s) ∧ D.loU+D.side-2*(D.c+D.s)<1/10 := by
  have ab := normal_bounds an
  have db := normal_bounds dn
  have cp : 0<A.c := by linarith only [ab.1]
  have dp : 0<D.c := by linarith only [db.1]
  have dNonnegative : 0≤D.s := dn.1
  let u := D.loU+D.side-2*(D.c+D.s)
  let e := A.loU-2*(A.c+A.s)
  let α := A.c*D.c+A.s*D.s
  have up : 0<u := by dsimp [u]; linarith only [center.2.1]
  have ep : 0≤e := sub_nonneg.mpr escape
  have e_def : e=A.loU-2*(A.c+A.s) := rfl
  have esmall : e<(13/50)*A.s := by dsimp [e]; linarith only [p.1]
  have ap : 0<α := by dsimp [α]; positivity
  have au : α≤1 := dot_le_one an dn
  have al : (7/10)*A.c≤α := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr db.1)
    have second := mul_nonneg sp.le dn.1
    dsimp [α]
    nlinarith only [first,second]
  refine ⟨up,?_⟩
  change u<1/10
  rcases axes with own | other
  · have face := bands_closed D (D.loU+D.side) (2*(D.c-D.s))
      ⟨by linarith only [D.side_pos],le_rfl⟩
      ⟨by linarith only [center.2.2.1],by linarith only [center.2.2.2]⟩
    have bound := (closed_bounds D _ _ A.c A.s face).2
    have identity :
        A.c*(D.c*(D.loU+D.side)-D.s*(2*(D.c-D.s)))+
          A.s*(D.s*(D.loU+D.side)+D.c*(2*(D.c-D.s)))-2*(A.c+A.s)=α*u := by
      dsimp [α,u]
      linear_combination (2*(A.c+A.s))*D.unit_normal
    have cut : α*u<(13/50)*A.s := by
      nlinarith only [bound,own,identity,esmall,e_def]
    apply lt_of_not_ge
    intro large
    have first := mul_nonneg ap.le (sub_nonneg.mpr large)
    nlinarith only [first,al,cut,narrow,cp]
  · have v := central_v_band A ha cp sp narrow high top
    have face := bands_closed A A.loU (2*(A.c-A.s))
      ⟨le_rfl,by linarith only [A.side_pos]⟩ ⟨v.1.le,v.2.le⟩
    have bound := (closed_bounds A _ _ D.c D.s face).1
    have identity :
        D.c*(A.c*A.loU-A.s*(2*(A.c-A.s)))+
          D.s*(A.s*A.loU+A.c*(2*(A.c-A.s)))-2*(D.c+D.s)=α*e := by
      dsimp [α,e]
      linear_combination (2*(D.c+D.s))*A.unit_normal
    have cut : u≤α*e := by dsimp [u]; nlinarith only [bound,other,identity]
    have weighted := mul_nonneg ep (sub_nonneg.mpr au)
    nlinarith only [cut,weighted,esmall,narrow,ab.2.1]

/-- The genuine foreign bottom point must lie below C's lower V face;
all other bands are forced by the small actual U excess and strict center. -/
theorem lower_v_face (D : OpenSquare) (dn : Normal D.c D.s)
    (ha : 1<D.side) (center : D.Inside 2 2)
    (excess : D.loU+D.side-2*(D.c+D.s)<1/10)
    (missing : ¬D.Inside (87/50) 1) : D.c-(87/50)*D.s≤D.loV := by
  have db := normal_bounds dn
  have dp : 0<D.c := by linarith only [db.1]
  have projection : (13/50)*D.c+D.s≤9/10 := by
    linarith only [dn.2.1,db.2.2.2.2.2]
  apply le_of_not_gt
  intro lower
  apply missing
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [excess,ha,projection]
  · nlinarith only [center.2.1,dp,dn.1]
  · linarith only [lower]
  · nlinarith only [center.2.2.2,dn.2.1,dp]

#print axioms alternatives
#print axioms upper_u_offset
#print axioms lower_v_face
end N12Compact.FullAuxWallPositiveOpposite
