import Compact.Geometry.PositiveCentralPositiveLeftBounds
import Compact.Geometry.PositiveCentralPositiveLeftArc
import Compact.Geometry.CornerWallPositiveLongitudinal
import Compact.Geometry.C977NegativeCorner

/-! Original positive-left supports in the missing-west sector. The
central square contributes its actual upper-left vertex. No replacement
coordinate wall or absent auxiliary-point exclusion is used. -/
namespace N12Compact.PositiveCentralPositiveLeft

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977ChainBridge C977CornerCubic C977CornerSectorBounds PositiveCentralEscapeOrder
open PositiveCentralPositiveLeftBounds

/-- Actual left and central seeds remove both transverse separators
and the reverse longitudinal directions for positive canonical frames. -/
theorem left_alternatives (L A : OpenSquare)
    (ln : Normal L.c L.s) (an : Normal A.c A.s) (same : L.side=A.side)
    (lNear : L.Inside 1 (28/25)) (lFar : L.Inside (19/25) (187/100))
    (aMarker : A.Inside (33/20) (33/20))
    (aE : A.Inside (87/50) 2) (aLow : A.Inside 2 (3/2))
    (apart : ∀ x y, ¬(L.Inside x y ∧ A.Inside x y)) :
    L.loU+L.side≤lower A L.c L.s ∨ upper L A.c A.s≤A.loU := by
  have forward (c s : ℝ) (normal : Normal c s)
      (sep : upper L c s≤lower A c s ∨ upper A c s≤lower L c s) :
      upper L c s≤lower A c s := by
    rcases sep with yes | no
    · exact yes
    · have b := normal_bounds normal
      have lp := strict_bounds L _ _ c s normal.2.2 lNear
      have ap := strict_bounds A _ _ c s normal.2.2 aMarker
      exfalso
      nlinarith only [no,lp.1,ap.2,b.1,normal.1]
  have transverse (c s : ℝ) (normal : Normal c s)
      (sep : upper L (-s) c≤lower A (-s) c ∨
        upper A (-s) c≤lower L (-s) c) : False := by
    have b := normal_bounds normal
    have unit : (-s)^2+c^2=1 := by nlinarith only [normal.2.2]
    have lf := strict_bounds L _ _ (-s) c unit lFar
    have al := strict_bounds A _ _ (-s) c unit aLow
    have ae := strict_bounds A _ _ (-s) c unit aE
    have ln := strict_bounds L _ _ (-s) c unit lNear
    rcases sep with lower | upper
    · nlinarith only [lower,lf.2,al.1,b.1,normal.1]
    · nlinarith only [upper,ae.2,ln.1,b.1,normal.2.1]
  have axes := CongruentSAT.faceSeparation_of_disjoint L A same apart
  change pairRadius L A≤|L.c*(centerX A-centerX L)+L.s*(centerY A-centerY L)| ∨
    pairRadius L A≤|-L.s*(centerX A-centerX L)+L.c*(centerY A-centerY L)| ∨
    pairRadius A L≤|A.c*(centerX A-centerX L)+A.s*(centerY A-centerY L)| ∨
    pairRadius A L≤|-A.s*(centerX A-centerX L)+A.c*(centerY A-centerY L)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius L nx ny+supportRadius A nx ny=R)
      (sep : R≤|nx*(centerX A-centerX L)+ny*(centerY A-centerY L)|) :=
    separated L A nx ny (by rwa [identity])
  rcases axes with lu | lv | au | av
  · left
    have h := forward L.c L.s ln (separateAxis _ _ _ (parallel_radius L A) lu)
    simpa only [(ownU L).2] using h
  · exact False.elim (transverse L.c L.s ln
      (separateAxis _ _ _ (transverse_radius L A) lv))
  · right
    have identity : supportRadius L A.c A.s+supportRadius A A.c A.s=pairRadius A L := by
      rw [add_comm]; exact parallel_radius A L
    have h := forward A.c A.s an (separateAxis _ _ _ identity au)
    simpa only [(ownU A).1] using h
  · have identity : supportRadius L (-A.s) A.c+supportRadius A (-A.s) A.c=pairRadius A L := by
      rw [add_comm]; exact transverse_radius A L
    exact False.elim (transverse A.c A.s an (separateAxis _ _ _ identity av))

/-- Quantitative position of the actual upper-left central vertex. -/
theorem vertex_bounds (A : OpenSquare) (p : ℝ)
    (an : Normal A.c A.s) (side : 1<A.side)
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (west : A.loV+A.side≤2*A.c-A.s)
    (floor : 1+(A.c+A.s)*(1-2*A.s)+A.c*(1-p)<A.c*(A.loV+A.side)) :
    A.c*A.loU-A.s*(A.loV+A.side)<
        1-(vertexDefect A.c A.s+A.s*(1-p)) ∧
      A.s*A.loU+A.c*(A.loV+A.side)≤2-A.s*(1-A.c) := by
  have ab := normal_bounds an
  have cp : 0<A.c := by linarith only [ab.1]
  have lo : A.loU<2*(A.c+A.s)-1 := by linarith only [cap,side]
  have first := mul_pos (mul_pos cp cp) (sub_pos.mpr lo)
  have second := mul_nonneg an.1 (sub_nonneg.mpr floor.le)
  have polynomial :
      A.c-A.c^2*(2*(A.c+A.s)-1)+
        A.s*(1+(A.c+A.s)*(1-2*A.s))=(1-A.c)*(1-A.s) := by
    linear_combination (1-2*(A.c+A.s))*an.2.2
  have defect : A.c*vertexDefect A.c A.s=(1-A.c)*(1-A.s) := by
    dsimp [vertexDefect]
    field_simp [ne_of_gt cp] <;> ring
  have xscaled : 0<A.c*((1-(vertexDefect A.c A.s+A.s*(1-p)))-
      (A.c*A.loU-A.s*(A.loV+A.side))) := by
    nlinarith only [first,second,polynomial,defect]
  have xgap := pos_of_mul_pos_right xscaled cp.le
  have upperU := mul_nonneg an.1 (sub_nonneg.mpr lo.le)
  have upperV := mul_nonneg cp.le (sub_nonneg.mpr west)
  exact ⟨by linarith only [xgap],by nlinarith only [upperU,upperV,an.2.2]⟩

private theorem vertex_closed (A : OpenSquare) :
    ClosedInside A (A.c*A.loU-A.s*(A.loV+A.side))
      (A.s*A.loU+A.c*(A.loV+A.side)) := by
  have u : A.c*(A.c*A.loU-A.s*(A.loV+A.side))+
      A.s*(A.s*A.loU+A.c*(A.loV+A.side))=A.loU := by
    linear_combination A.loU*A.unit_normal
  have v : -A.s*(A.c*A.loU-A.s*(A.loV+A.side))+
      A.c*(A.s*A.loU+A.c*(A.loV+A.side))=A.loV+A.side := by
    linear_combination (A.loV+A.side)*A.unit_normal
  change A.loU≤_ ∧ _≤A.loU+A.side ∧ A.loV≤_ ∧ _≤A.loV+A.side
  rw [u,v]
  exact ⟨le_rfl,by linarith only [A.side_pos],by linarith only [A.side_pos],le_rfl⟩

/-- The O-V / L-U pair of longitudinal separators is impossible on
the entire positive canonical left arc, including the axis endpoint. -/
theorem own_axis_impossible (O L A : OpenSquare)
    (on : Normal O.c O.s) (ln : Normal L.c L.s) (an : Normal A.c A.s)
    (side : 1<L.side) (aSide : 1<A.side) (lBox : InsideContainer L)
    (order : O.s≤A.s) (shallow : 9/10≤O.c)
    (wide : 4/5≤A.c) (small : A.s≤3/5)
    (bottom : B O.c O.s<O.loV+O.side)
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (west : A.loV+A.side≤2*A.c-A.s)
    (floor : 1+(A.c+A.s)*(1-2*A.s)+A.c*(1-O.c)<A.c*(A.loV+A.side))
    (ol : O.loV+O.side≤lower L (-O.s) O.c)
    (la : L.loU+L.side≤lower A L.c L.s) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have op : 0<O.c := by linarith only [ob.1]
  have lp : 0<L.c := by linarith only [lb.1]
  have oq : 0≤O.s := on.1
  have lr : 0≤L.s := ln.1
  let K := O.c*L.c+O.s*L.s
  let H := 1+L.s*L.c+(L.s/O.c)*(B O.c O.s+O.s*L.s)
  have kp : 0≤K := by dsimp [K]; positivity
  have coeff : 0<O.c+L.s*K := by
    have nonnegative := mul_nonneg ln.1 kp
    linarith only [op,nonnegative]
  have incoming := CornerWallPositiveLongitudinal.incoming O L on ln lBox ol
  have size := mul_pos (sub_pos.mpr side) coeff
  have bottomWeight := mul_nonneg ln.1 (sub_nonneg.mpr bottom.le)
  have formula : O.c*H=O.c+L.s*K+L.s*B O.c O.s := by
    dsimp [H,K]
    field_simp [ne_of_gt op] <;> ring
  have strict : 0<O.c*((L.loU+L.side)-H) := by
    dsimp [K] at size formula
    nlinarith only [incoming,size,bottomWeight,formula]
  have high : H<L.loU+L.side := by
    have gap := pos_of_mul_pos_right strict op.le
    linarith only [gap]
  have vertex := vertex_bounds A O.c an aSide cap west floor
  have lowerVertex := (closed_bounds A _ _ L.c L.s (vertex_closed A)).1
  have xWeight := mul_pos lp (sub_pos.mpr vertex.1)
  have yWeight := mul_nonneg ln.1 (sub_nonneg.mpr vertex.2)
  have scalar := own_axis_margin on an ln order shallow wide small
  have margin :
      L.c*(1-(vertexDefect A.c A.s+A.s*(1-O.c)))+
        L.s*(2-A.s*(1-A.c))≤H := by
    dsimp [H]
    simp only [div_eq_mul_inv] at scalar ⊢
    nlinarith only [scalar]
  nlinarith only [high,la,lowerVertex,xWeight,yWeight,margin]

/-- The complementary O-V / A-U pair is excluded by the full supports
and left wall of L. No corner or fixed replacement point is assumed. -/
theorem central_axis_impossible (O L A : OpenSquare)
    (on : Normal O.c O.s) (ln : Normal L.c L.s) (an : Normal A.c A.s)
    (side : 1≤L.side) (aSide : 1<A.side) (lBox : InsideContainer L)
    (order : O.s≤A.s) (wide : 4/5≤A.c) (small : A.s≤3/5)
    (bottom : B O.c O.s<O.loV+O.side)
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (ol : O.loV+O.side≤lower L (-O.s) O.c)
    (la : upper L A.c A.s≤A.loU) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have ab := normal_bounds an
  have op : 0<O.c := by linarith only [ob.1]
  have lp : 0≤L.c := by linarith only [lb.1]
  have cp : 0≤A.c := by linarith only [ab.1]
  have oq : 0≤O.s := on.1
  have lr : 0≤L.s := ln.1
  have aq : 0≤A.s := an.1
  let D := O.c*L.s-O.s*L.c
  let K := O.c*L.c+O.s*L.s
  let H := A.s*L.c-A.c*L.s
  let J := A.c*L.c+A.s*L.s
  let E := O.c*A.c+O.s*A.s
  let T := (E*(L.c+L.s)+O.c*(J+|H|)+A.s*(|D|+K))/2
  have kp : 0≤K := by dsimp [K]; positivity
  have jp : 0≤J := by dsimp [J]; positivity
  have ep : 0≤E := by dsimp [E]; positivity
  have tp : 0≤T := by dsimp [T]; positivity
  have low : lower L (-O.s) O.c=
      D*(L.loU+L.side/2)+K*(L.loV+L.side/2)-L.side*(|D|+K)/2 := by
    rw [C977NegativeCorner.lower_in_bands]
    have first : (-O.s)*L.c+O.c*L.s=D := by dsimp [D]; ring
    have second : -(-O.s)*L.s+O.c*L.c=K := by dsimp [K]; ring
    rw [first,second,abs_of_nonneg kp]
    ring
  have high : upper L A.c A.s=
      J*(L.loU+L.side/2)+H*(L.loV+L.side/2)+L.side*(J+|H|)/2 := by
    rw [C977NegativeCorner.upper_in_bands]
    have first : A.c*L.c+A.s*L.s=J := rfl
    have second : -A.c*L.s+A.s*L.c=H := by dsimp [H]; ring
    rw [first,second,abs_of_nonneg jp]
    ring
  have wall := FourSquareBLBridge.left_wall L lp lBox
  rw [abs_of_nonneg ln.1] at wall
  dsimp [centerX] at wall
  have position : 0≤L.c*L.loU-L.s*(L.loV+L.side) := by
    nlinarith only [wall]
  have identity :
      O.c*upper L A.c A.s-A.s*lower L (-O.s) O.c-L.side*T=
        E*(L.c*L.loU-L.s*(L.loV+L.side)) := by
    rw [low,high]
    dsimp [D,K,H,J,E,T]
    ring
  have walled := mul_nonneg ep position
  have supported : A.s*lower L (-O.s) O.c+L.side*T≤O.c*upper L A.c A.s := by
    linarith only [identity,walled]
  have bottomWeight := mul_nonneg an.1 (sub_nonneg.mpr bottom.le)
  have olWeight := mul_nonneg an.1 (sub_nonneg.mpr ol)
  have laWeight := mul_nonneg op.le (sub_nonneg.mpr la)
  have size := mul_nonneg tp (sub_nonneg.mpr side)
  have strict := mul_pos op (show 0<2*(A.c+A.s)-1-A.loU by
    linarith only [cap,aSide])
  have margin := PositiveCentralPositiveLeftArc.central_axis_margin on an ln order wide small
  have margin' : O.c*(2*(A.c+A.s)-1)≤A.s*B O.c O.s+T := by
    dsimp [T,E,J,H,D,K]
    linarith only [margin]
  nlinarith only [supported,bottomWeight,olWeight,laWeight,size,strict,margin']

#print axioms vertex_bounds
#print axioms left_alternatives
#print axioms own_axis_impossible
#print axioms central_axis_impossible
end N12Compact.PositiveCentralPositiveLeft
