import Compact.Geometry.PositiveCentralCrossMargin
import Compact.Geometry.PositiveCentralPositiveBottom
import Compact.Geometry.FourSquareBLBridge
import Compact.Geometry.PositiveLeftOwnVBounds
import Compact.Geometry.PositiveCentralPositiveLeft

/-! The positive left singleton's own transverse separator. Original
container support removes its translation, and the shared two-angle
inequality excludes separation on the central square's U axis. -/
namespace N12Compact.PositiveLeftOwnV

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds PositiveCentralCrossMargin
open PositiveCentralPositiveLeftBounds
set_option Elab.async false

/-- An actual lower support for L's upper V face, together with the
additional bound supplied by L's strict corner. -/
theorem face_bounds (O L : OpenSquare)
    (on : Normal O.c O.s) (ln : Normal L.c L.s)
    (oSide : 1<O.side) (lSide : 1<L.side) (box : InsideContainer O)
    (cap : O.loU+O.side≤2*O.c+(457/500)*O.s)
    (corner : L.Inside 1 1)
    (sep : upper O (-L.s) L.c≤L.loV) :
    F O.c O.s L.c L.s<L.loV+L.side ∧
      F O.c O.s L.c L.s<1+L.c-L.s := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have op : 0<O.c := by linarith only [ob.1]
  have lp : 0<L.c := by linarith only [lb.1]
  have oq : 0≤O.s := on.1
  have lr : 0≤L.s := ln.1
  let H := O.s*L.c-O.c*L.s
  let K := O.c*L.c+O.s*L.s
  let M := max H 0
  have kp : 0<K := by dsimp [K]; positivity
  have mp : 0≤M := le_max_right H 0
  have form : upper O (-L.s) L.c=
      H*O.loU+K*O.loV+O.side*(K+M) := by
    rw [upper_in_bands]
    have u : -L.s*O.c+L.c*O.s=H := by dsimp [H]; ring
    have v : -(-L.s)*O.s+L.c*O.c=K := by dsimp [K]; ring
    rw [u,v,abs_of_nonneg kp.le]
    by_cases sign : 0≤H
    · rw [abs_of_nonneg sign]
      have m : M=H := max_eq_left sign
      rw [m]
      ring
    · have negative : H≤0 := le_of_lt (lt_of_not_ge sign)
      rw [abs_of_nonpos negative]
      have m : M=0 := max_eq_right negative
      rw [m]
      ring
  have bottom := ThreeSquare.bottom_wall O op.le box
  rw [abs_of_nonneg oq] at bottom
  dsimp [centerY] at bottom
  have wall : 0≤O.c*O.loV+O.s*O.loU := by nlinarith only [bottom]
  have definition : O.c*(F O.c O.s L.c L.s-1)=
      -L.s*(2*O.c+(457/500)*O.s)+L.s+O.c*(K+M) := by
    dsimp [F,K,M,H]
    field_simp [op.ne']
    <;> ring
  have identity : O.c*(upper O (-L.s) L.c-(F O.c O.s L.c L.s-1))=
      K*(O.c*O.loV+O.s*O.loU)+
      L.s*(2*O.c+(457/500)*O.s-(O.loU+O.side))+
      (O.side-1)*(L.s+O.c*(K+M)) := by
    rw [mul_sub,definition,form]
    dsimp [K,H]
    linear_combination (-L.s*O.loU)*on.2.2
  have first := mul_nonneg kp.le wall
  have second := mul_nonneg lr (sub_nonneg.mpr cap)
  have coefficient : 0<L.s+O.c*(K+M) := by positivity
  have strict := mul_pos (sub_pos.mpr oSide) coefficient
  have scaled : 0<O.c*(upper O (-L.s) L.c-(F O.c O.s L.c L.s-1)) := by
    linarith only [identity,first,second,strict]
  have gap := pos_of_mul_pos_right scaled op.le
  have cornerV := corner.2.2.1
  constructor <;> nlinarith only [gap,sep,lSide,cornerV]

private theorem lower_face {p q l r : ℝ} (on : Normal p q) (ln : Normal l r) :
    2*l-2*r≤F p q l r := by
  have lb := normal_bounds ln
  have lp : 0<l := by linarith only [lb.1]
  have diagonal := diagonal_minimum on ln
  have first := mul_nonneg lp.le (sub_nonneg.mpr lb.2.1)
  have second := mul_nonneg ln.1
    (show 0≤1-(457/500)*r by linarith only [lb.2.2.2.1])
  have identity : l*((2-2*r+r*(1-(457/500)*r)/l)-(2*l-2*r))=
      2*l*(1-l)+r*(1-(457/500)*r) := by
    field_simp [lp.ne']
    <;> ring
  have scaled : 0≤l*((2-2*r+r*(1-(457/500)*r)/l)-(2*l-2*r)) := by
    nlinarith only [identity,first,second]
  have gap := nonneg_of_mul_nonneg_right scaled lp
  linarith only [diagonal,gap]

/-- The central-angle functional reaches its worst value when the two
square angles agree. Both relative-angle orders are covered continuously. -/
theorem central_margin {p q C S l r : ℝ}
    (on : Normal p q) (an : Normal C S) (ln : Normal l r)
    (corner : F p q l r≤1+l-r) :
    l*(2*(C+S)-1)≤S*F p q l r+
      l*(C*l+S*r+max (C*r-S*l) 0) := by
  have ab := normal_bounds an
  have lb := normal_bounds ln
  have lp : 0<l := by linarith only [lb.1]
  have cp : 0<C := by linarith only [ab.1]
  have endpoint := margin on ln
  by_cases order : S≤r
  · have cosine := cosine_order ln an order
    have cross : 0≤C*r-S*l := by
      have first := mul_nonneg ln.1 (sub_nonneg.mpr cosine)
      have second := mul_nonneg lp.le (sub_nonneg.mpr order)
      nlinarith only [first,second]
    rw [max_eq_left cross]
    let a := l*(2-l-r)
    let b := l*(2+l-r)-F p q l r
    have ap : 0≤a := by
      dsimp [a]
      exact mul_nonneg lp.le (by linarith only [lb.2.2.2.2.2])
    have slope : a*r≤b*l := by
      have first := mul_nonneg lp.le (sub_nonneg.mpr corner)
      have second := mul_nonneg lp.le (sub_nonneg.mpr ln.2.1)
      have identity : a*r-b*l=l*(F p q l r+2*r-2*l-1) := by
        dsimp [a,b]
        linear_combination (-l)*ln.2.2
      nlinarith only [first,second,identity]
    have arc := linear_arc_max ln an order ap slope
    have difference :
        S*F p q l r+l*(C*l+S*r+(C*r-S*l))-l*(2*(C+S)-1)=
          l-a*C-b*S := by dsimp [a,b]; ring
    have endpointIdentity : l-a*l-b*r=r*F p q l r-2*l*(l+r-1) := by
      dsimp [a,b]
      linear_combination l*ln.2.2
    nlinarith only [arc,difference,endpointIdentity,endpoint]
  · have order' : r≤S := le_of_lt (lt_of_not_ge order)
    have cosine := cosine_order an ln order'
    have cross : C*r-S*l≤0 := by
      have first := mul_nonneg ln.1 (sub_nonneg.mpr cosine)
      have second := mul_nonneg lp.le (sub_nonneg.mpr order')
      nlinarith only [first,second]
    rw [max_eq_right cross]
    let a := l*(2-l)
    let b := 2*l-l*r-F p q l r
    have ap : 0≤a := by
      dsimp [a]
      exact mul_nonneg lp.le (by linarith only [lb.2.1])
    have slope : 0≤a*r-b*l := by
      have bound := lower_face on ln
      have weighted := mul_nonneg lp.le (sub_nonneg.mpr bound)
      dsimp [a,b]
      nlinarith only [weighted]
    have first := mul_nonneg ap (sub_nonneg.mpr (dot_le_one ln an))
    have second := mul_nonneg slope (sub_nonneg.mpr order')
    have chord : l*((a*l+b*r)-(a*C+b*S))=
        a*(1-l*C-r*S)+(a*r-b*l)*(S-r) := by
      linear_combination a*ln.2.2
    have scaled : 0≤l*((a*l+b*r)-(a*C+b*S)) := by
      linarith only [chord,first,second]
    have arc := nonneg_of_mul_nonneg_right scaled lp
    have difference :
        S*F p q l r+l*(C*l+S*r+0)-l*(2*(C+S)-1)=
          l-a*C-b*S := by dsimp [a,b]; ring
    have endpointIdentity : l-a*l-b*r=r*F p q l r-2*l*(l+r-1) := by
      dsimp [a,b]
      linear_combination l*ln.2.2
    nlinarith only [arc,difference,endpointIdentity,endpoint]

/-- The L-axis singleton separator cannot be followed by an A-axis
left/central separator. This is a complete support-selector combination,
not a surrogate point constraint. -/
theorem central_axis_impossible (O L A : OpenSquare)
    (on : Normal O.c O.s) (ln : Normal L.c L.s) (an : Normal A.c A.s)
    (sameOL : O.side=L.side) (sameLA : L.side=A.side) (side : 1<A.side)
    (oBox : InsideContainer O) (lBox : InsideContainer L)
    (oCap : O.loU+O.side≤2*O.c+(457/500)*O.s)
    (corner : L.Inside 1 1) (cap : A.loU+A.side≤2*(A.c+A.s))
    (ol : upper O (-L.s) L.c≤L.loV) : ¬upper L A.c A.s≤A.loU := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have ab := normal_bounds an
  have lp : 0<L.c := by linarith only [lb.1]
  have cp : 0<A.c := by linarith only [ab.1]
  have lr : 0≤L.s := ln.1
  have aq : 0≤A.s := an.1
  have lSide : 1<L.side := by rwa [sameLA]
  have oSide : 1<O.side := by rwa [sameOL]
  have faces := face_bounds O L on ln oSide lSide oBox oCap corner ol
  let K := A.c*L.c+A.s*L.s
  let H := A.s*L.c-A.c*L.s
  let Z := max (-H) 0
  have kp : 0≤K := by dsimp [K]; positivity
  have zp : 0≤Z := le_max_right (-H) 0
  have form : upper L A.c A.s=
      K*(L.loU+L.side)+H*(L.loV+L.side)+Z*L.side := by
    rw [upper_in_bands]
    have u : A.c*L.c+A.s*L.s=K := rfl
    have v : -A.c*L.s+A.s*L.c=H := by dsimp [H]; ring
    rw [u,v,abs_of_nonneg kp]
    by_cases sign : 0≤H
    · rw [abs_of_nonneg sign]
      have z : Z=0 := max_eq_right (neg_nonpos.mpr sign)
      rw [z]
      ring
    · have negative : H≤0 := le_of_lt (lt_of_not_ge sign)
      rw [abs_of_nonpos negative]
      have z : Z=-H := max_eq_left (neg_nonneg.mpr negative)
      rw [z]
      ring
  have wall := FourSquareBLBridge.left_wall L lp.le lBox
  rw [abs_of_nonneg lr] at wall
  dsimp [centerX] at wall
  have position : 0≤L.c*L.loU-L.s*(L.loV+L.side) := by nlinarith only [wall]
  have identity : L.c*upper L A.c A.s-A.s*(L.loV+L.side)-
      L.side*L.c*(K+Z)=K*(L.c*L.loU-L.s*(L.loV+L.side)) := by
    rw [form]
    dsimp [H,K]
    linear_combination A.s*(L.loV+L.side)*ln.2.2
  have first := mul_nonneg kp position
  have second := mul_nonneg aq (sub_nonneg.mpr faces.1.le)
  have third := mul_nonneg (mul_nonneg lp.le (add_nonneg kp zp))
    (sub_nonneg.mpr lSide.le)
  have transfer : A.s*F O.c O.s L.c L.s+L.c*(K+Z)≤L.c*upper L A.c A.s := by
    nlinarith only [identity,first,second,third]
  have scalar := central_margin on an ln faces.2.le
  have z : Z=max (A.c*L.s-A.s*L.c) 0 := by
    dsimp [Z,H]
    congr 1
    ring
  rw [←z] at scalar
  change L.c*(2*(A.c+A.s)-1)≤A.s*F O.c O.s L.c L.s+L.c*(K+Z) at scalar
  have upper : A.loU<2*(A.c+A.s)-1 := by linarith only [cap,side]
  have strict := mul_pos lp (sub_pos.mpr upper)
  intro separated
  have last := mul_nonneg lp.le (sub_nonneg.mpr separated)
  nlinarith only [transfer,scalar,strict,last]

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
  exact ⟨le_rfl,by linarith only [A.side_pos],
    by linarith only [A.side_pos],le_rfl⟩

/-- The remaining L-V / L-U selector pair is impossible. When A's
tilt is smaller, its lower-left corner suffices. In the other angle order,
the genuine upper-left vertex and the shared endpoint margin apply. -/
theorem own_axis_impossible (O L A : OpenSquare)
    (on : Normal O.c O.s) (ln : Normal L.c L.s) (an : Normal A.c A.s)
    (oSide : 1<O.side) (lSide : 1<L.side) (aSide : 1<A.side)
    (oBox : InsideContainer O) (lBox : InsideContainer L)
    (oCap : O.loU+O.side≤2*O.c+(457/500)*O.s)
    (corner : L.Inside 1 1)
    (order : O.s≤A.s) (shallow : 9/10≤O.c)
    (wide : 4/5≤A.c) (small : A.s≤3/5)
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (west : A.loV+A.side≤2*A.c-A.s)
    (floor : 1+(A.c+A.s)*(1-2*A.s)+A.c*(1-O.c)<A.c*(A.loV+A.side))
    (ol : upper O (-L.s) L.c≤L.loV) :
    ¬L.loU+L.side≤lower A L.c L.s := by
  have lb := normal_bounds ln
  have ab := normal_bounds an
  have lp : 0<L.c := by linarith only [lb.1]
  have cp : 0<A.c := by linarith only [ab.1]
  have lr : 0≤L.s := ln.1
  have aq : 0≤A.s := an.1
  have faces := face_bounds O L on ln oSide lSide oBox oCap corner ol
  have wall := FourSquareBLBridge.left_wall L lp.le lBox
  rw [abs_of_nonneg lr] at wall
  dsimp [centerX] at wall
  have position : 0≤L.c*L.loU-L.s*(L.loV+L.side) := by
    nlinarith only [wall]
  have faceWeight := mul_nonneg lr (sub_nonneg.mpr faces.1.le)
  have size := mul_pos lp (sub_pos.mpr lSide)
  have high : L.c+L.s*F O.c O.s L.c L.s<L.c*(L.loU+L.side) := by
    nlinarith only [position,faceWeight,size]
  intro la
  rcases le_total A.s L.s with smaller | larger
  · have cosine : L.c≤A.c := cosine_order ln an smaller
    let K := A.c*L.c+A.s*L.s
    let H := A.c*L.s-A.s*L.c
    have kp : 0≤K := by dsimp [K]; positivity
    have hp : 0≤H := by
      have first := mul_nonneg lr (sub_nonneg.mpr cosine)
      have second := mul_nonneg lp.le (sub_nonneg.mpr smaller)
      dsimp [H]
      nlinarith only [first,second]
    have form : lower A L.c L.s=K*A.loU+H*A.loV := by
      rw [lower_in_bands]
      have u : L.c*A.c+L.s*A.s=K := by dsimp [K]; ring
      have v : -L.c*A.s+L.s*A.c=H := by dsimp [H]; ring
      rw [u,v,abs_of_nonneg kp,abs_of_nonneg hp]
      ring
    have chord : (L.c+A.c)*(K+(1-A.s)*H-1)=
        H*((L.c+A.c-1)*(1-A.s)+(1-L.s)) := by
      dsimp [K,H]
      linear_combination A.c*ln.2.2+L.c*an.2.2
    have bracket : 0≤(L.c+A.c-1)*(1-A.s)+(1-L.s) := by
      have first := mul_nonneg
        (show 0≤L.c+A.c-1 by linarith only [lb.1,ab.1])
        (sub_nonneg.mpr ab.2.2.2.1)
      linarith only [first,lb.2.2.2.1]
    have scaled : 0≤(L.c+A.c)*(K+(1-A.s)*H-1) := by
      rw [chord]
      exact mul_nonneg hp bracket
    have angle := nonneg_of_mul_nonneg_right scaled (add_pos lp cp)
    have first := mul_nonneg kp (sub_nonneg.mpr cap)
    have second := mul_nonneg hp (sub_nonneg.mpr west)
    have third := mul_nonneg (add_nonneg kp hp) (sub_nonneg.mpr aSide.le)
    have identity : K*(2*(A.c+A.s)-A.side)+H*(2*A.c-A.s-A.side)=
        2*(L.c+L.s)+A.s*H-A.side*(K+H) := by
      dsimp [K,H]
      linear_combination (2*(L.c+L.s))*an.2.2
    have low : lower A L.c L.s≤2*(L.c+L.s)-1 := by
      nlinarith only [form,first,second,third,identity,angle]
    have scalar := margin on ln
    have last := mul_nonneg lp.le (sub_nonneg.mpr (le_trans la low))
    nlinarith only [high,scalar,last]
  · have vertex := PositiveCentralPositiveLeft.vertex_bounds A O.c an aSide cap west floor
    have bound := (closed_bounds A _ _ L.c L.s (vertex_closed A)).1
    have first := mul_pos (mul_pos lp lp) (sub_pos.mpr vertex.1)
    have second := mul_nonneg (mul_nonneg lp.le lr) (sub_nonneg.mpr vertex.2)
    have weighted := mul_nonneg lp.le (sub_nonneg.mpr bound)
    have scalar := PositiveLeftOwnVBounds.vertex_margin on an ln order larger shallow wide small
    have last := mul_nonneg lp.le (sub_nonneg.mpr la)
    nlinarith only [high,first,second,weighted,scalar,last]

#print axioms central_axis_impossible
#print axioms own_axis_impossible
end N12Compact.PositiveLeftOwnV
