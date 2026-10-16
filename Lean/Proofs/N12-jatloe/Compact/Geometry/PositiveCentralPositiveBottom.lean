import Compact.Geometry.C977NegativeCorner
import Compact.Geometry.C696PositiveCorner
import Compact.Geometry.PositiveCentralNegativeBottom
import Compact.Geometry.PositiveCentralTransverse
import Compact.Geometry.PositiveCentralLeftBand
import Compact.Geometry.C977CornerHalfAngle

/-! The positive-bottom counterpart of the left-point support reduction.
The actual bottom wall and original upper-U cap rule out separation on the
central square's transverse axis. Both continuous relative-angle sectors
are covered; the own-bottom transverse separator is not discarded. -/
namespace N12Compact.PositiveCentralPositiveBottom

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner C977CornerSectorBounds
set_option Elab.async false

private theorem endpoint {c s : ℝ} (hn : Normal c s) :
    0≤(1-c)*((543/500)*c+s-457/500) := by
  have b := normal_bounds hn
  exact mul_nonneg (show 0≤1-c by linarith only [b.2.1])
    (show 0≤(543/500)*c+s-457/500 by linarith only [b.1,b.2.2.2.2.1])

private theorem central_above {c s C S : ℝ}
    (hn : Normal c s) (h : Normal C S) (order : s*C-c*S≤0) :
    0≤c-c*(2-c)*C+(1-c+(c-457/500)*s)*S := by
  have b := normal_bounds hn
  have angles := C977CornerCubic.ordered_normals hn h
    (show 0≤c*S-s*C by linarith only [order])
  have fp : 0≤c*(2-c) := mul_nonneg (show 0≤c by linarith only [b.1])
    (show 0≤2-c by linarith only [b.2.1])
  have gp : 0≤1-c+(c-457/500)*s := by
    have product := mul_nonneg (show 0≤1-c by linarith only [b.2.1])
      (show 0≤1-s by linarith only [b.2.2.2.1])
    nlinarith only [product,hn.1]
  have first := mul_nonneg fp (sub_nonneg.mpr angles.1)
  have second := mul_nonneg gp (sub_nonneg.mpr angles.2)
  have atEndpoint : c-c*(2-c)*c+(1-c+(c-457/500)*s)*s =
      (1-c)*((543/500)*c+s-457/500) := by
    linear_combination (c-457/500)*hn.2.2
  nlinarith only [first,second,atEndpoint,endpoint hn]

private theorem central_below {c s C S : ℝ}
    (hn : Normal c s) (h : Normal C S) (order : 0≤s*C-c*S) :
    0≤c-c*(2-c-s)*C-(c-s*(c+s-457/500))*S := by
  have b := normal_bounds hn
  have B := normal_bounds h
  let F := c*(2-c-s)
  let G := c-s*(c+s-457/500)
  have atEndpoint : c-F*c-G*s =
      (1-c)*((543/500)*c+s-457/500) := by
    dsimp [F,G]
    linear_combination (c+s-457/500)*hn.2.2
  change 0≤c-F*C-G*S
  by_cases shallow : (543/500)*s≤c
  · have sp : S≤s := sine_order hn h
      (show c*S-s*C≤0 by linarith only [order])
    have fp : 0≤F := mul_nonneg (show 0≤c by linarith only [b.1])
      (show 0≤2-c-s by linarith only [b.2.2.2.2.2])
    have slope : F*s≤G*c := by
      have product := mul_nonneg (show 0≤c by linarith only [b.1])
        (sub_nonneg.mpr shallow)
      dsimp [F,G]
      nlinarith only [product]
    have maximum := linear_arc_max hn h sp fp slope
    clear_value F G
    linarith only [maximum,atEndpoint,endpoint hn]
  · have sum : (4/3:ℝ)≤c+s := by linarith only [shallow,b.1]
    have ratio : (9/10)*c≤s := by linarith only [shallow,b.1]
    have fBound : F≤(2/3)*c := by
      have product := mul_nonneg (show 0≤c by linarith only [b.1])
        (show 0≤c+s-4/3 by linarith only [sum])
      dsimp [F]
      nlinarith only [product]
    have gBound : G≤(2/3)*c := by
      have product := mul_nonneg hn.1
        (show 0≤c+s-457/500-2/5 by linarith only [sum])
      dsimp [G]
      nlinarith only [product,ratio,b.1]
    have first := mul_nonneg (show 0≤C by linarith only [B.1])
      (sub_nonneg.mpr fBound)
    have second := mul_nonneg h.1 (sub_nonneg.mpr gBound)
    have last := mul_nonneg (show 0≤c by linarith only [b.1])
      (show 0≤1-(2/3)*(C+S) by linarith only [B.2.2.2.2.2])
    clear_value F G
    nlinarith only [first,second,last]

/-- The true upper-U face bound comes from the absent original bottom
marker. Keeping it explicit avoids importing any saved enclosure. -/
theorem upper_axis (O : OpenSquare) (C S : ℝ)
    (hn : Normal O.c O.s) (h : Normal C S)
    (side : 1<O.side) (box : InsideContainer O)
    (cap : O.loU+O.side≤2*O.c+(457/500)*O.s) :
    2*C-S < upper O (-S) C+O.side := by
  have b := normal_bounds hn
  have B := normal_bounds h
  have hc : 0<O.c := by linarith only [b.1]
  let K := O.c*C+O.s*S
  let H := O.s*C-O.c*S
  have kp : 0≤K := add_nonneg
    (mul_nonneg hc.le (show 0≤C by linarith only [B.1]))
    (mul_nonneg hn.1 h.1)
  have bottom := ThreeSquare.bottom_wall O hc.le box
  rw [abs_of_nonneg hn.1] at bottom
  have wall : 0≤O.c*O.loV+O.s*O.loU := by
    dsimp [centerY] at bottom
    nlinarith only [bottom]
  have transfer (J : ℝ) (jp : 0≤J)
      (form : upper O (-S) C=H*O.loU+K*O.loV+(K+J)*O.side)
      (scalar : 0≤O.c*(K+J)+S+O.c-O.c*S-(457/500)*O.s*S-2*O.c*C) :
      2*C-S < upper O (-S) C+O.side := by
    let E := O.c*(K+J)+S+O.c
    have ep : 0<E := by
      have product := mul_nonneg hc.le (add_nonneg kp jp)
      dsimp [E]
      linarith only [product,h.1,hc]
    have strict := mul_pos ep (sub_pos.mpr side)
    have wallTerm := mul_nonneg kp wall
    have capTerm := mul_nonneg h.1 (sub_nonneg.mpr cap)
    have identity : O.c*(upper O (-S) C+O.side-(2*C-S)) =
        K*(O.c*O.loV+O.s*O.loU)+
        S*(2*O.c+(457/500)*O.s-(O.loU+O.side))+E*(O.side-1)+
        (O.c*(K+J)+S+O.c-O.c*S-(457/500)*O.s*S-2*O.c*C) := by
      rw [form]
      dsimp [E,K,H]
      linear_combination (-S*O.loU)*hn.2.2
    have positive : 0<O.c*(upper O (-S) C+O.side-(2*C-S)) := by
      clear_value E K H
      linarith only [identity,strict,wallTerm,capTerm,scalar]
    have difference := pos_of_mul_pos_right positive hc.le
    linarith only [difference]
  have u : -S*O.c+C*O.s=H := by dsimp [H]; ring
  have v : -(-S)*O.s+C*O.c=K := by dsimp [K]; ring
  by_cases sign : H≤0
  · apply transfer 0 (by norm_num)
    · rw [upper_in_bands,u,v,abs_of_nonpos sign,abs_of_nonneg kp]
      ring
    · have scalar := central_above hn h
        (show O.s*C-O.c*S≤0 by exact sign)
      dsimp [K]
      nlinarith only [scalar]
  · have hp : 0≤H := le_of_lt (lt_of_not_ge sign)
    apply transfer H hp
    · rw [upper_in_bands,u,v,abs_of_nonneg hp,abs_of_nonneg kp]
      ring
    · have scalar := central_below hn h
        (show 0≤O.s*C-O.c*S by exact hp)
      have identity :
          O.c*(K+H)+S+O.c-O.c*S-(457/500)*O.s*S-2*O.c*C =
          O.c-O.c*(2-O.c-O.s)*C-(O.c-O.s*(O.c+O.s-457/500))*S := by
        dsimp [K,H]
        linear_combination (-S)*hn.2.2
      rw [identity]
      exact scalar

theorem central_axis_impossible (O A : OpenSquare)
    (hn : Normal O.c O.s) (h : Normal A.c A.s)
    (same : O.side=A.side) (side : 1<A.side) (box : InsideContainer O)
    (capO : O.loU+O.side≤2*O.c+(457/500)*O.s)
    (capA : A.loV+A.side≤2*A.c-A.s) :
    ¬upper O (-A.s) A.c≤A.loV := by
  have bound := upper_axis O A.c A.s hn h
    (by rw [same]; exact side) box capO
  rw [same] at bound
  intro separator
  linarith only [bound,capA,separator]

/-- A reuse of the exact sine-coordinate chord inequality. It controls
the remaining bottom-axis support when the central tilt is no larger. -/
theorem own_axis_margin {c s C S : ℝ} (hn : Normal c s) (h : Normal C S)
    (positive : 0<s) (order : S≤s) :
    c*(2+(1/2)*C*S-C)+s*(-3/2+(1/2)*S^2-S)≤
      C696CornerMargins.boundary c s := by
  have b := normal_bounds hn
  have hc : 0<c := by linarith only [b.1]
  let R := c+s-(1/2)*c*s-(457/500)*s^2-2*c^2
  have zeroEndpoint : 0≤R+c^2 := by
    have radialProduct := mul_nonneg
      (show 0≤1-c by linarith only [b.2.1])
      (show 0≤(3/5)*c-2/5 by linarith only [b.1])
    have radial : 1-c≤(3/5)*s^2 := by
      nlinarith only [radialProduct,hn.2.2]
    have upper : s≤5/7 := by linarith only [hn.2.1,b.2.2.2.2.2]
    have squareBound := mul_nonneg hn.1 (sub_nonneg.mpr upper)
    have productBound := mul_nonneg hn.1
      (show 0≤1-c by linarith only [b.2.1])
    dsimp [R]
    nlinarith only [radial,squareBound,productBound,hn.1,hn.2.2]
  have sameEndpoint : 0≤R+c*(1-s/2) := by
    have identity : R+c*(1-s/2)=(1-c)*((543/500)*c+s-457/500) := by
      dsimp [R]
      linear_combination (-(457/500))*hn.2.2
    rw [identity]
    exact endpoint hn
  have chord := arc_chord hn h order (show 0≤(1/2:ℝ) by norm_num)
  have chordScaled := mul_nonneg hc.le
    (show 0≤s*((1-S/2)*(c*C+s*S))-((s-S)*c+S*(1-s/2)) by
      linarith only [chord])
  have first := mul_nonneg (sub_nonneg.mpr order) zeroEndpoint
  have second := mul_nonneg h.1 sameEndpoint
  have identity : s*(R+c*(c*C+s*S)*(1-S/2)) =
      (s-S)*(R+c^2)+S*(R+c*(1-s/2))+
      c*(s*((1-S/2)*(c*C+s*S))-((s-S)*c+S*(1-s/2))) := by ring
  have scaled : 0≤s*(R+c*(c*C+s*S)*(1-S/2)) := by
    clear_value R
    linarith only [identity,first,second,chordScaled]
  have unscaled := nonneg_of_mul_nonneg_right scaled positive
  have boundaryFormula : c*C696CornerMargins.boundary c s =
      c+s-2*c*s-(457/500)*s^2 := by
    unfold C696CornerMargins.boundary
    field_simp [hc.ne']
  have difference :
      c*(C696CornerMargins.boundary c s-
        (c*(2+(1/2)*C*S-C)+s*(-3/2+(1/2)*S^2-S))) =
      R+c*(c*C+s*S)*(1-S/2) := by
    rw [mul_sub,boundaryFormula]
    dsimp [R]
    ring
  have nonnegative : 0≤c*(C696CornerMargins.boundary c s-
      (c*(2+(1/2)*C*S-C)+s*(-3/2+(1/2)*S^2-S))) := by
    rw [difference]
    exact unscaled
  have result := nonneg_of_mul_nonneg_right nonnegative hc
  linarith only [result]

/-- If the positive bottom square still separates on its own axis under
the left-point escape, its canonical tilt is strictly below the central
tilt. This is a genuine geometric restriction, not a whole exclusion. -/
theorem own_axis_angle (O A : OpenSquare)
    (on : Normal O.c O.s) (an : Normal A.c A.s)
    (same : O.side=A.side) (side : 1<A.side) (box : InsideContainer O)
    (oM : O.Inside 1 (457/500)) (oN : O.Inside (28/25) 1)
    (missingCorner : ¬O.Inside 1 1) (missingMarker : ¬O.Inside 2 (457/500))
    (aWest : A.Inside (3/2) 2) (capA : A.loV+A.side≤2*A.c-A.s)
    (separator : O.loV+O.side≤lower A (-O.s) O.c) : O.s<A.s := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have faces := C696PositiveCorner.corner_faces O on
    (by rw [same]; exact side) box oM oN missingCorner missingMarker
  by_contra failure
  have order : A.s≤O.s := le_of_not_gt failure
  have cosine := cosine_order on an order
  let H := O.s*A.c-O.c*A.s
  let K := O.c*A.c+O.s*A.s
  have hp : 0≤H := by
    have first := mul_nonneg on.1 (sub_nonneg.mpr cosine)
    have second := mul_nonneg (show 0≤O.c by linarith only [ob.1])
      (sub_nonneg.mpr order)
    dsimp [H]
    nlinarith only [first,second]
  have kp : 0≤K := add_nonneg
    (mul_nonneg (show 0≤O.c by linarith only [ob.1])
      (show 0≤A.c by linarith only [ab.1]))
    (mul_nonneg on.1 an.1)
  have form : lower A (-O.s) O.c = -H*(A.loU+A.side)+K*A.loV := by
    have u : -O.s*A.c+O.c*A.s = -H := by dsimp [H]; ring
    have v : -(-O.s)*A.s+O.c*A.c = K := by dsimp [K]; ring
    rw [lower_in_bands,u,v,abs_of_nonpos (neg_nonpos.mpr hp),abs_of_nonneg kp]
    ring
  have first := mul_nonneg hp
    (show 0≤A.loU+A.side-((3/2)*A.c+2*A.s) by linarith only [aWest.2.1])
  have second := mul_nonneg kp (sub_nonneg.mpr capA)
  have width := mul_nonneg kp (sub_nonneg.mpr side.le)
  have identity : -H*((3/2)*A.c+2*A.s)+K*(2*A.c-A.s-1) =
      O.c*(2+(1/2)*A.c*A.s-A.c)+O.s*(-3/2+(1/2)*A.s^2-A.s) := by
    dsimp [H,K]
    linear_combination (2*O.c-(3/2)*O.s)*an.2.2
  have lowerBound : lower A (-O.s) O.c≤
      O.c*(2+(1/2)*A.c*A.s-A.c)+O.s*(-3/2+(1/2)*A.s^2-A.s) := by
    clear_value H K
    nlinarith only [form,first,second,width,identity]
  have scalar := own_axis_margin on an faces.1 order
  linarith only [separator,faces.2.2.2.2,lowerBound,scalar]

end N12Compact.PositiveCentralPositiveBottom

namespace N12Compact.PositiveCentralTransverse

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977CornerCubic

/-- Under the actual original bottom-square premises, failure of the left
point leaves only the bottom square's own transverse separator. This is
an exact reduction, not a claim that the point or the whole case is proved. -/
theorem only_bottom_axis (O A : OpenSquare)
    (oc : 0<O.c) (canonicalO : |O.s|≤O.c) (an : Normal A.c A.s)
    (same : O.side=A.side) (side : 1<A.side) (box : InsideContainer O)
    (oM : O.Inside 1 (457/500)) (oN : O.Inside (28/25) 1)
    (oF : O.Inside (187/100) (19/25))
    (missingCorner : ¬O.Inside 1 1) (missingMarker : ¬O.Inside 2 (457/500))
    (aP : A.Inside (33/20) (33/20)) (aD : A.Inside 2 (87/50))
    (aLeft : A.Inside (3/2) 2) (aLow : A.Inside 2 (3/2))
    (cap : A.loU+A.side≤2*(A.c+A.s)) (missingLeft : ¬A.Inside 1 2)
    (apart : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y)) :
    O.loV+O.side≤lower A (-O.s) O.c := by
  have ab := normal_bounds an
  have ac : 0<A.c := by linarith only [ab.1]
  have capV := PositiveCentralLeftBand.upper_face A side ac an.1 cap aP aLeft missingLeft
  rcases alternatives O A oc canonicalO an same side oN oF aP aD aLeft aLow cap apart with own | central
  · exact own
  · exfalso
    have signed := abs_le.mp canonicalO
    by_cases positive : 0≤O.s
    · have on : Normal O.c O.s := ⟨positive,signed.2,O.unit_normal⟩
      have faces := C696PositiveCorner.corner_faces O on
        (by rw [same]; exact side) box oM oN missingCorner missingMarker
      exact PositiveCentralPositiveBottom.central_axis_impossible O A on an same side
        box faces.2.2.1 capV central
    · have negative : O.s<0 := lt_of_not_ge positive
      have on : Normal O.c (-O.s) := by
        refine ⟨by linarith only [negative],by linarith only [signed.1],?_⟩
        nlinarith only [O.unit_normal]
      exact PositiveCentralNegativeBottom.central_axis_impossible O A (-O.s)
        (by ring) on an same side box oM capV central

end N12Compact.PositiveCentralTransverse
