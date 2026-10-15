import Compact.Completion.C1092.MPPMAllNonpositiveAlternatingScalars
import Compact.Completion.C1092.MPPMInwardFinalScalars
import Compact.Geometry.C977CornerSectorBounds

/-! Exact whole-arc comparisons shared by the missing-center and
center-owned outer-owned inward far endings. No angular derivatives
or subdivisions are needed. -/
namespace N12Compact.C1092MPPMInwardOuterFar
open C977CornerCubic C977CornerSectorBounds C1092WallProfileScalars
set_option Elab.async false
noncomputable section

def alpha (c s : ℝ) : ℝ := 1-c+(13/50)*s
def centralGap (c s d t : ℝ) : ℝ :=
  alpha c s+(c*d+s*t)*(1-d-t)+(c*t-s*d)*(1-t+(14/25)*d)
def recipientGap (eta c s d t : ℝ) : ℝ :=
  1-d-t+(c*d+s*t)*alpha c s+(1-eta)*(c*t-s*d)

theorem cap_coordinates {c s m : ℝ} (cn : Normal c s)
    (mn : 0≤m) (mu : m≤1) (cap : half c s≤m) :
    1-m^2≤(1+m^2)*c ∧ (1+m^2)*s≤2*m := by
  have cb := normal_bounds cn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  let x := half c s
  have den : 0<1+x^2 := by positivity
  have square := mul_nonneg (sub_nonneg.mpr cap) (show 0≤m+x by linarith only [mn,data.1])
  have cosine : (1+x^2)*((1+m^2)*c-(1-m^2))=2*(m^2-x^2) := by
    linear_combination (1+m^2)*data.2.2.2.1
  have cosineNonnegative : 0≤(1+x^2)*((1+m^2)*c-(1-m^2)) := by
    rw [cosine]
    nlinarith only [square]
  have first := nonneg_of_mul_nonneg_right cosineNonnegative den
  have product := mul_nonneg mn (show 0≤1-x by linarith only [data.2.1])
  have last := mul_nonneg (sub_nonneg.mpr cap)
    (show 0≤1-m*x by nlinarith only [product,mu])
  have sine : (1+x^2)*(2*m-(1+m^2)*s)=2*(m-x)*(1-m*x) := by
    linear_combination -(1+m^2)*data.2.2.2.2
  have sineNonnegative : 0≤(1+x^2)*(2*m-(1+m^2)*s) := by
    rw [sine]
    nlinarith only [last]
  have second := nonneg_of_mul_nonneg_right sineNonnegative den
  exact ⟨by linarith only [first],by linarith only [second]⟩

theorem far_coordinates {d t : ℝ} (en : Normal d t) (far : 7/18<half d t) :
    252/373<t ∧ d<275/373 := by
  have eb := normal_bounds en
  have data := quarter_data d t (by linarith only [eb.1]) en.1 en.2.2
  let z := half d t
  have den : 0<1+z^2 := by positivity
  have square := mul_pos (show 0<z-7/18 by exact sub_pos.mpr far)
    (show 0<z+7/18 by linarith only [data.1])
  have cosine : d<275/373 := by
    apply lt_of_not_ge
    intro high
    have bad := mul_nonneg den.le (show 0≤d-275/373 by linarith only [high])
    nlinarith only [bad,square,data.2.2.2.1]
  have sine : 252/373<t := by
    have product := mul_pos (show 0<z-7/18 by exact sub_pos.mpr far)
      (show 0<1-(7/18)*z by linarith only [data.2.1])
    apply lt_of_not_ge
    intro low
    have bad := mul_nonneg den.le (show 0≤252/373-t by linarith only [low])
    nlinarith only [bad,product,data.2.2.2.2]
  exact ⟨sine,cosine⟩

/-- The coefficient bounds hold on the complete steep successor arc,
including the diagonal. Their finite algebra replaces both derivatives. -/
theorem central_positive {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (far : 7/18<half d t) : 0<centralGap c s d t := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have coordinates := far_coordinates en far
  have bounds := C1092MPPMAllNonpositive.missing_bounds en coordinates.1.le
  have cross : d*t≤1/2 := by nlinarith only [en.2.2,sq_nonneg (d-t)]
  have P : 2-d-t+(11/25)*d*t<81/100 := by
    linarith only [bounds.sum,cross]
  have chord := mul_nonneg (sub_nonneg.mpr en.2.1)
    (show 0≤d+t-141/100 by linarith only [bounds.sum])
  have Q : d-t+3/10+(11/25)*t^2<57/100 := by
    nlinarith only [chord,en.2.2,bounds.difference]
  have norm : (81/100)*c+(57/100)*s<1 := by
    apply lt_of_not_ge
    intro high
    have square := sq_nonneg ((57/100)*c-(81/100)*s)
    have positive := mul_nonneg
      (show 0≤(81/100)*c+(57/100)*s-1 by linarith only [high])
      (show 0≤(81/100)*c+(57/100)*s+1 by linarith only [cb.1,cn.1])
    nlinarith only [square,positive,cn.2.2]
  have first := mul_nonneg (show 0≤c by linarith only [cb.1]) (sub_nonneg.mpr P.le)
  have last := mul_nonneg cn.1 (sub_nonneg.mpr Q.le)
  have identity : centralGap c s d t=
      1-(2-d-t+(11/25)*d*t)*c-(d-t+3/10+(11/25)*t^2)*s := by
    dsimp [centralGap,alpha]
    linear_combination -(c+(14/25)*s)*en.2.2
  nlinarith only [first,last,norm,identity]

/-- A linear support decreases beyond the exact base angle. The second
coefficient may have either sign; only the endpoint derivative is used. -/
theorem recipient_order {d t A B : ℝ} (en : Normal d t)
    (large : 252/373≤t) (An : 0≤A) (slope : 0≤(252/373)*A-(275/373)*B) :
    A*d+B*t≤A*(275/373)+B*(252/373) := by
  have base : Normal (275/373 : ℝ) (252/373) := by norm_num [Normal]
  have dot := dot_le_one base en
  have first := mul_nonneg An (sub_nonneg.mpr dot)
  have last := mul_nonneg slope (sub_nonneg.mpr large)
  have identity : (275/373)*(A*(275/373)+B*(252/373)-(A*d+B*t))=
      A*(1-((275/373)*d+(252/373)*t))+
        ((252/373)*A-(275/373)*B)*(t-252/373) := by ring
  nlinarith only [first,last,identity]

end
end N12Compact.C1092MPPMInwardOuterFar
