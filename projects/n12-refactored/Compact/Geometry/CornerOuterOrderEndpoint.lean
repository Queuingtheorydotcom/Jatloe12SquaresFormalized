import Compact.Geometry.C977CornerSectorBounds

/-! Exact endpoint of the actual bottom-to-wall angle comparison.
The rational expression factors into two elementary unit-circle defects;
there is no angle subdivision or numerical inequality certificate. -/
namespace N12Compact.CornerOuterOrderEndpoint
open C977CornerCubic
set_option Elab.async false

/-- On the canonical quarter arc the cosine defect is at most half the
sine. The proof also includes the horizontal endpoint. -/
theorem half_chord {d t : ℝ} (normal : Normal d t) : 1-d≤t/2 := by
  have b := normal_bounds normal
  have factor : 0≤(1+d)/2-t := by linarith only [normal.2.1,b.2.1]
  have product := mul_nonneg normal.1 factor
  have identity : (1+d)*(t/2-(1-d))=t*((1+d)/2-t) := by
    linear_combination normal.2.2
  have scaled : 0≤(1+d)*(t/2-(1-d)) := by linarith only [identity,product]
  have gap := nonneg_of_mul_nonneg_right scaled
    (show 0<1+d by linarith only [b.1])
  linarith only [gap]

/-- The response at equal bottom and wall angles is nonpositive. The
coefficient 72/25 in the actual wall bound supplies an additional positive
margin outside this endpoint lemma. -/
theorem endpoint {d t : ℝ} (normal : Normal d t) :
    (2*(d^2-t^2)-(d+t)*(1-2*t+t*(1-t)/d))*(d+t)+
      t-(d^2-t^2)-2*d*t≤0 := by
  have b := normal_bounds normal
  have hd : 0<d := by linarith only [b.1]
  have chord := half_chord normal
  have coefficient : 1/2≤d^2+(1-d)^2 := by nlinarith only [sq_nonneg (d-1/2)]
  have weighted := mul_nonneg normal.1 (sub_nonneg.mpr coefficient)
  have bracket : 0≤t*(d^2+(1-d)^2)-(1-d) := by
    nlinarith only [weighted,chord]
  have product := mul_nonneg (sub_nonneg.mpr b.2.1) bracket
  have identity :
      d*((2*(d^2-t^2)-(d+t)*(1-2*t+t*(1-t)/d))*(d+t)+
        t-(d^2-t^2)-2*d*t)=
        (1-d)*((1-d)-t*(d^2+(1-d)^2)) := by
    calc
      _ = (1-d)*((1-d)-t*(d^2+(1-d)^2))+
          (2*d^2+2*d*t-2*d+t^2-t+1)*(d^2+t^2-1) := by
        field_simp [ne_of_gt hd]
        <;> ring
      _ = _ := by rw [normal.2.2]; ring
  have scaled : d*((2*(d^2-t^2)-(d+t)*(1-2*t+t*(1-t)/d))*(d+t)+
      t-(d^2-t^2)-2*d*t)≤0 := by nlinarith only [identity,product]
  exact nonpos_of_mul_nonpos_right scaled hd

#print axioms endpoint
end N12Compact.CornerOuterOrderEndpoint
