import Compact.Geometry.CentralRightIncomingOrdered

/-! The remaining reversed order for two negative canonical central
frames is controlled by the actual lower crosspoint (2,1.5). The cone
endpoints are B's own normal and the negative diagonal. -/
namespace N12Compact.CentralNegativeIncoming

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem margin {C S c t : ℝ} (an : Normal C S) (bn : Normal c t)
    (order : C*t≤S*c) :
    C*((1-c)*(1+t))+S*(1/2-c-t-t^2)≤0 := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  let X := (1-c)*(1+t)
  let Y := 1/2-c-t-t^2
  have parallel : c*X+t*Y=c-1-t/2 := by
    dsimp [X,Y]
    linear_combination -(1+t)*bn.2.2
  have diagonal : X+Y=(1-c)^2-1/2-c*t := by
    dsimp [X,Y]
    linear_combination -bn.2.2
  have square := mul_nonneg (show 0≤1-c by linarith only [bb.2.1])
    (show 0≤c-7/10 by linarith only [bb.1])
  have product := mul_nonneg (show 0≤c by linarith only [bb.1]) bn.1
  have last : X+Y≤0 := by nlinarith only [diagonal,square,bb.1,bb.2.1,product]
  by_cases equal : c=t
  · have same : C=S := by nlinarith only [order,equal,an.2.1,bb.1]
    have weighted := mul_nonneg (show 0≤C by linarith only [ab.1])
      (neg_nonneg.mpr last)
    change C*X+S*Y≤0
    nlinarith only [weighted,same]
  · have positive : 0<c-t := by linarith only [bn.2.1,equal]
    have first := mul_nonneg (sub_nonneg.mpr an.2.1)
      (show 0≤1+t/2-c by linarith only [bb.2.1,bn.1])
    have second := mul_nonneg (sub_nonneg.mpr order) (neg_nonneg.mpr last)
    have identity : (c-t)*(C*X+S*Y)=
        (C-S)*(c*X+t*Y)+(S*c-C*t)*(X+Y) := by ring
    have scaledParallel := congrArg (fun z : ℝ => (C-S)*z) parallel
    have scaled : (c-t)*(C*X+S*Y)≤0 := by
      nlinarith only [identity,scaledParallel,first,second]
    exact nonpos_of_mul_nonpos_right scaled positive

/-- With the southeast lower-V escape and genuine inward upper-U cap,
B's complete lower support cannot lie beyond the lower crosspoint. -/
theorem lower_bound (B : OpenSquare) (t : ℝ) {C S : ℝ}
    (signed : B.s=-t) (an : Normal C S) (bn : Normal B.c t)
    (side : 1≤B.side) (order : C*t≤S*B.c)
    (floor : B.c+3*t≤B.loV) (cap : B.loU+B.side≤3*B.c-2*t) :
    lower B C (-S)≤2*C-(3/2)*S := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  let K := C*B.c+S*t
  let H := C*t-S*B.c
  have kp : 0≤K := by
    dsimp [K]
    exact add_nonneg (mul_nonneg (by linarith only [ab.1]) (by linarith only [bb.1]))
      (mul_nonneg an.1 bn.1)
  have hn : H≤0 := by dsimp [H]; linarith only [order]
  have formula : lower B C (-S)=K*B.loU+H*(B.loV+B.side) := by
    rw [lower_in_bands,signed]
    have u : C*B.c+(-S)*(-t)=K := by dsimp [K]; ring
    have v : -C*(-t)+(-S)*B.c=H := by dsimp [H]; ring
    rw [u,v,abs_of_nonneg kp,abs_of_nonpos hn]
    ring
  have first := mul_nonneg kp (sub_nonneg.mpr cap)
  have second := mul_nonneg (neg_nonneg.mpr hn) (sub_nonneg.mpr floor)
  have width := mul_nonneg (show 0≤K-H by linarith only [kp,hn]) (sub_nonneg.mpr side)
  have identity : K*(3*B.c-2*t-1)+H*(B.c+3*t+1)-(2*C-(3/2)*S)=
      C*((1-B.c)*(1+t))+S*(1/2-B.c-t-t^2) := by
    dsimp [K,H]
    linear_combination (3*C-S)*bn.2.2
  have bound := margin an bn order
  nlinarith only [formula,first,second,width,identity,bound]

#print axioms lower_bound
end N12Compact.CentralNegativeIncoming
