import Compact.Geometry.CentralNegativeFarUpper

/-! A negative central incoming support reduces to the horizontal test
in the only difficult farther-point range. This reuses the complete
negative-wall coupling instead of introducing new mixed-axis cases. -/
namespace N12Compact.CentralNegativeFarIncoming

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem horizontal_nonpos {c t : ℝ} (bn : Normal c t) (small : t≤63/100) :
    43/50-c-t+(7/50)*t^2+c*t≤0 := by
  have b := normal_bounds bn
  have square := mul_self_le_mul_self bn.1 small
  have wide : 77/100≤c := by nlinarith only [square,bn.2.2,b.1]
  have floor : 6031/10000≤c^2 := by nlinarith only [square,bn.2.2]
  have product := mul_nonneg bn.1 (sub_nonneg.mpr small)
  have factor : 0≤63/100+t-(63/100)^2-(63/100)*t-t^2 := by
    nlinarith only [product,small]
  have chord := mul_nonneg (sub_nonneg.mpr small) factor
  have cubic : t^2*(1-t)≤146853/1000000 := by nlinarith only [chord]
  have first := mul_nonneg (sub_nonneg.mpr floor)
    (show 0≤1+c by linarith only [b.1])
  have last := mul_nonneg (show 0≤6031/10000 by norm_num) (sub_nonneg.mpr wide)
  have identity : (1+c)*(43/50-c-t+(7/50)*t^2+c*t)=
      t^2*(1-t)-(7/50)*c^2*(1+c) := by
    linear_combination (t-1+(7/50)*(1+c))*bn.2.2
  have scaled : (1+c)*(43/50-c-t+(7/50)*t^2+c*t)≤0 := by
    nlinarith only [identity,cubic,first,last]
  exact nonpos_of_mul_nonpos_right scaled (by linarith only [b.1])

private theorem parallel_short {c t : ℝ} (bn : Normal c t) :
    (43/50)*c+t/2≤1 := by
  nlinarith only [bn.2.2,sq_nonneg (c-43/50),sq_nonneg (t-1/2)]

private theorem last_margin {C S c t : ℝ} (an : Normal C S) (bn : Normal c t)
    (order : C*t-S*c≤0) :
    C*(43/50-c-(51/100)*t^2+(13/20)*c*t)-
      S*(3/20-(13/20)*t^2-(51/100)*c*t+t)≤0 := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have arcProduct := mul_nonneg (sub_nonneg.mpr bb.2.2.2.2.1)
    (sub_nonneg.mpr bb.2.2.2.2.2)
  have ct := mul_nonneg (show 0≤c by linarith only [bb.1]) bn.1
  have arc : 1+(41/50)*c*t≤c+t := by nlinarith only [arcProduct,bn.2.2,ct]
  have ordered := mul_nonneg (sub_nonneg.mpr bn.2.1)
    (show 0≤c+t by linarith only [bb.1,bn.1])
  have square : t^2≤1/2 := by nlinarith only [ordered,bn.2.2]
  have mixed : c*t≤1/2 := by nlinarith only [bn.2.2,sq_nonneg (c-t)]
  let X := 43/50-c-(51/100)*t^2+(13/20)*c*t
  let Y := 3/20-(13/20)*t^2-(51/100)*c*t+t
  have parallel : c*X-t*Y=(43/50)*c+t/2-1 := by
    dsimp [X,Y]
    linear_combination ((13/20)*t-1)*bn.2.2
  have short := parallel_short bn
  have diagonal : X-Y≤0 := by dsimp [X,Y]; nlinarith only [arc,square,mixed]
  by_cases equal : c=t
  · have same : C=S := by nlinarith only [order,equal,an.2.1,bb.1]
    have product := mul_nonneg (show 0≤C by linarith only [ab.1])
      (neg_nonneg.mpr diagonal)
    change C*X-S*Y≤0
    nlinarith only [same,product]
  · have positive : 0<c-t := by linarith only [bn.2.1,equal]
    have first := mul_nonneg (sub_nonneg.mpr an.2.1) (sub_nonneg.mpr short)
    have last := mul_nonneg (show 0≤S*c-C*t by linarith only [order])
      (neg_nonneg.mpr diagonal)
    have scaledParallel := congrArg (fun z : ℝ => (C-S)*z) parallel
    have identity : (c-t)*(C*X-S*Y)=
        (C-S)*(c*X-t*Y)+(S*c-C*t)*(X-Y) := by ring
    have scaled : (c-t)*(C*X-S*Y)≤0 := by
      nlinarith only [first,last,scaledParallel,identity]
    exact nonpos_of_mul_nonpos_right scaled positive

/-- The existing actual 2.6 lower-face bound raises B's lower-left
vertex above the central lower crosspoint in the only possible range.
The negative incoming direction therefore forces horizontal incoming. -/
theorem horizontal (B : OpenSquare) (t : ℝ) {C S : ℝ}
    (an : Normal C S) (bn : Normal B.c t) (signed : B.s=-t)
    (side : 1≤B.side) (marker : B.Inside (47/20) (33/20))
    (capU : B.loU+B.side≤(143/50)*B.c-t)
    (capV : B.loV+B.side≤2*B.c+3*t)
    (floor : B.c+(13/5)*t≤B.loV)
    (incoming : 2*C-(3/2)*S<lower B C (-S)) : 2<lower B 1 0 := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have cp : 0<C := by linarith only [ab.1]
  let K := C*B.c+S*t
  let H := C*t-S*B.c
  have kp : 0≤K := by
    dsimp [K]
    exact add_nonneg (mul_nonneg cp.le (by linarith only [bb.1])) (mul_nonneg an.1 bn.1)
  by_cases positive : 0≤H
  · have formula : lower B C (-S)=K*B.loU+H*B.loV := by
      rw [lower_in_bands,signed]
      have u : C*B.c+(-S)*(-t)=K := by dsimp [K]; ring
      have v : -C*(-t)+(-S)*B.c=H := by dsimp [H]; ring
      rw [u,v,abs_of_nonneg kp,abs_of_nonneg positive]; ring
    let X := 43/50-B.c-t+(7/50)*t^2+B.c*t
    let Y := 1/2-t^2+(7/50)*B.c*t+t-B.c
    have first := mul_nonneg kp (sub_nonneg.mpr capU)
    have last := mul_nonneg positive (sub_nonneg.mpr capV)
    have width := mul_nonneg (add_nonneg kp positive) (sub_nonneg.mpr side)
    have identity : K*((143/50)*B.c-t-1)+H*(2*B.c+3*t-1)-(2*C-(3/2)*S)=C*X-S*Y := by
      dsimp [K,H,X,Y]
      linear_combination ((143/50)*C-2*S)*bn.2.2
    have excess : 0<C*X-S*Y := by nlinarith only [formula,first,last,width,identity,incoming]
    have steep : 63/100<t := by
      by_contra no
      have horizontal : X≤0 := horizontal_nonpos bn (le_of_not_gt no)
      have parallel : B.c*X-t*Y=(43/50)*B.c+t/2-1 := by
        dsimp [X,Y]
        linear_combination (t-1)*bn.2.2
      have short := parallel_short bn
      by_cases tilt : 0<t
      · have first := mul_nonneg positive (neg_nonneg.mpr horizontal)
        have last := mul_nonneg an.1 (sub_nonneg.mpr short)
        have scaledParallel := congrArg (fun z : ℝ => S*z) parallel
        have identity : t*(C*X-S*Y)=H*X+S*(B.c*X-t*Y) := by dsimp [H]; ring
        have strict := mul_pos tilt excess
        nlinarith only [first,last,scaledParallel,identity,strict]
      · have zero : t=0 := by linarith only [tilt,bn.1]
        have order : 0≤C*t-S*B.c := positive
        rw [zero] at order
        have sine : S=0 := by nlinarith only [order,an.1,bb.1]
        have product := mul_nonneg cp.le (neg_nonneg.mpr horizontal)
        nlinarith only [excess,sine,product]
    have yBound : 3/2< -t*B.loU+B.c*B.loV := by
      have first := mul_nonneg bn.1 (sub_nonneg.mpr capU)
      have last := mul_nonneg (show 0≤B.c by linarith only [bb.1]) (sub_nonneg.mpr floor)
      have width := mul_nonneg bn.1 (sub_nonneg.mpr side)
      have mixed : B.c*t≤1/2 := by nlinarith only [bn.2.2,sq_nonneg (B.c-t)]
      nlinarith only [first,last,width,bn.2.2,mixed,steep]
    have yWeight := mul_nonneg an.1 (sub_nonneg.mpr yBound.le)
    have horizontalFormula : lower B 1 0=B.c*B.loU+t*B.loV := by
      rw [lower_in_bands,signed]
      have u : 1*B.c+0*(-t)=B.c := by ring
      have v : -1*(-t)+0*B.c=t := by ring
      rw [u,v,abs_of_nonneg (show 0≤B.c by linarith only [bb.1]),abs_of_nonneg bn.1]
      ring
    have projection : K*B.loU+H*B.loV=
        C*(B.c*B.loU+t*B.loV)-S*(-t*B.loU+B.c*B.loV) := by dsimp [K,H]; ring
    have scaled : 0<C*(lower B 1 0-2) := by
      nlinarith only [incoming,formula,projection,yWeight,horizontalFormula]
    have gap := pos_of_mul_pos_right scaled cp.le
    linarith only [gap]
  · have negative : H≤0 := le_of_lt (lt_of_not_ge positive)
    have formula : lower B C (-S)=K*B.loU+H*(B.loV+B.side) := by
      rw [lower_in_bands,signed]
      have u : C*B.c+(-S)*(-t)=K := by dsimp [K]; ring
      have v : -C*(-t)+(-S)*B.c=H := by dsimp [H]; ring
      rw [u,v,abs_of_nonneg kp,abs_of_nonpos negative]; ring
    have marked := (negative_bands B t _ _ signed).mp marker
    have first := mul_nonneg kp (sub_nonneg.mpr capU)
    have last := mul_nonneg (neg_nonneg.mpr negative)
      (show 0≤B.loV+B.side-((33/20)*B.c+(47/20)*t) by linarith only [marked.2.2.2])
    have width := mul_nonneg kp (sub_nonneg.mpr side)
    have identity : K*((143/50)*B.c-t-1)+H*((33/20)*B.c+(47/20)*t)-(2*C-(3/2)*S)=
        C*(43/50-B.c-(51/100)*t^2+(13/20)*B.c*t)-
          S*(3/20-(13/20)*t^2-(51/100)*B.c*t+t) := by
      dsimp [K,H]
      linear_combination ((143/50)*C-(33/20)*S)*bn.2.2
    have margin := last_margin an bn negative
    exfalso
    nlinarith only [formula,first,last,width,identity,margin,incoming]

theorem impossible (D B : OpenSquare) (r t : ℝ) {C S : ℝ}
    (an : Normal C S) (bn : Normal B.c t) (dn : Normal D.c r)
    (bs : B.s=-t) (ds : D.s=-r) (side : 1≤B.side)
    (marker : B.Inside (47/20) (33/20)) (far : D.Inside (143/50) 1)
    (capU : B.loU+B.side≤(143/50)*B.c-t)
    (capV : B.loV+B.side≤2*B.c+3*t) (floor : B.c+(13/5)*t≤B.loV)
    (incoming : 2*C-(3/2)*S<lower B C (-S))
    (separation : upper D t B.c≤B.loV ∨ D.loV+D.side≤lower B r D.c) : False := by
  have point := horizontal B t an bn bs side marker capU capV floor incoming
  exact CentralNegativeFarUpper.impossible D B r t (C := 1) (S := 0)
    (by norm_num [Normal]) bn dn bs ds side far capU capV
    (by simpa using point) separation

#print axioms horizontal
#print axioms impossible
end N12Compact.CentralNegativeFarIncoming
