import Compact.Geometry.C977CornerSectorBounds

/-! Full-interval scalar margins for POSITIVE-BOUNDARY-ORIGIN §§4--5.
Exact circle-chord identities replace angular derivatives and concavity.
The positive-order margin has a four-product chord decomposition; the
negative-order margin uses the rational bound c+s<17/12. -/
namespace N12Compact.C1092MPPMPositiveBoundaryOrigin.Scalars
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false
noncomputable section

def endpoint (b r : ℝ) : ℝ := 2*b+r-2+r^2-b*r
def vMargin (c s b r : ℝ) : ℝ :=
  b+(c*b+s*r)*(b+r-2)+s*(r-b)+b*max (-(c*r-s*b)) 0
def plusPhi (c s b r : ℝ) : ℝ :=
  b*(c-s+s^2/2)+r*(c+s-1-c*s/2)
def minusPhi (c s b r : ℝ) : ℝ := b*(c+s-c*s)+r*(s-s^2-c)
def plusMargin (c s b r : ℝ) : ℝ := b+r-2+r^2+b*plusPhi c s b r
def minusMargin (c s b r : ℝ) : ℝ := b+r-2+r^2+b*minusPhi c s b r

private theorem sum_bounds {c s : ℝ} (cn : Normal c s) :
    1≤c+s ∧ c+s<17/12 := by
  have cb := normal_bounds cn
  refine ⟨cb.2.2.2.2.1,?_⟩
  apply lt_of_not_ge
  intro high
  have product := mul_nonneg (show 0≤c+s-17/12 by linarith only [high])
    (show 0≤c+s+17/12 by linarith only [cb.1,cn.1])
  nlinarith only [product,cn.2.2,sq_nonneg (c-s)]

theorem endpoint_positive {b r : ℝ} (bn : Normal b r) (rp : 0<r) :
    0<endpoint b r := by
  have bb := normal_bounds bn
  have bp : 0<b := by linarith only [bb.1]
  have sum : 1<b+r := by
    apply lt_of_not_ge
    intro low
    have product := mul_nonneg (show 0≤1-b-r by linarith only [low])
      (show 0≤1+b+r by linarith only [bp,rp])
    nlinarith only [product,bn.2.2,mul_pos bp rp]
  have identity : (1+b)*endpoint b r=r^2*(b+r-1) := by
    dsimp [endpoint]
    linear_combination (2-r)*bn.2.2
  have positive : 0<(1+b)*endpoint b r := by
    rw [identity]
    exact mul_pos (sq_pos_of_pos rp) (by linarith only [sum])
  exact pos_of_mul_pos_right positive (by linarith only [bp])

theorem v_positive {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (rp : 0<r) : 0<vMargin c s b r := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0<c := by linarith only [cb.1]
  have bp : 0<b := by linarith only [bb.1]
  have ending := endpoint_positive bn rp
  by_cases order : 0≤c*r-s*b
  · have sine : s≤r := sine_order bn cn (by nlinarith only [order])
    have cosine : b≤c := cosine_order bn cn sine
    let A := b*(2-b-r)
    let B := b-r*(b+r-1)
    have Ap : 0<A := by dsimp [A]; exact mul_pos bp (by linarith only [bb.2.2.2.2.2])
    have Bn : 0≤B := by
      have first := mul_nonneg bn.1 (show 0≤2-b-r by linarith only [bb.2.2.2.2.2])
      dsimp [B]
      nlinarith only [first,bn.2.1]
    have form : vMargin c s b r=b-A*c-B*s := by
      dsimp [vMargin]
      rw [max_eq_right (show -(c*r-s*b)≤0 by linarith only [order])]
      dsimp [A,B]
      ring
    have endpointForm : endpoint b r=b-A*b-B*r := by
      dsimp [endpoint,A,B]
      linear_combination (2-b-r)*bn.2.2
    have first := mul_nonneg Bn (show 0≤c-b by linarith only [cosine])
    have last := mul_nonneg Ap.le (show 0≤r-s by linarith only [sine])
    have diagonal := mul_nonneg bp.le (sub_nonneg.mpr bn.2.1)
    have base : 0≤B*(c+b)-A*(r+s) := by
      dsimp [A,B] at first last ⊢
      nlinarith only [first,last,diagonal]
    have product := mul_nonneg (sub_nonneg.mpr sine) base
    have identity : (c+b)*(vMargin c s b r-endpoint b r)=
        (r-s)*(B*(c+b)-A*(r+s)) := by
      rw [form,endpointForm]
      linear_combination -A*cn.2.2+A*bn.2.2
    have comparison : endpoint b r≤vMargin c s b r := by
      have gap := nonneg_of_mul_nonneg_right (show 0≤(c+b)*(vMargin c s b r-endpoint b r) by
        rw [identity]; exact product) (show 0<c+b by linarith only [cp,bp])
      linarith only [gap]
    exact ending.trans_le comparison
  · have order : c*r-s*b≤0 := (lt_of_not_ge order).le
    have sine : r≤s := sine_order cn bn order
    have cosine : c≤b := cosine_order cn bn sine
    let Q := 1+b*r-b-r
    have qn : 0≤Q := by
      have identity : 2*Q=(b+r-1)^2 := by dsimp [Q]; linear_combination -bn.2.2
      nlinarith only [identity,sq_nonneg (b+r-1)]
    have form : vMargin c s b r=b-b*(2-b)*c+Q*s := by
      dsimp [vMargin]
      rw [max_eq_left (show 0≤-(c*r-s*b) by linarith only [order])]
      dsimp [Q]
      linear_combination s*bn.2.2
    have endpointForm : endpoint b r=b-b*(2-b)*b+Q*r := by
      dsimp [endpoint,Q]
      linear_combination (2-b)*bn.2.2
    have first := mul_nonneg (mul_nonneg bp.le (show 0≤2-b by linarith only [bb.2.1]))
      (sub_nonneg.mpr cosine)
    have last := mul_nonneg qn (sub_nonneg.mpr sine)
    have comparison : endpoint b r≤vMargin c s b r := by
      rw [form,endpointForm]
      nlinarith only [first,last]
    exact ending.trans_le comparison

/-- In the positive relative order, four nonnegative products replace
the manuscript's concavity argument on the complete interval. -/
theorem plus_positive {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (rp : 0<r) (order : 0≤c*r-s*b) : 0<plusMargin c s b r := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0<c := by linarith only [cb.1]
  have bp : 0<b := by linarith only [bb.1]
  have sine : s≤r := sine_order bn cn (by nlinarith only [order])
  let J := (b-r)*(c+b)+b*(r+s)*(1-(c+b)/2)+
    r*(r+s)*(1-r/2)+(r*c/2)*(c+b)
  have j0 := mul_nonneg (sub_nonneg.mpr bn.2.1) (show 0≤c+b by linarith only [cp,bp])
  have j1 := mul_nonneg (mul_nonneg bp.le (add_nonneg bn.1 cn.1))
    (show 0≤1-(c+b)/2 by linarith only [cb.2.1,bb.2.1])
  have j2 := mul_nonneg (mul_nonneg bn.1 (add_nonneg bn.1 cn.1))
    (show 0≤1-r/2 by linarith only [bb.2.2.2.1])
  have j3 := mul_nonneg (div_nonneg (mul_nonneg bn.1 cp.le) (by norm_num : (0:ℝ)≤2))
    (show 0≤c+b by linarith only [cp,bp])
  have jn : 0≤J := by dsimp [J]; linarith only [j0,j1,j2,j3]
  have product := mul_nonneg (sub_nonneg.mpr sine) jn
  have identity : (c+b)*(plusPhi c s b r-plusPhi b r b r)=(r-s)*J := by
    dsimp [plusPhi,J]
    linear_combination (b+r-r^2/2)*cn.2.2-(b+r-r^2/2)*bn.2.2
  have comparison : plusPhi b r b r≤plusPhi c s b r := by
    have gap := nonneg_of_mul_nonneg_right (show 0≤(c+b)*(plusPhi c s b r-plusPhi b r b r) by
      rw [identity]; exact product) (show 0<c+b by linarith only [cp,bp])
    linarith only [gap]
  have endpointForm : b+r-2+r^2+b*plusPhi b r b r=endpoint b r := by
    dsimp [plusPhi,endpoint]
    linear_combination b*bn.2.2
  have weighted := mul_le_mul_of_nonneg_left comparison bp.le
  have ending := endpoint_positive bn rp
  dsimp [plusMargin]
  linarith only [weighted,ending,endpointForm]

/-- The other relative order uses the same exact chord, the rational
canonical sum bound and the strict boundary slope5/12. -/
theorem minus_positive {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (ratio : (5/12)*b<r) (order : c*r-s*b≤0) : 0<minusMargin c s b r := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0<c := by linarith only [cb.1]
  have bp : 0<b := by linarith only [bb.1]
  have rp : 0<r := by linarith only [ratio,bp]
  have sine : r≤s := sine_order cn bn order
  have cs := sum_bounds cn
  have bs := sum_bounds bn
  let P := c+b
  let Q := s+r
  let Z := P-Q
  let H := P+Q
  let L := H-P*Q
  let J := r*L-b*Z*(H/2-1)
  have zn : 0≤Z := by dsimp [Z,P,Q]; linarith only [cn.2.1,bn.2.1]
  have qn : 0≤Q := by dsimp [Q]; linarith only [cn.1,bn.1]
  have pl : P≤2 := by dsimp [P]; linarith only [cb.2.1,bb.2.1]
  have gap := mul_nonneg qn (show 0≤2-P by linarith only [pl])
  have ll : Z≤L := by dsimp [L,H,Z] at *; nlinarith only [gap]
  have first := mul_nonneg (by norm_num : (0:ℝ)≤5/12) (sub_nonneg.mpr ll)
  have last := mul_nonneg zn
    (show 0≤5/12-(H/2-1) by dsimp [H,P,Q]; linarith only [cs.2,bs.2])
  have bracket : 0≤(5/12)*L-Z*(H/2-1) := by nlinarith only [first,last]
  have lnonnegative : 0≤L := zn.trans ll
  have base := mul_nonneg (show 0≤r-(5/12)*b by linarith only [ratio]) lnonnegative
  have rest := mul_nonneg bp.le bracket
  have jn : 0≤J := by dsimp [J]; nlinarith only [base,rest]
  have product := mul_nonneg (sub_nonneg.mpr sine) jn
  have identity : (c+b)*(minusPhi c s b r-minusPhi b r b r)=(s-r)*J := by
    dsimp [minusPhi,J,L,H,Z,P,Q]
    linear_combination (b-r-b*(s+r)/2)*cn.2.2-
      (b-r-b*(s+r)/2)*bn.2.2
  have comparison : minusPhi b r b r≤minusPhi c s b r := by
    have gap := nonneg_of_mul_nonneg_right (show 0≤(c+b)*(minusPhi c s b r-minusPhi b r b r) by
      rw [identity]; exact product) (show 0<c+b by linarith only [cp,bp])
    linarith only [gap]
  have endpointForm : b+r-2+r^2+b*minusPhi b r b r=endpoint b r := by
    dsimp [minusPhi,endpoint]
    linear_combination b*(1-r)*bn.2.2
  have weighted := mul_le_mul_of_nonneg_left comparison bp.le
  have ending := endpoint_positive bn rp
  dsimp [minusMargin]
  linarith only [weighted,ending,endpointForm]

end
#print axioms v_positive
#print axioms plus_positive
#print axioms minus_positive
end N12Compact.C1092MPPMPositiveBoundaryOrigin.Scalars
