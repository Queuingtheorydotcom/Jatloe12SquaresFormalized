import Compact.Completion.C1092.MPPMMissingNegativeCrosspointG01Models

/-! The remaining central/boundary scalar in MISSING-NEGATIVE-WALL-
SCALARS. Both genuine FE bounds hold globally. Consequently only the
three C-angle ranges remain, with no successor-angle partition. The
middle range clamps the actual C linear functional at its aligned value;
the other ranges use the two exact fixed models. -/
namespace N12Compact.C1092MPPMMissingNegativeCrosspointSupport
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false
noncomputable section

private theorem before_formula (c s d t h r : ℝ) (q : Quarter h r)
    (order : deltaC c s h r≤0) :
    G01 c s d t h r=c*h*(h-2)+s*(1+h*r-2*r-h-FE d t h r)+h := by
  rw [G01,abs_of_nonpos order]
  dsimp [kC,C1092MPPMNegativeCrosspointSupport.kC,deltaC,C1092MPPMNegativeCrosspointSupport.deltaC,C0,C1092MPPMNegativeCrosspointSupport.C0]
  linear_combination (s/2)*q.unit

private theorem after_formula (c s d t h r : ℝ) (q : Quarter h r)
    (order : 0≤deltaC c s h r) :
    G01 c s d t h r=c*h*(h+r-2)+s*(r*(h+r-2)-h-FE d t h r)+h := by
  rw [G01,abs_of_nonneg order]
  dsimp [kC,C1092MPPMNegativeCrosspointSupport.kC,deltaC,C1092MPPMNegativeCrosspointSupport.deltaC,C0,C1092MPPMNegativeCrosspointSupport.C0]
  linear_combination -(s/2)*q.unit

private theorem first_before (epsilon c s d t h r : ℝ) (cn : Normal c s)
    (en : Normal d t) (large : 252/373≤t) (q : Quarter h r)
    (allowance : epsilon≤43/500) (order : deltaC c s h r≤0) :
    c*(h*(h-2))+s*(1+h*r-(61/50)*r-(112/125)*h)+h≤
      G01star epsilon c s d t h r := by
  have cap := mul_le_mul_of_nonneg_left (FE_first_cap d t h r en large q) cn.1
  have perturb := mul_le_mul_of_nonneg_right allowance (mul_nonneg cn.1 q.cosine)
  rw [G01star,before_formula c s d t h r q order]
  nlinarith only [cap,perturb]

private theorem first_after (epsilon c s d t h r : ℝ) (cn : Normal c s)
    (en : Normal d t) (large : 252/373≤t) (q : Quarter h r)
    (allowance : epsilon≤43/500) (order : 0≤deltaC c s h r) :
    c*(h*(h+r-2))+s*(r*(h+r-61/50)-(112/125)*h)+h≤
      G01star epsilon c s d t h r := by
  have cap := mul_le_mul_of_nonneg_left (FE_first_cap d t h r en large q) cn.1
  have perturb := mul_le_mul_of_nonneg_right allowance (mul_nonneg cn.1 q.cosine)
  rw [G01star,after_formula c s d t h r q order]
  nlinarith only [cap,perturb]

private theorem second_after (epsilon c s d t h r : ℝ) (cn : Normal c s)
    (en : Normal d t) (large : 252/373≤t) (q : Quarter h r)
    (allowance : epsilon≤43/500) (order : 0≤deltaC c s h r) :
    c*(h*(h+r-2))+s*(r*(h+r-17/25)-(182/125)*h)+h≤
      G01star epsilon c s d t h r := by
  have cap := mul_le_mul_of_nonneg_left (FE_second_cap d t h r en large q) cn.1
  have perturb := mul_le_mul_of_nonneg_right allowance (mul_nonneg cn.1 q.cosine)
  rw [G01star,after_formula c s d t h r q order]
  nlinarith only [cap,perturb]

private theorem low (epsilon c s d t h r : ℝ) (cn : Normal c s) (steep : 3/5≤s)
    (en : Normal d t) (large : 252/373≤t) (q : Quarter h r)
    (allowance : epsilon≤43/500) (hh : 4/5≤h) (rr : r≤3/5) :
    1/100≤G01star epsilon c s d t h r := by
  have cb := normal_bounds cn
  have cs := C1092MPPMCrosspointSupport.steep_bounds cn steep
  have first := mul_nonneg (show 0≤c by linarith only [cb.1])
    (show 0≤3/5-r by linarith only [rr])
  have last := mul_nonneg cn.1 (show 0≤h-4/5 by linarith only [hh])
  have order : deltaC c s h r≤0 := by
    dsimp [deltaC,C1092MPPMNegativeCrosspointSupport.deltaC]
    nlinarith only [first,last,cs.1,steep]
  have lower := first_before epsilon c s d t h r cn en large q allowance order
  have hu : h≤1 := by nlinarith only [q.unit,sq_nonneg r,sq_nonneg (h-1)]
  let A := h*(h-2)
  let B := 1+h*r-(61/50)*r-(112/125)*h
  have An : A≤0 := mul_nonpos_of_nonneg_of_nonpos q.cosine (by linarith only [hu])
  have aw := mul_le_mul_of_nonpos_right cs.1 An
  by_cases Bn : 0≤B
  · have bw := mul_le_mul_of_nonneg_right steep Bn
    have model := G01_low_model (3/5) h r (by norm_num) (by norm_num) q hh rr
    dsimp [A,B] at aw bw
    nlinarith only [lower,aw,bw,model]
  · have bw := mul_le_mul_of_nonpos_right cs.2.1.le (lt_of_not_ge Bn).le
    have model := G01_low_model (71/100) h r (by norm_num) (by norm_num) q hh rr
    dsimp [A,B] at aw bw
    nlinarith only [lower,aw,bw,model]

private theorem middle (epsilon c s d t h r : ℝ) (cn : Normal c s)
    (en : Normal d t) (large : 252/373≤t) (bn : Normal h r) (steep : 3/5≤r)
    (allowance : epsilon≤43/500) : 1/100≤G01star epsilon c s d t h r := by
  have bb := normal_bounds bn
  have cb := normal_bounds cn
  have bs := C1092MPPMCrosspointSupport.steep_bounds bn steep
  have q : Quarter h r := ⟨by linarith only [bb.1],bn.1,bn.2.2⟩
  have Hu : h+r≤283/200 := by
    nlinarith only [bn.2.2,sq_nonneg (h-r),sq_nonneg (h+r-283/200)]
  have model := G01_middle_model h r bn steep
  by_cases branch : deltaC c s h r≤0
  · let A := h*(h-2)
    let B := 1+h*r-(61/50)*r-(112/125)*h
    have An : A≤0 := mul_nonpos_of_nonneg_of_nonpos q.cosine
      (by linarith only [bb.2.1])
    have Dn : 0≤h-r := sub_nonneg.mpr bn.2.1
    have Du : h-r≤1/5 := by linarith only [bs.1,steep]
    have positive := mul_nonneg Dn
      (show 0≤81/500-(h-r)/2 by linarith only [Du])
    have Bn : 0≤B := by dsimp [B]; nlinarith only [positive,Hu,bn.2.2]
    have sine : r≤s := sine_order cn bn branch
    have cosine : c≤h := cosine_order cn bn sine
    have aw := mul_le_mul_of_nonpos_right cosine An
    have bw := mul_le_mul_of_nonneg_right sine Bn
    have lower := first_before epsilon c s d t h r cn en large q allowance branch
    have identity : h*A+r*B+h=2*h+r-2-(112/125)*h*r+(39/50)*r^2 := by
      dsimp [A,B]
      linear_combination (h-2)*bn.2.2
    dsimp [A,B] at aw bw identity
    nlinarith only [lower,aw,bw,identity,model]
  · let A := h*(h+r-2)
    let B := r*(h+r-61/50)-(112/125)*h
    have An : A≤0 := mul_nonpos_of_nonneg_of_nonpos q.cosine (by linarith only [Hu])
    have product := mul_nonneg bn.1 (show 0≤71/50-(h+r) by linarith only [Hu])
    have Bn : B≤0 := by dsimp [B]; nlinarith only [product,bn.2.1,bn.1]
    have derivative : 0≤(-B)*h-(-A)*r := by
      have product := mul_nonneg q.cosine
        (show 0≤(112/125)*h-(39/50)*r by linarith only [bn.2.1,bn.1])
      dsimp [A,B]
      nlinarith only [product]
    have sine : s≤r := sine_order bn cn (by dsimp [deltaC,C1092MPPMNegativeCrosspointSupport.deltaC] at branch; linarith only [branch])
    have compare := CommonCases.UnitCircleChord.increasing (A:=-A) (B:=-B)
      (show 0<h by linarith only [bb.1]) (show 0≤c by linarith only [cb.1])
      bn.2.2 cn.2.2 bn.1 cn.1 sine (neg_nonneg.mpr An) (neg_nonneg.mpr Bn) derivative
    have lower := first_after epsilon c s d t h r cn en large q allowance
      (lt_of_not_ge branch).le
    have identity : h*A+r*B+h=2*h+r-2-(112/125)*h*r+(39/50)*r^2 := by
      dsimp [A,B]
      linear_combination (h+r-2)*bn.2.2
    dsimp [A,B] at compare identity
    nlinarith only [lower,compare,identity,model]

private theorem high (epsilon c s d t h r : ℝ) (cn : Normal c s) (steep : 3/5≤s)
    (en : Normal d t) (large : 252/373≤t) (q : Quarter h r)
    (allowance : epsilon≤43/500) (order : h≤r) :
    1/100≤G01star epsilon c s d t h r := by
  have cb := normal_bounds cn
  have cs := C1092MPPMCrosspointSupport.steep_bounds cn steep
  have first := mul_nonneg (sub_nonneg.mpr cn.2.1) q.sine
  have last := mul_nonneg cn.1 (sub_nonneg.mpr order)
  have cross : 0≤deltaC c s h r := by dsimp [deltaC,C1092MPPMNegativeCrosspointSupport.deltaC]; nlinarith only [first,last]
  have lower := second_after epsilon c s d t h r cn en large q allowance cross
  have Hu : h+r≤2 := by nlinarith only [q.unit,sq_nonneg (h-r),sq_nonneg (h+r-2)]
  have Hl : 1≤h+r := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (show 0<1-(h+r) by linarith only [bad])
      (show 0<1+(h+r) by linarith only [q.cosine,q.sine])
    nlinarith only [product,q.unit,mul_nonneg q.cosine q.sine]
  let A := h*(h+r-2)
  let B := r*(h+r-17/25)-(182/125)*h
  have An : A≤0 := mul_nonpos_of_nonneg_of_nonpos q.cosine (by linarith only [Hu])
  have aw := mul_le_mul_of_nonpos_right cs.1 An
  by_cases Bn : 0≤B
  · have bw := mul_le_mul_of_nonneg_right steep Bn
    have Hweight := mul_nonneg q.cosine (show 0≤h+r-1 by linarith only [Hl])
    have simple : h/5+(3/5)*B≤G01star epsilon c s d t h r := by
      dsimp [A,B] at aw bw ⊢
      nlinarith only [lower,aw,bw,Hweight]
    by_cases hh : 1/20≤h
    · nlinarith only [simple,Bn,hh]
    · have rh : 99/100≤r := by
        have square := mul_nonneg (show 0≤1/20-h by linarith only [hh])
          (show 0≤1/20+h by linarith only [q.cosine])
        apply le_of_not_gt
        intro bad
        have product := mul_pos (show 0<99/100-r by linarith only [bad])
          (show 0<99/100+r by linarith only [q.sine])
        nlinarith only [square,q.unit,product]
      have product := mul_nonneg (show 0≤r-99/100 by linarith only [rh])
        (show 0≤h+r-17/25 by linarith only [rh,q.cosine])
      have Bpositive : 1/5≤B := by dsimp [B]; nlinarith only [product,rh,q.cosine,hh]
      nlinarith only [simple,Bpositive,q.cosine]
  · have bw := mul_le_mul_of_nonpos_right cs.2.1.le (lt_of_not_ge Bn).le
    have model := G01_high_model h r q order
    dsimp [A,B] at aw bw
    nlinarith only [lower,aw,bw,model]

/-- Full closed quadrant, with the original positive-face allowance. -/
theorem G01star_lower (epsilon c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (large : 252/373≤t)
    (q : Quarter h r) (allowance : epsilon≤43/500) :
    1/100≤G01star epsilon c s d t h r := by
  by_cases small : r≤3/5
  · have square := mul_nonneg (show 0≤3/5-r by linarith only [small])
      (show 0≤3/5+r by linarith only [q.sine])
    have hh : 4/5≤h := by
      apply le_of_not_gt
      intro bad
      have product := mul_pos (show 0<4/5-h by linarith only [bad])
        (show 0<4/5+h by linarith only [q.cosine])
      nlinarith only [square,q.unit,product]
    exact low epsilon c s d t h r cn steep en large q allowance hh small
  · by_cases upper : h≤r
    · exact high epsilon c s d t h r cn steep en large q allowance upper
    · have bn : Normal h r := ⟨q.sine,(lt_of_not_ge upper).le,q.unit⟩
      exact middle epsilon c s d t h r cn en large bn (lt_of_not_ge small).le allowance

end
#print axioms G01star_lower
end N12Compact.C1092MPPMMissingNegativeCrosspointSupport
