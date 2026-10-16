import Compact.Completion.C1092.MPPMInwardFinalCenteredCaps

/-! The full-domain predecessor margins in CENTERED-NEGATIVE-INWARD-H-CAP.
All printed quartics are retained as exact identities. Concavity and
angular monotonicity are replaced by algebraic chord decompositions. -/
namespace N12Compact.C1092MPPMInwardFinal
open C977CornerCubic C1092WallProfileScalars CommonCases.CanonicalProjection
set_option Elab.async false
noncomputable section

def centeredD (c s : ℝ) := 1-(7/50)*c-s/2
def capB (c s eta : ℝ) := 543/500-s*centeredD c s-eta*c
def capR (c s eta : ℝ) := 1-c*centeredD c s+eta*s

theorem centered_D_bounds {c s : ℝ} (cn : Normal c s) :
    27/50<centeredD c s ∧ centeredD c s≤43/50 := by
  have cb := normal_bounds cn
  dsimp [centeredD]
  constructor <;> linarith only [cn.1,cn.2.1,cb.2.2.2.2.1,cb.2.2.2.2.2]

theorem dot_strict {b r P Q K : ℝ} (unit : b^2+r^2=1) (positive : 0<K)
    (norm : P^2+Q^2<K^2) : P*b+Q*r<K := by
  have identity : (P*b+Q*r)^2+(P*r-Q*b)^2=(P^2+Q^2)*(b^2+r^2) := by ring
  rw [unit] at identity
  apply lt_of_not_ge
  intro no
  have square := mul_nonneg (show 0≤P*b+Q*r-K by linarith only [no])
    (show 0≤P*b+Q*r+K by linarith only [no,positive])
  nlinarith only [identity,square,norm,sq_nonneg (P*r-Q*b)]

private theorem half_bounds {c s : ℝ} (cn : Normal c s) :
    0≤half c s ∧ half c s≤5/12 := by
  have cb := normal_bounds cn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  let x := half c s
  have den : 0≤1+x^2 := by nlinarith only [sq_nonneg x]
  have ordered := mul_nonneg den (sub_nonneg.mpr cn.2.1)
  refine ⟨data.1,?_⟩
  apply le_of_not_gt
  intro large
  have square := mul_nonneg (show 0≤x-5/12 by linarith only [large])
    (show 0≤x+5/12 by linarith only [data.1])
  nlinarith only [ordered,data.2.2.2.1,data.2.2.2.2,square,large]

theorem cap_norm {c s : ℝ} (cn : Normal c s) :
    capB c s (17/125)^2+capR c s (17/125)^2<1 := by
  have cb := normal_bounds cn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  let x := half c s
  have xb := half_bounds cn
  have den : 0<1+x^2 := by nlinarith only [sq_nonneg x]
  have cf : c=(1-x^2)/(1+x^2) :=
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.1])
  have sf : s=2*x/(1+x^2) :=
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.2])
  let b : ℝ := 5/12
  let P (z : ℝ) := -1268221*z^4+2172040*z^3-2285146*z^2+727960*z+19475
  let Q := -1268221*(x^2+b*x+b^2)+2172040*(x+b)-2285146
  have negative : Q<0 := by dsimp [Q,b]; nlinarith only [xb.1,xb.2,sq_nonneg x]
  have chord : (b-x)*P 0+x*P b-b*P x=b*x*(b-x)*Q := by dsimp [P,Q]; ring
  have p0 : 0<P 0 := by norm_num [P]
  have p1 : 0<P b := by norm_num [P,b]
  have correction := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (show 0≤b by norm_num [b]) xb.1)
      (show 0≤b-x by exact sub_nonneg.mpr xb.2)) negative.le
  have first := mul_nonneg (show 0≤b-x by exact sub_nonneg.mpr xb.2) p0.le
  have last := mul_nonneg xb.1 p1.le
  have strict : 0<(b-x)*P 0+x*P b := by
    by_cases zero : x=0
    · have product := mul_pos (show 0<b by norm_num [b]) p0
      simpa only [zero,sub_zero,zero_mul,add_zero] using product
    · have product := mul_pos (lt_of_le_of_ne xb.1 (Ne.symm zero)) p1
      linarith only [first,product]
  have polynomial : 0<P x := by
    apply lt_of_not_ge
    intro no
    have bad := mul_nonpos_of_nonneg_of_nonpos (show 0≤b by norm_num [b]) no
    linarith only [chord,correction,strict,bad]
  have identity : 250000*(1+x^2)^2*(1-capB c s (17/125)^2-capR c s (17/125)^2)=P x := by
    dsimp [capB,capR,centeredD]
    rw [cf,sf]
    dsimp [P]
    field_simp [den.ne']
    <;> ring
  have scaled : 0<250000*(1+x^2)^2*(1-capB c s (17/125)^2-capR c s (17/125)^2) := by
    rw [identity]; exact polynomial
  have positive := pos_of_mul_pos_right scaled
    (show 0≤250000*(1+x^2)^2 by exact mul_nonneg (by norm_num) (sq_nonneg _))
  linarith only [positive]

theorem cap_own_positive {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r) :
    0<1-(543/500)*b-r+(c*r+s*b)*centeredD c s+(c*b-s*r)*(17/125) := by
  have norm := cap_norm cn
  have bound := dot_strict bn.2.2 (by norm_num : (0:ℝ)<1) (by simpa only [one_pow] using norm)
  dsimp [capB,capR] at bound
  nlinarith only [bound]

theorem cap_left_positive {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r) :
    0<1-b-r+(c*b+s*r)*centeredD c s+(c*r-s*b)*(17/125) := by
  have cb := normal_bounds cn
  have small : s<71/100 := by
    have compare := mul_nonneg (sub_nonneg.mpr cn.2.1)
      (show 0≤c+s by linarith only [cb.1,cn.1])
    nlinarith only [compare,cn.2.2,sq_nonneg (s-71/100)]
  have bp : 43/1000<capB c s (17/125) := by
    have d := centered_D_bounds cn
    have product := mul_nonneg cn.1 (show 0≤1-centeredD c s by linarith only [d.2])
    dsimp [capB]
    nlinarith only [product,small,cb.2.1]
  have norm : capR c s (17/125)^2+(capB c s (17/125)-43/500)^2<1 := by
    nlinarith only [cap_norm cn,bp]
  have bound := dot_strict bn.2.2 (by norm_num : (0:ℝ)<1) (by simpa only [one_pow] using norm)
  dsimp [capB,capR] at bound
  nlinarith only [bound]

theorem cap_left_before {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (order : c*r≤s*b) :
    0<1-b-r+(c*b+s*r)*centeredD c s+(s*b-c*r)*(1-(7/20)*(c-s)) := by
  have cb := normal_bounds cn
  have d := centered_D_bounds cn
  let E := 1-(7/20)*(c-s)
  let P := 1-c*centeredD c s-s*E
  let Q := 1-s*centeredD c s+c*E
  have ep : 0<E := by dsimp [E]; linarith only [cb.2.1,cn.1]
  have derivativeIdentity : Q*c-P*s=c-s+E := by
    dsimp [P,Q]
    linear_combination E*cn.2.2
  have derivative : P*s≤Q*c := by
    linarith only [derivativeIdentity,cn.2.1,ep]
  have valueIdentity : P*c+Q*s=c+s-centeredD c s := by
    dsimp [P,Q]
    linear_combination -(centeredD c s)*cn.2.2
  have value : 0≤P*c+Q*s := by
    linarith only [valueIdentity,cb.2.2.2.2.1,d.2]
  have comparison := before b r c s P Q bn.2.2 cn.2.2 order derivative value
  have bound : (57/50)*c+(3/2)*s<2 :=
    dot_strict cn.2.2 (by norm_num) (by norm_num)
  have formula : 1-b-r+(c*b+s*r)*centeredD c s+(s*b-c*r)*E=1-P*b-Q*r := by
    dsimp [P,Q]; ring
  change 0<1-b-r+(c*b+s*r)*centeredD c s+(s*b-c*r)*E
  rw [formula]
  dsimp [centeredD] at valueIdentity
  linarith only [comparison,bound,valueIdentity]

theorem cap_f0 {b r : ℝ} (bn : Normal b r) :
    (b+r-1)^2/2+(43/500)*r^2<13/100 ∧ 0≤r^2+b-r-(43/500)*b*r := by
  have bb := normal_bounds bn
  have sum : b+r≤99/70 := by
    nlinarith only [bn.2.2,sq_nonneg (b-r),sq_nonneg (b+r-99/70)]
  have half : r^2≤1/2 := by
    have compare := mul_nonneg (sub_nonneg.mpr bn.2.1)
      (show 0≤b+r by linarith only [bb.1,bn.1])
    nlinarith only [compare,bn.2.2]
  have square := mul_nonneg (show 0≤99/70-(b+r) by linarith only [sum])
    (show 0≤b+r-1+29/70 by linarith only [bb.2.2.2.2.1])
  have order := mul_nonneg (sub_nonneg.mpr bn.2.1)
    (show 0≤1-(43/500)*r by linarith only [bb.2.2.2.1])
  constructor <;> nlinarith only [square,half,order,sq_nonneg r]

theorem cap_g0 {b r : ℝ} (bn : Normal b r) (sum : b+r<29/25) :
    43/500+(b+r-1)^2/2<247/2500 ∧ 0≤r^2+b-r := by
  have bb := normal_bounds bn
  have square := mul_pos (show 0<29/25-(b+r) by linarith only [sum])
    (show 0<b+r-1+4/25 by linarith only [bb.2.2.2.2.1])
  constructor <;> nlinarith only [square,bn.2.1,sq_nonneg r]

theorem cap_negative_fg {b r : ℝ} (bn : Normal b r) :
    (43/500)*b^2+f b r<17/125 ∧ 0≤g b r-(43/500)*b*r := by
  have bb := normal_bounds bn
  have data := quarter_data b r (by linarith only [bb.1]) bn.1 bn.2.2
  let w := half b r
  let h := w-1/3
  have wb := half_bounds bn
  have den : 0<1+w^2 := by nlinarith only [sq_nonneg w]
  have bf : b=(1-w^2)/(1+w^2) :=
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.1])
  have rf : r=2*w/(1+w^2) :=
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.2])
  have hl : -1/3≤h := by dsimp [h]; linarith only [wb.1]
  have hu : h≤1/12 := by dsimp [h]; linarith only [wb.2]
  have square := mul_nonneg (show 0≤1/3-h by linarith only [hu])
    (show 0≤1/3+h by linarith only [hl])
  have coefficient : 691/3≤572+700*h-975*h^2 := by nlinarith only [square,hl]
  have weighted := mul_nonneg (sq_nonneg h) (sub_nonneg.mpr coefficient)
  have quadratic : 0<16/27+(32/9)*h+(691/3)*h^2 := by
    nlinarith only [sq_nonneg ((1382/3)*h+32/9)]
  have identity : 500*(1+w^2)^2*(17/125-((43/500)*b^2+f b r))=
      16/27+(32/9)*h+h^2*(572+700*h-975*h^2) := by
    rw [bf,rf]
    dsimp [f,h]
    field_simp [den.ne']
    <;> ring
  have scaled : 0<500*(1+w^2)^2*(17/125-((43/500)*b^2+f b r)) := by
    nlinarith only [identity,quadratic,weighted]
  have margin := pos_of_mul_pos_right scaled
    (show 0≤500*(1+w^2)^2 by exact mul_nonneg (by norm_num) (sq_nonneg _))
  have last := mul_nonneg bn.1 (show 0≤1-b by linarith only [bb.2.1])
  have small := mul_nonneg bn.1 (show 0≤1-r by linarith only [bb.2.2.2.1])
  constructor <;> nlinarith only [margin,last,small,(fg_bounds bn).2.2.2,bn.1]

#print axioms cap_norm
#print axioms cap_negative_fg
end
end N12Compact.C1092MPPMInwardFinal
