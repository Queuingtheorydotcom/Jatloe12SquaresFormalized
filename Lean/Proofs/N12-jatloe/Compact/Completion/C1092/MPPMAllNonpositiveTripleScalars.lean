import Compact.Completion.C1092.MPPMAllNonpositiveCore
import Compact.Completion.CommonCases.UnitCircleChord
import Compact.Geometry.C977CornerSectorBounds

/-! ALL-NEGATIVE-MIXED-FORWARD-ENDING section 3. Four exact support
gaps, for both longitudinal normals and both angle orders. A finite
one-half Lipschitz bound for G replaces its derivative estimate; the
last branch is the unit identity (1-k)(1+k)=delta^2. -/
namespace N12Compact.C1092MPPMAllNonpositive.TripleScalars
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false
noncomputable section

def G (d t : ℝ) : ℝ := (1-d)*(1-t)/d
def k (c s d t : ℝ) : ℝ := c*d+s*t
def delta (c s d t : ℝ) : ℝ := c*t-s*d

private theorem circle {c s : ℝ} (cn : Normal c s) (sp : 0<s) :
    0<c ∧ c<1 ∧ 1<c+s := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have ch : c<1 := by
    have positive := sq_pos_of_pos sp
    nlinarith only [cn.2.2,positive,cb.2.1,sq_nonneg (c-1)]
  have sum : 1<c+s := by
    apply lt_of_not_ge
    intro low
    have product := mul_nonneg (show 0≤1-c-s by linarith only [low])
      (show 0≤1+c+s by linarith only [cp,sp])
    nlinarith only [product,cn.2.2,mul_pos cp sp]
  exact ⟨cp,ch,sum⟩

private theorem relative {c s d t : ℝ} (cn : Normal c s) (en : Normal d t) :
    0<k c s d t ∧ k c s d t≤1 ∧ (k c s d t)^2+(delta c s d t)^2=1 := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have positive := mul_pos (show 0<c by linarith only [cb.1])
    (show 0<d by linarith only [eb.1])
  have extra := mul_nonneg cn.1 en.1
  refine ⟨by dsimp [k]; linarith only [positive,extra],dot_le_one cn en,?_⟩
  dsimp [k,delta]
  linear_combination (d^2+t^2)*cn.2.2+en.2.2

private theorem G_spec {c s : ℝ} (cn : Normal c s) :
    (1+s)*(G c s+1-s)=c := by
  have cp : 0<c := by linarith only [(normal_bounds cn).1]
  have eq : c*G c s=(1-c)*(1-s) := by
    dsimp [G]
    field_simp [cp.ne']
  apply mul_left_cancel₀ cp.ne'
  linear_combination (1+s)*eq-cn.2.2

theorem endpoint {c s : ℝ} (cn : Normal c s) (sp : 0<s) : 0<1-c-G c s := by
  have cb := circle cn sp
  have eq : c*G c s=(1-c)*(1-s) := by dsimp [G]; field_simp [cb.1.ne']
  have product := mul_pos (show 0<1-c by linarith only [cb.2.1])
    (show 0<c+s-1 by linarith only [cb.2.2])
  have identity : c*(1-c-G c s)=(1-c)*(c+s-1) := by linear_combination -eq
  rw [←identity] at product
  exact pos_of_mul_pos_right product cb.1.le

/-- The weaker one-half constant suffices for the support reserve and
holds on the entire ordered canonical arc, including zero endpoints. -/
theorem G_difference {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (order : s≤t) : G d t-G c s≤(t-s)/2 := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cp : 0<c := by linarith only [cb.1]
  have dp : 0<d := by linarith only [eb.1]
  let I := (1-c)*(1-d)+(t-s)+s*(2-c-d+t)
  have first := mul_nonneg (show 0≤1-c by linarith only [cb.2.1])
    (show 0≤1-d by linarith only [eb.2.1])
  have last := mul_nonneg cn.1 (show 0≤2-c-d+t by linarith only [cb.2.1,eb.2.1,en.1])
  have In : 0≤I := by dsimp [I]; linarith only [first,last,order]
  have product := mul_nonneg (sub_nonneg.mpr order) In
  have gc := G_spec cn
  have gd := G_spec en
  have identity : (c+d)*(1+s)*((1+t)*(G d t-G c s)-t*(t-s))=-(t-s)*I := by
    dsimp [I]
    linear_combination (c+d)*(1+s)*gd-(c+d)*(1+t)*gc-
      (1+t)*cn.2.2+(1+s)*en.2.2
  have weighted : (c+d)*(1+s)*((1+t)*(G d t-G c s)-t*(t-s))≤0 := by
    rw [identity]
    linarith only [product]
  have inner := nonpos_of_mul_nonpos_right weighted
    (mul_pos (show 0<c+d by linarith only [cp,dp]) (show 0<1+s by linarith only [cn.1]))
  have allowance := mul_nonneg (sub_nonneg.mpr order)
    (show 0≤1-t by linarith only [eb.2.2.2.1])
  have difference : 0≤(1+t)*((t-s)/2-(G d t-G c s)) := by
    nlinarith only [inner,allowance]
  have result := nonneg_of_mul_nonneg_right difference (show 0<1+t by linarith only [en.1])
  linarith only [result]

private theorem delta_difference {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (order : s≤t) : t-s≤delta c s d t := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have first := mul_nonneg (show 0≤1-c by linarith only [cb.2.1])
    (show 0≤1-d by linarith only [eb.2.1])
  have last := mul_nonneg cn.1 en.1
  have product := mul_nonneg (sub_nonneg.mpr order) (add_nonneg first last)
  have identity : (c+d)*(delta c s d t-(t-s))=
      (t-s)*((1-c)*(1-d)+s*t) := by
    dsimp [delta]
    linear_combination t*cn.2.2-s*en.2.2
  rw [←identity] at product
  have result := nonneg_of_mul_nonneg_right product (show 0<c+d by linarith only [cb.1,eb.1])
  linarith only [result]

theorem source_before {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (sp : 0<s) (tp : 0<t) (order : delta c s d t≤0) :
    0<d*(1-c)+(1-d)*(s-k c s d t) := by
  have cb := circle cn sp
  have eb := circle en tp
  have angles : t≤s := sine_order cn en order
  have cosine : c≤d := cosine_order cn en angles
  have rel := relative cn en
  have first := mul_nonneg eb.1.le (sub_nonneg.mpr cosine)
  have last := mul_nonneg (show 0≤1-d by linarith only [eb.2.1])
    (show 0≤1-k c s d t by linarith only [rel.2.1])
  have strict := mul_pos (show 0<1-d by linarith only [eb.2.1])
    (show 0<d+s-1 by linarith only [eb.2.2,angles])
  nlinarith only [first,last,strict]

theorem source_after {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (sp : 0<s) (tp : 0<t) (order : 0≤delta c s d t) :
    0<d*(1-c)+(1-d)*(s-k c s d t)+d*delta c s d t := by
  have eb := circle en tp
  have angles : s≤t := sine_order en cn (by dsimp [delta] at order; nlinarith only [order])
  let P := d*(2-d-t)
  let Q := d^2-(1-d)*(1-t)
  have Pn : 0≤P := mul_nonneg eb.1.le
    (show 0≤2-d-t by linarith only [(normal_bounds en).2.2.2.2.2])
  have slope : P*t≤Q*d := by
    have positive := mul_nonneg eb.1.le (sub_nonneg.mpr en.2.1)
    have identity : Q*d-P*t=d*(d-t) := by
      dsimp [P,Q]
      linear_combination d*en.2.2
    linarith only [positive,identity]
  have compare := linear_arc_max en cn angles Pn slope
  have strict := mul_pos (show 0<1-d by linarith only [eb.2.1])
    (show 0<d+t-1 by linarith only [eb.2.2])
  have endpointIdentity : d-P*d-Q*t=(1-d)*(d+t-1) := by
    dsimp [P,Q]
    linear_combination (d-1)*en.2.2
  have identity : d*(1-c)+(1-d)*(s-k c s d t)+d*delta c s d t=d-P*c-Q*s := by
    dsimp [k,delta,P,Q]
    ring
  nlinarith only [compare,strict,endpointIdentity,identity]

theorem target_after {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (sp : 0<s) (close : 873/1000<c) (order : 0≤delta c s d t) :
    0<k c s d t*(1-c)+delta c s d t*(1-(7/20)*(c-s))-G d t := by
  have cb := normal_bounds cn
  have angles : s≤t := sine_order en cn (by dsimp [delta] at order; nlinarith only [order])
  have rel := relative cn en
  have endpoint := endpoint cn sp
  have gap := G_difference cn en angles
  have deltaGap := delta_difference cn en angles
  have deficit : 1-k c s d t≤delta c s d t := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (show 0<1-k c s d t-delta c s d t by linarith only [bad])
      (show 0<1-k c s d t+delta c s d t by linarith only [bad,order])
    have extra := mul_nonneg rel.1.le (show 0≤1-k c s d t by linarith only [rel.2.1])
    nlinarith only [product,extra,rel.2.2]
  have first := mul_le_mul_of_nonneg_right deficit (show 0≤1-c by linarith only [cb.2.1])
  have last := mul_le_mul_of_nonneg_left
    (show 1-c≤127/1000 by linarith only [close]) order
  have cap := mul_nonneg order (show 0≤1-(7/20)*(c-s)-13/20 by linarith only [cb.2.1,cn.1])
  nlinarith only [endpoint,gap,deltaGap,first,last,cap,order]

theorem target_before {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (sp : 0<s) (tp : 0<t) (closeC : 873/1000<c) (closeE : 873/1000<d)
    (order : delta c s d t≤0) :
    0<k c s d t*(1-c)+(13/50)*delta c s d t*s-G d t := by
  have eb := normal_bounds en
  have rel := relative cn en
  have endpoint := endpoint en tp
  let h := -delta c s d t
  have hn : 0≤h := neg_nonneg.mpr order
  have hcap : h≤s := by
    have first := mul_le_mul_of_nonneg_left eb.2.1 cn.1
    have last := mul_nonneg (show 0≤c by linarith only [closeC]) en.1
    dsimp [h,delta]
    nlinarith only [first,last]
  have closeProduct := mul_nonneg (show 0≤c-873/1000 by linarith only [closeC])
    (show 0≤d-873/1000 by linarith only [closeE])
  have kcap : 1/2≤k c s d t := by
    dsimp [k]
    nlinarith only [closeProduct,closeC,closeE,mul_nonneg cn.1 en.1]
  have coefficient := mul_nonneg cn.1
    (show 0≤(37/50)*(1+k c s d t)-1 by linarith only [kcap])
  have bracket : 0≤(37/50)*s*(1+k c s d t)-h := by nlinarith only [coefficient,hcap]
  have product := mul_nonneg hn bracket
  have identity : (1+k c s d t)*(k c s d t-1+(37/50)*s*h)=
      h*((37/50)*s*(1+k c s d t)-h) := by
    dsimp [h]
    linear_combination rel.2.2
  rw [←identity] at product
  have positive := nonneg_of_mul_nonneg_right product (show 0<1+k c s d t by linarith only [rel.1])
  have difference : k c s d t*(1-c)+(13/50)*delta c s d t*s-(1-d)=
      k c s d t-1+(37/50)*s*h := by
    dsimp [k,delta,h]
    linear_combination -d*cn.2.2
  nlinarith only [endpoint,positive,difference]

end
end N12Compact.C1092MPPMAllNonpositive.TripleScalars
