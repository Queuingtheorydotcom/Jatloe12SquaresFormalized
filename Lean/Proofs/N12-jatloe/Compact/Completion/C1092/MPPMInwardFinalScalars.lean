import Compact.Completion.C1092.WallProfileScalars
import Compact.Geometry.C977CornerCubic

/-! Shared continuous predecessor estimates for CENTERED-INWARD-OIOI
and OPPOSED-MISSING-INWARD. All normal intervals are closed; the sharp
f/g comparison retains the equality at half-angle 1/3. -/
namespace N12Compact.C1092MPPMInwardFinal
open C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

def f (b r : ℝ) : ℝ := (b+r-1)^2/2
def g (b r : ℝ) : ℝ := b^2-b+r

theorem fg_bounds {b r : ℝ} (bn : Normal b r) :
    0≤f b r ∧ f b r≤(2/11)*g b r ∧ g b r≤1/2 ∧ r-r^2/2≤g b r := by
  have bounds := normal_bounds bn
  have bp : 0≤b := by linarith only [bounds.1]
  have data := quarter_data b r bp bn.1 bn.2.2
  let w := half b r
  have wn : 0≤w := data.1
  have wu : w≤1 := data.2.1
  have den : 0<1+w^2 := by nlinarith only [sq_nonneg w]
  have bf : b=(1-w^2)/(1+w^2) :=
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.1])
  have rf : r=2*w/(1+w^2) :=
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.2])
  have factor :
      11*(1+w^2)^2*((2/11)*g b r-f b r)=2*w*(1-3*w)^2*(2-w) := by
    rw [bf,rf]
    dsimp [f,g]
    field_simp [den.ne']
    <;> ring
  have positive := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) wn) (sq_nonneg (1-3*w)))
    (show 0≤2-w by linarith only [wu])
  have ratio : f b r≤(2/11)*g b r := by
    have scale : 0<11*(1+w^2)^2 := mul_pos (by norm_num) (pow_pos den 2)
    have nonnegative : 0≤11*(1+w^2)^2*((2/11)*g b r-f b r) := by
      rw [factor]; exact positive
    have result := nonneg_of_mul_nonneg_right nonnegative scale
    linarith only [result]
  have upper := mul_nonneg (sub_nonneg.mpr bn.2.1)
    (show 0≤1-(b+r)/2 by linarith only [bounds.2.2.2.2.2])
  refine ⟨by exact div_nonneg (sq_nonneg _) (by norm_num),ratio,?_,?_⟩
  · dsimp [g]
    nlinarith only [upper,bn.2.2]
  · dsimp [g]
    nlinarith only [sq_nonneg (1-b),bn.2.2]

theorem g_positive {b r : ℝ} (bn : Normal b r) (rp : 0<r) : 0<g b r := by
  have bounds := normal_bounds bn
  have product := mul_nonneg bn.1
    (show 0≤1-r by linarith only [bounds.2.2.2.1])
  nlinarith only [(fg_bounds bn).2.2.2,product,rp]

theorem g_lower {b r : ℝ} (bn : Normal b r) (low : 8/17≤r) : 104/289≤g b r := by
  have bounds := normal_bounds bn
  have monotone := mul_nonneg (sub_nonneg.mpr low)
    (show 0≤1-(r+8/17)/2 by linarith only [bounds.2.2.2.1])
  nlinarith only [monotone,(fg_bounds bn).2.2.2]

/-- The actual predecessor's two simultaneous faces imply a strict
quarter half-angle threshold, without a derivative or angle sample. -/
theorem predecessor_angle {b r : ℝ} (bn : Normal b r) (width : 1<r+(3/5)*b) :
    1/4<half b r ∧ b<15/17 ∧ 8/17<r := by
  have bounds := normal_bounds bn
  have data := quarter_data b r (by linarith only [bounds.1]) bn.1 bn.2.2
  let w := half b r
  have wn : 0≤w := data.1
  have wu : w≤1 := data.2.1
  have den : 0<1+w^2 := by nlinarith only [sq_nonneg w]
  have identity : (1+w^2)*(r+(3/5)*b-1)=(2/5)*(1-w)*(4*w-1) := by
    nlinarith only [data.2.2.2.1,data.2.2.2.2]
  have positive := mul_pos den (sub_pos.mpr width)
  have threshold : 1/4<w := by
    apply lt_of_not_ge
    intro no
    have bad := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤1-w by linarith only [wu])
      (show 4*w-1≤0 by linarith only [no])
    nlinarith only [positive,identity,bad]
  have square := mul_pos (show 0<w-1/4 by linarith only [threshold])
    (show 0<w+1/4 by linarith only [wn])
  have cosine : b<15/17 := by
    apply lt_of_not_ge
    intro no
    have product := mul_nonneg den.le (show 0≤b-15/17 by linarith only [no])
    nlinarith only [data.2.2.2.1,square,product]
  have sine : 8/17<r := by
    have product := mul_pos (show 0<w-1/4 by linarith only [threshold])
      (show 0<4-w by linarith only [wu])
    apply lt_of_not_ge
    intro no
    have bad := mul_nonneg den.le (show 0≤8/17-r by linarith only [no])
    nlinarith only [data.2.2.2.2,product,bad]
  exact ⟨threshold,cosine,sine⟩

theorem relative_order {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (order : half c s<half b r) : 0<c*r-s*b := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cd := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  have bd := quarter_data b r (by linarith only [bb.1]) bn.1 bn.2.2
  let x := half c s
  let w := half b r
  have xp : 0<1+x^2 := by nlinarith only [sq_nonneg x]
  have wp : 0<1+w^2 := by nlinarith only [sq_nonneg w]
  have cf : c=(1-x^2)/(1+x^2) :=
    (eq_div_iff xp.ne').mpr (by nlinarith only [cd.2.2.2.1])
  have sf : s=2*x/(1+x^2) :=
    (eq_div_iff xp.ne').mpr (by nlinarith only [cd.2.2.2.2])
  have bf : b=(1-w^2)/(1+w^2) :=
    (eq_div_iff wp.ne').mpr (by nlinarith only [bd.2.2.2.1])
  have rf : r=2*w/(1+w^2) :=
    (eq_div_iff wp.ne').mpr (by nlinarith only [bd.2.2.2.2])
  have identity : (1+x^2)*(1+w^2)*(c*r-s*b)=2*(w-x)*(1+w*x) := by
    rw [cf,sf,bf,rf]
    field_simp [xp.ne',wp.ne']
    <;> ring
  have last : 0<1+w*x := by
    have product := mul_nonneg bd.1 cd.1
    linarith only [product]
  have positive := mul_pos (mul_pos (by norm_num : (0:ℝ)<2) (sub_pos.mpr order)) last
  have scaled : 0<(1+x^2)*(1+w^2)*(c*r-s*b) := by rw [identity]; exact positive
  exact pos_of_mul_pos_right scaled (mul_pos xp wp).le

/-- A strict predecessor support bound gives a strict angle bound even
at the isolated equality of the sharp f/g certificate. -/
theorem centered_height {c s b r H : ℝ} (cn : Normal c s) (bn : Normal b r)
    (rp : 0<r) (hp : 0<H) (bound : H<c*f b r-s*g b r) :
    H<c/11-s/2 ∧ 11*s<2*c := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have fg := fg_bounds bn
  have gp := g_positive bn rp
  have compare := mul_le_mul_of_nonneg_left fg.2.1 cp.le
  have coefficient : 0<(2/11)*c-s := by
    apply lt_of_not_ge
    intro no
    have bad := mul_nonpos_of_nonpos_of_nonneg no gp.le
    nlinarith only [bound,hp,compare,bad]
  have ceiling := mul_le_mul_of_nonneg_left fg.2.2.1 coefficient.le
  exact ⟨by nlinarith only [bound,compare,ceiling],by linarith only [coefficient]⟩

theorem centered_cap {c s : ℝ} (cn : Normal c s) (small : half c s<21/100) :
    0≤(7/50)*c+s/2 ∧ (7/50)*c+s/2<33/100 := by
  have cb := normal_bounds cn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  let x := half c s
  have xn : 0≤x := data.1
  have den : 0<1+x^2 := by nlinarith only [sq_nonneg x]
  have remainder := mul_nonneg
    (show 0≤21/100-x by linarith only [small])
    (show 0≤1-(47/100)*(x+21/100) by linarith only [small,xn])
  have polynomial : 0<19/100-x+(47/100)*x^2 := by
    nlinarith only [remainder]
  have identity :
      (1+x^2)*(33/100-((7/50)*c+s/2))=19/100-x+(47/100)*x^2 := by
    nlinarith only [data.2.2.2.1,data.2.2.2.2]
  constructor
  · linarith only [cb.1,cn.1]
  · have positive : 0<(1+x^2)*(33/100-((7/50)*c+s/2)) := by
      rw [identity]; exact polynomial
    have result := pos_of_mul_pos_right positive den.le
    linarith only [result]

/-- The full predecessor-normal margin needs only a rational bound for
the canonical sum. Its weaker 1/20 margin suffices on the entire interval. -/
theorem predecessor_margin {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (small : half c s<21/100) :
    0<1-b-r+(c*b+s*r)*(1-(7/50)*c-s/2) := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cap := centered_cap cn small
  let D := 1-(7/50)*c-s/2
  let B := 1-c*D
  let R := 1-s*D
  have dn : 0≤D := by dsimp [D]; linarith only [cap.2]
  have du : D≤1 := by dsimp [D]; linarith only [cap.1]
  have bc := mul_le_mul_of_nonneg_left du (by linarith only [cb.1] : 0≤c)
  have rs := mul_le_mul_of_nonneg_left du cn.1
  have Bn : 0≤B := by dsimp [B]; linarith only [bc,cb.2.1]
  have Rn : 0≤R := by dsimp [R]; linarith only [rs,cb.2.2.2.1]
  have sumLower := mul_le_mul_of_nonneg_right cb.2.2.2.2.1 dn
  have dl : 67/100<D := by dsimp [D]; linarith only [cap.2]
  have sumCap : B+R<133/100 := by dsimp [B,R]; nlinarith only [sumLower,dl]
  have ordered := mul_nonneg (sub_nonneg.mpr cn.2.1) dn
  have tangent := mul_nonpos_of_nonpos_of_nonneg
    (show B-R≤0 by dsimp [B,R]; nlinarith only [ordered]) (sub_nonneg.mpr bn.2.1)
  have radial := mul_le_mul_of_nonneg_left bb.2.2.2.2.2 (add_nonneg Bn Rn)
  have bound : B*b+R*r<1 := by nlinarith only [tangent,radial,sumCap]
  dsimp [B,R,D] at bound
  nlinarith only [bound]

theorem centered_small {c s : ℝ} (cn : Normal c s) (sp : 0<s) (angle : 11*s<2*c) :
    49/50<c ∧ s<9/50 ∧ half c s<91/1000 := by
  have cb := normal_bounds cn
  have square := mul_pos (show 0<2*c-11*s by linarith only [angle])
    (show 0<2*c+11*s by linarith only [cb.1,sp])
  have close : 49/50<c := by
    apply lt_of_not_ge
    intro no
    have bad := mul_nonneg (show 0≤49/50-c by linarith only [no])
      (show 0≤49/50+c by linarith only [cb.1])
    nlinarith only [square,bad,cn.2.2]
  have sine : s<9/50 := by
    apply lt_of_not_ge
    intro no
    have bad := mul_nonneg (show 0≤s-9/50 by linarith only [no])
      (show 0≤s+9/50 by linarith only [sp])
    nlinarith only [square,bad,cn.2.2]
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  let x := half c s
  have den : 0<1+x^2 := by nlinarith only [sq_nonneg x]
  have weighted := mul_pos den (show 0<2*c-11*s by linarith only [angle])
  have halfBound : x<91/1000 := by
    apply lt_of_not_ge
    intro no
    have bad := mul_nonneg (show 0≤x-91/1000 by linarith only [no])
      (show 0≤x+91/1000 by linarith only [data.1])
    nlinarith only [weighted,data.2.2.2.1,data.2.2.2.2,bad,no]
  exact ⟨close,sine,halfBound⟩

end
#print axioms fg_bounds
#print axioms centered_height
end N12Compact.C1092MPPMInwardFinal
