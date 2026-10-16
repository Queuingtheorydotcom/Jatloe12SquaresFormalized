import Compact.Completion.C1092.MPPMCrosspointBoundaryG01High
import Compact.Completion.C1092.MPPMCrosspointBoundaryAligned
import Compact.Completion.C1092.MPPMCrosspointBoundaryHalf
import Compact.Completion.C1092.MPPMCrosspointCentralEndpointE

/-! The complete G01 inequality. Below the diagonal, four polynomial
pieces lie below the literal support expression. Exact sine interpolation
joins the zero, E-aligned, C-aligned and diagonal endpoints. Above the
diagonal the separate rational Bernstein proof covers the whole arc. -/
namespace N12Compact.C1092MPPMCrosspointSupport
open C977CornerCubic C977CornerSectorBounds C1092ShallowPositiveScalars
set_option Elab.async false
noncomputable section

private def sg (b : Bool) : ℝ := if b then 1 else -1
private def support (e : Bool) (d t h r : ℝ) : ℝ :=
  if e then kE d t h r*E0 d t+deltaE d t h r*(-d-(2/5)*t)
  else kE d t h r*E0 d t-(d/2)*deltaE d t h r
private def piece (b e : Bool) (c s d t h r : ℝ) : ℝ :=
  (kC c s h r*(h+r)+h*(kC c s h r+sg b*deltaC c s h r)+s)/2-
    2*kC c s h r-h*C0 s-s*support e d t h r
private def qa (b : Bool) (c s : ℝ) : ℝ := if b then c-s else c
private def qb (b : Bool) (c s : ℝ) : ℝ := if b then c+s else s
private def ex (e : Bool) (d t : ℝ) : ℝ :=
  if e then P d t else 1-t^2-(3/50)*d*t-d
private def ey (e : Bool) (d t : ℝ) : ℝ :=
  if e then -Q d t else d*t-(3/50)*t^2-t-1/2
private def ax (e : Bool) (c s d t : ℝ) : ℝ := 1-2*c-(543/500)*s-s*ex e d t
private def ay (e : Bool) (s d t : ℝ) : ℝ := -2*s-s*ey e d t

private theorem support_form (e : Bool) (d t h r : ℝ) (en : Normal d t) :
    support e d t h r=ex e d t*h+ey e d t*r := by
  cases e
  · dsimp [support,ex,ey,kE,deltaE,E0]
    linear_combination (h-r/2)*en.2.2
  · dsimp [support,ex,ey,kE,deltaE,E0,P,Q]
    linear_combination (h-r)*en.2.2

private theorem support_up (d t h r : ℝ) (order : 0≤deltaE d t h r) :
    support true d t h r=FE d t h r := by simp only [support,FE,ite_true,ite_eq_left order]

private theorem support_down (d t h r : ℝ) (order : deltaE d t h r≤0) :
    support false d t h r=FE d t h r := by
  by_cases branch : 0≤deltaE d t h r
  · have zero : deltaE d t h r=0 := le_antisymm order branch
    simp only [support,Bool.false_eq_true,FE,zero,zero_mul,mul_zero,
      add_zero,sub_zero,ite_self]
  · simp only [support,Bool.false_eq_true,ite_false,FE,ite_eq_right branch]

private theorem support_above (e : Bool) (d t h r : ℝ) (en : Normal d t) :
    FE d t h r≤support e d t h r := by
  have dp : 0≤d := by linarith only [(normal_bounds en).1]
  have coef : 0≤d/2+(2/5)*t := by linarith only [dp,en.1]
  by_cases order : 0≤deltaE d t h r
  · cases e
    · have product := mul_nonneg order coef
      simp only [FE,ite_eq_left order,support,Bool.false_eq_true,ite_false]
      nlinarith only [product]
    · exact le_of_eq (support_up d t h r order).symm
  · have order' : deltaE d t h r≤0 := (lt_of_not_ge order).le
    cases e
    · exact le_of_eq (support_down d t h r order').symm
    · have product := mul_nonpos_of_nonneg_of_nonpos coef order'
      simp only [FE,ite_eq_right order,support,ite_true]
      nlinarith only [product]

private theorem piece_below (b e : Bool) (c s d t h r : ℝ)
    (cn : Normal c s) (en : Normal d t) (hn : 0≤h) :
    piece b e c s d t h r≤G01 c s d t h r := by
  have absbound : sg b*deltaC c s h r≤|deltaC c s h r| := by
    cases b
    · simpa [sg] using neg_le_abs (deltaC c s h r)
    · simpa [sg] using le_abs_self (deltaC c s h r)
  have first := mul_le_mul_of_nonneg_left absbound hn
  have last := mul_le_mul_of_nonneg_left (support_above e d t h r en) cn.1
  dsimp [piece,G01]
  linarith only [first,last]

private theorem piece_exact (b e : Bool) (c s d t h r : ℝ)
    (central : sg b*deltaC c s h r=|deltaC c s h r|)
    (eastern : support e d t h r=FE d t h r) :
    piece b e c s d t h r=G01 c s d t h r := by
  dsimp [piece,G01]
  rw [central,eastern]

private theorem piece_form (b e : Bool) (c s d t h r : ℝ)
    (en : Normal d t) (q : Quarter h r) :
    piece b e c s d t h r=qa b c s*h^2+qb b c s*h*r+s+
      ax e c s d t*h+ay e s d t*r := by
  have form := support_form e d t h r en
  dsimp only [piece]
  rw [form]
  cases b <;> dsimp [qa,qb,sg,ax,ay,kC,deltaC,C0] <;>
    linear_combination (s/2)*q.unit

private theorem piece_half (b e : Bool) (c s d t H R : ℝ)
    (en : Normal d t) (hn : Normal H R) :
    QuadraticArc.value (qa b c s) (qb b c s) s (ax e c s d t) (ay e s d t)
      (half H R)=piece b e c s d t H R := by
  have hd := normal_half hn
  have hb := normal_bounds hn
  have form := piece_form b e c s d t H R en
    ⟨by linarith only [hb.1],hn.1,hn.2.2⟩
  dsimp [QuadraticArc.value]
  rw [hd.2.2.2.1,hd.2.2.2.2]
  exact form.symm

private theorem low_arc (e : Bool) (c s d t h r H R C S : ℝ)
    (cn : Normal c s) (en : Normal d t) (bn : Normal h r)
    (ln : Normal H R) (un : Normal C S)
    (left : R≤r) (right : r≤S) (upper : S≤s)
    (first : 0≤piece false e c s d t H R) (last : 0≤piece false e c s d t C S) :
    0≤G01 c s d t h r := by
  have pd := normal_half cn
  have ld := normal_half ln
  have bd := normal_half bn
  have ud := normal_half un
  have rb := rho_bounds
  have qp := half_order ln cn (le_trans left (le_trans right upper))
  have zp := half_order bn cn (le_trans right upper)
  have rp := half_order un cn upper
  have rem := QuadraticArc.central_remainder (half c s) (half H R) (half h r) (half C S)
    pd.1 (le_trans pd.2.1 (by linarith only [rb.2.1])) pd.2.2.1
    ld.1 qp bd.1 zp ud.1 rp
  rw [pd.2.2.2.1,pd.2.2.2.2] at rem
  have result := QuadraticArc.nonnegative c s s (ax e c s d t) (ay e s d t)
    (half H R) (half h r) (half C S) ld.1 (half_order ln bn left)
    (half_order bn un right) rem
    (by simpa only [←piece_half false e c s d t H R en ln,qa,qb,Bool.false_eq_true,ite_false] using first)
    (by simpa only [←piece_half false e c s d t C S en un,qa,qb,Bool.false_eq_true,ite_false] using last)
  have result' : 0≤piece false e c s d t h r := by
    simpa only [←piece_half false e c s d t h r en bn,qa,qb,Bool.false_eq_true,ite_false] using result
  exact le_trans result' (piece_below false e c s d t h r cn en
    (by linarith only [(normal_bounds bn).1]))

private theorem middle_arc (e : Bool) (c s d t h r H R C S : ℝ)
    (cn : Normal c s) (en : Normal d t) (steep : 3/5≤s) (bn : Normal h r)
    (ln : Normal H R) (un : Normal C S)
    (lower : s≤R) (left : R≤r) (right : r≤S)
    (first : 0≤piece true e c s d t H R) (last : 0≤piece true e c s d t C S) :
    0≤G01 c s d t h r := by
  have ld := normal_half ln
  have bd := normal_half bn
  have ud := normal_half un
  have rb := rho_bounds
  have cs := steep_bounds cn steep
  have start := steep_half cn steep
  have ql := le_trans start (half_order cn ln lower)
  have zl := le_trans ql (half_order ln bn left)
  have rl := le_trans zl (half_order bn un right)
  have rem := QuadraticArc.middle_remainder (c-s) (c+s) s
    (half H R) (half h r) (half C S)
    (sub_nonneg.mpr cn.2.1) (by linarith only [cs.1,steep]) cs.2.2.1 cn.1 cs.2.1.le
    ql (le_trans ld.2.1 (by linarith only [rb.2.1]))
    zl (le_trans bd.2.1 (by linarith only [rb.2.1]))
    rl (le_trans ud.2.1 (by linarith only [rb.2.1]))
  have result := QuadraticArc.nonnegative (c-s) (c+s) s (ax e c s d t) (ay e s d t)
    (half H R) (half h r) (half C S) ld.1 (half_order ln bn left)
    (half_order bn un right) rem
    (by simpa only [←piece_half true e c s d t H R en ln,qa,qb,ite_true] using first)
    (by simpa only [←piece_half true e c s d t C S en un,qa,qb,ite_true] using last)
  have result' : 0≤piece true e c s d t h r := by
    simpa only [←piece_half true e c s d t h r en bn,qa,qb,ite_true] using result
  exact le_trans result' (piece_below true e c s d t h r cn en
    (by linarith only [(normal_bounds bn).1]))

private theorem at_C (b e : Bool) (c s d t : ℝ) (cn : Normal c s)
    (eastern : support e d t c s=FE d t c s) :
    piece b e c s d t c s=alignedBoundary c s d t := by
  have zero : deltaC c s c s=0 := by dsimp [deltaC]; ring
  have self : kC c s c s=1 := by dsimp [kC]; nlinarith only [cn.2.2]
  dsimp [piece]
  rw [zero,self,eastern]
  dsimp [alignedBoundary,C0]
  ring

private theorem at_E (b e : Bool) (c s d t : ℝ) (en : Normal d t)
    (central : sg b*deltaC c s d t=|deltaC c s d t|) :
    piece b e c s d t d t=G00 c s d t d t := by
  have zero : deltaE d t d t=0 := by dsimp [deltaE]; ring
  have self : kE d t d t=1 := by dsimp [kE]; nlinarith only [en.2.2]
  have eastern : support e d t d t=E0 d t := by
    cases e <;> simp [support,zero,self]
  dsimp [piece,G00]
  rw [central,eastern,zero,self,abs_zero]
  dsimp [k,kC]
  ring

private theorem zero_endpoint (c s d t : ℝ) (cn : Normal c s)
    (en : Normal d t) (steep : 3/5≤s) : 0≤piece false false c s d t 1 0 := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cs := steep_bounds cn steep
  have product := mul_nonneg cn.1 (show 0≤4*s-3*c by linarith only [steep,cs.1])
  have span : c+s/3≤1 := by
    nlinarith only [product,cn.2.2,sq_nonneg (c+s/3-1)]
  have first := mul_nonneg (show 0≤d by linarith only [eb.1])
    (show 0≤1-d by linarith only [eb.2.1])
  have last := mul_nonneg (show 0≤d by linarith only [eb.1]) en.1
  have extra := mul_nonneg cn.1
    (show 0≤d*(1-d)+(3/50)*d*t by nlinarith only [first,last])
  have identity : piece false false c s d t 1 0=
      1-c-(43/500)*s+s*(d*(1-d)+(3/50)*d*t) := by
    dsimp [piece,sg,support,kC,deltaC,kE,deltaE,C0,E0]
    ring
  nlinarith only [identity,span,extra,cn.1]

theorem G01_nonnegative (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (q : Quarter h r) :
    0≤G01 c s d t h r := by
  by_cases high : h≤r
  · exact G01_high_nonnegative c s d t h r cn steep en q high
  have bn : Normal h r := ⟨q.sine,(lt_of_not_ge high).le,q.unit⟩
  have cp : 0≤c := by linarith only [(normal_bounds cn).1]
  have dp : 0≤d := by linarith only [(normal_bounds en).1]
  let v := Real.sqrt 2/2
  have vn : Normal v v := by
    refine ⟨by dsimp [v]; positivity,le_rfl,?_⟩
    dsimp [v]
    nlinarith only [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
  have vq : Quarter v v := ⟨vn.1,vn.1,vn.2.2⟩
  have rv : r≤v := by
    have hb := normal_bounds bn
    have product := mul_nonneg (sub_nonneg.mpr bn.2.1)
      (show 0≤h+r by linarith only [hb.1,bn.1])
    apply le_of_not_gt
    intro bad
    have strict := mul_pos (sub_pos.mpr bad) (show 0<r+v by linarith only [bad,vn.1])
    nlinarith only [strict,product,bn.2.2,vn.2.2]
  have zeroNormal : Normal 1 0 := by norm_num [Normal]
  have zero := zero_endpoint c s d t cn en steep
  have dcV : 0≤deltaC c s v v := by
    have product := mul_nonneg (sub_nonneg.mpr cn.2.1) vn.1
    dsimp [deltaC]; nlinarith only [product]
  have deV : 0≤deltaE d t v v := by
    have product := mul_nonneg (sub_nonneg.mpr en.2.1) vn.1
    dsimp [deltaE]; nlinarith only [product]
  have diagonal : 0≤piece true true c s d t v v := by
    rw [piece_exact true true c s d t v v
      (by simp only [sg,ite_true,one_mul,abs_of_nonneg dcV]) (support_up d t v v deV)]
    exact G01_high_nonnegative c s d t v v cn steep en vq le_rfl
  have central := (alignedBoundary_positive cn en steep).le
  have eastern : 0≤G00 c s d t d t := by linarith only [Central.aligned_E cn en steep]
  by_cases order : t≤s
  · have cross := CommonCases.UnitCircleChord.cross_order dp cp en.2.2 cn.2.2 en.1 cn.1 order
    have deC : 0≤deltaE d t c s := cross
    have dcE : deltaC c s d t≤0 := by dsimp [deltaC]; nlinarith only [cross]
    have c0 : 0≤piece false true c s d t c s := by
      rw [at_C false true c s d t cn (support_up d t c s deC)]; exact central
    have c1 : 0≤piece true true c s d t c s := by
      rw [at_C true true c s d t cn (support_up d t c s deC)]; exact central
    have e0 : 0≤piece false false c s d t d t := by
      rw [at_E false false c s d t en (by simp only [sg,Bool.false_eq_true,ite_false,
        neg_one_mul,abs_of_nonpos dcE])]; exact eastern
    have e1 : 0≤piece false true c s d t d t := by
      rw [at_E false true c s d t en (by simp only [sg,Bool.false_eq_true,ite_false,
        neg_one_mul,abs_of_nonpos dcE])]; exact eastern
    by_cases low : r≤t
    · exact low_arc false c s d t h r 1 0 d t cn en bn zeroNormal en q.sine low order zero e0
    · have low : t≤r := (lt_of_not_ge low).le
      by_cases middle : r≤s
      · exact low_arc true c s d t h r d t c s cn en bn en cn low middle le_rfl e1 c0
      · exact middle_arc true c s d t h r c s v v cn en steep bn cn vn le_rfl
          (lt_of_not_ge middle).le rv c1 diagonal
  · have order : s≤t := (lt_of_not_ge order).le
    have cross := CommonCases.UnitCircleChord.cross_order cp dp cn.2.2 en.2.2 cn.1 en.1 order
    have deC : deltaE d t c s≤0 := by dsimp [deltaE]; nlinarith only [cross]
    have dcE : 0≤deltaC c s d t := cross
    have c0 : 0≤piece false false c s d t c s := by
      rw [at_C false false c s d t cn (support_down d t c s deC)]; exact central
    have c1 : 0≤piece true false c s d t c s := by
      rw [at_C true false c s d t cn (support_down d t c s deC)]; exact central
    have e0 : 0≤piece true false c s d t d t := by
      rw [at_E true false c s d t en (by simp only [sg,ite_true,one_mul,abs_of_nonneg dcE])]
      exact eastern
    have e1 : 0≤piece true true c s d t d t := by
      rw [at_E true true c s d t en (by simp only [sg,ite_true,one_mul,abs_of_nonneg dcE])]
      exact eastern
    by_cases low : r≤s
    · exact low_arc false c s d t h r 1 0 c s cn en bn zeroNormal cn q.sine low le_rfl zero c0
    · have low : s≤r := (lt_of_not_ge low).le
      by_cases middle : r≤t
      · exact middle_arc false c s d t h r c s d t cn en steep bn cn en le_rfl low middle c1 e0
      · exact middle_arc true c s d t h r d t v v cn en steep bn en vn order
          (lt_of_not_ge middle).le rv e1 diagonal

#print axioms G01_nonnegative
end
end N12Compact.C1092MPPMCrosspointSupport
