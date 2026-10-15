import Compact.Completion.C1092.MPPMCrosspointCentralEndpointE

/-! STEEP-POSITIVE-CENTRAL-SCALAR §4. On each of the three angle pieces
G00 is linear in the boundary unit vector with a nonnegative horizontal
coefficient. Exact circle-chord interpolation therefore replaces the
sine-interpolation/ODE step on the complete closed quadrant. -/
namespace N12Compact.C1092MPPMCrosspointSupport.Central
open C977CornerCubic C977CornerSectorBounds
open C1092MPPMPositiveRetainingSteep.Scalars
set_option Elab.async false
noncomputable section

private def coordinateValue (c s d t : ℝ) : ℝ :=
  d*(1-c-(543/500)*s)+s*(1-(11/25)*t)

private theorem coordinate_lower {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤s) : 1/3125≤coordinateValue c s d t := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have arc := steep_bounds cn steep
  have sp : 0<s := by linarith only [steep]
  have dp : 0<d := by linarith only [eb.1]
  have product := mul_nonneg cn.1
    (show 0≤4*s-3*c by linarith only [steep,arc.1])
  have span : c+s/3≤1 := by
    nlinarith only [product,cn.2.2,sq_nonneg (c+s/3-1)]
  have gap := mul_nonneg dp.le
    (show 0≤1-c-(143/500)*s by linarith only [span,cn.1])
  have cross := mul_nonneg cn.1 en.1
  have bound : (4/5)*d+t/2<19/20 := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg
      (show 0≤(4/5)*d+t/2-19/20 by linarith only [bad])
      (show 0≤(4/5)*d+t/2+19/20 by linarith only [bad])
    have square := sq_nonneg (d/2-(4/5)*t)
    nlinarith only [product,square,en.2.2]
  have weight := mul_pos sp
    (show 0<19/20-(4/5)*d-t/2 by linarith only [bound])
  dsimp [coordinateValue]
  nlinarith only [gap,cross,weight,steep]

private def sign (b : Bool) : ℝ := if b then 1 else -1
private def piece (b e : Bool) (c s d t h r : ℝ) : ℝ :=
  (k c s d t*(h+r)+d*(kC c s h r+sign b*deltaC c s h r)+
    s*(kE d t h r+sign e*deltaE d t h r))/2-
      2*k c s d t-d*C0 s-s*E0 d t
private def coefficientX (b e : Bool) (c s d t : ℝ) : ℝ :=
  (k c s d t+d*(c-sign b*s)+s*(d-sign e*t))/2
private def coefficientY (b e : Bool) (c s d t : ℝ) : ℝ :=
  (k c s d t+d*(s+sign b*c)+s*(t+sign e*d))/2
private def constant (c s d t : ℝ) : ℝ := -2*k c s d t-d*C0 s-s*E0 d t

private theorem piece_form (b e : Bool) (c s d t h r : ℝ) :
    piece b e c s d t h r=constant c s d t+
      coefficientX b e c s d t*h+coefficientY b e c s d t*r := by
  dsimp [piece,constant,coefficientX,coefficientY,kC,kE,deltaC,deltaE]
  ring

private theorem sign_abs (b : Bool) (x : ℝ) : sign b*x≤|x| := by
  cases b
  · simpa only [sign,Bool.false_eq_true,if_false,neg_one_mul] using neg_le_abs x
  · simpa only [sign,if_true,one_mul] using le_abs_self x

private theorem piece_below {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (b e : Bool) (h r : ℝ) : piece b e c s d t h r≤G00 c s d t h r := by
  have dp : 0≤d := by linarith only [(normal_bounds en).1]
  have first := mul_le_mul_of_nonneg_left (sign_abs b (deltaC c s h r)) dp
  have last := mul_le_mul_of_nonneg_left (sign_abs e (deltaE d t h r)) cn.1
  dsimp [piece,G00]
  linarith only [first,last]

private theorem coefficient_nonnegative {c s d t : ℝ}
    (cn : Normal c s) (en : Normal d t) (b e : Bool) :
    0≤coefficientX b e c s d t := by
  have cp : 0≤c := by linarith only [(normal_bounds cn).1]
  have dp : 0≤d := by linarith only [(normal_bounds en).1]
  have first : 0≤c-sign b*s := by
    cases b <;> norm_num only [sign,Bool.false_eq_true,if_false,if_true,
      neg_one_mul,one_mul] <;> linarith only [cn.1,cn.2.1,cp]
  have last : 0≤d-sign e*t := by
    cases e <;> norm_num only [sign,Bool.false_eq_true,if_false,if_true,
      neg_one_mul,one_mul] <;> linarith only [en.1,en.2.1,dp]
  have p0 := mul_nonneg cp dp
  have p1 := mul_nonneg cn.1 en.1
  have p2 := mul_nonneg dp first
  have p3 := mul_nonneg cn.1 last
  dsimp [coefficientX,k]
  nlinarith only [p0,p1,p2,p3]

private theorem piece_arc {c s d t h r H R C S : ℝ}
    (cn : Normal c s) (en : Normal d t) (bn : Quarter h r)
    (first : Quarter H R) (last : Quarter C S)
    (low : R≤r) (high : r≤S) (b e : Bool)
    (f0 : 1/3125≤piece b e c s d t H R)
    (f1 : 1/3125≤piece b e c s d t C S) :
    1/3125≤G00 c s d t h r := by
  have left : 0≤(constant c s d t-1/3125)+
      coefficientX b e c s d t*H+coefficientY b e c s d t*R := by
    rw [piece_form] at f0
    linarith only [f0]
  have right : 0≤(constant c s d t-1/3125)+
      coefficientX b e c s d t*C+coefficientY b e c s d t*S := by
    rw [piece_form] at f1
    linarith only [f1]
  have bound := CommonCases.UnitCircleChord.linear_nonnegative
    first.cosine last.cosine bn.cosine first.unit last.unit bn.unit low high
    (coefficient_nonnegative cn en b e) left right
  have form := piece_form b e c s d t h r
  have comparison := piece_below cn en b e h r
  linarith only [bound,form,comparison]

private theorem coordinate_zero {c s d t : ℝ} (cn : Normal c s) (en : Normal d t) :
    piece false false c s d t 1 0=coordinateValue c s d t := by
  dsimp [piece,sign,k,kC,kE,deltaC,deltaE,C0,E0,coordinateValue]
  ring

private theorem coordinate_vertical {c s d t : ℝ} (cn : Normal c s) (en : Normal d t) :
    piece true true c s d t 0 1=coordinateValue c s d t := by
  dsimp [piece,sign,k,kC,kE,deltaC,deltaE,C0,E0,coordinateValue]
  ring

private theorem at_C_up {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (order : t≤s) (b : Bool) : G00 c s d t c s=piece b true c s d t c s := by
  have cp : 0≤c := by linarith only [(normal_bounds cn).1]
  have dp : 0≤d := by linarith only [(normal_bounds en).1]
  have de : 0≤deltaE d t c s := by
    exact CommonCases.UnitCircleChord.cross_order dp cp en.2.2 cn.2.2 en.1 cn.1 order
  have dc : deltaC c s c s=0 := by dsimp [deltaC]; ring
  dsimp [G00,piece]
  rw [dc,abs_zero,abs_of_nonneg de]
  dsimp [sign]
  ring

private theorem at_C_down {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (order : s≤t) (b : Bool) : G00 c s d t c s=piece b false c s d t c s := by
  have cp : 0≤c := by linarith only [(normal_bounds cn).1]
  have dp : 0≤d := by linarith only [(normal_bounds en).1]
  have de : deltaE d t c s≤0 := by
    have cross := CommonCases.UnitCircleChord.cross_order cp dp cn.2.2 en.2.2 cn.1 en.1 order
    dsimp [deltaE]
    linarith only [cross]
  have dc : deltaC c s c s=0 := by dsimp [deltaC]; ring
  dsimp [G00,piece]
  rw [dc,abs_zero,abs_of_nonpos de]
  dsimp [sign]
  ring

private theorem at_E_up {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (order : s≤t) (e : Bool) : G00 c s d t d t=piece true e c s d t d t := by
  have cp : 0≤c := by linarith only [(normal_bounds cn).1]
  have dp : 0≤d := by linarith only [(normal_bounds en).1]
  have dc : 0≤deltaC c s d t :=
    CommonCases.UnitCircleChord.cross_order cp dp cn.2.2 en.2.2 cn.1 en.1 order
  have de : deltaE d t d t=0 := by dsimp [deltaE]; ring
  dsimp [G00,piece]
  rw [de,abs_zero,abs_of_nonneg dc]
  dsimp [sign]
  ring

private theorem at_E_down {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (order : t≤s) (e : Bool) : G00 c s d t d t=piece false e c s d t d t := by
  have cp : 0≤c := by linarith only [(normal_bounds cn).1]
  have dp : 0≤d := by linarith only [(normal_bounds en).1]
  have dc : deltaC c s d t≤0 := by
    have cross := CommonCases.UnitCircleChord.cross_order dp cp en.2.2 cn.2.2 en.1 cn.1 order
    dsimp [deltaC]
    linarith only [cross]
  have de : deltaE d t d t=0 := by dsimp [deltaE]; ring
  dsimp [G00,piece]
  rw [de,abs_zero,abs_of_nonpos dc]
  dsimp [sign]
  ring

/-- The full three-angle central/central scalar, with its exact sharp
lower bound. All alignments and both coordinate endpoints are included. -/
theorem g00_lower {c s d t h r : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤s) (bn : Quarter h r) : 1/3125≤G00 c s d t h r := by
  have cp : 0≤c := by linarith only [(normal_bounds cn).1]
  have dp : 0≤d := by linarith only [(normal_bounds en).1]
  have cq : Quarter c s := ⟨cp,cn.1,cn.2.2⟩
  have eq : Quarter d t := ⟨dp,en.1,en.2.2⟩
  have zq : Quarter 1 0 := by constructor <;> norm_num
  have vq : Quarter 0 1 := by constructor <;> norm_num
  have ru : r≤1 := by
    nlinarith only [bn.unit,sq_nonneg h,sq_nonneg (r-1)]
  have zero : 1/3125≤piece false false c s d t 1 0 := by
    rw [coordinate_zero cn en]
    exact coordinate_lower cn en steep
  have vertical : 1/3125≤piece true true c s d t 0 1 := by
    rw [coordinate_vertical cn en]
    exact coordinate_lower cn en steep
  have central := aligned_C cn en steep
  have recipient := aligned_E cn en steep
  by_cases order : t≤s
  · have cc0 : 1/3125≤piece false true c s d t c s := by
      rw [←at_C_up cn en order false]; exact central
    have cc1 : 1/3125≤piece true true c s d t c s := by
      rw [←at_C_up cn en order true]; exact central
    have ee0 : 1/3125≤piece false false c s d t d t := by
      rw [←at_E_down cn en order false]; exact recipient
    have ee1 : 1/3125≤piece false true c s d t d t := by
      rw [←at_E_down cn en order true]; exact recipient
    by_cases low : r≤t
    · exact piece_arc cn en bn zq eq bn.sine low false false zero ee0
    · have low : t≤r := (lt_of_not_ge low).le
      by_cases high : r≤s
      · exact piece_arc cn en bn eq cq low high false true ee1 cc0
      · exact piece_arc cn en bn cq vq (lt_of_not_ge high).le ru true true cc1 vertical
  · have order : s≤t := (lt_of_not_ge order).le
    have cc0 : 1/3125≤piece false false c s d t c s := by
      rw [←at_C_down cn en order false]; exact central
    have cc1 : 1/3125≤piece true false c s d t c s := by
      rw [←at_C_down cn en order true]; exact central
    have ee0 : 1/3125≤piece true false c s d t d t := by
      rw [←at_E_up cn en order false]; exact recipient
    have ee1 : 1/3125≤piece true true c s d t d t := by
      rw [←at_E_up cn en order true]; exact recipient
    by_cases low : r≤s
    · exact piece_arc cn en bn zq cq bn.sine low false false zero cc0
    · have low : s≤r := (lt_of_not_ge low).le
      by_cases high : r≤t
      · exact piece_arc cn en bn cq eq low high true false cc1 ee0
      · exact piece_arc cn en bn eq vq (lt_of_not_ge high).le ru true true ee1 vertical

end
#print axioms g00_lower
end N12Compact.C1092MPPMCrosspointSupport.Central
