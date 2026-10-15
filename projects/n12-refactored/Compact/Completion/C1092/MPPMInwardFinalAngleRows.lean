import Compact.Completion.C1092.MPPMInwardFinalAngleScalars

/-! The three positive-predecessor rows and both relative negative
rows in the centered angle proof. Exact polynomial remainders replace
all differentiations, on the same complete intervals. -/
namespace N12Compact.C1092MPPMInwardFinal
open C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

def angleFz (b r : ℝ) := (543/500)*b^2+(7/20)*r^2-(7/20)*b*r-b
def angleGz (b r : ℝ) := (7/20)*b^2+(92/125)*b*r-r
def angleFl (b r : ℝ) := (543/500)*b^2+(7/20)*b*r+(7/20)*r^2-b
def angleGl (b r : ℝ) := (7/20)*b^2-(92/125)*b*r+r

private theorem rational_frame {b r : ℝ} (bn : Normal b r) :
    b=(1-(half b r)^2)/(1+(half b r)^2) ∧ r=2*half b r/(1+(half b r)^2) := by
  have bb := normal_bounds bn
  have data := quarter_data b r (by linarith only [bb.1]) bn.1 bn.2.2
  have den : 0<1+(half b r)^2 := by nlinarith only [sq_nonneg (half b r)]
  constructor <;> apply (eq_div_iff den.ne').mpr <;>
    nlinarith only [data.2.2.2.1,data.2.2.2.2]

theorem angle_z_row {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (low : (2/5)*c≤s) : c*angleFz b r-s*angleGz b r≤0 := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0<c := by linarith only [cb.1]
  let w := half b r
  have wb := canonical_half_bounds bn
  have den : 0<1+w^2 := by nlinarith only [sq_nonneg w]
  have frames := rational_frame bn
  have bf : b=(1-w^2)/(1+w^2) := frames.1
  have rf : r=2*w/(1+w^2) := frames.2
  have w2 : w^2≤25/144 := by
    have product := mul_nonneg (show 0≤5/12-w by linarith only [wb.2])
      (show 0≤5/12+w by linarith only [wb.1])
    nlinarith only [product]
  have w3 : w^3≤125/1728 := by
    have product := mul_nonneg (show 0≤5/12-w by linarith only [wb.2]) (sq_nonneg w)
    nlinarith only [product,w2]
  have coefficient : 4865*w^3+5222*w^2≤1260 := by nlinarith only [w2,w3]
  have product := mul_nonneg wb.1 (sub_nonneg.mpr coefficient)
  have polynomial : 4865*w^4+5222*w^3-1230*w^2-1222*w-135<0 := by
    nlinarith only [product,wb.2,sq_nonneg w]
  have identity : 2500*(1+w^2)^2*(angleFz b r-(2/5)*angleGz b r)=
      4865*w^4+5222*w^3-1230*w^2-1222*w-135 := by
    dsimp [angleFz,angleGz]
    rw [bf,rf]
    change 2500*(1+w^2)^2*
      ((543/500)*((1-w^2)/(1+w^2))^2+(7/20)*(2*w/(1+w^2))^2-
        (7/20)*((1-w^2)/(1+w^2))*(2*w/(1+w^2))-(1-w^2)/(1+w^2)-
        (2/5)*((7/20)*((1-w^2)/(1+w^2))^2+(92/125)*((1-w^2)/(1+w^2))*(2*w/(1+w^2))-2*w/(1+w^2)))=_
    field_simp [den.ne']
    <;> ring
  have scaled : 2500*(1+w^2)^2*(angleFz b r-(2/5)*angleGz b r)<0 := by
    rw [identity]; exact polynomial
  have negative : angleFz b r-(2/5)*angleGz b r<0 := by
    apply lt_of_not_ge
    intro no
    have bad := mul_nonneg (show 0≤2500*(1+w^2)^2 by exact mul_nonneg (by norm_num) (sq_nonneg _)) no
    linarith only [scaled,bad]
  by_cases sign : 0≤angleGz b r
  · have first := mul_neg_of_pos_of_neg cp negative
    have last := mul_nonneg (sub_nonneg.mpr low) sign
    nlinarith only [first,last]
  · have difference : angleFz b r-angleGz b r=(b-r)*((92/125)*b-(7/20)*r-1) := by
      dsimp [angleFz,angleGz]; ring
    have first := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr bn.2.1)
      (show (92/125)*b-(7/20)*r-1≤0 by linarith only [bb.2.1,bn.1])
    have last := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr cn.2.1)
      (show angleGz b r≤0 by linarith only [sign])
    have weighted := mul_nonpos_of_nonneg_of_nonpos cp.le
      (show angleFz b r-angleGz b r≤0 by rw [difference]; exact first)
    nlinarith only [weighted,last]

theorem angle_f0_row {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (low : (2/5)*c≤s) :
    c*((b+r-1)^2/2+(43/500)*r^2)-s*(r^2+b-r-(43/500)*b*r)<0 := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0<c := by linarith only [cb.1]
  have product := mul_nonneg (sub_nonneg.mpr bn.2.1)
    (show 0≤2-b-r by linarith only [bb.2.2.2.2.2])
  have cross : b*r≤1/2 := by nlinarith only [bn.2.2,sq_nonneg (b-r)]
  have lower : 457/1000≤r^2+b-r-(43/500)*b*r := by nlinarith only [product,cross,bn.2.2]
  have first := mul_lt_mul_of_pos_left (cap_f0 bn).1 cp
  have last := mul_nonneg cn.1 (sub_nonneg.mpr lower)
  nlinarith only [first,last,low,cp]

theorem angle_g0_row {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (low : (2/5)*c≤s) (angle : half b r<43/500) (sum : b+r<29/25) :
    c*(43/500+(b+r-1)^2/2)-s*(r^2+b-r)<0 := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have endpoint : Normal (248151/251849) (43000/251849) := by norm_num [Normal]
  have endpointHalf : half (248151/251849) (43000/251849)=(43:ℝ)/500 := by norm_num [half]
  have cross := half_cross bn endpoint (by simpa only [endpointHalf] using angle.le)
  have coordinates := coordinates_after endpoint bn cross
  have lower : 101/125<r^2+b-r := by nlinarith only [coordinates.1,coordinates.2,sq_nonneg r]
  have first := mul_lt_mul_of_pos_left (cap_g0 bn sum).1 cp
  have last := mul_nonneg cn.1 (show 0≤r^2+b-r-101/125 by linarith only [lower])
  nlinarith only [first,last,low,cp]

theorem angle_left_row {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (low : (7/16)*c≤s) : c*angleFl b r-s*angleGl b r<0 := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0<c := by linarith only [cb.1]
  have gp : 0<angleGl b r := by
    have product := mul_nonneg bn.1 (show 0≤1-(92/125)*b by linarith only [bb.2.1])
    dsimp [angleGl]
    nlinarith only [product,bb.1,sq_nonneg (b-7/10)]
  let w := half b r
  let h := w-1/4
  have wb := canonical_half_bounds bn
  have den : 0<1+w^2 := by nlinarith only [sq_nonneg w]
  have frames := rational_frame bn
  have bf : b=(1-w^2)/(1+w^2) := frames.1
  have rf : r=2*w/(1+w^2) := frames.2
  have hl : -1/4≤h := by dsimp [h]; linarith only [wb.1]
  have hu : h≤1/6 := by dsimp [h]; linarith only [wb.2]
  have square := mul_nonneg (show 0≤1/4-h by linarith only [hu])
    (show 0≤1/4+h by linarith only [hl])
  have coefficient : 15463*h^2-2289*h-60123/8≤0 := by nlinarith only [square,hl]
  have correction := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg h) coefficient
  have quadratic : -12505/256-(7569/16)*h-3726*h^2<0 := by
    nlinarith only [sq_nonneg (7452*h+7569/16)]
  have expanded : 15463*w^4-17752*w^3-3726*w^2+3752*w-537=
      -12505/256-(7569/16)*h-3726*h^2+h^2*(15463*h^2-2289*h-60123/8) := by
    dsimp [h]; ring
  have polynomial : 15463*w^4-17752*w^3-3726*w^2+3752*w-537<0 := by
    linarith only [expanded,quadratic,correction]
  have identity : 8000*(1+w^2)^2*(angleFl b r-(7/16)*angleGl b r)=
      15463*w^4-17752*w^3-3726*w^2+3752*w-537 := by
    dsimp [angleFl,angleGl]
    rw [bf,rf]
    change 8000*(1+w^2)^2*
      ((543/500)*((1-w^2)/(1+w^2))^2+(7/20)*((1-w^2)/(1+w^2))*(2*w/(1+w^2))+
        (7/20)*(2*w/(1+w^2))^2-(1-w^2)/(1+w^2)-
        (7/16)*((7/20)*((1-w^2)/(1+w^2))^2-(92/125)*((1-w^2)/(1+w^2))*(2*w/(1+w^2))+2*w/(1+w^2)))=_
    field_simp [den.ne']
    <;> ring
  have negative : angleFl b r-(7/16)*angleGl b r<0 := by
    apply lt_of_not_ge
    intro no
    have bad := mul_nonneg (show 0≤8000*(1+w^2)^2 by exact mul_nonneg (by norm_num) (sq_nonneg _)) no
    nlinarith only [identity,polynomial,bad]
  have first := mul_neg_of_pos_of_neg cp negative
  have last := mul_nonneg (sub_nonneg.mpr low) gp.le
  nlinarith only [first,last]

theorem angle_right_row {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (low : (7/16)*c≤s) (angle : 21/100≤half b r) :
    c*((43/500)*b^2+f b r)-s*(g b r-(43/500)*b*r)<0 := by
  have cp : 0<c := by linarith only [(normal_bounds cn).1]
  let w := half b r
  let a : ℝ := 21/100
  have wb := canonical_half_bounds bn
  have den : 0<1+w^2 := by nlinarith only [sq_nonneg w]
  have frames := rational_frame bn
  have bf : b=(1-w^2)/(1+w^2) := frames.1
  have rf : r=2*w/(1+w^2) := frames.2
  let P (x : ℝ) := 4844*x^4-19801*x^3+10812*x^2-3199*x+344
  let R := 4844*w^2+(9688*a-19801)*w+14532*a^2-39602*a+10812
  have product := mul_nonneg wb.1 (show 0≤5/12-w by exact sub_nonneg.mpr wb.2)
  have remainder : R<0 := by dsimp [R,a]; nlinarith only [product,angle]
  have base : P a<0 := by norm_num [P,a]
  have derivative : 19376*a^3-59403*a^2+21624*a-3199<0 := by norm_num [a]
  have identity : P w=P a+(w-a)*(19376*a^3-59403*a^2+21624*a-3199)+(w-a)^2*R := by
    dsimp [P,R]; ring
  have first := mul_nonpos_of_nonneg_of_nonpos (show 0≤w-a by exact sub_nonneg.mpr angle) derivative.le
  have last := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w-a)) remainder.le
  have polynomial : P w<0 := by linarith only [identity,base,first,last]
  have formula : 4000*(1+w^2)^2*((43/500)*b^2+f b r-(7/16)*(g b r-(43/500)*b*r))=P w := by
    dsimp [f,g]
    rw [bf,rf]
    dsimp [P]
    change 4000*(1+w^2)^2*((43/500)*((1-w^2)/(1+w^2))^2+
      ((1-w^2)/(1+w^2)+2*w/(1+w^2)-1)^2/2-
      (7/16)*(((1-w^2)/(1+w^2))^2-(1-w^2)/(1+w^2)+2*w/(1+w^2)-
        (43/500)*((1-w^2)/(1+w^2))*(2*w/(1+w^2))))=_
    field_simp [den.ne']
    <;> ring
  have negative : (43/500)*b^2+f b r-(7/16)*(g b r-(43/500)*b*r)<0 := by
    apply lt_of_not_ge
    intro no
    have bad := mul_nonneg (show 0≤4000*(1+w^2)^2 by exact mul_nonneg (by norm_num) (sq_nonneg _)) no
    nlinarith only [formula,polynomial,bad]
  have first := mul_neg_of_pos_of_neg cp negative
  have last := mul_nonneg (sub_nonneg.mpr low) (cap_negative_fg bn).2
  nlinarith only [first,last]

#print axioms angle_z_row
#print axioms angle_left_row
#print axioms angle_right_row
end N12Compact.C1092MPPMInwardFinal
