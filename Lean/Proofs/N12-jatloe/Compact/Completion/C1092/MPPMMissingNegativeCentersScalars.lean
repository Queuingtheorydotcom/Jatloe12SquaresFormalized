import Compact.Completion.C1092.MPPMMissingNegativeCrosspointEnvelope
import Compact.Completion.C1092.MPPMMissingPositiveBoundEnvelopesScalars
import Compact.Completion.C1092.MPPMCrosspointBoundaryHalf

/-! Continuous support margins in MISSING-NEGATIVE-BOUNDARIES, Theorems
2--3. The difficult upper bottom arc is one exact quadratic-circle chord;
the other arcs use finite unit-circle differences. No angular derivative,
numerical grid, side cap, or abstract boundary orientation is assumed. -/
namespace N12Compact.C1092MPPMMissingNegativeCenters
open C977CornerCubic C977CornerSectorBounds C1092ShallowPositiveScalars
open C1092MPPMCrosspointSupport
open C1092MPPMMissingPositiveBoundaries.Envelopes
set_option Elab.async false
noncomputable section

def Fb (c s : ℝ) : ℝ := 3/2-(4/5)*c-2*s+s*(c+s)/2
def Fl (c s : ℝ) : ℝ := 3/2-(36/25)*c-(6/5)*s+c*(c+s)/2
def bottomPlusA (c s : ℝ) : ℝ := c-s-4/5+(37/50)*s^2
def bottomPlusB (c s : ℝ) : ℝ := c+s-2-(37/50)*c*s
def bottomMinusA (c s : ℝ) : ℝ := c-4/5+(13/20)*s^2-(7/20)*c*s
def bottomMinusB (c s : ℝ) : ℝ := -2+s+(7/20)*c^2-(13/20)*c*s
def leftPlusA (c s : ℝ) : ℝ := c-36/25-(21/100)*s^2-(13/20)*c*s
def leftPlusB (c s : ℝ) : ℝ := s-(13/20)*s^2-11/20+(21/100)*c*s
def leftMinusA (c s : ℝ) : ℝ := c+s-36/25-(3/10)*s^2-c*s
def leftMinusB (c s : ℝ) : ℝ := s-c-s^2+(3/10)*c*s-1/5

theorem bounds {c s : ℝ} (cn : Normal c s) (large : 252/373≤s) :
    7/10<c ∧ c≤369/500 ∧ 27/40≤s ∧ s≤71/100 ∧
      9/20≤s^2 ∧ s^2≤1/2 ∧ c^2≤11/20 ∧
      49/100≤c*s ∧ c*s≤1/2 ∧ 141/100≤c+s ∧
      c+s≤283/200 ∧ 0≤c-s ∧ c-s≤31/500 := by
  have cb := normal_bounds cn
  have endpoint : Normal (275/373:ℝ) (252/373) := by norm_num [Normal]
  have cosine := cosine_order cn endpoint large
  have sum := C1092MPPMMissingNegativeCrosspointSupport.large_sum cn large
  have arc := steep_bounds cn (show 3/5≤s by linarith only [large])
  have order := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤c+s by linarith only [cb.1,cn.1])
  have square := mul_nonneg (show 0≤s-27/40 by linarith only [large])
    (show 0≤s+27/40 by linarith only [cn.1])
  have sumSquare := mul_nonneg (show 0≤c+s-141/100 by linarith only [sum])
    (show 0≤c+s+141/100 by linarith only [cb.1,cn.1])
  have strictCosine : 7/10<c := by nlinarith only [cn.2.2,order,cb.1]
  refine ⟨strictCosine,by linarith only [cosine],by linarith only [large],arc.2.1.le,
    ?_,?_,?_,?_,?_,sum,by linarith only [arc.2.2.2],sub_nonneg.mpr cn.2.1,?_⟩
  · nlinarith only [square]
  · nlinarith only [order,cn.2.2]
  · nlinarith only [square,cn.2.2]
  · nlinarith only [sumSquare,cn.2.2]
  · nlinarith only [cn.2.2,sq_nonneg (c-s)]
  · linarith only [cosine,large]

theorem central_margins {c s : ℝ} (cn : Normal c s) (large : 252/373≤s) :
    19/1000≤Fb c s ∧ 13/100≤Fl c s := by
  rcases bounds cn large with ⟨cp,ch,sl,sh,ss,ssu,cc,cs,csu,sum,sumu,Dn,Du⟩
  have bottom := mul_nonneg Dn (show 0≤3/5-c/2 by linarith only [ch])
  have left := mul_nonneg Dn (show 0≤s/2-3/25 by linarith only [sl])
  have bidentity : Fb c s=2-(7/5)*(c+s)+(c-s)*(3/5-c/2) := by
    dsimp [Fb]; linear_combination (1/2)*cn.2.2
  have lidentity : Fl c s=2-(33/25)*(c+s)+(c-s)*(s/2-3/25) := by
    dsimp [Fl]; linear_combination (1/2)*cn.2.2
  constructor <;> nlinarith only [bottom,left,bidentity,lidentity,sumu]

theorem coefficient_bounds {c s : ℝ} (cn : Normal c s) (large : 252/373≤s) :
    0≤bottomMinusA c s ∧ bottomMinusB c s≤-7/5 ∧
      leftPlusA c s≤-111/100 ∧ -1/10≤leftPlusB c s ∧
      -7/10≤leftMinusA c s ∧ leftMinusB c s≤-1/2 := by
  rcases bounds cn large with ⟨cp,ch,sl,sh,ss,ssu,cc,cs,csu,sum,sumu,Dn,Du⟩
  dsimp [bottomMinusA,bottomMinusB,leftPlusA,leftPlusB,leftMinusA,leftMinusB]
  constructor
  · linarith only [cp,ss,csu]
  · constructor
    · linarith only [sh,cc,cs]
    · constructor
      · linarith only [ch,ss,cs]
      · constructor
        · linarith only [sl,ssu,cs]
        · constructor
          · linarith only [sum,ssu,csu]
          · linarith only [Dn,ss,csu]

theorem aligned (c s : ℝ) (cn : Normal c s) :
    bottomValue 1 (bottomPlusA c s) (bottomPlusB c s) c s=Fb c s ∧
    bottomValue 1 (bottomMinusA c s) (bottomMinusB c s) c s=Fb c s ∧
    leftValue 1 (leftPlusA c s) (leftPlusB c s) c s=Fl c s ∧
    leftValue 1 (leftMinusA c s) (leftMinusB c s) c s=Fl c s := by
  dsimp [bottomValue,leftValue,bottomPlusA,bottomPlusB,bottomMinusA,bottomMinusB,
    leftPlusA,leftPlusB,leftMinusA,leftMinusB,Fb,Fl]
  constructor
  · linear_combination cn.2.2
  · constructor
    · linear_combination cn.2.2
    · constructor
      · linear_combination (1-(13/20)*s)*cn.2.2
      · linear_combination (1-s)*cn.2.2

private theorem swapped_remainder (z R : ℝ) (zn : 0≤z) (zu : z≤1/2)
    (rn : 0≤R) (ru : R≤1/2) :
    0≤QuadraticArc.remainder (1/2) (1/2) (1/2) 0 z R := by
  have zz := mul_le_mul_of_nonneg_right zu zn
  have rr := mul_le_mul_of_nonneg_right ru rn
  have zr0 := mul_le_mul_of_nonneg_left ru zn
  have zr1 := mul_le_mul_of_nonneg_left zu rn
  have product := mul_le_mul zu ru rn (by norm_num : (0:ℝ)≤1/2)
  have zrn := mul_nonneg zn rn
  have square := mul_le_mul_of_nonneg_right product zrn
  have identity : QuadraticArc.remainder (1/2) (1/2) (1/2) 0 z R=
      z+R-z^2-R^2-z*R-z^2*R^2 := by
    dsimp [QuadraticArc.remainder,QuadraticArc.X,QuadraticArc.Y,QuadraticArc.Z,
      QuadraticArc.sum3,QuadraticArc.pair3,QuadraticArc.triple3]
    ring
  nlinarith only [identity,zz,rr,zr0,zr1,square,zn,rn]

theorem bottom_plus (c s h t : ℝ) (cn : Normal c s) (large : 252/373≤s)
    (q : Quarter h t) (cross : 0≤c*t-s*h) :
    0<bottomValue 1 (bottomPlusA c s) (bottomPlusB c s) h t := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have sp : 0<s := by linarith only [large]
  have order := circle_order s c h t sp cp q.cosine q.sine
    (by nlinarith only [cn.2.2]) q.unit cross
  let z := half t h
  let R := half s c
  have zh := quarter_half (show Quarter t h from ⟨q.sine,q.cosine,by nlinarith only [q.unit]⟩)
  have rh := quarter_half (show Quarter s c from ⟨cn.1,cp.le,by nlinarith only [cn.2.2]⟩)
  have range : z≤R := by
    dsimp [z,R,half]
    apply (div_le_div_iff₀ (by linarith only [q.sine]) (by linarith only [cn.1])).mpr
    have first := mul_nonneg (sub_nonneg.mpr order.1) (show 0≤1+s by linarith only [cn.1])
    have last := mul_nonneg cp.le (sub_nonneg.mpr order.2)
    nlinarith only [first,last]
  have Ru : R≤1/2 := by
    have b := bounds cn large
    apply (div_le_iff₀ (show 0<1+s by linarith only [cn.1])).mpr
    linarith only [b.2.1,b.2.2.1]
  have margin := central_margins cn large
  have endpoint : 0<1+bottomPlusB c s := by
    have b := bounds cn large
    dsimp [bottomPlusB]
    linarith only [b.2.2.2.2.2.2.2.2.1,b.2.2.2.2.2.2.2.2.2.1]
  let m := min (Fb c s) (1+bottomPlusB c s)
  have mp : 0<m := lt_min (by linarith only [margin.1]) endpoint
  have rem0 := swapped_remainder z R zh.1 (le_trans range Ru) rh.1 Ru
  have rem : 0≤QuadraticArc.remainder (1/2) (1/2) (1/2-m) 0 z R := by
    have Zpositive : 0≤QuadraticArc.Z 0 z R := by dsimp [QuadraticArc.Z]; positivity
    have positive := mul_nonneg mp.le Zpositive
    dsimp [QuadraticArc.remainder] at rem0 ⊢
    nlinarith only [rem0,positive]
  have first : 0≤QuadraticArc.value (1/2) (1/2) (1/2-m)
      (bottomPlusB c s) (bottomPlusA c s) 0 := by
    norm_num [QuadraticArc.value,cosH,sinH]
    have lower := min_le_right (Fb c s) (1+bottomPlusB c s)
    change m≤1+bottomPlusB c s at lower
    linarith only [lower]
  have last : 0≤QuadraticArc.value (1/2) (1/2) (1/2-m)
      (bottomPlusB c s) (bottomPlusA c s) R := by
    have value := (aligned c s cn).1
    dsimp [QuadraticArc.value]
    rw [rh.2.2.1,rh.2.2.2]
    dsimp [bottomValue] at value
    have lower := min_le_left (Fb c s) (1+bottomPlusB c s)
    change m≤Fb c s at lower
    nlinarith only [value,lower]
  have result := QuadraticArc.nonnegative (1/2) (1/2) (1/2-m)
    (bottomPlusB c s) (bottomPlusA c s) 0 z R (by norm_num) zh.1 range rem first last
  dsimp [QuadraticArc.value] at result
  rw [zh.2.2.1,zh.2.2.2] at result
  dsimp [bottomValue]
  nlinarith only [result,mp]

theorem bottom_minus (c s h t : ℝ) (cn : Normal c s) (large : 252/373≤s)
    (q : Quarter h t) (cross : c*t-s*h≤0) :
    0<bottomValue 1 (bottomMinusA c s) (bottomMinusB c s) h t := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have sp : 0<s := by linarith only [large]
  have order := circle_order_reverse s c h t sp cp q.cosine q.sine
    (by nlinarith only [cn.2.2]) q.unit cross
  have bs := bounds cn large
  have coefficients := coefficient_bounds cn large
  let H := (h+c)/2
  let T := (t+s)/2
  have Hn : 0≤H := by dsimp [H]; linarith only [q.cosine,cp]
  have Hp : 0<H := by dsimp [H]; linarith only [q.cosine,cp]
  have Hh : H≤1 := by
    have hh : h≤1 := by nlinarith only [q.unit,sq_nonneg t,sq_nonneg (h-1)]
    dsimp [H]; linarith only [hh,cb.2.1]
  have Tn : 0≤T := by dsimp [T]; linarith only [q.sine,cn.1]
  have Th : T≤71/100 := by dsimp [T]; linarith only [order.2,bs.2.2.2.1]
  have first := mul_nonpos_of_nonneg_of_nonpos Hn
    (show T+H/2-7/5≤0 by linarith only [Th,Hh])
  have last := mul_nonneg coefficients.1 Tn
  have Bweight := mul_le_mul_of_nonneg_right coefficients.2.1 Hn
  have derivative : H*T+(H^2-T^2)/2-bottomMinusA c s*T+bottomMinusB c s*H≤0 := by
    nlinarith only [first,last,Bweight,sq_nonneg T]
  have product := mul_nonneg (show 0≤s-t by linarith only [order.2])
    (neg_nonneg.mpr derivative)
  have identity := bottom_difference 1 (bottomMinusA c s) (bottomMinusB c s) h t c s
    (by nlinarith only [q.unit,cn.2.2])
  simp only [one_mul] at identity
  change H*(bottomValue 1 (bottomMinusA c s) (bottomMinusB c s) h t-
      bottomValue 1 (bottomMinusA c s) (bottomMinusB c s) c s)=
      (t-s)*(H*T+(H^2-T^2)/2-bottomMinusA c s*T+bottomMinusB c s*H) at identity
  have weighted : 0≤H*(bottomValue 1 (bottomMinusA c s) (bottomMinusB c s) h t-
      bottomValue 1 (bottomMinusA c s) (bottomMinusB c s) c s) := by
    rw [identity]
    nlinarith only [product]
  have result := nonneg_of_mul_nonneg_right weighted Hp
  have endpoint := (aligned c s cn).2.1
  have margin := (central_margins cn large).1
  linarith only [result,endpoint,margin]

private theorem sloping_cap (c s h t : ℝ) (cn : Normal c s) (large : 252/373≤s)
    (q : Quarter h t) (order : s≤t) : h+t/2≤27/25 := by
  have endpoint : Normal (275/373:ℝ) (252/373) := by norm_num [Normal]
  have cb := normal_bounds cn
  have initial := CommonCases.UnitCircleChord.decreasing (A:=(1:ℝ)) (B:=1/2)
    (by norm_num : (0:ℝ)<275/373) (show 0≤c by linarith only [cb.1])
    endpoint.2.2 cn.2.2 endpoint.1 cn.1 large (by norm_num) (by norm_num) (by norm_num)
  have final := CommonCases.UnitCircleChord.decreasing (A:=(1:ℝ)) (B:=1/2)
    (show 0<c by linarith only [cb.1]) q.cosine cn.2.2 q.unit cn.1 q.sine order
    (by norm_num) (by norm_num) (by linarith only [large,(bounds cn large).2.1])
  linarith only [initial,final]

theorem left_plus (c s h t : ℝ) (cn : Normal c s) (large : 252/373≤s)
    (q : Quarter h t) (cross : 0≤c*t-s*h) :
    0<leftValue 1 (leftPlusA c s) (leftPlusB c s) h t := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have sp : 0<s := by linarith only [large]
  have order := circle_order s c h t sp cp q.cosine q.sine
    (by nlinarith only [cn.2.2]) q.unit cross
  have coefficients := coefficient_bounds cn large
  let H := (h+c)/2
  let T := (t+s)/2
  have Hn : 0≤H := by dsimp [H]; linarith only [q.cosine,cp]
  have Hp : 0<H := by dsimp [H]; linarith only [q.cosine,cp]
  have Tn : 0≤T := by dsimp [T]; linarith only [q.sine,cn.1]
  have Tl : 27/40≤T := by dsimp [T]; linarith only [large,order.2]
  have cap : H+T/2≤27/25 := by
    have first := sloping_cap c s h t cn large q order.2
    have last := sloping_cap c s c s cn large ⟨cp.le,cn.1,cn.2.2⟩ le_rfl
    dsimp [H,T]; linarith only [first,last]
  have first := mul_le_mul_of_nonneg_right coefficients.2.2.1 Tn
  have last := mul_le_mul_of_nonneg_right coefficients.2.2.2.1 Hn
  have product := mul_nonneg Tn (show 0≤27/25-H-T/2 by linarith only [cap])
  have derivative : 0≤-H*T+(H^2-T^2)/2-leftPlusA c s*T+leftPlusB c s*H := by
    nlinarith only [first,last,product,sq_nonneg (H-1/10),Tl]
  have weight := mul_nonneg (sub_nonneg.mpr order.2) derivative
  have identity := left_difference 1 (leftPlusA c s) (leftPlusB c s) h t c s
    (by nlinarith only [q.unit,cn.2.2])
  simp only [one_mul] at identity
  change H*(leftValue 1 (leftPlusA c s) (leftPlusB c s) h t-
      leftValue 1 (leftPlusA c s) (leftPlusB c s) c s)=
      (t-s)*(-H*T+(H^2-T^2)/2-leftPlusA c s*T+leftPlusB c s*H) at identity
  have weighted : 0≤H*(leftValue 1 (leftPlusA c s) (leftPlusB c s) h t-
      leftValue 1 (leftPlusA c s) (leftPlusB c s) c s) := by
    rw [identity]; exact weight
  have result := nonneg_of_mul_nonneg_right weighted Hp
  have endpoint := (aligned c s cn).2.2.1
  have margin := (central_margins cn large).2
  linarith only [result,endpoint,margin]

theorem left_minus (c s h t : ℝ) (cn : Normal c s) (large : 252/373≤s)
    (q : Quarter h t) (cross : c*t-s*h≤0) :
    0<leftValue 1 (leftMinusA c s) (leftMinusB c s) h t := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have sp : 0<s := by linarith only [large]
  have order := circle_order_reverse s c h t sp cp q.cosine q.sine
    (by nlinarith only [cn.2.2]) q.unit cross
  have coefficients := coefficient_bounds cn large
  let H := (h+c)/2
  let T := (t+s)/2
  have Hp : 0<H := by dsimp [H]; linarith only [q.cosine,cp]
  have Hl : 7/10≤H := by dsimp [H]; linarith only [order.1,cb.1]
  have Hh : H≤1 := by
    have hh : h≤1 := by nlinarith only [q.unit,sq_nonneg t,sq_nonneg (h-1)]
    dsimp [H]; linarith only [hh,cb.2.1]
  have Tn : 0≤T := by dsimp [T]; linarith only [q.sine,cn.1]
  have first := mul_le_mul_of_nonneg_right coefficients.2.2.2.2.1 Tn
  have last := mul_le_mul_of_nonneg_right coefficients.2.2.2.2.2 Hp.le
  have a := mul_nonpos_of_nonneg_of_nonpos Hp.le (show H/2-1/2≤0 by linarith only [Hh])
  have b := mul_nonpos_of_nonneg_of_nonpos Tn (show 7/10-H-T/2≤0 by linarith only [Hl,Tn])
  have derivative : -H*T+(H^2-T^2)/2-leftMinusA c s*T+leftMinusB c s*H≤0 := by
    nlinarith only [first,last,a,b]
  have weight := mul_nonneg (show 0≤s-t by linarith only [order.2]) (neg_nonneg.mpr derivative)
  have identity := left_difference 1 (leftMinusA c s) (leftMinusB c s) h t c s
    (by nlinarith only [q.unit,cn.2.2])
  simp only [one_mul] at identity
  change H*(leftValue 1 (leftMinusA c s) (leftMinusB c s) h t-
      leftValue 1 (leftMinusA c s) (leftMinusB c s) c s)=
      (t-s)*(-H*T+(H^2-T^2)/2-leftMinusA c s*T+leftMinusB c s*H) at identity
  have weighted : 0≤H*(leftValue 1 (leftMinusA c s) (leftMinusB c s) h t-
      leftValue 1 (leftMinusA c s) (leftMinusB c s) c s) := by
    rw [identity]; nlinarith only [weight]
  have result := nonneg_of_mul_nonneg_right weighted Hp
  have endpoint := (aligned c s cn).2.2.2
  have margin := (central_margins cn large).2
  linarith only [result,endpoint,margin]

end
end N12Compact.C1092MPPMMissingNegativeCenters
