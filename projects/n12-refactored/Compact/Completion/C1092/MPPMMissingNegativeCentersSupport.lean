import Compact.Completion.C1092.MPPMMissingNegativeCentersScalars
import Compact.Completion.C1092.MPPMMissingNegativeProfile
import Compact.Completion.C1092.MPPMMissingPositiveBoundEnvelopesBottom

/-! Whole-square support comparisons for the two actual boundary-center
theorems. The strong faces belong to the same actual negative square;
the original marker and ordinary P remain strict. -/
namespace N12Compact.C1092MPPMMissingNegativeCenters
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports C1092ShallowBoundarySupport
open C1092MPPMMissingPositiveBoundaries.Envelopes
set_option Elab.async false

structure Data (C : OpenSquare) : Prop where
  normal : Normal C.c (-C.s)
  marker : C.Inside (-7/20) (-7/20)
  ordinaryP : C.Inside (-1) (-13/50)
  faces : C1092MPPMMissingNegativeProfile.StrongFaces C

theorem Data.large (C : OpenSquare) (side : 1<C.side) (d : Data C) : 252/373≤-C.s := by
  apply le_of_not_gt
  intro low
  have cp : 0<C.c := by linarith only [(normal_bounds d.normal).1]
  have support := CommonCases.UnitCircleChord.increasing
    (c:=275/373) (s:=252/373) (d:=C.c) (t:=-C.s) (A:=11/25) (B:=1)
    (by norm_num) cp.le (by norm_num) d.normal.2.2 (by norm_num) d.normal.1 low.le
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at support
  linarith only [side,d.faces.widthU,support]

/-- The signed width lemma applied after swapping the boundary frame.
This keeps its orientation unrestricted while using the direction (-c,s). -/
theorem negative_widths (Q : OpenSquare) {c s : ℝ} (cn : Normal c s) :
    Q.side*(1+s*(c+s))/2≤s*(Q.side*width0 Q/2)+supportRadius Q (-c) s ∧
    Q.side*(1+c*(c+s))/2≤c*(Q.side*width0 Q/2)+supportRadius Q (-c) s := by
  have widths := C1092ShallowWidths.signed_widths cn Q.s Q.c
    (by nlinarith only [Q.unit_normal])
  have first : |c*Q.c-s*Q.s|=|(-c)*Q.c+s*Q.s| := by
    rw [show (-c)*Q.c+s*Q.s=-(c*Q.c-s*Q.s) by ring,abs_neg]
  have last : |c*Q.s+s*Q.c|=|-(-c)*Q.s+s*Q.c| := by congr 1; ring
  have factor := (div_pos Q.side_pos (by norm_num : (0:ℝ)<2)).le
  have a := mul_le_mul_of_nonneg_left widths.2 factor
  have b := mul_le_mul_of_nonneg_left widths.1 factor
  rw [first,last] at a b
  constructor
  · convert a using 1 <;> dsimp [width0,supportRadius] <;> ring
  · convert b using 1 <;> dsimp [width0,supportRadius] <;> ring

theorem northwest (C : OpenSquare) (side : 1<C.side) (d : Data C)
    (h t : ℝ) (q : C1092MPPMCrosspointSupport.Quarter h t) :
    lower C (-h) t<(1/5)*h-2*t+(C.side/2)*(1+t^2+h*t) ∧
    2*h+(1/5)*t-(C.side/2)*(1+h^2+h*t)<upper C (-h) t := by
  let c := C.c
  let s := -C.s
  let k := c*h+s*t
  let sigma := c*t-s*h
  have cn : Normal c s := d.normal
  have cp : 0<c := by linarith only [(normal_bounds cn).1]
  have sp : 0<s := by dsimp [s]; linarith only [d.faces.negative]
  have kn : 0≤k := add_nonneg (mul_nonneg cp.le q.cosine) (mul_nonneg sp.le q.sine)
  have large : 252/373≤s := Data.large C side d
  have u : (-h)*C.c+t*C.s=-k := by dsimp [k,c,s]; ring
  have v : -(-h)*C.s+t*C.c=sigma := by dsimp [sigma,c,s]; ring
  have J : C.side-c≤C.loU+C.side := by dsimp [c]; linarith only [d.faces.lowerU]
  have U : C.loU≤s-(14/25)*c-C.side := by dsimp [s,c]; linarith only [d.faces.upperU]
  have V : C.loV≤-(13/50)*s-C.side := by dsimp [s]; linarith only [d.faces.upperV]
  have K : -(7/20)*(c+s)≤C.loV+C.side := by
    dsimp [c,s]
    linarith only [d.marker.2.2.2]
  by_cases sign : 0≤sigma
  · have lower := lower_np C (-h) t (-k) sigma u v (neg_nonpos.mpr kn) sign
    have upper := upper_np C (-h) t (-k) sigma u v (neg_nonpos.mpr kn) sign
    have jweight := mul_le_mul_of_nonpos_left J (neg_nonpos.mpr kn)
    have vweight := mul_le_mul_of_nonneg_left V sign
    have uweight := mul_le_mul_of_nonpos_left U (neg_nonpos.mpr kn)
    have kweight := mul_le_mul_of_nonneg_left K sign
    have bottom := bottom_plus c s h t cn large q sign
    have left := left_plus c s h t cn large q sign
    have bottomCoefficient : 0<(1+t^2+h*t)/2+k+sigma := by
      have ht := mul_nonneg q.cosine q.sine
      nlinarith only [sq_nonneg t,ht,kn,sign]
    have leftCoefficient : 0<(1+h^2+h*t)/2+k := by
      have ht := mul_nonneg q.cosine q.sine
      nlinarith only [sq_nonneg h,ht,kn]
    have extraB := mul_pos (sub_pos.mpr side) bottomCoefficient
    have extraL := mul_pos (sub_pos.mpr side) leftCoefficient
    have bidentity : (1/5)*h-2*t+(C.side/2)*(1+t^2+h*t)-
        ((-k)*(C.side-c)+sigma*(-(13/50)*s-C.side))=
        bottomValue 1 (bottomPlusA c s) (bottomPlusB c s) h t+
          (C.side-1)*((1+t^2+h*t)/2+k+sigma) := by
      dsimp [bottomValue,bottomPlusA,bottomPlusB,k,sigma]
      linear_combination -h*cn.2.2
    have lidentity : (-k)*(s-(14/25)*c-C.side)+sigma*(-(7/20)*(c+s))-
        (2*h+(1/5)*t-(C.side/2)*(1+h^2+h*t))=
        leftValue 1 (leftPlusA c s) (leftPlusB c s) h t+
          (C.side-1)*((1+h^2+h*t)/2+k) := by
      dsimp [leftValue,leftPlusA,leftPlusB,k,sigma]
      linear_combination ((14/25)*h-(7/20)*t)*cn.2.2
    constructor <;> nlinarith only [lower,upper,jweight,vweight,uweight,kweight,
      bottom,left,extraB,extraL,bidentity,lidentity]
  · have sign' : sigma≤0 := (lt_of_not_ge sign).le
    have lower : lower C (-h) t=(-k)*(C.loU+C.side)+sigma*(C.loV+C.side) := by
      rw [(formulas C (-h) t).1,u,v,min_eq_left (neg_nonpos.mpr kn),min_eq_left sign']
      ring
    have upper : upper C (-h) t=(-k)*C.loU+sigma*C.loV := by
      rw [(formulas C (-h) t).2,u,v,max_eq_right (neg_nonpos.mpr kn),max_eq_right sign']
      ring
    have jweight := mul_le_mul_of_nonpos_left J (neg_nonpos.mpr kn)
    have kweight := mul_le_mul_of_nonpos_left K sign'
    have uweight := mul_le_mul_of_nonpos_left U (neg_nonpos.mpr kn)
    have vweight := mul_le_mul_of_nonpos_left V sign'
    have bottom := bottom_minus c s h t cn large q sign'
    have left := left_minus c s h t cn large q sign'
    have bottomCoefficient : 0<(1+t^2+h*t)/2+k := by
      have ht := mul_nonneg q.cosine q.sine
      nlinarith only [sq_nonneg t,ht,kn]
    have leftCoefficient : 0<(1+h^2+h*t)/2+k-sigma := by
      have ht := mul_nonneg q.cosine q.sine
      nlinarith only [sq_nonneg h,ht,kn,sign']
    have extraB := mul_pos (sub_pos.mpr side) bottomCoefficient
    have extraL := mul_pos (sub_pos.mpr side) leftCoefficient
    have bidentity : (1/5)*h-2*t+(C.side/2)*(1+t^2+h*t)-
        ((-k)*(C.side-c)+sigma*(-(7/20)*(c+s)))=
        bottomValue 1 (bottomMinusA c s) (bottomMinusB c s) h t+
          (C.side-1)*((1+t^2+h*t)/2+k) := by
      dsimp [bottomValue,bottomMinusA,bottomMinusB,k,sigma]
      linear_combination -h*cn.2.2
    have lidentity : (-k)*(s-(14/25)*c-C.side)+sigma*(-(13/50)*s-C.side)-
        (2*h+(1/5)*t-(C.side/2)*(1+h^2+h*t))=
        leftValue 1 (leftMinusA c s) (leftMinusB c s) h t+
          (C.side-1)*((1+h^2+h*t)/2+k-sigma) := by
      dsimp [leftValue,leftMinusA,leftMinusB,k,sigma]
      linear_combination ((14/25)*h)*cn.2.2
    constructor <;> nlinarith only [lower,upper,jweight,kweight,uweight,vweight,
      bottom,left,extraB,extraL,bidentity,lidentity]

/-- Strict F2 and D comparisons exclude every northeast normal in the
actual anchor cone. The weaker bottom cone also covers the left cone. -/
theorem northeast (C : OpenSquare) (side : 1<C.side) (d : Data C)
    (h t : ℝ) (hn : 0≤h) (tp : 0<t) (cone : h<(413/500)*t) :
    lower C h t<-(2/5)*h-t ∧ -h<upper C h t := by
  let c := C.c
  let s := -C.s
  let lambda := c*h-s*t
  let mu := s*h+c*t
  have cn : Normal c s := d.normal
  have large : 252/373≤s := Data.large C side d
  rcases bounds cn large with ⟨cp,ch,sl,sh,ss,ssu,cc,cs,csu,sum,sumu,Dn,Du⟩
  have lp : lambda<0 := by
    have first := mul_lt_mul_of_pos_left cone cp
    have last := mul_pos tp (show 0<s-(413/500)*c by linarith only [sl,ch])
    dsimp [lambda]
    nlinarith only [first,last]
  have mp : 0<mu := by
    have first := mul_nonneg (show 0≤s by linarith only [sl]) hn
    have last := mul_pos cp tp
    dsimp [mu]; nlinarith only [first,last]
  have u : h*C.c+t*C.s=lambda := by dsimp [lambda,c,s]; ring
  have v : -h*C.s+t*C.c=mu := by dsimp [mu,c,s]; ring
  have lower := lower_np C h t lambda mu u v lp.le mp.le
  have upper := upper_np C h t lambda mu u v lp.le mp.le
  have J : C.side-c≤C.loU+C.side := by dsimp [c]; linarith only [d.faces.lowerU]
  have U : C.loU≤s-(14/25)*c-C.side := by dsimp [s,c]; linarith only [d.faces.upperU]
  have V : C.loV≤-(13/50)*s-C.side := by dsimp [s]; linarith only [d.faces.upperV]
  have K : -(7/20)*(c+s)≤C.loV+C.side := by dsimp [c,s]; linarith only [d.marker.2.2.2]
  have jweight := mul_le_mul_of_nonpos_left J lp.le
  have vweight := mul_le_mul_of_nonneg_left V mp.le
  have uweight := mul_le_mul_of_nonpos_left U lp.le
  have kweight := mul_le_mul_of_nonneg_left K mp.le
  have excessB := mul_pos (sub_pos.mpr side) (show 0<mu-lambda by linarith only [lp,mp])
  have excessL := mul_pos (sub_pos.mpr side) (show 0< -lambda by linarith only [lp])
  have bA : c-s-3/5+(37/50)*s^2≤0 := by linarith only [Du,ssu]
  have bB : 1+(37/50)*c*s-(c+s)<0 := by linarith only [sum,csu]
  have lA : 0≤11/25-c+(21/100)*s^2+(13/20)*c*s := by linarith only [ch,ss,cs]
  have lB : 0<s-(13/20)*s^2-7/20+(21/100)*c*s := by linarith only [sl,ssu,cs]
  have ba := mul_nonpos_of_nonneg_of_nonpos hn bA
  have bb := mul_neg_of_pos_of_neg tp bB
  have la := mul_nonneg hn lA
  have lb := mul_pos tp lB
  have bi : lambda*(1-c)+mu*(-(13/50)*s-1)+(2/5)*h+t=
      h*(c-s-3/5+(37/50)*s^2)+t*(1+(37/50)*c*s-(c+s)) := by
    dsimp [lambda,mu]
    linear_combination -h*cn.2.2
  have li : lambda*(s-(14/25)*c-1)+mu*(-(7/20)*(c+s))+h=
      h*(11/25-c+(21/100)*s^2+(13/20)*c*s)+
        t*(s-(13/20)*s^2-7/20+(21/100)*c*s) := by
    dsimp [lambda,mu]
    linear_combination (-(14/25)*h-(7/20)*t)*cn.2.2
  constructor <;> nlinarith only [lower,upper,jweight,vweight,uweight,kweight,
    excessB,excessL,ba,bb,la,lb,bi,li]

end N12Compact.C1092MPPMMissingNegativeCenters
