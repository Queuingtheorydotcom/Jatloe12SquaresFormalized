import Compact.Completion.C1092.MPPMMissingPositiveBoundCoefficients
import Compact.Completion.C1092.ShallowBoundarySupport

/-! Continuous northwest boundary margins from MISSING-POSITIVE-BOUNDARIES
sections 4--6. Circle differences replace derivatives; the weak arc lemma
retains the aligned endpoints. No angle samples or extra face bounds occur.
This is written proof source, not a compilation receipt. -/
namespace N12Compact.C1092MPPMMissingPositiveBoundaries.Envelopes
open S12 S12Pilot C977CornerCubic C1092WallProfileScalars
open C1092ShallowPositiveScalars C1092ShallowCentralScalars Scalars
set_option Elab.async false
noncomputable section

def bottomValue (a A B h t : ℝ) : ℝ := (a/2)*(1+t^2+h*t)+A*h+B*t
def leftValue (a A B h t : ℝ) : ℝ := (a/2)*(1+h^2+h*t)+A*h+B*t
def bottomPlusA (a c s : ℝ) : ℝ :=
  -a*(3/2+c*(c+s)/2)/s+a*(s-c)+c*(2/s+(37/50)*c)
def bottomPlusB (a c s : ℝ) : ℝ := a*(c+s)-2-(37/50)*c*s

theorem diagonal_bounds :
    7/5<Real.sqrt 2 ∧ Real.sqrt 2<3/2 ∧ (Real.sqrt 2)^2=2 := by
  have p : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have sq : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  constructor
  · nlinarith only [p,sq]
  · constructor
    · nlinarith only [p,sq]
    · exact sq

theorem circle_data (h t : ℝ) (hn : 0≤h) (tn : 0≤t) (unit : h^2+t^2=1) :
    0≤half t h ∧ half t h≤1 ∧ t=cosH (half t h) ∧ h=sinH (half t h) := by
  have q := quarter_data t h tn hn (by nlinarith only [unit])
  refine ⟨q.1,q.2.1,?_,?_⟩
  · dsimp [cosH]
    apply (eq_div_iff (half_den_pos _).ne').mpr
    nlinarith only [q.2.2.2.1]
  · dsimp [sinH]
    apply (eq_div_iff (half_den_pos _).ne').mpr
    nlinarith only [q.2.2.2.2]

theorem half_mono (h t H T : ℝ) (hn : 0≤h) (tn : 0≤t)
    (hl : h≤H) (tl : T≤t) (Tn : 0≤T) : half t h≤half T H := by
  unfold half
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have extra := mul_nonneg hn (sub_nonneg.mpr tl)
  have gap := mul_nonneg (sub_nonneg.mpr hl) (show 0≤1+t by positivity)
  nlinarith only [extra,gap]

theorem circle_order (c s h t : ℝ) (cp : 0<c) (sp : 0<s)
    (hn : 0≤h) (tn : 0≤t) (cu : c^2+s^2=1) (hu : h^2+t^2=1)
    (cross : 0≤s*t-c*h) : h≤s ∧ c≤t := by
  have low : h≤s := by
    by_contra bad
    have hs : s<h := lt_of_not_ge bad
    have ct : t<c := by nlinarith only [cu,hu,hs,sp,cp,tn]
    have first := mul_pos cp (sub_pos.mpr hs)
    have last := mul_pos sp (sub_pos.mpr ct)
    nlinarith only [first,last,cross]
  have high : c≤t := by
    by_contra bad
    have ct : t<c := lt_of_not_ge bad
    have hs : s<h := by nlinarith only [cu,hu,ct,sp,cp,hn,tn]
    linarith only [low,hs]
  exact ⟨low,high⟩

theorem circle_order_reverse (c s h t : ℝ) (cp : 0<c) (sp : 0<s)
    (hn : 0≤h) (tn : 0≤t) (cu : c^2+s^2=1) (hu : h^2+t^2=1)
    (cross : s*t-c*h≤0) : s≤h ∧ t≤c := by
  have high : t≤c := by
    by_contra bad
    have ct : c<t := lt_of_not_ge bad
    have hs : h<s := by nlinarith only [cu,hu,ct,sp,cp,hn]
    have first := mul_pos cp (sub_pos.mpr hs)
    have last := mul_pos sp (sub_pos.mpr ct)
    nlinarith only [first,last,cross]
  have low : s≤h := by
    by_contra bad
    have hs : h<s := lt_of_not_ge bad
    have ct : c<t := by nlinarith only [cu,hu,hs,sp,cp,hn,tn]
    linarith only [high,ct]
  exact ⟨low,high⟩

/-- The derivative at the coordinate midpoint is an exact finite
difference because the support polynomial is quadratic. -/
theorem bottom_difference (a A B h t H T : ℝ)
    (unit : h^2+t^2=H^2+T^2) :
    ((h+H)/2)*(bottomValue a A B h t-bottomValue a A B H T)=
      (t-T)*(a*(((h+H)/2)*((t+T)/2)+
        (((h+H)/2)^2-((t+T)/2)^2)/2)-A*((t+T)/2)+B*((h+H)/2)) := by
  dsimp [bottomValue]
  linear_combination (a*(t+T)/8+A/2)*unit

theorem left_difference (a A B h t H T : ℝ)
    (unit : h^2+t^2=H^2+T^2) :
    ((h+H)/2)*(leftValue a A B h t-leftValue a A B H T)=
      (t-T)*(a*(-((h+H)/2)*((t+T)/2)+
        (((h+H)/2)^2-((t+T)/2)^2)/2)-A*((t+T)/2)+B*((h+H)/2)) := by
  dsimp [leftValue]
  linear_combination (a*(2*(h+H)+t+T)/8+A/2)*unit

theorem aligned (C : OpenSquare) (side : 1<C.side) (d : Data C) :
    bottomValue C.side (bottomPlusA C.side C.c C.s)
      (bottomPlusB C.side C.c C.s) C.s C.c=0 ∧
    bottomValue C.side (bottomA C.side C.c C.s)
      (bottomB C.side C.c C.s) C.s C.c=0 ∧
    leftValue C.side (leftPlusA C.side C.c C.s)
      (leftPlusB C.side C.c C.s) C.s C.c=0 ∧
    leftValue C.side (leftMinusA C.side C.c C.s)
      (leftMinusB C.side C.c C.s) C.s C.c=0 := by
  have hs := half_specs C side d
  let q := half C.c C.s
  have cf : C.c=cosH q := hs.2.2.2.1
  have sf : C.s=sinH q := hs.2.2.2.2
  rw [cf,sf]
  dsimp [bottomValue,leftValue,bottomPlusA,bottomPlusB,bottomA,bottomB,
    leftPlusA,leftPlusB,leftMinusA,leftMinusB,cosH,sinH]
  have positive : 0<1-q^2 := by
    nlinarith only [hs.1,hs.2.1]
  constructor
  · field_simp [hs.1.ne',(half_den_pos q).ne',positive.ne']; ring
  · constructor
    · field_simp [hs.1.ne',(half_den_pos q).ne',positive.ne']; ring
    · constructor <;> field_simp [hs.1.ne',(half_den_pos q).ne',positive.ne'] <;> ring

theorem bottom_diagonal (C : OpenSquare) (side : 1<C.side) (d : Data C) :
    0≤bottomValue C.side (bottomA C.side C.c C.s)
      (bottomB C.side C.c C.s) (Real.sqrt 2/2) (Real.sqrt 2/2) := by
  have p := profile C side d
  have cb := normal_bounds d.normal
  have cp : 0<C.c := by linarith only [cb.1]
  have sp := p.positive
  have root := diagonal_bounds
  let r := Real.sqrt 2
  let D := C.c-C.s
  let L := C.c+C.s
  have Dn : 0≤D := sub_nonneg.mpr d.normal.2.1
  have Du : D≤1 := by dsimp [D]; linarith only [cb.2.1,d.normal.1]
  have Ln : 1≤L := cb.2.2.2.2.1
  have Lu : L≤r := by
    dsimp [L,r]
    nlinarith only [d.normal.2.2,sq_nonneg (C.c-C.s),root.1,root.2.2]
  have coefficient : r-1/C.s+D/2≤0 := by
    have first := mul_nonneg (show 0≤r/2 by dsimp [r]; linarith only [root.1])
      (sub_nonneg.mpr Lu)
    have last := mul_nonneg Dn (show 0≤r-C.s by dsimp [r]; linarith only [root.1,cb.2.2.2.1])
    have cancelled : C.s*(r-1/C.s+D/2)=r*C.s-1+C.s*D/2 := by field_simp [sp.ne']; ring
    have weighted : C.s*(r-1/C.s+D/2)≤0 := by
      rw [cancelled]
      dsimp [L,D] at first last ⊢
      nlinarith only [first,last,root.2.2]
    exact nonpos_of_mul_nonpos_right weighted sp
  let F := r*(C.c+(11/25)*C.s)-36/25+
    (3/50)*C.c^2+(4/25)*C.c*C.s-(11/50)*C.s^2
  have chord := mul_nonneg (show 0≤r-L by linarith only [Lu])
    (show 0≤(3/5)*(r+L)-r by dsimp [r]; linarith only [Ln,root.2.1])
  have deficit : r*(r-L)≤(3/5)*D^2 := by
    dsimp [D,L] at chord ⊢
    nlinarith only [chord,d.normal.2.2,root.2.2]
  have bracket : 0≤(7/25)*r+(7/50)*L-(64/125)*D := by
    dsimp [r]
    linarith only [root.1,Ln,Du]
  have last := mul_nonneg Dn bracket
  have Fn : 0≤F := by
    have identity : F= -(18/25)*r*(r-L)+D*((7/25)*r+(7/50)*L-(2/25)*D) := by
      dsimp [F,D,L,r]
      linear_combination (18/25)*root.2.2
    rw [identity]
    nlinarith only [deficit,last]
  have sideWeight := mul_nonneg (sub_nonneg.mpr p.widthV) (neg_nonneg.mpr coefficient)
  have identity : r*bottomValue C.side (bottomA C.side C.c C.s)
      (bottomB C.side C.c C.s) (r/2) (r/2)=
      C.side*(r-1/C.s+D/2)+D*(1/C.s-(11/25)*C.c) := by
    have reciprocal : C.s*(1/C.s)=1 := by field_simp [sp.ne']
    dsimp [bottomValue,bottomA,bottomB,D]
    linear_combination (C.side*r/4+(C.side*(C.c-C.s)/2-C.side/C.s+
      C.c/C.s-(11/25)*C.c^2-1+(11/25)*C.c*C.s)/2)*root.2.2+reciprocal
  have intrinsic : (C.c+(11/25)*C.s)*(r-1/C.s+D/2)+D*(1/C.s-(11/25)*C.c)=F := by
    dsimp [D,F]
    field_simp [sp.ne']
    ring
  have lower : F≤r*bottomValue C.side (bottomA C.side C.c C.s)
      (bottomB C.side C.c C.s) (r/2) (r/2) := by
    rw [identity,←intrinsic]
    nlinarith only [sideWeight]
  exact nonneg_of_mul_nonneg_right (Fn.trans lower)
    (show 0<r by dsimp [r]; linarith only [root.1])

theorem bottom_minus_low (C : OpenSquare) (side : 1<C.side)
    (cap : C.side≤1001/1000) (d : Data C)
    (h t : ℝ) (hn : 0≤h) (tn : 0≤t) (unit : h^2+t^2=1) (order : t≤h) :
    0≤bottomValue C.side (bottomA C.side C.c C.s) (bottomB C.side C.c C.s) h t := by
  have coefficients := bottom_coefficients C side cap d
  have root := diagonal_bounds
  let r := Real.sqrt 2/2
  let H := (h+r)/2
  let T := (t+r)/2
  have rp : 0<r := by dsimp [r]; linarith only [root.1]
  have rs : r^2+r^2=1 := by dsimp [r]; nlinarith only [root.2.2]
  have tr : t≤r := by nlinarith only [unit,rs,order,tn,rp]
  have Hp : 0<H := by dsimp [H]; linarith only [hn,rp]
  have Tn : 0≤T := by dsimp [T]; positivity
  have bound : T+H/2≤9/8 := by
    have sum : h+t≤3/2 := by nlinarith only [unit,sq_nonneg (h-t),hn,tn]
    dsimp [T,H,r]
    linarith only [sum,tr,root.2.1]
  have boundWeight := mul_le_mul_of_nonneg_left bound (show 0≤C.side by linarith only [side])
  have bracket : C.side*(T+H/2)+bottomB C.side C.c C.s<0 := by
    linarith only [boundWeight,cap,coefficients.2]
  have first := mul_neg_of_pos_of_neg Hp bracket
  have last := mul_nonneg (show 0≤bottomA C.side C.c C.s by linarith only [coefficients.1]) Tn
  have square := mul_nonneg (show 0≤C.side by linarith only [side]) (sq_nonneg T)
  have derivative : C.side*(H*T+(H^2-T^2)/2)-bottomA C.side C.c C.s*T+
      bottomB C.side C.c C.s*H<0 := by nlinarith only [first,last,square]
  have product := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr tr) derivative.le
  have identity := bottom_difference C.side (bottomA C.side C.c C.s)
    (bottomB C.side C.c C.s) h t r r (by linarith only [unit,rs])
  have difference : 0≤H*(bottomValue C.side (bottomA C.side C.c C.s)
      (bottomB C.side C.c C.s) h t-
      bottomValue C.side (bottomA C.side C.c C.s) (bottomB C.side C.c C.s) r r) := by
    rw [identity]
    exact product
  have comparison := nonneg_of_mul_nonneg_right difference Hp
  have endpoint := bottom_diagonal C side d
  linarith only [comparison,endpoint]

theorem bottom_plus (C : OpenSquare) (side : 1<C.side) (d : Data C)
    (h t : ℝ) (hn : 0≤h) (tn : 0≤t) (unit : h^2+t^2=1)
    (sign : 0≤C.s*t-C.c*h) :
    0≤bottomValue C.side (bottomPlusA C.side C.c C.s) (bottomPlusB C.side C.c C.s) h t := by
  have p := profile C side d
  have cp : 0<C.c := by linarith only [(normal_bounds d.normal).1]
  have order := circle_order C.c C.s h t cp p.positive hn tn C.unit_normal unit sign
  have hc := half_specs C side d
  have hw := circle_data h t hn tn unit
  have zh := half_mono h t C.s C.c hn tn order.1 order.2 cp.le
  have positive : 0≤Arc.value C.side (bottomPlusA C.side C.c C.s)
      (bottomPlusB C.side C.c C.s) 0 := by
    have arc := C1092ShallowCentralScalars.arc d.normal
    have cross := mul_pos cp p.positive
    have extra := mul_pos (sub_pos.mpr side) (show 0<1+C.c+C.s by positivity)
    dsimp [Arc.value,cosH,sinH,bottomPlusB]
    norm_num
    nlinarith only [arc,cross,extra]
  have endpoint : 0≤Arc.value C.side (bottomPlusA C.side C.c C.s)
      (bottomPlusB C.side C.c C.s) (half C.c C.s) := by
    simpa only [Arc.value,←hc.2.2.2.1,←hc.2.2.2.2,bottomValue] using
      (aligned C side d).1.ge
  have bound := Arc.nonneg Arc.diagonal C.side (bottomPlusA C.side C.c C.s)
    (bottomPlusB C.side C.c C.s) 0 (half t h) (half C.c C.s)
    Arc.diagonal_data.1.le Arc.diagonal_data.2.2.1 (by linarith only [side])
    le_rfl hw.1 zh hc.2.2.1 positive endpoint
  simpa only [Arc.value,←hw.2.2.1,←hw.2.2.2,bottomValue] using bound

theorem bottom_minus (C : OpenSquare) (side : 1<C.side)
    (cap : C.side≤1001/1000) (d : Data C)
    (h t : ℝ) (hn : 0≤h) (tn : 0≤t) (unit : h^2+t^2=1)
    (sign : C.s*t-C.c*h≤0) :
    0≤bottomValue C.side (bottomA C.side C.c C.s) (bottomB C.side C.c C.s) h t := by
  by_cases low : t≤h
  · exact bottom_minus_low C side cap d h t hn tn unit low
  have cp : 0<C.c := by linarith only [(normal_bounds d.normal).1]
  have order := circle_order_reverse C.c C.s h t cp (profile C side d).positive
    hn tn C.unit_normal unit sign
  have hc := half_specs C side d
  have hw := circle_data h t hn tn unit
  have qz := half_mono C.s C.c h t d.normal.1 cp.le order.1 order.2 tn
  have dd := Arc.diagonal_data
  have zr : half t h≤Arc.diagonal := by
    have data := quarter_data t h tn hn (by nlinarith only [unit])
    have scaled := mul_le_mul_of_nonneg_left (lt_of_not_ge low).le (half_den_pos (half t h)).le
    rw [data.2.2.2.1,data.2.2.2.2] at scaled
    nlinarith only [scaled,dd.2.2.1,hw.1,dd.1]
  have left : 0≤Arc.value C.side (bottomA C.side C.c C.s)
      (bottomB C.side C.c C.s) (half C.c C.s) := by
    simpa only [Arc.value,←hc.2.2.2.1,←hc.2.2.2.2,bottomValue] using
      (aligned C side d).2.1.ge
  have right : 0≤Arc.value C.side (bottomA C.side C.c C.s)
      (bottomB C.side C.c C.s) Arc.diagonal := by
    simpa only [Arc.value,dd.2.2.2.1,dd.2.2.2.2,bottomValue] using bottom_diagonal C side d
  have bound := Arc.nonneg Arc.diagonal C.side (bottomA C.side C.c C.s)
    (bottomB C.side C.c C.s) (half C.c C.s) (half t h) Arc.diagonal
    dd.1.le dd.2.2.1 (by linarith only [side]) hc.1.le qz zr le_rfl left right
  simpa only [Arc.value,←hw.2.2.1,←hw.2.2.2,bottomValue] using bound

/-- On the upper half of the northwest quadrant, the exact midpoint
derivative of the left-plus gap is positive. -/
theorem left_plus (C : OpenSquare) (side : 1<C.side)
    (cap : C.side≤1001/1000) (d : Data C)
    (h t : ℝ) (hn : 0≤h) (tn : 0≤t) (unit : h^2+t^2=1)
    (sign : 0≤C.s*t-C.c*h) :
    0≤leftValue C.side (leftPlusA C.side C.c C.s) (leftPlusB C.side C.c C.s) h t := by
  have cb := central_bounds C side d
  have p := profile C side d
  have cp : 0<C.c := by linarith only [cb.1]
  have ord := circle_order C.c C.s h t cp p.positive hn tn C.unit_normal unit sign
  let H := (h+C.s)/2
  let T := (t+C.c)/2
  have Hp : 0<H := by dsimp [H]; linarith only [hn,p.positive]
  have Tlow : 7/10<T := by dsimp [T]; linarith only [ord.2,cb.1]
  have Tn : 0≤T := by linarith only [Tlow]
  have sum : h+t≤C.c+C.s := by
    have product := mul_nonneg (sub_nonneg.mpr ord.1)
      (show 0≤t+C.c-C.s-h by linarith only [ord.1,ord.2,d.normal.2.1])
    have weighted : 0≤(C.c+C.s-h-t)*(t+C.c) := by
      nlinarith only [product,C.unit_normal,unit]
    have gap := nonneg_of_mul_nonneg_left weighted (by linarith only [tn,cp])
    linarith only [gap]
  have direction : -(9/25)<C.c-H-T/2 := by
    dsimp [H,T]
    linarith only [sum,ord.1,cb.1,cb.2.2.1]
  have weight := mul_pos (show 0<C.side by linarith only [side])
    (show 0<C.c-H-T/2+9/25 by linarith only [direction])
  have bracket : 13/100<C.side*(C.c-H-T/2)+1-C.c*C.s := by
    nlinarith only [weight,cap,cb.2.2.2.1]
  have first := mul_pos (show 0<T by linarith only [Tlow])
    (show 0<C.side*(C.c-H-T/2)+1-C.c*C.s-13/100 by linarith only [bracket])
  have coefficient := left_plus_coefficient C side cap d
  have last := mul_pos Hp (show 0<leftPlusB C.side C.c C.s+11/50 by linarith only [coefficient])
  have excess := mul_nonneg (show 0≤C.side-1 by linarith only [side]) (sq_nonneg H)
  have derivative : 0<C.side*(-H*T+(H^2-T^2)/2)-leftPlusA C.side C.c C.s*T+
      leftPlusB C.side C.c C.s*H := by
    dsimp [leftPlusA]
    nlinarith only [first,last,excess,sq_nonneg (H-11/50),Tlow]
  have positive := mul_nonneg (sub_nonneg.mpr ord.2) derivative.le
  have identity := left_difference C.side (leftPlusA C.side C.c C.s)
    (leftPlusB C.side C.c C.s) h t C.s C.c (by nlinarith only [unit,C.unit_normal])
  have weighted : 0≤H*(leftValue C.side (leftPlusA C.side C.c C.s)
      (leftPlusB C.side C.c C.s) h t) := by
    rw [(aligned C side d).2.2.1,sub_zero] at identity
    rw [identity]
    exact positive
  exact nonneg_of_mul_nonneg_right weighted Hp

theorem left_minus_high (C : OpenSquare) (side : 1<C.side) (d : Data C)
    (h t : ℝ) (hn : 0≤h) (tn : 0≤t) (unit : h^2+t^2=1)
    (sign : C.s*t-C.c*h≤0) (order : h≤t) :
    0≤leftValue C.side (leftMinusA C.side C.c C.s) (leftMinusB C.side C.c C.s) h t := by
  have cb := central_bounds C side d
  have p := profile C side d
  have cp : 0<C.c := by linarith only [cb.1]
  have ord := circle_order_reverse C.c C.s h t cp p.positive hn tn C.unit_normal unit sign
  let H := (h+C.s)/2
  let T := (t+C.c)/2
  have Hp : 0<H := by dsimp [H]; linarith only [hn,p.positive]
  have Tp : 0<T := by dsimp [T]; linarith only [tn,cp]
  have HT : H≤T := by dsimp [H,T]; linarith only [order,d.normal.2.1]
  have sum : C.c+C.s≤h+t := by
    have product := mul_nonneg (sub_nonneg.mpr ord.2)
      (show 0≤C.c+t-h-C.s by linarith only [ord.1,ord.2,order,d.normal.2.1])
    have weighted : 0≤(h+t-C.c-C.s)*(h+C.s) := by
      nlinarith only [product,C.unit_normal,unit]
    have gap := nonneg_of_mul_nonneg_left weighted (by linarith only [hn,p.positive])
    linarith only [gap]
  have sumLow : 156/125<H+T := by dsimp [H,T]; linarith only [sum,cb.2.2.2.2.1]
  have ratio : (61/200)*T<H := by
    dsimp [H,T]
    linarith only [ord.1,ord.2,cb.2.2.2.2.2.2.2.1]
  have coefficients := left_minus_coefficients C side d
  have quadratic : -H*T+(H^2-T^2)/2≤0 := by
    have first := mul_nonneg (sub_nonneg.mpr HT) (show 0≤H+T by positivity)
    have last := mul_nonneg Hp.le Tp.le
    nlinarith only [first,last]
  have first := mul_nonpos_of_nonneg_of_nonpos (show 0≤C.side-1 by linarith only [side]) quadratic
  have second := mul_pos Tp (show 0<leftMinusA C.side C.c C.s+3/4 by linarith only [coefficients.1])
  have third := mul_pos Hp (show 0< -23/50-leftMinusB C.side C.c C.s by linarith only [coefficients.2])
  have square := mul_nonneg Hp.le (sub_nonneg.mpr HT)
  have sumWeight := mul_pos Tp (show 0<H+T-156/125 by linarith only [sumLow])
  have derivative : C.side*(-H*T+(H^2-T^2)/2)-leftMinusA C.side C.c C.s*T+
      leftMinusB C.side C.c C.s*H<0 := by
    nlinarith only [first,second,third,square,sumWeight,ratio,Tp]
  have positive := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr ord.2) derivative.le
  have identity := left_difference C.side (leftMinusA C.side C.c C.s)
    (leftMinusB C.side C.c C.s) h t C.s C.c (by nlinarith only [unit,C.unit_normal])
  have weighted : 0≤H*(leftValue C.side (leftMinusA C.side C.c C.s)
      (leftMinusB C.side C.c C.s) h t) := by
    rw [(aligned C side d).2.2.2,sub_zero] at identity
    rw [identity]
    exact positive
  exact nonneg_of_mul_nonneg_right weighted Hp

/-- The lower quadrant follows directly from its diagonal endpoint and
the coefficient bound. This exact square decomposition includes h=t. -/
theorem left_minus_low (C : OpenSquare) (side : 1<C.side) (d : Data C)
    (h t : ℝ) (hn : 0≤h) (tn : 0≤t) (unit : h^2+t^2=1) (order : t≤h) :
    0≤leftValue C.side (leftMinusA C.side C.c C.s) (leftMinusB C.side C.c C.s) h t := by
  have coefficients := left_minus_coefficients C side d
  have root := diagonal_bounds
  let r := Real.sqrt 2
  have rp : 0<r := by dsimp [r]; linarith only [root.1]
  have rs : (r/2)^2+(r/2)^2=1 := by dsimp [r]; nlinarith only [root.2.2]
  have sign : C.s*(r/2)-C.c*(r/2)≤0 := by
    have weighted := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr d.normal.2.1)
      (show 0≤r/2 by positivity)
    nlinarith only [weighted]
  have diagonal := left_minus_high C side d (r/2) (r/2) (by positivity) (by positivity) rs sign le_rfl
  have endpoint : 0≤C.side*r+leftMinusA C.side C.c C.s+leftMinusB C.side C.c C.s := by
    have weighted := mul_nonneg rp.le diagonal
    have identity : r*leftValue C.side (leftMinusA C.side C.c C.s)
        (leftMinusB C.side C.c C.s) (r/2) (r/2)=
        C.side*r+leftMinusA C.side C.c C.s+leftMinusB C.side C.c C.s := by
      dsimp [leftValue]
      linear_combination (C.side*r/4+
        (leftMinusA C.side C.c C.s+leftMinusB C.side C.c C.s)/2)*root.2.2
    rwa [identity] at weighted
  have A : -(3/4)*C.side≤leftMinusA C.side C.c C.s := by
    linarith only [coefficients.1,side]
  have first := mul_nonneg (sub_nonneg.mpr A) (sub_nonneg.mpr order)
  have last := mul_nonneg tn endpoint
  have sumLow : 1≤h+t := by nlinarith only [unit,mul_nonneg hn tn,hn,tn]
  have bracket : 0≤(h+t)/4+r/2-3/4 := by
    dsimp [r]
    linarith only [sumLow,root.1]
  have chord := add_nonneg (div_nonneg (sq_nonneg (r-h-t)) (by norm_num : (0:ℝ)≤4))
    (mul_nonneg (sub_nonneg.mpr order) bracket)
  have identity : (1+h^2+h*t)/2-r*t-(3/4)*(h-t)=
      (r-h-t)^2/4+(h-t)*((h+t)/4+r/2-3/4) := by
    linear_combination -(1/4)*root.2.2
  have base : 0≤(1+h^2+h*t)/2-r*t-(3/4)*(h-t) := by rwa [←identity] at chord
  have weighted := mul_nonneg (show 0≤C.side by linarith only [side]) base
  dsimp [leftValue]
  nlinarith only [first,last,weighted]

theorem left_minus (C : OpenSquare) (side : 1<C.side) (d : Data C)
    (h t : ℝ) (hn : 0≤h) (tn : 0≤t) (unit : h^2+t^2=1)
    (sign : C.s*t-C.c*h≤0) :
    0≤leftValue C.side (leftMinusA C.side C.c C.s) (leftMinusB C.side C.c C.s) h t := by
  by_cases order : h≤t
  · exact left_minus_high C side d h t hn tn unit sign order
  · exact left_minus_low C side d h t hn tn unit (lt_of_not_ge order).le

def bottomGap (a c s J K h t : ℝ) : ℝ :=
  -h*b a c s K-2*t+(a/2)*(1+t^2+h*t)-
    ((s*t-c*h)*J+(s*h+c*t)*(K-a)-a*max (s*t-c*h) 0)

def leftGap (a c s J K h t : ℝ) : ℝ :=
  (s*t-c*h)*J+(s*h+c*t)*K+a*max (c*h-s*t) 0-
    (2*h+t*ell a c s K-(a/2)*(1+h^2+h*t))

theorem margins (C : OpenSquare) (side : 1<C.side) (cap : C.side≤1001/1000)
    (d : Data C) (h t : ℝ) (hn : 0≤h) (tn : 0≤t) (unit : h^2+t^2=1) :
    0≤bottomGap C.side C.c C.s (C.loU+C.side) (C.loV+C.side) h t ∧
      0≤leftGap C.side C.c C.s (C.loU+C.side) (C.loV+C.side) h t := by
  have p := profile C side d
  have cp : 0<C.c := by linarith only [(normal_bounds d.normal).1]
  have sp := p.positive
  have hc := half_specs C side d
  have hw := circle_data h t hn tn unit
  let q := half C.c C.s
  have cf : C.c=cosH q := hc.2.2.2.1
  have sf : C.s=sinH q := hc.2.2.2.2
  let delta := C.s*t-C.c*h
  by_cases sign : 0≤delta
  · have bp := bottom_plus C side d h t hn tn unit sign
    have lp := left_plus C side cap d h t hn tn unit sign
    have bottomIdentity : bottomGap C.side C.c C.s (C.loU+C.side) (C.loV+C.side) h t=
        bottomValue C.side (bottomPlusA C.side C.c C.s) (bottomPlusB C.side C.c C.s) h t+
        delta*(-(13/50)*C.c-(C.loU+C.side))+
        (C.c*delta/C.s)*(C.s-(C.loV+C.side)) := by
      dsimp [bottomGap]
      rw [max_eq_left sign]
      dsimp [bottomValue,bottomPlusA,bottomPlusB,b,delta]
      rw [cf,sf]
      dsimp [cosH,sinH]
      field_simp [hc.1.ne',(half_den_pos q).ne'] <;> ring
    have leftIdentity : leftGap C.side C.c C.s (C.loU+C.side) (C.loV+C.side) h t=
        leftValue C.side (leftPlusA C.side C.c C.s) (leftPlusB C.side C.c C.s) h t+
        delta*((C.loU+C.side)-(C.side-C.c-C.s))+
        (C.s*delta/C.c)*(C.s-(C.loV+C.side)) := by
      dsimp [leftGap]
      rw [max_eq_right (show C.c*h-C.s*t≤0 by dsimp [delta] at sign; linarith only [sign])]
      dsimp [leftValue,leftPlusA,leftPlusB,ell,delta]
      rw [cf,sf]
      dsimp [cosH,sinH]
      have square : 0<1-q^2 := by nlinarith only [hc.1,hc.2.1]
      field_simp [square.ne',(half_den_pos q).ne'] <;> ring
    constructor
    · rw [bottomIdentity]
      exact add_nonneg (add_nonneg bp (mul_nonneg sign (sub_nonneg.mpr p.upperU)))
        (mul_nonneg (div_nonneg (mul_nonneg cp.le sign) sp.le) (sub_nonneg.mpr p.upperV))
    · rw [leftIdentity]
      exact add_nonneg (add_nonneg lp (mul_nonneg sign (by linarith only [p.lowerU])))
        (mul_nonneg (div_nonneg (mul_nonneg sp.le sign) cp.le) (sub_nonneg.mpr p.upperV))
  · have negative : delta≤0 := (lt_of_not_ge sign).le
    have bp := bottom_minus C side cap d h t hn tn unit negative
    have lp := left_minus C side d h t hn tn unit negative
    have bottomIdentity : bottomGap C.side C.c C.s (C.loU+C.side) (C.loV+C.side) h t=
        bottomValue C.side (bottomA C.side C.c C.s) (bottomB C.side C.c C.s) h t+
        (-delta)*((C.loU+C.side)-(C.side-C.c-C.s))+
        (-C.c*delta/C.s)*((C.loV+C.side)-(C.side+(14/25)*C.s-C.c)) := by
      dsimp [bottomGap]
      rw [max_eq_right negative]
      dsimp [bottomValue,bottomA,bottomB,b,delta]
      rw [cf,sf]
      dsimp [cosH,sinH]
      field_simp [hc.1.ne',(half_den_pos q).ne'] <;> ring
    have leftIdentity : leftGap C.side C.c C.s (C.loU+C.side) (C.loV+C.side) h t=
        leftValue C.side (leftMinusA C.side C.c C.s) (leftMinusB C.side C.c C.s) h t+
        (-delta)*(-(13/50)*C.c-(C.loU+C.side))+
        (-C.s*delta/C.c)*((C.loV+C.side)-(C.side+(14/25)*C.s-C.c)) := by
      dsimp [leftGap]
      rw [max_eq_left (show 0≤C.c*h-C.s*t by dsimp [delta] at negative; linarith only [negative])]
      dsimp [leftValue,leftMinusA,leftMinusB,ell,delta]
      rw [cf,sf]
      dsimp [cosH,sinH]
      have square : 0<1-q^2 := by nlinarith only [hc.1,hc.2.1]
      field_simp [square.ne',(half_den_pos q).ne'] <;> ring
    constructor
    · rw [bottomIdentity]
      exact add_nonneg (add_nonneg bp (mul_nonneg (neg_nonneg.mpr negative) (by linarith only [p.lowerU])))
        (mul_nonneg (div_nonneg (by nlinarith only [mul_nonpos_of_nonneg_of_nonpos cp.le negative]) sp.le)
          (by linarith only [p.lowerV]))
    · rw [leftIdentity]
      exact add_nonneg (add_nonneg lp (mul_nonneg (neg_nonneg.mpr negative) (sub_nonneg.mpr p.upperU)))
        (mul_nonneg (div_nonneg (by nlinarith only [mul_nonpos_of_nonneg_of_nonpos sp.le negative]) cp.le)
          (by linarith only [p.lowerV]))

#print axioms margins

end
end N12Compact.C1092MPPMMissingPositiveBoundaries.Envelopes
