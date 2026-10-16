import Compact.Completion.C1092.MPPMMissingPositiveBoundArc

/-! Exact continuous coefficient bounds for sections 5--6. Finite circle
differences replace the prose derivatives. The only side cap is the
original a <= 1.001; there are no sampled angle or pose hypotheses.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMMissingPositiveBoundaries.Scalars
open S12 S12Pilot C977CornerCubic C1092WallProfileScalars C1092ShallowPositiveScalars
set_option Elab.async false
noncomputable section

def bottomA (a c s : ℝ) : ℝ := a*((c+s)/2-1/s)+c/s-(11/25)*c^2
def bottomB (a c s : ℝ) : ℝ := -a*s-1+(11/25)*c*s
def leftPlusA (a c s : ℝ) : ℝ := -a*c-1+c*s
def leftPlusB (a c s : ℝ) : ℝ := a*((c+s)/2-1/c)+s/c-s^2
def leftMinusA (a c s : ℝ) : ℝ := a*(c+s)-(3/10)*c^2-c*s-36/25
def leftMinusB (a c s : ℝ) : ℝ :=
  -a*((1+s*(c+s))/(2*c)+s+s^2/c)+(3/10)*c*s+s^2+(36/25)*s/c

theorem half_specs (C : OpenSquare) (side : 1<C.side) (h : Data C) :
    let q := half C.c C.s
    0<q ∧ q<1/2 ∧ q≤Arc.diagonal ∧ C.c=cosH q ∧ C.s=sinH q := by
  let q := half C.c C.s
  have p := profile C side h
  have cp : 0<C.c := by linarith only [(normal_bounds h.normal).1]
  have qn : 0≤q := (quarter_data C.c C.s cp.le h.normal.1 h.normal.2.2).1
  have hd := quarter_data C.c C.s cp.le h.normal.1 h.normal.2.2
  have den := half_den_pos q
  have cf : C.c=cosH q := by
    dsimp [cosH]
    apply (eq_div_iff den.ne').mpr
    nlinarith only [hd.2.2.2.1]
  have sf : C.s=sinH q := by
    dsimp [sinH]
    apply (eq_div_iff den.ne').mpr
    nlinarith only [hd.2.2.2.2]
  have order : q^2+2*q≤1 := by
    have weighted := mul_le_mul_of_nonneg_left h.normal.2.1 den.le
    rw [hd.2.2.2.1,hd.2.2.2.2] at weighted
    linarith only [weighted]
  have dd := Arc.diagonal_data
  have qd : q≤Arc.diagonal := by
    by_contra failed
    have gap : 0<q-Arc.diagonal := sub_pos.mpr (lt_of_not_ge failed)
    have product := mul_pos gap (show 0<q+Arc.diagonal+2 by linarith only [qn,dd.1])
    nlinarith only [order,dd.2.2.1,product]
  exact ⟨by linarith only [p.halfLow],p.halfHigh,qd,cf,sf⟩

theorem bottom_coefficients (C : OpenSquare) (side : 1<C.side)
    (cap : C.side≤1001/1000) (h : Data C) :
    3/100<bottomA C.side C.c C.s ∧ bottomB C.side C.c C.s< -(1453/1250) := by
  have b := central_bounds C side h
  have p := profile C side h
  have cp : 0<C.c := by linarith only [b.1]
  have sp : 0<C.s := p.positive
  let q := half C.c C.s
  have hs := half_specs C side h
  have qn : 0≤q := hs.1.le
  have qu : q≤1/2 := hs.2.1.le
  have cf : C.c=cosH q := hs.2.2.2.1
  have sf : C.s=sinH q := hs.2.2.2.2
  have square : q^2≤1/4 := by
    nlinarith only [mul_nonneg (show 0≤1/2-q by linarith only [qu])
      (show 0≤1/2+q by linarith only [qn])]
  have cube : q^3≤1/8 := by
    have first := mul_le_mul_of_nonneg_right square qn
    nlinarith only [first,qu]
  have bracket : -(7/2)≤40-50*q-49*q^2-50*q^3 := by
    nlinarith only [qu,square,cube]
  have polynomial : 0<1+q^2*(40-50*q-49*q^2-50*q^3) := by
    have weighted := mul_le_mul_of_nonneg_left bracket (sq_nonneg q)
    nlinarith only [weighted,square]
  have identity : 50*(1+q^2)^2*(bottomA 1 C.c C.s-1/25)=
      1+q^2*(40-50*q-49*q^2-50*q^3) := by
    rw [cf,sf]
    dsimp [bottomA,cosH,sinH]
    have qne : q ≠ 0 := hs.1.ne'
    field_simp [qne,(half_den_pos q).ne']
    <;> ring
  have base : 1/25<bottomA 1 C.c C.s := by
    have product : 0<50*(1+q^2)^2*(bottomA 1 C.c C.s-1/25) := by
      rw [identity]
      exact polynomial
    exact sub_pos.mp (pos_of_mul_pos_right product (by positivity))
  have first : 3/100<bottomA C.side C.c C.s := by
    have extra := mul_nonneg (show 0≤C.side-1 by linarith only [side])
      (mul_nonneg sp.le (show 0≤(C.c+C.s)/2 by linarith only [cp,sp]))
    have weighted := mul_pos sp (sub_pos.mpr base)
    have correction : C.s*(bottomA C.side C.c C.s-bottomA 1 C.c C.s)=
        (C.side-1)*(C.s*(C.c+C.s)/2-1) := by
      dsimp [bottomA]
      field_simp [sp.ne']
      <;> ring
    have positive : 0<C.s*(bottomA C.side C.c C.s-3/100) := by
      nlinarith only [extra,weighted,correction,cap,b.2.1]
    exact sub_pos.mp (pos_of_mul_pos_right positive sp.le)
  have second : bottomB C.side C.c C.s< -(1453/1250) := by
    have weighted := mul_pos sp (sub_pos.mpr side)
    have cosine := mul_nonneg sp.le
      (sub_nonneg.mpr (normal_bounds h.normal).2.1)
    dsimp [bottomB]
    nlinarith only [weighted,cosine,b.2.1]
  exact ⟨first,second⟩

/-- A cubic chord gives the left-plus coefficient bound. The tangent
c <= 1-s^2/2 makes the comparison one-dimensional on [.29,.71]. -/
theorem left_plus_coefficient (C : OpenSquare) (side : 1<C.side)
    (cap : C.side≤1001/1000) (h : Data C) :
    -(11/50)<leftPlusB C.side C.c C.s := by
  have b := central_bounds C side h
  have p := profile C side h
  have cp : 0<C.c := by linarith only [b.1]
  have sn : 0≤C.s := h.normal.1
  have su : C.s<1 := by linarith only [b.2.2.1]
  let B1 := (C.c+C.s)/2-C.c/(1+C.s)-C.s^2
  let N := fun s : ℝ => -57/100+(243/100)*s-s^2/2-(5/2)*s^3
  have identity (s : ℝ) :
      (71/100-29/100)*N s=
        (71/100-s)*N (29/100)+(s-29/100)*N (71/100)+
        (71/100-29/100)*(s-29/100)*(71/100-s)*(3+(5/2)*s) := by
    dsimp [N]
    ring
  have left : 0<N (29/100) := by norm_num [N]
  have right : 0<N (71/100) := by norm_num [N]
  have one := mul_pos (show 0<71/100-C.s by linarith only [b.2.2.1]) left
  have two := mul_nonneg (show 0≤C.s-29/100 by linarith only [b.2.1]) right.le
  have lower : 0≤C.s-29/100 := by linarith only [b.2.1]
  have upper : 0≤71/100-C.s := by linarith only [b.2.2.1]
  have three : 0≤(71/100-29/100)*(C.s-29/100)*(71/100-C.s)*(3+(5/2)*C.s) := by
    positivity
  have positive : 0<N C.s := by nlinarith only [identity C.s,one,two,three]
  have tangent : C.c≤1-C.s^2/2 := by
    nlinarith only [h.normal.2.2,sq_nonneg (C.c-1)]
  have weight := mul_le_mul_of_nonpos_right tangent
    (show C.s-1≤0 by linarith only [su])
  have numerator : 2*(1+C.s)*(B1+43/200)=
      C.c*(C.s-1)+C.s-C.s^2-2*C.s^3+(43/100)*(1+C.s) := by
    dsimp [B1]
    field_simp [(show 1+C.s≠0 by positivity)]
    <;> ring
  have lower : N C.s≤2*(1+C.s)*(B1+43/200) := by
    rw [numerator]
    dsimp [N]
    nlinarith only [weight]
  have base : -(43/200)<B1 := by
    have product : 0<2*(1+C.s)*(B1+43/200) := positive.trans_le lower
    have last := pos_of_mul_pos_right product (show 0≤2*(1+C.s) by positivity)
    linarith only [last]
  have identity' : C.c*(leftPlusB C.side C.c C.s-B1)=
      (C.side-1)*(C.c*(C.c+C.s)/2-1) := by
    have fraction : C.c^2/(1+C.s)=1-C.s := by
      apply (div_eq_iff (show 1+C.s≠0 by positivity)).mpr
      nlinarith only [h.normal.2.2]
    calc
      _ = (C.side-1)*C.c*(C.c+C.s)/2-C.side+C.s+C.c^2/(1+C.s) := by
        dsimp [leftPlusB,B1]
        field_simp [cp.ne',(show 1+C.s≠0 by positivity)]
        <;> ring
      _ = _ := by rw [fraction]; ring
  have extra := mul_nonneg (show 0≤C.side-1 by linarith only [side])
    (show 0≤C.c*(C.c+C.s)/2 by positivity)
  have first := mul_pos cp (show 0<B1+43/200 by linarith only [base])
  have result : 0<C.c*(leftPlusB C.side C.c C.s+11/50) := by
    nlinarith only [identity',extra,first,cap,b.1]
  have last := pos_of_mul_pos_right result cp.le
  linarith only [last]

private theorem left_minus_at_one (C : OpenSquare) (side : 1<C.side) (h : Data C) :
    -(3/4)<leftMinusA 1 C.c C.s := by
  have b := central_bounds C side h
  let c0 : ℝ := 3700/3869
  let s0 : ℝ := 1131/3869
  let c := (C.c+c0)/2
  let s := (C.s+s0)/2
  have cp : 0<c := by dsimp [c,c0]; linarith only [b.1]
  have sp : 0<s := by dsimp [s,s0]; linarith only [b.2.1]
  have order : 0≤c-s := by
    dsimp [c,s,c0,s0]
    linarith only [h.normal.2.1]
  have sum : 156/125<c+s := by
    dsimp [c,s,c0,s0]
    linarith only [b.2.2.2.2.1]
  have diff : c-s<133/200 := by
    dsimp [c,s,c0,s0]
    linarith only [b.2.2.2.2.2.2.1]
  have unit : c^2+s^2≤1 := by
    dsimp [c,s,c0,s0]
    nlinarith only [h.normal.2.2,sq_nonneg (C.c-3700/3869),sq_nonneg (C.s-1131/3869)]
  have bracket : 0<(3/5)*(1+c+s)-2*(c-s) := by linarith only [sum,diff]
  have first := mul_pos (mul_pos cp sp) bracket
  have correction := mul_nonneg order (show 0≤1-c^2-s^2 by linarith only [unit])
  have derivative : 0<(c-s)*(1-c-s)+(3/5)*c*s := by
    have product : 0<(1+c+s)*((c-s)*(1-c-s)+(3/5)*c*s) := by
      nlinarith only [first,correction]
    exact pos_of_mul_pos_right product (by positivity)
  have relation : c*(c0-C.c)=s*(C.s-s0) := by
    dsimp [c,s,c0,s0]
    nlinarith only [h.normal.2.2]
  have identity : c*(leftMinusA 1 C.c C.s-leftMinusA 1 c0 s0)=
      (C.s-s0)*((c-s)*(1-c-s)+(3/5)*c*s) := by
    dsimp [leftMinusA,c,s]
    linear_combination (-1+(3/5)*((C.c+c0)/2)+(C.s+s0)/2)*relation
  have weighted : 0≤c*(leftMinusA 1 C.c C.s-leftMinusA 1 c0 s0) := by
    rw [identity]
    exact mul_nonneg (by dsimp [s0]; linarith only [b.2.2.2.2.2.2.2.2.2]) derivative.le
  have comparison := nonneg_of_mul_nonneg_right weighted cp
  have endpoint : -(3/4)<leftMinusA 1 c0 s0 := by norm_num [leftMinusA,c0,s0]
  linarith only [comparison,endpoint]

theorem left_minus_coefficients (C : OpenSquare) (side : 1<C.side) (h : Data C) :
    -(3/4)<leftMinusA C.side C.c C.s ∧ leftMinusB C.side C.c C.s< -(23/50) := by
  have b := central_bounds C side h
  have p := profile C side h
  have cp : 0<C.c := by linarith only [b.1]
  have sp : 0<C.s := p.positive
  have first : -(3/4)<leftMinusA C.side C.c C.s := by
    have base := left_minus_at_one C side h
    have extra := mul_pos (sub_pos.mpr side) (show 0<C.c+C.s by positivity)
    dsimp [leftMinusA] at base ⊢
    nlinarith only [base,extra]
  let q := half C.c C.s
  have hs := half_specs C side h
  have qn : 0≤q := hs.1.le
  have qu : q≤1/2 := hs.2.1.le
  have cf : C.c=cosH q := hs.2.2.2.1
  have sf : C.s=sinH q := hs.2.2.2.2
  let P := 24*q^6-162*q^5+299*q^4-114*q^3+76*q^2-12*q+1
  have quadratic : 0<40-114*q+218*q^2 := by
    nlinarith only [sq_nonneg (q-57/218)]
  have extra := mul_nonneg (sq_nonneg q) (show 0≤1-2*q by linarith only [qu])
  have bracket : 0<40-114*q+299*q^2-162*q^3+24*q^4 := by
    nlinarith only [quadratic,extra,sq_nonneg (q^2)]
  have positive : 0<P := by
    have last := mul_pos (sq_pos_of_pos hs.1) bracket
    have identity : P=(1-6*q)^2+q^2*(40-114*q+299*q^2-162*q^3+24*q^4) := by dsimp [P]; ring
    rw [identity]
    nlinarith only [last,sq_nonneg (1-6*q)]
  have square : q^2≤1/4 := by
    have product := mul_nonneg (show 0≤1/2-q by linarith only [qu])
      (show 0≤1/2+q by linarith only [qn])
    nlinarith only [product]
  have den : 0<25*(1-q^2)*(1+q^2)^2 := by
    have positive : 0<1-q^2 := by linarith only [square]
    positivity
  have identity : 25*(1-q^2)*(1+q^2)^2*(leftMinusB 1 C.c C.s+23/50)=-P := by
    rw [cf,sf]
    dsimp [leftMinusB,P,cosH,sinH]
    field_simp [(half_den_pos q).ne',(show 1-q^2≠0 by linarith only [square])]
    <;> ring
  have base : leftMinusB 1 C.c C.s< -(23/50) := by
    by_contra failed
    have bad := mul_nonneg den.le (show 0≤leftMinusB 1 C.c C.s+23/50 by linarith only [failed])
    rw [identity] at bad
    linarith only [positive,bad]
  have weight : 0<(1+C.s*(C.c+C.s))/(2*C.c)+C.s+C.s^2/C.c := by positivity
  have decrease := mul_pos (sub_pos.mpr side) weight
  have second : leftMinusB C.side C.c C.s< -(23/50) := by
    dsimp [leftMinusB] at base ⊢
    nlinarith only [base,decrease]
  exact ⟨first,second⟩

#print axioms bottom_coefficients
#print axioms left_plus_coefficient
#print axioms left_minus_coefficients
end
end N12Compact.C1092MPPMMissingPositiveBoundaries.Scalars
