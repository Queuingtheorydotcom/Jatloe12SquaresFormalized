import Compact.Completion.OtherCases.SharpPointScalars

/-! The two uniform coupled-support margins for the outward southeast
pair. A single positive cubic and rational circle endpoint replace every
calculus step in C974-C976-OUTWARD-PAIR. -/
namespace N12Compact.Completion.OtherCases.OutwardPairScalars
open C1092WallProfileScalars
set_option Elab.async false

private theorem cubic_positive (t : ℝ) (tn : 0≤t) (tu : t≤3/10) :
    0 < 20-66*t+40*t^2-75*t^3 := by
  have bracket : 0 ≤ 75*t^2-(35/2)*t+243/4 := by
    nlinarith only [sq_nonneg t,tu]
  have remainder := mul_nonneg (sub_nonneg.mpr tu) bracket
  have identity : 20-66*t+40*t^2-75*t^3 =
      71/40+(3/10-t)*(75*t^2-(35/2)*t+243/4) := by ring
  linarith only [identity,remainder]

private theorem norm_gap (c s : ℝ) (cp : 0<c) (sp : 0<s) (unit : c^2+s^2=1)
    (cutoff : half c s < 3/10) :
    (2-c-s+(1/5)*c*s)^2+(1-c+s-(1/5)*s^2)^2 < 1 := by
  let t := half c s
  let D := 1+t^2
  have data := quarter_data c s cp.le sp.le unit
  have tp : 0<t := div_pos sp (by linarith only [cp])
  have dt : 0<D := by dsimp only [D]; nlinarith only [sq_nonneg t]
  have cform : D*c=1-t^2 := data.2.2.2.1
  have sform : D*s=2*t := data.2.2.2.2
  have polynomial := cubic_positive t tp.le cutoff.le
  have positive := mul_pos (show 0<4*t by linarith only [tp]) polynomial
  have reduction : 1-(2-c-s+(1/5)*c*s)^2-(1-c+s-(1/5)*s^2)^2 =
      6*(c-1)+(12/5)*s+(9/25)*s^2-(4/5)*c*s := by
    linear_combination (-2-s^2/25+(2/5)*s)*unit
  have identity : 25*D^2*(1-(2-c-s+(1/5)*c*s)^2-(1-c+s-(1/5)*s^2)^2)=
      4*t*(20-66*t+40*t^2-75*t^3) := by
    rw [reduction]
    calc
      _ = 25*(6*D*(D*c-D)+(12/5)*D*(D*s)+
          (9/25)*(D*s)^2-(4/5)*(D*c)*(D*s)) := by ring
      _ = _ := by rw [cform,sform]; dsimp only [D]; ring
  have scaled : 0 < 25*D^2*(1-(2-c-s+(1/5)*c*s)^2-(1-c+s-(1/5)*s^2)^2) := by
    rwa [identity]
  have weight : 0 < 25*D^2 := mul_pos (by norm_num) (sq_pos_of_pos dt)
  have gap := (mul_pos_iff_of_pos_left weight).mp scaled
  linarith only [gap]

theorem first_margin (c s C S : ℝ) (cp : 0<c) (sp : 0<s)
    (unit : c^2+s^2=1) (otherUnit : C^2+S^2=1)
    (cutoff : half c s < 3/10) :
    0 < 1+(c*S+s*C)+(c*C-s*S)-
      (c*S+s*C)*(c+s)-(c*C-s*S)*(c-(4/5)*s)-C := by
  let A := 2-c-s+(1/5)*c*s
  let B := 1-c+s-(1/5)*s^2
  have norm : A^2+B^2 < 1 := norm_gap c s cp sp unit cutoff
  have dotIdentity : (A*C+B*S)^2+(A*S-B*C)^2=A^2+B^2 := by
    linear_combination (A^2+B^2)*otherUnit
  have dot : A*C+B*S < 1 := by
    nlinarith only [norm,dotIdentity,sq_nonneg (A*S-B*C),sq_nonneg (A*C+B*S-1)]
  have identity : 1+(c*S+s*C)+(c*C-s*S)-
      (c*S+s*C)*(c+s)-(c*C-s*S)*(c-(4/5)*s)-C=1-A*C-B*S := by
    dsimp only [A,B]
    linear_combination -(C+S)*unit
  rw [identity]
  linarith only [dot]

theorem second_margin (c s C S : ℝ) (cp : 0<c) (sn : 0≤s) (order : s≤c)
    (unit : c^2+s^2=1) (Cp : 0<C) (Sn : 0≤S) (otherOrder : S≤C)
    (otherUnit : C^2+S^2=1) (cutoff : half c s < 3/10) :
    0 < 1+(c*C-s*S)+(c*S+s*C)+(7/20)*(c*C-s*S)*(S-C)-
      (c*S+s*C)*C-c-s := by
  let A := 1-C-S+(7/20)*C^2+(13/20)*C*S
  let B := 2-C+S-(13/20)*S^2-(7/20)*C*S
  have bounds := CommonCases.CanonicalScalars.bounds C S Cp Sn otherOrder otherUnit
  have cross := mul_nonneg Cp.le Sn
  have squareS := sq_nonneg S
  have aBound : A ≤ 7/20 := by
    dsimp only [A]
    nlinarith only [bounds.2.2.2.2,cross,squareS,otherUnit]
  have crossUpper : C*S ≤ 1/2 := by nlinarith only [otherUnit,sq_nonneg (C-S)]
  have smallSquare : (1-C)^2 < 9/100 := by
    have product := mul_pos (show 0<C-7/10 by linarith only [bounds.1])
      (show 0<13/10-C by linarith only [bounds.2.1])
    nlinarith only [product]
  have sumIdentity : A+B=27/20+(1-C)^2+(3/10)*C*S := by
    dsimp only [A,B]
    linear_combination -(13/20)*otherUnit
  have sumBound : A+B ≤ 8/5 := by linarith only [sumIdentity,smallSquare,crossUpper]
  have first := mul_nonneg (sub_nonneg.mpr order) (sub_nonneg.mpr aBound)
  have last := mul_nonneg sn (sub_nonneg.mpr sumBound)
  have dotBound : A*c+B*s ≤ (7/20)*c+(5/4)*s := by
    nlinarith only [first,last]
  have circle := SharpPointScalars.half_before c s (91/109) (60/109) (3/10)
    cp sn unit (by norm_num) (by norm_num) (by norm_num) cutoff.le
  have projection := CommonCases.CanonicalProjection.before c s (91/109) (60/109)
    (7/20) (5/4) unit (by norm_num) circle (by norm_num) (by norm_num)
  have dot : A*c+B*s < 1 := by linarith only [dotBound,projection]
  have identity : 1+(c*C-s*S)+(c*S+s*C)+(7/20)*(c*C-s*S)*(S-C)-
      (c*S+s*C)*C-c-s=1-A*c-B*s := by
    dsimp only [A,B]
    linear_combination -s*otherUnit
  rw [identity]
  linarith only [dot]

#print axioms first_margin
#print axioms second_margin
end N12Compact.Completion.OtherCases.OutwardPairScalars

