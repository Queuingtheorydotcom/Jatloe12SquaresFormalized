import Compact.Completion.C1092.ShallowCentralScalars
import Compact.Completion.C1092.WallProfileScalars

/-! The entire northwest bottom support comparison, using the same
central faces A and K in both relative-angle intervals. The coordinate
endpoint h=0 retains its independent strict margin. -/
namespace N12Compact.C1092ShallowBottomMargin
open C977CornerCubic C1092ShallowPositiveScalars C1092ShallowCentralScalars
set_option Elab.async false
noncomputable section

def gap (a c s A K h t : ℝ) : ℝ :=
  -h*b a c s K-2*t+(a/2)*(1+t^2+h*t)-
    ((s*t-c*h)*A+(s*h+c*t)*(K-a)-a*max (s*t-c*h) 0)

private theorem upper_endpoint (a x : ℝ) (side : 1<a) (xp : 0<x) (xu : x≤1/4) :
    0<C1092ShallowBottom.upper a x 1 := by
  have cosine : cosH 1=0 := by norm_num [cosH]
  have sine : sinH 1=1 := by norm_num [sinH]
  have identity : C1092ShallowBottom.upper a x 1=
      a*(1+cosH x+sinH x)-2-cosH x*sinH x+(sinH x)^2/2 := by
    dsimp [C1092ShallowBottom.upper]
    rw [cosine,sine]
    dsimp [wallWeight]
    rw [cosine,sine]
    ring
  have cp := half_cos_pos x xp.le (by linarith only [xu])
  have sp := half_sin_pos x xp
  have excess := mul_pos (sub_pos.mpr side)
    (show 0<1+cosH x+sinH x by linarith only [cp,sp])
  have base := bottom_far_endpoint_pos x xp xu
  rw [identity]
  calc
    _ = (a-1)*(1+cosH x+sinH x)+
        (cosH x+sinH x-1-cosH x*sinH x+(sinH x)^2/2) := by ring
    _ > 0 := add_pos excess base

theorem margin (a c s A K h t x : ℝ) (side : 1<a)
    (xp : 0<x) (xu : x≤1/4) (cframe : c=cosH x) (sframe : s=sinH x)
    (hn : 0≤h) (tn : 0≤t) (unit : h^2+t^2=1)
    (Alow : a-c-s≤A) (Ahigh : A≤-s/2)
    (Klow : a+(14/25)*s-c≤K) (Khigh : K≤s)
    (intrinsic : a≤c+(11/25)*s) :
    0≤gap a c s A K h t ∧ (h=0 → 0<gap a c s A K h t) := by
  have cp : 0<c := by rw [cframe]; exact half_cos_pos x xp.le (by linarith only [xu])
  have sp : 0<s := by rw [sframe]; exact half_sin_pos x xp
  let z := C1092WallProfileScalars.half h t
  have quarter := C1092WallProfileScalars.quarter_data h t hn tn unit
  have zn : 0≤z := quarter.1
  have zu : z≤1 := quarter.2.1
  have hspec : h=cosH z := by
    dsimp [cosH]
    apply (eq_div_iff (half_den_pos z).ne').mpr
    nlinarith only [quarter.2.2.2.1]
  have tspec : t=sinH z := by
    dsimp [sinH]
    apply (eq_div_iff (half_den_pos z).ne').mpr
    nlinarith only [quarter.2.2.2.2]
  let delta := s*t-c*h
  have factor : (1+x^2)*(1+z^2)*delta=
      (x*z+x+z-1)*(1+x+z-x*z) := by
    dsimp [delta]
    rw [cframe,sframe,hspec,tspec]
    dsimp [cosH,sinH]
    field_simp [(half_den_pos x).ne',(half_den_pos z).ne']
    <;> ring
  have other : 0<1+x+z-x*z := by
    have product := mul_nonneg xp.le (sub_nonneg.mpr zu)
    nlinarith only [product,zn]
  have denominator : 0<(1+x^2)*(1+z^2) := mul_pos (half_den_pos x) (half_den_pos z)
  by_cases sign : 0≤delta
  · have angle : 1≤x*z+x+z := by
      have product := mul_nonneg denominator.le sign
      have nonnegative : 0≤(x*z+x+z-1)*(1+x+z-x*z) := by
        rw [←factor]
        exact product
      have bound := nonneg_of_mul_nonneg_left nonnegative other
      linarith only [bound]
    have base := C1092ShallowBottom.upper_nonneg a x z side.le xp xu zn zu angle
    have first := mul_nonneg sign (sub_nonneg.mpr Ahigh)
    have coefficient : 0≤c*delta/s := div_nonneg (mul_nonneg cp.le sign) sp.le
    have last := mul_nonneg coefficient (sub_nonneg.mpr Khigh)
    have identity : gap a c s A K h t=C1092ShallowBottom.upper a x z+
        delta*(-s/2-A)+(c*delta/s)*(s-K) := by
      dsimp [gap]
      change _=C1092ShallowBottom.upper a x z+delta*(-s/2-A)+(c*delta/s)*(s-K)
      rw [max_eq_left sign]
      dsimp [delta]
      rw [cframe,sframe,hspec,tspec]
      dsimp [C1092ShallowBottom.upper,b,scalarB,wallWeight,cosH,sinH]
      field_simp [xp.ne',(half_den_pos x).ne',(half_den_pos z).ne']
      <;> ring
    constructor
    · rw [identity]
      exact add_nonneg (add_nonneg base first) last
    · intro zero
      have tone : t=1 := by rw [zero] at unit; nlinarith only [unit,tn]
      have zone : z=1 := by dsimp [z,C1092WallProfileScalars.half]; rw [zero,tone]; norm_num
      have positive : 0<C1092ShallowBottom.upper a x z := by
        rw [zone]
        exact upper_endpoint a x side xp xu
      rw [identity]
      exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg positive first) last
  · have sign' : delta≤0 := (lt_of_not_ge sign).le
    have angle : x*z+x+z≤1 := by
      have product := mul_nonpos_of_nonneg_of_nonpos denominator.le sign'
      have nonpositive : (x*z+x+z-1)*(1+x+z-x*z)≤0 := by
        rw [←factor]
        exact product
      have bound := nonpos_of_mul_nonpos_left nonpositive other
      linarith only [bound]
    have base := C1092ShallowBottom.lower_nonneg a x z xp xu zn zu
      (by simpa only [←cframe,←sframe] using intrinsic) angle
    have first := mul_nonneg (neg_nonneg.mpr sign') (sub_nonneg.mpr Alow)
    have coefficient : 0≤-(c*delta/s) := neg_nonneg.mpr
      (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos cp.le sign') sp.le)
    have last := mul_nonneg coefficient (sub_nonneg.mpr Klow)
    have identity : gap a c s A K h t=bottomMinus a x z+
        (-delta)*(A-(a-c-s))+(-(c*delta/s))*(K-(a+(14/25)*s-c)) := by
      dsimp [gap]
      rw [max_eq_right sign']
      dsimp [delta]
      rw [cframe,sframe,hspec,tspec]
      dsimp [bottomMinus,b,scalarB,wallWeight,cosH,sinH]
      field_simp [xp.ne',(half_den_pos x).ne',(half_den_pos z).ne']
      <;> ring
    constructor
    · rw [identity]
      exact add_nonneg (add_nonneg base first) last
    · intro zero
      have tone : t=1 := by rw [zero] at unit; nlinarith only [unit,tn]
      have contrary : 0<delta := by dsimp [delta]; rw [zero,tone]; linarith only [sp]
      exact ((not_lt_of_ge sign') contrary).elim

#print axioms margin
end
end N12Compact.C1092ShallowBottomMargin
