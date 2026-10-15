import Compact.Completion.C1092.ShallowBottom
import Compact.Geometry.C977CornerCubic

/-! Same-face scalars for the actual shallow-positive wall order. The
functions b and ell retain one central upper face K throughout. -/
namespace N12Compact.C1092ShallowCentralScalars
open C977CornerCubic C1092ShallowPositiveScalars
set_option Elab.async false
noncomputable section

def b (a c s K : ℝ) : ℝ := (a*(3/2+c*(c+s)/2)-K-2*c)/s
def ell (a c s K : ℝ) : ℝ := (K-2*s+(a/2)*(1+s*(c+s)))/c

theorem bounds (x : ℝ) (xp : 0<x) (xu : x≤1/4) :
    15/17≤cosH x ∧ sinH x≤8/17 ∧ 7/17≤cosH x-sinH x := by
  have den := half_den_pos x
  have low : 0≤1-4*x := by linarith only [xu]
  have xSquare : x^2≤1/16 := by
    have product := mul_nonneg low (show 0≤1+4*x by linarith only [xp])
    nlinarith only [product]
  have first : 15/17≤cosH x := by
    dsimp [cosH]
    apply (le_div_iff₀ den).mpr
    nlinarith only [xSquare]
  have sineProduct := mul_nonneg low (show 0≤4-x by linarith only [xu])
  have second : sinH x≤8/17 := by
    dsimp [sinH]
    apply (div_le_iff₀ den).mpr
    nlinarith only [sineProduct]
  have difference : cosH x-sinH x=(1-x^2-2*x)/(1+x^2) := by
    dsimp [cosH,sinH]
    ring
  have lastProduct := mul_nonneg low (show 0≤5+3*x by linarith only [xp])
  have last : 7/17≤cosH x-sinH x := by
    rw [difference]
    apply (le_div_iff₀ den).mpr
    nlinarith only [lastProduct]
  exact ⟨first,second,last⟩

theorem arc {c s : ℝ} (normal : Normal c s) : 1+(4/5)*c*s≤c+s := by
  have data := normal_bounds normal
  have cross := mul_nonneg (show 0≤c by linarith only [data.1]) normal.1
  have product := mul_nonneg (sub_nonneg.mpr data.2.2.2.2.1)
    (sub_nonneg.mpr data.2.2.2.2.2)
  nlinarith only [normal.2.2,product,cross]

theorem brackets (x : ℝ) (xp : 0<x) (xu : x≤1/4)
    (normal : Normal (cosH x) (sinH x)) :
    -cosH x+sinH x+2/5-(sinH x)^2-(1/2)*cosH x*sinH x<0 ∧
      1-cosH x-sinH x+cosH x*sinH x-(sinH x)^2/2<0 ∧
      0<cosH x-sinH x+(11/25)*(sinH x)^2 ∧
      0<cosH x+sinH x-1-(11/25)*cosH x*sinH x := by
  have data := bounds x xp xu
  have cp := half_cos_pos x xp.le (by linarith only [xu])
  have sp := half_sin_pos x xp
  have cross := mul_pos cp sp
  have far := bottom_far_endpoint_pos x xp xu
  have curved := arc normal
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [data.2.2,sq_nonneg (sinH x),cross]
  · linarith only [far]
  · nlinarith only [data.2.2,sq_nonneg (sinH x)]
  · nlinarith only [curved,cross]

theorem same_face_sum {a c s K : ℝ} (side : 1<a) (normal : Normal c s)
    (sp : 0<s) (cap : K≤s) : 0<b a c s K+ell a c s K := by
  have data := normal_bounds normal
  have cp : 0<c := by linarith only [data.1]
  have cross := mul_pos cp sp
  have sum : 1<c+s := by
    nlinarith only [normal.2.2,cross,data.2.2.2.2.1]
  have coordinate : s*b a c s K=a*(3/2+c*(c+s)/2)-K-2*c := by
    dsimp [b]
    field_simp [sp.ne']
  have transverse : c*ell a c s K=K-2*s+(a/2)*(1+s*(c+s)) := by
    dsimp [ell]
    field_simp [cp.ne']
  have identity : c*s*(b a c s K+ell a c s K)=a*(2*c+s)-(c-s)*K-2 := by
    calc
      _ = c*(s*b a c s K)+s*(c*ell a c s K) := by ring
      _ = _ := by
        rw [coordinate,transverse]
        linear_combination (a*(c+s)/2-2)*normal.2.2
  have intrinsic : (1+c)*(2*c+s-c*s+s^2-2)=s^2*(c+s-1) := by
    linear_combination (2-s)*normal.2.2
  have intrinsicPositive : 0<2*c+s-c*s+s^2-2 := by
    have product := mul_pos (sq_pos_of_pos sp) (sub_pos.mpr sum)
    have positive : 0<1+c := by linarith only [cp]
    have weighted : 0<(1+c)*(2*c+s-c*s+s^2-2) := by rw [intrinsic]; exact product
    by_contra failure
    have weak := mul_nonpos_of_nonneg_of_nonpos positive.le (le_of_not_gt failure)
    linarith only [weighted,weak]
  have first := mul_pos (sub_pos.mpr side) (show 0<2*c+s by linarith only [cp,sp])
  have last := mul_nonneg (sub_nonneg.mpr normal.2.1) (sub_nonneg.mpr cap)
  have productPositive : 0<c*s*(b a c s K+ell a c s K) := by
    rw [identity]
    have decomposition : a*(2*c+s)-(c-s)*K-2=
        (a-1)*(2*c+s)+(c-s)*(s-K)+(2*c+s-c*s+s^2-2) := by ring
    rw [decomposition]
    exact add_pos_of_nonneg_of_pos (add_nonneg first.le last) intrinsicPositive
  by_contra failure
  have weak := mul_nonpos_of_nonneg_of_nonpos cross.le (le_of_not_gt failure)
  exact (not_lt_of_ge weak) productPositive

theorem small_left (a x : ℝ) (side : 1<a) (xp : 0<x) (xu : x≤1/4)
    (normal : Normal (cosH x) (sinH x)) :
    0<a*(cosH x+sinH x)-(1/2)*cosH x*sinH x+(14/25)*(sinH x)^2-1 ∧
      0<(a*(cosH x+sinH x)-(1/2)*cosH x*sinH x+(14/25)*(sinH x)^2-1)+
        (a*(cosH x-sinH x)+(14/25)*cosH x*sinH x-(sinH x)^2/2-(cosH x)^2) := by
  let c := cosH x
  let s := sinH x
  have data := normal_bounds normal
  have cp : 0<c := half_cos_pos x xp.le (by linarith only [xu])
  have sp : 0<s := half_sin_pos x xp
  have cross := mul_pos cp sp
  have curved := arc normal
  have extra := mul_pos (sub_pos.mpr side) (show 0<c+s by linarith only [cp,sp])
  have first : 0<a*(c+s)-(1/2)*c*s+(14/25)*s^2-1 := by
    nlinarith only [curved,extra,cross,sq_nonneg s]
  have unitAngle : s*x=1-c := by
    dsimp [s,c,sinH,cosH]
    field_simp [(half_den_pos x).ne']
    <;> ring
  have xSquare : x^2≤1/16 := by
    have product := mul_nonneg (show 0≤1/4-x by linarith only [xu])
      (show 0≤1/4+x by linarith only [xp])
    nlinarith only [product]
  have sineBound := (bounds x xp xu).2.1
  have weighted := mul_le_mul_of_nonneg_left xSquare sp.le
  have sBound : s≤8/17 := sineBound
  have sumBound : 1≤c+s := data.2.2.2.2.1
  have small : 0<(3/50)*(c+s)-s*x^2 := by
    nlinarith only [weighted,sBound,sumBound]
  have gap : 0< -(1-c)^2+(3/50)*s*(c+s) := by
    have identity : -(1-c)^2+(3/50)*s*(c+s)=s*((3/50)*(c+s)-s*x^2) := by
      rw [←unitAngle]
      ring
    rw [identity]
    exact mul_pos sp small
  have lastExtra := mul_pos (sub_pos.mpr side) (mul_pos (by norm_num : (0:ℝ)<2) cp)
  have last : 0<(a*(c+s)-(1/2)*c*s+(14/25)*s^2-1)+
      (a*(c-s)+(14/25)*c*s-s^2/2-c^2) := by
    calc
      _ = (a-1)*(2*c)+(-(1-c)^2+(3/50)*s*(c+s)) := by ring
      _ > 0 := add_pos lastExtra gap
  exact ⟨first,last⟩

#print axioms brackets
#print axioms same_face_sum
#print axioms small_left
end
end N12Compact.C1092ShallowCentralScalars
