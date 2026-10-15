import Compact.Completion.C1092.MPPMMissingPositiveBoundArc

/-! Exact sine interpolation for an arbitrary quadratic plus a linear
functional on a unit arc. The complete remainder is an explicit symmetric
polynomial. This lemma uses no derivatives or ODE assumption. -/
namespace N12Compact.C1092MPPMCrosspointSupport.QuadraticArc
open C1092ShallowPositiveScalars
set_option Elab.async false
noncomputable section

def sum3 (q z r : ℝ) : ℝ := q+z+r
def pair3 (q z r : ℝ) : ℝ := q*z+q*r+z*r
def triple3 (q z r : ℝ) : ℝ := q*z*r
def X (q z r : ℝ) : ℝ :=
  1-(sum3 q z r)^2-(pair3 q z r)^2+(triple3 q z r)^2
def Y (q z r : ℝ) : ℝ := sum3 q z r-triple3 q z r*pair3 q z r
def Z (q z r : ℝ) : ℝ := (1+q^2)*(1+z^2)*(1+r^2)
def remainder (a b C q z r : ℝ) : ℝ := a*X q z r+2*b*Y q z r-C*Z q z r

def value (a b C A B z : ℝ) : ℝ :=
  a*(cosH z)^2+b*cosH z*sinH z+C+A*cosH z+B*sinH z

/-- Both zero endpoint values and a degenerate interval are retained.
The single sign premise concerns the displayed exact remainder, which
the application proves algebraically on its entire parameter interval. -/
theorem nonnegative (a b C A B q z r : ℝ)
    (qn : 0≤q) (qz : q≤z) (zr : z≤r)
    (rem : 0≤remainder a b C q z r)
    (first : 0≤value a b C A B q) (last : 0≤value a b C A B r) :
    0≤value a b C A B z := by
  by_cases same : q=r
  · have zeq : z=q := by linarith only [qz,zr,same]
    simpa only [zeq] using first
  have gap : 0<r-q := by linarith only [qz,zr,same]
  have zn : 0≤z := qn.trans qz
  have rn : 0≤r := zn.trans zr
  have leftDistance : 0≤z-q := sub_nonneg.mpr qz
  have rightDistance : 0≤r-z := sub_nonneg.mpr zr
  let alpha := (r-z)*(1+r*z)*(1+q^2)/((r-q)*(1+r*q)*(1+z^2))
  let beta := (z-q)*(1+z*q)*(1+r^2)/((r-q)*(1+r*q)*(1+z^2))
  have den : 0<(r-q)*(1+r*q)*(1+z^2) := by positivity
  have an : 0≤alpha := by dsimp [alpha]; positivity
  have bn : 0≤beta := by dsimp [beta]; positivity
  have endpoints : 0≤alpha*value a b C A B q+beta*value a b C A B r :=
    add_nonneg (mul_nonneg an first) (mul_nonneg bn last)
  have product : 0≤2*(z-q)*(r-z)*remainder a b C q z r := by positivity
  have scale : 0<(1+q*r)*(1+z^2)^2*(1+q^2)*(1+r^2) := by positivity
  have identity : ((1+q*r)*(1+z^2)^2*(1+q^2)*(1+r^2))*
      (value a b C A B z-alpha*value a b C A B q-beta*value a b C A B r)=
      2*(z-q)*(r-z)*remainder a b C q z r := by
    dsimp [value,alpha,beta,remainder,X,Y,Z,sum3,pair3,triple3,cosH,sinH]
    field_simp [gap.ne',(half_den_pos q).ne',(half_den_pos z).ne',
      (half_den_pos r).ne',(show 1+r*q≠0 by positivity)]
    <;> ring
  have weighted : 0≤((1+q*r)*(1+z^2)^2*(1+q^2)*(1+r^2))*
      (value a b C A B z-alpha*value a b C A B q-beta*value a b C A B r) := by
    rw [identity]; exact product
  have comparison := nonneg_of_mul_nonneg_right weighted scale
  linarith only [comparison,endpoints]

end
end N12Compact.C1092MPPMCrosspointSupport.QuadraticArc
