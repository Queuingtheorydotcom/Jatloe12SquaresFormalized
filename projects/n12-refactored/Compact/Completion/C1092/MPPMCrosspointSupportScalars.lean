import Compact.Geometry.C977CornerSectorBounds

/-! Literal scalar expressions in STEEP-POSITIVE-CENTRAL-SCALAR and
STEEP-POSITIVE-BOUNDARY-SCALARS. These definitions alone assert no
inequality or original-case conclusion. -/
namespace N12Compact.C1092MPPMCrosspointSupport
open C977CornerCubic
set_option Elab.async false
noncomputable section

structure Quarter (h r : ℝ) : Prop where
  cosine : 0≤h
  sine : 0≤r
  unit : h^2+r^2=1

def k (c s d t : ℝ) : ℝ := c*d+s*t
def kC (c s h r : ℝ) : ℝ := c*h+s*r
def deltaC (c s h r : ℝ) : ℝ := c*r-s*h
def kE (d t h r : ℝ) : ℝ := d*h+t*r
def deltaE (d t h r : ℝ) : ℝ := d*r-t*h
def C0 (s : ℝ) : ℝ := (543/500)*s-1
def E0 (d t : ℝ) : ℝ := d-(14/25)*t-1

def FC (c s h r : ℝ) : ℝ :=
  if 0≤deltaC c s h r then
    deltaC c s h r*(c+s)+kC c s h r*(543/500)*s-
      (kC c s h r+deltaC c s h r)
  else
    (c/2)*deltaC c s h r+kC c s h r*(543/500)*s-
      (kC c s h r-deltaC c s h r)

def FE (d t h r : ℝ) : ℝ :=
  if 0≤deltaE d t h r then
    kE d t h r*E0 d t+deltaE d t h r*(-d-(2/5)*t)
  else kE d t h r*E0 d t-(d/2)*deltaE d t h r

def G00 (c s d t h r : ℝ) : ℝ :=
  (k c s d t*(h+r)+d*(kC c s h r+|deltaC c s h r|)+
    s*(kE d t h r+|deltaE d t h r|))/2-
      2*k c s d t-d*C0 s-s*E0 d t

def G01 (c s d t h r : ℝ) : ℝ :=
  (kC c s h r*(h+r)+h*(kC c s h r+|deltaC c s h r|)+s)/2-
    2*kC c s h r-h*C0 s-s*FE d t h r

def G10 (c s d t h r : ℝ) : ℝ :=
  (kE d t h r*(h+r)+d+r*(kE d t h r+|deltaE d t h r|))/2-
    2*kE d t h r-d*FC c s h r-r*E0 d t

def G11 (c s d t h r : ℝ) : ℝ := h+r-2-h*FC c s h r-r*FE d t h r

end
end N12Compact.C1092MPPMCrosspointSupport
