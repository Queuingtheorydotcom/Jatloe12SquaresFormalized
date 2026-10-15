import Compact.Completion.C1092.MPPMCrosspointSupportScalars

/-! Literal continuous support expressions for STEEP-POSITIVE-NEGATIVE-
WALL-SCALARS. The successor has the actual negative orientation. No
inequality or original-family exclusion is asserted by these definitions. -/
namespace N12Compact.C1092MPPMNegativeCrosspointSupport
open C977CornerCubic
set_option Elab.async false
noncomputable section

abbrev Quarter := C1092MPPMCrosspointSupport.Quarter
def ell (c s d t : ℝ) : ℝ := c*t+s*d
def kC (c s h r : ℝ) : ℝ := c*h+s*r
def deltaC (c s h r : ℝ) : ℝ := c*r-s*h
def kE (d t h r : ℝ) : ℝ := t*h+d*r
def deltaE (d t h r : ℝ) : ℝ := t*r-d*h
def C0 (s : ℝ) : ℝ := s-1
def E0 (d t : ℝ) : ℝ := (13/50)*t-d

def FC (c s h r : ℝ) : ℝ :=
  if 0≤deltaC c s h r then
    deltaC c s h r*(c+s)+kC c s h r*s-(kC c s h r+deltaC c s h r)
  else (c/2)*deltaC c s h r+kC c s h r*s-(kC c s h r-deltaC c s h r)

def P (d t : ℝ) : ℝ := (37/50)*d*t-(13/50)*t^2
def Q (d t : ℝ) : ℝ := 1-(37/50)*t^2-(13/50)*d*t
def P2 (d t : ℝ) : ℝ := d-7/20+(61/100)*t^2-(13/20)*d*t
def Q2 (d t : ℝ) : ℝ := -1-t+(13/20)*t^2+(61/100)*d*t
def FE (d t h r : ℝ) : ℝ :=
  if 0≤deltaE d t h r then P2 d t*h+Q2 d t*r
  else -P d t*h-Q d t*r

def width (c s d t h r : ℝ) : ℝ :=
  ell c s d t*(h+r)+t*(kC c s h r+|deltaC c s h r|)+
    s*(kE d t h r+|deltaE d t h r|)
def G00 (c s d t h r : ℝ) : ℝ :=
  width c s d t h r/2-2*ell c s d t-t*C0 s-s*E0 d t
def G01 (c s d t h r : ℝ) : ℝ :=
  (kC c s h r*(h+r)+h*(kC c s h r+|deltaC c s h r|)+s)/2-
    2*kC c s h r-h*C0 s-s*FE d t h r
def G10 (c s d t h r : ℝ) : ℝ :=
  (kE d t h r*(h+r)+t+r*(kE d t h r+|deltaE d t h r|))/2-
    2*kE d t h r-t*FC c s h r-r*E0 d t
def G11 (c s d t h r : ℝ) : ℝ := h+r-2-h*FC c s h r-r*FE d t h r

end
end N12Compact.C1092MPPMNegativeCrosspointSupport
