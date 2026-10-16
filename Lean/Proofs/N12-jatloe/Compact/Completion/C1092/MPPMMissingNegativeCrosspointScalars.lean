import Compact.Completion.C1092.MPPMNegativeCrosspointSupportScalars

/-! Literal supports in STEEP-POSITIVE-MISSING-NEGATIVE-WALL-SCALARS.
The epsilon allowance is explicit; its source is the unconditional positive
upper-v face, rather than an assumed preceding-origin owner. -/
namespace N12Compact.C1092MPPMMissingNegativeCrosspointSupport
open C977CornerCubic
set_option Elab.async false
noncomputable section
abbrev Quarter := C1092MPPMNegativeCrosspointSupport.Quarter
abbrev ell := C1092MPPMNegativeCrosspointSupport.ell
abbrev kC := C1092MPPMNegativeCrosspointSupport.kC
abbrev deltaC := C1092MPPMNegativeCrosspointSupport.deltaC
abbrev kE := C1092MPPMNegativeCrosspointSupport.kE
abbrev deltaE := C1092MPPMNegativeCrosspointSupport.deltaE
abbrev C0 := C1092MPPMNegativeCrosspointSupport.C0
abbrev FC := C1092MPPMNegativeCrosspointSupport.FC
abbrev width := C1092MPPMNegativeCrosspointSupport.width
def E0 (d t : ℝ) : ℝ := t-(14/25)*d-1
def FE (d t h r : ℝ) : ℝ :=
  if 0≤deltaE d t h r then
    -deltaE d t h r*(1+(13/50)*t)+kE d t h r*E0 d t
  else -deltaE d t h r*(d+t-1)+kE d t h r*E0 d t
def G00 (c s d t h r : ℝ) : ℝ :=
  width c s d t h r/2-2*ell c s d t-t*C0 s-s*E0 d t
def G01 (c s d t h r : ℝ) : ℝ :=
  (kC c s h r*(h+r)+h*(kC c s h r+|deltaC c s h r|)+s)/2-
    2*kC c s h r-h*C0 s-s*FE d t h r
def G10 (c s d t h r : ℝ) : ℝ :=
  (kE d t h r*(h+r)+t+r*(kE d t h r+|deltaE d t h r|))/2-
    2*kE d t h r-t*FC c s h r-r*E0 d t
def G11 (c s d t h r : ℝ) : ℝ := h+r-2-h*FC c s h r-r*FE d t h r
def G00star (epsilon c s d t h r : ℝ) : ℝ := G00 c s d t h r-epsilon*s*t
def G01star (epsilon c s d t h r : ℝ) : ℝ := G01 c s d t h r-epsilon*s*h
def G10star (epsilon c s d t h r : ℝ) : ℝ := G10 c s d t h r-epsilon*s*t*kC c s h r
def G11star (epsilon c s d t h r : ℝ) : ℝ := G11 c s d t h r-epsilon*s*h*kC c s h r
end
end N12Compact.C1092MPPMMissingNegativeCrosspointSupport
