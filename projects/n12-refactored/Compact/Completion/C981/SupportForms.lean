import Compact.Geometry.ABTransverse
import Compact.Geometry.C977CornerCubic
import Mathlib.Tactic.LinearCombination

/-! Elementary band formulas needed by the C981 central endings. These
identities depend only on the actual square's support function. -/
namespace N12Compact.C981CompletionSupportForms

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

theorem upper_in_bands (q : OpenSquare) (nx ny : ℝ) :
    upper q nx ny =
      (nx*q.c+ny*q.s)*(q.loU+q.side/2)+
      (-nx*q.s+ny*q.c)*(q.loV+q.side/2)+
      q.side/2*(|nx*q.c+ny*q.s|+|-nx*q.s+ny*q.c|) := by
  unfold upper supportRadius centerX centerY
  ring

theorem lower_in_bands (q : OpenSquare) (nx ny : ℝ) :
    lower q nx ny =
      (nx*q.c+ny*q.s)*(q.loU+q.side/2)+
      (-nx*q.s+ny*q.c)*(q.loV+q.side/2)-
      q.side/2*(|nx*q.c+ny*q.s|+|-nx*q.s+ny*q.c|) := by
  unfold lower supportRadius centerX centerY
  ring

theorem lower_negative_pos (q : OpenSquare) (t nx ny : ℝ) (hs : q.s = -t)
    (hu : 0 ≤ nx*q.c-ny*t) (hv : 0 ≤ nx*t+ny*q.c) :
    lower q nx ny = (nx*q.c-ny*t)*q.loU+(nx*t+ny*q.c)*q.loV := by
  rw [lower_in_bands, hs]
  have u : nx*q.c+ny*(-t)=nx*q.c-ny*t := by ring
  have v : -nx*(-t)+ny*q.c=nx*t+ny*q.c := by ring
  rw [u,v,abs_of_nonneg hu,abs_of_nonneg hv]
  ring

end N12Compact.C981CompletionSupportForms
