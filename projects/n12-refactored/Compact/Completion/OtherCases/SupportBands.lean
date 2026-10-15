import Compact.Completion.C981.SupportForms

/-! Full-square lower supports in their actual face coordinates. The
one-sided bound retains the unfavorable upper-U term when necessary. -/
namespace N12Compact.Completion.OtherCases.SupportBands
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C981CompletionSupportForms
set_option Elab.async false

theorem lower_pn (q : OpenSquare) (nx ny : ℝ)
    (u : 0≤nx*q.c+ny*q.s) (v : -nx*q.s+ny*q.c≤0) :
    lower q nx ny=(nx*q.c+ny*q.s)*q.loU+
      (-nx*q.s+ny*q.c)*(q.loV+q.side) := by
  rw [lower_in_bands,abs_of_nonneg u,abs_of_nonpos v]
  ring

theorem lower_nn (q : OpenSquare) (nx ny : ℝ)
    (u : nx*q.c+ny*q.s≤0) (v : -nx*q.s+ny*q.c≤0) :
    lower q nx ny=(nx*q.c+ny*q.s)*(q.loU+q.side)+
      (-nx*q.s+ny*q.c)*(q.loV+q.side) := by
  rw [lower_in_bands,abs_of_nonpos u,abs_of_nonpos v]
  ring

theorem lower_bound_pn (q : OpenSquare) (nx ny : ℝ)
    (v : -nx*q.s+ny*q.c≤0) :
    lower q nx ny≤(nx*q.c+ny*q.s)*q.loU+
      (-nx*q.s+ny*q.c)*(q.loV+q.side) := by
  rw [lower_in_bands,abs_of_nonpos v]
  have weight := mul_nonneg q.side_pos.le
    (sub_nonneg.mpr (le_abs_self (nx*q.c+ny*q.s)))
  nlinarith only [weight]

#print axioms lower_pn
#print axioms lower_nn
#print axioms lower_bound_pn
end N12Compact.Completion.OtherCases.SupportBands

