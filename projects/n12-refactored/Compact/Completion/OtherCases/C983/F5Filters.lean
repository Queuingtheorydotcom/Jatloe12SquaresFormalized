import Compact.Completion.OtherCases.C983.SharpApplications

/-! The authentic merged-F5 entrance. G6 in the actual southeast owner
is proved from the full bar contradiction; all remaining component cuts
are finite deductions within a single original owner list at a time. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private theorem southeast_no_g6_check :
    ∀ owned∈originalComponents 5,5∉owned → 16∉owned →
      (4∈owned ∨ 8∈owned) ∧ 18∈owned := by decide +kernel

private theorem right_avoiding_f8_check :
    ∀ owned∈originalComponents 10,8∉owned → 9∈owned ∧ 19∈owned := by decide +kernel

private theorem northeast_outward_check :
    ∀ owned∈originalComponents 6,5∉owned → 13∉owned → 8∉owned →
      9∉owned → 19∉owned → 7∈owned := by decide +kernel

private theorem top_avoiding_f5_f7_check :
    ∀ owned∈originalComponents 11,5∉owned → 7∉owned → 3∈owned ∧ 14∈owned := by
  decide +kernel

/-- This holds whenever the actual merged owner owns F5, including the
two-inward merged branch. No exact three-owner vector is assumed. -/
theorem f5_southeast_g6 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : 16∈actual p 5 := by
  by_contra noG6
  have noF5 := absent_of_foreign p hf 7 5 5 (by decide +kernel) f5
  have outward := southeast_no_g6_check _ (original_actual_mem p hf 5) noF5 noG6
  have noF4 : 4∉actual p 5 :=
    fun own => southeast_inward_outward_exclusion p hf own outward.2 noG6
  have f8 := outward.1.resolve_left noF4
  have right := right_avoiding_f8_check _ (original_actual_mem p hf 10)
    (absent_of_foreign p hf 5 10 8 (by decide +kernel) f8)
  have nNoF5 := absent_of_foreign p hf 7 6 5 (by decide +kernel) f5
  have nF7 := northeast_outward_check _ (original_actual_mem p hf 6) nNoF5
    (absent_of_foreign p hf 7 6 13 (by decide +kernel) (merged_g3 p hf))
    (absent_of_foreign p hf 5 6 8 (by decide +kernel) f8)
    (absent_of_foreign p hf 10 6 9 (by decide +kernel) right.1)
    (absent_of_foreign p hf 10 6 19 (by decide +kernel) right.2)
  have top := top_avoiding_f5_f7_check _ (original_actual_mem p hf 11)
    (absent_of_foreign p hf 7 11 5 (by decide +kernel) f5)
    (absent_of_foreign p hf 6 11 7 (by decide +kernel) nF7)
  have upperPoint := northeast_upper_point p hf nF7 nNoF5 (top_origin_of_f3 p hf top.1)
    (right_bar_of_f8 p hf f8 right.1 right.2)
  have lowerPoint := southeast_outward_point p hf f8 outward.2 noG6
  exact owners_apart p hf 5 6 (by decide +kernel) _ _ ⟨lowerPoint,upperPoint⟩

def f5NortheastComponents : List (Finset Nat) :=
  [{7,17},{7,19},{7,17,19},{9,17},{9,19},{9,17,19},{7,9,17},{7,9,19},{7,9,17,19}]

private theorem northeast_f5_check :
    ∀ owned∈originalComponents 6,5∉owned → 13∉owned → 16∉owned →
      owned∈f5NortheastComponents := by decide +kernel

theorem f5_northeast_components (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : actual p 6∈f5NortheastComponents :=
  northeast_f5_check _ (original_actual_mem p hf 6)
    (absent_of_foreign p hf 7 6 5 (by decide +kernel) f5)
    (absent_of_foreign p hf 7 6 13 (by decide +kernel) (merged_g3 p hf))
    (absent_of_foreign p hf 5 6 16 (by decide +kernel) (f5_southeast_g6 p hf f5))

private theorem northeast_cover_check : ∀ owned∈f5NortheastComponents,
    (7∈owned ∨ 9∈owned) ∧ (17∈owned ∨ 19∈owned) := by decide +kernel

theorem f5_northeast_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) :
    (7∈actual p 6 ∨ 9∈actual p 6) ∧ (17∈actual p 6 ∨ 19∈actual p 6) :=
  northeast_cover_check _ (f5_northeast_components p hf f5)

private theorem right_outer_check : ∀ owned∈originalComponents 10,8∈owned ∨ 9∈owned := by
  decide +kernel

private theorem right_f7_check :
    ∀ owned∈originalComponents 10,16∉owned → 7∈owned → 9∈owned := by decide +kernel

theorem f5_right_avoids_f7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : 7∉actual p 10 := by
  intro rightF7
  have rightF9 := right_f7_check _ (original_actual_mem p hf 10)
    (absent_of_foreign p hf 5 10 16 (by decide +kernel) (f5_southeast_g6 p hf f5)) rightF7
  have nNoF7 := absent_of_foreign p hf 10 6 7 (by decide +kernel) rightF7
  have nNoF9 := absent_of_foreign p hf 10 6 9 (by decide +kernel) rightF9
  exact nNoF9 ((f5_northeast_cover p hf f5).1.resolve_left nNoF7)

def f5SoutheastComponents : List (Finset Nat) :=
  [{4,16},{4,16,18},{8,16},{8,16,18},{4,8,16},{4,8,16,18},{4,9,16}]

private theorem southeast_f5_check :
    ∀ owned∈originalComponents 5,5∉owned → 16∈owned → ¬(8∈owned ∧ 9∈owned) →
      owned∈f5SoutheastComponents := by decide +kernel

theorem f5_southeast_components (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : actual p 5∈f5SoutheastComponents := by
  apply southeast_f5_check _ (original_actual_mem p hf 5)
    (absent_of_foreign p hf 7 5 5 (by decide +kernel) f5) (f5_southeast_g6 p hf f5)
  rintro ⟨f8,f9⟩
  have noF8 := absent_of_foreign p hf 5 10 8 (by decide +kernel) f8
  have noF9 := absent_of_foreign p hf 5 10 9 (by decide +kernel) f9
  exact (right_outer_check _ (original_actual_mem p hf 10)).elim noF8 noF9

def f5RightComponents : List (Finset Nat) :=
  [{8,18},{9,19},{8,9,18},{8,9,19},{8,9,18,19}]

private theorem right_f5_check :
    ∀ owned∈originalComponents 10,16∉owned → 7∉owned → owned∈f5RightComponents := by
  decide +kernel

theorem f5_right_components (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : actual p 10∈f5RightComponents :=
  right_f5_check _ (original_actual_mem p hf 10)
    (absent_of_foreign p hf 5 10 16 (by decide +kernel) (f5_southeast_g6 p hf f5))
    (f5_right_avoids_f7 p hf f5)

private theorem northeast_avoiding_right_check :
    ∀ owned∈f5NortheastComponents,9∉owned → 19∉owned → owned={7,17} := by decide +kernel

private theorem right_g9_check :
    ∀ owned∈f5RightComponents,19∈owned → 9∈owned := by decide +kernel

private theorem top_avoiding_central_check :
    ∀ owned∈originalComponents 11,5∉owned → 7∉owned → 17∉owned → owned={3,14} := by
  decide +kernel

theorem f5_upper_of_right_g9 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) (g9 : 19∈actual p 10) :
    actual p 6={7,17} ∧ actual p 11={3,14} := by
  have rightF9 := right_g9_check _ (f5_right_components p hf f5) g9
  have northeast := northeast_avoiding_right_check _ (f5_northeast_components p hf f5)
    (absent_of_foreign p hf 10 6 9 (by decide +kernel) rightF9)
    (absent_of_foreign p hf 10 6 19 (by decide +kernel) g9)
  have nF7 : 7∈actual p 6 := by rw [northeast]; decide +kernel
  have nG7 : 17∈actual p 6 := by rw [northeast]; decide +kernel
  exact ⟨northeast,top_avoiding_central_check _ (original_actual_mem p hf 11)
    (absent_of_foreign p hf 7 11 5 (by decide +kernel) f5)
    (absent_of_foreign p hf 6 11 7 (by decide +kernel) nF7)
    (absent_of_foreign p hf 6 11 17 (by decide +kernel) nG7)⟩

end
#print axioms f5_southeast_g6
#print axioms f5_right_components
#print axioms f5_upper_of_right_g9
end N12Compact.Completion.OtherCases.C983

