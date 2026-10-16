import Compact.Completion.C1092.MPPMAllNonpositivePair
import Compact.Completion.C1092.MPPMAllNonpositiveAlternating

/-! ALL-NEGATIVE-MIXED-FORWARD-ENDING sections 3 and 7. The first
theorem joins the same three native central squares and their two real
foreign bars. The last theorem is only the four-membership combinator;
the actual packing adapter must supply all three geometric exclusions. -/
namespace N12Compact.C1092MPPMAllNonpositive
open S12 S12Pilot C1092MMMPEndingAxes
set_option Elab.async false
noncomputable section

theorem three_retaining_impossible (C D F B R : OpenSquare)
    (c : Core C) (d : Core D) (f : Core F) (same : C.side=D.side)
    (apartCD : ∀ x y,¬(C.Inside x y ∧ (clockwise D).Inside x y))
    (apartDF : ∀ x y,¬(D.Inside x y ∧ (clockwise F).Inside x y))
    (barC : ∀ x : ℝ,-14/25≤x → x≤0 → B.Inside x (-1))
    (apartCB : ∀ x y,¬(C.Inside x y ∧ B.Inside x y))
    (barD : ∀ x : ℝ,-14/25≤x → x≤0 → R.Inside x (-1))
    (apartDR : ∀ x y,¬(D.Inside x y ∧ R.Inside x y)) : False := by
  have nextC : ¬C.Inside 0 (-13/50) := by
    intro own
    apply apartCD 0 (-13/50) ⟨own,?_⟩
    apply (inside_clockwise D _ _).mpr
    simpa only [neg_zero] using d.forward
  have nextD : ¬D.Inside 0 (-13/50) := by
    intro own
    apply apartDF 0 (-13/50) ⟨own,?_⟩
    apply (inside_clockwise F _ _).mpr
    simpa only [neg_zero] using f.forward
  have clearC := clearance C B c nextC barC apartCB
  have clearD := clearance D R d nextD barD apartDR
  apply pair_impossible C (clockwise D) c clearC.close
    (cleared_successor D d clearD) same ?_ ?_ apartCD
  · apply (inside_clockwise D _ _).mpr
    norm_num
    simpa only [neg_div] using d.marker
  · apply (inside_clockwise D _ _).mpr
    norm_num
    simpa only [neg_div] using d.ordinary

/-- This is the exhaustive four-cycle of literal strict memberships.
A boundary contact is a missing membership; no other owner is inferred
from that omission. The alternating obstruction requires only the
retaining owner and its two missing neighbors. -/
theorem binary_cycle (retains : Fin 4 → Prop)
    (adjacent : ∀ i,¬retains i → ¬retains (i+1) → False)
    (triple : ∀ i,retains i → retains (i+1) → retains (i+2) → False)
    (alternating : ∀ i,retains i → ¬retains (i+1) → ¬retains (i+3) → False) :
    False := by
  classical
  by_cases h0 : retains 0
  · by_cases h1 : retains 1
    · by_cases h2 : retains 2
      · exact triple 0 h0 (by simpa using h1) (by simpa using h2)
      · by_cases h3 : retains 3
        · exact triple 3 h3 (by simpa using h0) (by simpa using h1)
        · exact adjacent 2 h2 (by simpa using h3)
    · by_cases h3 : retains 3
      · by_cases h2 : retains 2
        · exact triple 2 h2 (by simpa using h3) (by simpa using h0)
        · exact adjacent 1 h1 (by simpa using h2)
      · exact alternating 0 h0 (by simpa using h1) (by simpa using h3)
  · by_cases h1 : retains 1
    · by_cases h2 : retains 2
      · by_cases h3 : retains 3
        · exact triple 1 h1 (by simpa using h2) (by simpa using h3)
        · exact adjacent 3 h3 (by simpa using h0)
      · exact alternating 1 h1 (by simpa using h2) (by simpa using h0)
    · exact adjacent 0 h0 (by simpa using h1)

end
#print axioms three_retaining_impossible
#print axioms binary_cycle
end N12Compact.C1092MPPMAllNonpositive
