import Compact.Completion.C1092.MPPMActualRetaining

/-! Exhaustive sign patterns of four fixed actual sector frames. This
finite lemma only chooses a simultaneous sector rotation; it makes no
claim about square poses, omitted points or geometric hypotheses. -/
namespace N12Compact.C1092MPPMFourCycle
open C1092MPPMActualRetaining
set_option Elab.async false

def AllNonpositive (P : Fin 4→Prop) : Prop := ∀ i,¬P i
def AllPositive (P : Fin 4→Prop) : Prop := ∀ i,P i
def OnePositive (P : Fin 4→Prop) (i : Fin 4) : Prop :=
  P i ∧ ¬P (addSector i 1) ∧ ¬P (addSector i 2) ∧ ¬P (addSector i 3)
def Sandwich (P : Fin 4→Prop) (i : Fin 4) : Prop :=
  P i ∧ ¬P (addSector i 1) ∧ P (addSector i 2)
def AdjacentPositive (P : Fin 4→Prop) (i : Fin 4) : Prop :=
  P i ∧ P (addSector i 1) ∧ ¬P (addSector i 2) ∧ ¬P (addSector i 3)

/-- All sixteen sign patterns are covered by the five geometric
schemas. The sandwich includes three-positive and alternating cases. -/
theorem classify (P : Fin 4→Prop) :
    AllNonpositive P ∨ AllPositive P ∨ (∃ i,OnePositive P i) ∨
      (∃ i,Sandwich P i) ∨ (∃ i,AdjacentPositive P i) := by
  classical
  by_cases p0 : P 0 <;> by_cases p1 : P 1 <;>
    by_cases p2 : P 2 <;> by_cases p3 : P 3
  all_goals first
    | exact Or.inl (by intro i; fin_cases i <;> assumption)
    | exact Or.inr (Or.inl (by intro i; fin_cases i <;> assumption))
    | exact Or.inr (Or.inr (Or.inl ⟨0,by simp [OnePositive,addSector,p0,p1,p2,p3]⟩))
    | exact Or.inr (Or.inr (Or.inl ⟨1,by simp [OnePositive,addSector,p0,p1,p2,p3]⟩))
    | exact Or.inr (Or.inr (Or.inl ⟨2,by simp [OnePositive,addSector,p0,p1,p2,p3]⟩))
    | exact Or.inr (Or.inr (Or.inl ⟨3,by simp [OnePositive,addSector,p0,p1,p2,p3]⟩))
    | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨0,by simp [Sandwich,addSector,p0,p1,p2,p3]⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨1,by simp [Sandwich,addSector,p0,p1,p2,p3]⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨2,by simp [Sandwich,addSector,p0,p1,p2,p3]⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨3,by simp [Sandwich,addSector,p0,p1,p2,p3]⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0,by simp [AdjacentPositive,addSector,p0,p1,p2,p3]⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1,by simp [AdjacentPositive,addSector,p0,p1,p2,p3]⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨2,by simp [AdjacentPositive,addSector,p0,p1,p2,p3]⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨3,by simp [AdjacentPositive,addSector,p0,p1,p2,p3]⟩)))

end N12Compact.C1092MPPMFourCycle
