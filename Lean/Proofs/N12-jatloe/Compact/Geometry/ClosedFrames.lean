import Compact.Geometry.FourSquareAnchors
import S12.WallGeometry
import S12.SymmetryBase

/-! Face reindexing and reflection preserve closed compulsory points as well
as strict interiors. Reindexing changes no geometric square or ownership. -/

namespace N12Compact.ClosedFrames

open S12 S12Pilot FourSquareAnchors

@[simp] theorem closed_turnFrame (q : OpenSquare) (x y : ℝ) :
    ClosedInside (turnFrame q) x y ↔ ClosedInside q x y := by
  dsimp [ClosedInside, turnFrame]
  constructor <;> rintro ⟨h₀,h₁,h₂,h₃⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem closed_pullX (q : OpenSquare) (x y : ℝ) :
    ClosedInside (pullX q) x y ↔ ClosedInside q (4-x) y := by
  dsimp [ClosedInside, pullX]
  constructor <;> rintro ⟨h₀,h₁,h₂,h₃⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith

private theorem nonnegative_frame (q : OpenSquare) :
    ∃ r : OpenSquare, 0 ≤ r.c ∧ 0 ≤ r.s ∧ r.side = q.side ∧
      (∀ x y, r.Inside x y ↔ q.Inside x y) ∧
      (∀ x y, ClosedInside r x y ↔ ClosedInside q x y) := by
  by_cases hc : 0 ≤ q.c
  · by_cases hs : 0 ≤ q.s
    · exact ⟨q,hc,hs,rfl,by intros; rfl,by intros; rfl⟩
    · refine ⟨turnFrame q,?_,hc,by simp,by simp,by simp⟩
      dsimp [turnFrame]; linarith
  · by_cases hs : 0 ≤ q.s
    · refine ⟨turnFrame (turnFrame (turnFrame q)),?_,?_,by simp,by simp,by simp⟩ <;>
        dsimp [turnFrame] <;> linarith
    · refine ⟨turnFrame (turnFrame q),?_,?_,by simp,by simp,by simp⟩ <;>
        dsimp [turnFrame] <;> linarith

/-- Every orientation has a representative with positive first normal
component and nonnegative second component, preserving all four closed faces. -/
theorem positive_frame (q : OpenSquare) :
    ∃ r : OpenSquare, 0 < r.c ∧ 0 ≤ r.s ∧ r.side = q.side ∧
      (∀ x y, r.Inside x y ↔ q.Inside x y) ∧
      (∀ x y, ClosedInside r x y ↔ ClosedInside q x y) := by
  obtain ⟨r,hc,hs,ha,hi,hcl⟩ := nonnegative_frame q
  rcases hc.eq_or_lt with hz | hp
  · have hc0 : r.c = 0 := hz.symm
    have hspos : 0 < r.s := by nlinarith [r.unit_normal]
    refine ⟨turnFrame (turnFrame (turnFrame r)),?_,?_,by simpa using ha,?_,?_⟩
    · simpa [turnFrame] using hspos
    · simp [turnFrame,hc0]
    · intro x y; simpa using hi x y
    · intro x y; simpa using hcl x y
  · exact ⟨r,hp,hs,ha,hi,hcl⟩

/-- Signed canonical face frame, still preserving the same physical square.
The only remaining choice is the sign of the second normal component. -/
theorem canonical_frame (q : OpenSquare) :
    ∃ r : OpenSquare, 0 < r.c ∧ |r.s| ≤ r.c ∧ r.side = q.side ∧
      (∀ x y, r.Inside x y ↔ q.Inside x y) ∧
      (∀ x y, ClosedInside r x y ↔ ClosedInside q x y) := by
  obtain ⟨r,hc,hs,ha,hi,hcl⟩ := positive_frame q
  by_cases hsc : r.s ≤ r.c
  · exact ⟨r,hc,by simpa only [abs_of_nonneg hs] using hsc,ha,hi,hcl⟩
  · refine ⟨turnFrame (turnFrame (turnFrame r)),?_,?_,by simpa using ha,?_,?_⟩
    · simpa [turnFrame] using hc.trans (lt_of_not_ge hsc)
    · simpa [turnFrame,abs_of_pos hc] using (lt_of_not_ge hsc).le
    · intro x y; simpa using hi x y
    · intro x y; simpa using hcl x y

end N12Compact.ClosedFrames
