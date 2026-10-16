import S12.Convex
import Mathlib.Analysis.Convex.Hull

namespace S12
open S12Pilot

def squareSet (q : OpenSquare) : Set (ℝ × ℝ) := {p | q.Inside p.1 p.2}

theorem squareSet_convex (q : OpenSquare) : Convex ℝ (squareSet q) := by
  intro p hp r hr a b ha hb hab
  have hh := inside_segment q p.1 p.2 r.1 r.2 b hp hr hb (by linarith)
  have hea : a=1-b := by linarith
  simpa only [squareSet, Set.mem_ofPred_eq, hea, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_add, Prod.snd_add, smul_eq_mul] using hh

def OverlapsAt (q r : OpenSquare) (A B : ℝ × ℝ) : Prop :=
  ∃ P : ℝ × ℝ,P-A∈squareSet q ∧ P-B∈squareSet r

theorem OverlapsAt.symm (q r : OpenSquare) (A B : ℝ × ℝ) :
    OverlapsAt q r A B ↔ OverlapsAt r q B A := by
  constructor <;> rintro ⟨P,h0,h1⟩ <;> exact ⟨P,h1,h0⟩

theorem overlapsAt_convex_left (q r : OpenSquare) (B : ℝ × ℝ) :
    Convex ℝ {A | OverlapsAt q r A B} := by
  intro A0 h0 A1 h1 a b ha hb hab
  obtain ⟨P0,hq0,hr0⟩ := h0
  obtain ⟨P1,hq1,hr1⟩ := h1
  refine ⟨a • P0+b • P1,?_,?_⟩
  · have hh := squareSet_convex q hq0 hq1 ha hb hab
    have he : (a • P0+b • P1)-(a • A0+b • A1)=a • (P0-A0)+b • (P1-A1) := by
      simp only [smul_sub]; abel
    rw [he]
    exact hh
  · have hh := squareSet_convex r hr0 hr1 ha hb hab
    have he : (a • P0+b • P1)-B=a • (P0-B)+b • (P1-B) := by
      simp only [smul_sub]
      rw [show a • P0-a • B+(b • P1-b • B)=(a • P0+b • P1)-(a • B+b • B) by abel,
        ←add_smul,hab,one_smul]
    rw [he]
    exact hh

theorem overlapsAt_convex_right (q r : OpenSquare) (A : ℝ × ℝ) :
    Convex ℝ {B | OverlapsAt q r A B} := by
  simpa only [OverlapsAt.symm q r A] using overlapsAt_convex_left r q A

/-- Interior witnesses at every pair of polygon vertices certify overlap
for every pair of centers in their convex hulls. This needs no separating-axis
algorithm or floating-point polygon computation. -/
theorem vertex_overlap_extends (q r : OpenSquare) (VA VB : Set (ℝ × ℝ))
    (h : ∀ A∈VA,∀ B∈VB,OverlapsAt q r A B) :
    ∀ A∈convexHull ℝ VA,∀ B∈convexHull ℝ VB,OverlapsAt q r A B := by
  intro A hA
  have hB : ∀ B∈VB,OverlapsAt q r A B := by
    intro B hB
    exact convexHull_min (fun A hA => h A hA B hB) (overlapsAt_convex_left q r B) hA
  exact convexHull_min hB (overlapsAt_convex_right q r A)

#print axioms vertex_overlap_extends
end S12
