import S12.SquareSupportBase
import S12.CornerCover
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
set_option Elab.async false
namespace S12
open S12Pilot
set_option maxHeartbeats 0

theorem squareSet_isOpen (q : OpenSquare) : IsOpen (squareSet q) := by
  simp only [squareSet,OpenSquare.Inside,InBands,Set.setOf_and]
  exact (isOpen_lt (by fun_prop) (by fun_prop)).inter
    ((isOpen_lt (by fun_prop) (by fun_prop)).inter
      ((isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt (by fun_prop) (by fun_prop))))

theorem real_plane_linear_eval (f : (ℝ × ℝ) →L[ℝ] ℝ) (x y : ℝ) :
    f (x,y)=f (1,0)*x+f (0,1)*y := by
  have h : (x,y)=x • (1,0)+y • (0,1) := by ext <;> simp
  rw [h,map_add,map_smul,map_smul]
  simp only [smul_eq_mul]
  ring

/-- Disjoint square interiors have a nonzero separating linear functional.
No separation theorem or separating direction is imported as an axiom. -/
theorem square_linear_separator (q r : OpenSquare)
    (hd : ∀ x y,¬(q.Inside x y ∧ r.Inside x y)) :
    ∃ nx ny u : ℝ,(nx≠0 ∨ ny≠0) ∧
      (∀ x y,q.Inside x y → nx*x+ny*y<u) ∧
      (∀ x y,r.Inside x y → u≤nx*x+ny*y) := by
  have hdis : Disjoint (squareSet q) (squareSet r) := by
    apply Set.disjoint_left.mpr
    intro P hq hr
    exact hd P.1 P.2 ⟨hq,hr⟩
  obtain ⟨f,u,hq,hr⟩ := geometric_hahn_banach_open (squareSet_convex q) (squareSet_isOpen q)
    (squareSet_convex r) hdis
  have hq' : ∀ x y,q.Inside x y → f (1,0)*x+f (0,1)*y<u := by
    intro x y h
    have hh := hq (x,y) h
    rw [real_plane_linear_eval f x y] at hh
    exact hh
  have hr' : ∀ x y,r.Inside x y → u≤f (1,0)*x+f (0,1)*y := by
    intro x y h
    have hh := hr (x,y) h
    rw [real_plane_linear_eval f x y] at hh
    exact hh
  refine ⟨f (1,0),f (0,1),u,?_,hq',hr'⟩
  by_contra h
  push_neg at h
  have h0 := hq' (centerX q) (centerY q) (square_center_inside q)
  have h1 := hr' (centerX r) (centerY r) (square_center_inside r)
  simp only [h.1,h.2,zero_mul,zero_add] at h0 h1
  linarith

#print axioms square_linear_separator
end S12
