import Compact.Completion.OtherCases.C976NegativeTop.MixedAngle
import Compact.Completion.OtherCases.WallProfile.VertexGeometry

/-! The genuine northeast-square premises and forced faces in section 1
of C976-NEGATIVE-NE-TOP-ENDING. In the outer branch F is only excluded:
no owner is invented for that absent auxiliary point. -/
namespace N12Compact.Completion.OtherCases.C976NegativeTop
open S12 S12Pilot
set_option Elab.async false

def Alternative (N : OpenSquare) : Prop :=
  (N.Inside 0 (-19/50) ∧ ¬N.Inside 0 (-37/50)) ∨
  (N.Inside 0 (-37/50) ∧
    ∀ x : ℝ,13/50≤x → x≤1/2 → ¬N.Inside x (-1))

structure Faces (N : OpenSquare) (s : ℝ) : Prop where
  lowerU : 0≤N.loU
  elbowU : N.loU<(13/50)*N.c
  inwardU : N.loU<(37/50)*s
  lowerV : N.loV<0
  upperU : N.loU+N.side≤N.c+(11/25)*s
  floor : -N.c≤N.loV
  alternatives : (-(37/50)*N.c≤N.loV) ∨
    ((1/2)*s-N.c≤N.loV ∧ s<(13/25)*N.c)

theorem faces (N : OpenSquare) (s : ℝ) (signed : N.s= -s)
    (side : 1<N.side) (cp : 0<N.c) (sp : 0<s) (order : s≤N.c)
    (marker : N.Inside (7/20) (-13/20)) (elbow : N.Inside (13/50) 0)
    (origin : ¬N.Inside 0 0) (right : ¬N.Inside 1 (-11/25))
    (alternative : Alternative N) : Faces N s := by
  have unit : N.c^2+s^2=1 := by simpa only [signed,neg_sq] using N.unit_normal
  have bands (x y : ℝ) : N.Inside x y ↔
      N.loU<N.c*x-s*y ∧ N.c*x-s*y<N.loU+N.side ∧
      N.loV<s*x+N.c*y ∧ s*x+N.c*y<N.loV+N.side := by
    simp only [OpenSquare.Inside,InBands,signed,neg_mul,neg_neg,sub_eq_add_neg]
  have m := (bands _ _).mp marker
  have g := (bands _ _).mp elbow
  have vLower : N.loV<0 := by linarith only [m.2.2.1,order,cp]
  have uLower : 0≤N.loU := by
    apply le_of_not_gt
    intro low
    exact origin ((bands _ _).mpr ⟨by linarith only [low],
      by linarith only [g.2.1,cp],by linarith only [vLower],
      by linarith only [g.2.2.2,sp]⟩)
  have uInward : N.loU<(37/50)*s := by
    rcases alternative with outer | mixed
    · have x := (bands _ _).mp outer.1
      linarith only [x.1,sp]
    · have f := (bands _ _).mp mixed.1
      linarith only [f.1]
  have floors : (-(37/50)*N.c≤N.loV) ∨
      ((1/2)*s-N.c≤N.loV ∧ s<(13/25)*N.c) := by
    rcases alternative with outer | mixed
    · left
      have x := (bands _ _).mp outer.1
      apply le_of_not_gt
      intro low
      exact outer.2 ((bands _ _).mpr ⟨
        by linarith only [x.1,sp],
        by linarith only [m.2.1,order,cp],
        by linarith only [low],
        by linarith only [g.2.2.2,cp,sp]⟩)
    · have data := mixed_angle N s signed side cp sp.le order
        marker mixed.1 elbow origin mixed.2
      exact Or.inr ⟨data.2.2.2,data.2.1⟩
  have vFloor : -N.c≤N.loV := by
    rcases floors with outer | mixed
    · linarith only [outer,cp]
    · linarith only [mixed.1,sp]
  have tHighV : s-(11/25)*N.c<N.loV+N.side := by
    apply lt_of_not_ge
    intro high
    rcases floors with outer | mixed
    · have short := CommonCases.OutwardScalars.increasing_projection N.c s (3/10) 1
        cp sp.le order unit (by norm_num) (by norm_num) (by norm_num)
      linarith only [outer,high,side,short]
    · have short := (short_projections N (1/2) (14/25) (by norm_num)).2.2.2
      rw [signed] at short
      linarith only [mixed.1,high,side,short]
  have uUpper : N.loU+N.side≤N.c+(11/25)*s := by
    apply le_of_not_gt
    intro high
    exact right ((bands _ _).mpr ⟨
      by linarith only [m.1,order,cp],
      by linarith only [high],
      by linarith only [m.2.2.1,cp,sp],
      by linarith only [tHighV]⟩)
  exact ⟨uLower,by linarith only [g.1],uInward,vLower,uUpper,vFloor,floors⟩

/-- The strict x=0 point used to determine the actual separating cone. -/
theorem alternative_anchor (N : OpenSquare) (h : Alternative N) :
    ∃ y : ℝ,y<0 ∧ N.Inside 0 y := by
  rcases h with outer | mixed
  · exact ⟨-19/50,by norm_num,outer.1⟩
  · exact ⟨-37/50,by norm_num,mixed.1⟩

#print axioms faces
end N12Compact.Completion.OtherCases.C976NegativeTop
