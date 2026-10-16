import Compact.Completion.OtherCases.C1089.ContinuousReach
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin

/-! The corner-to-right-origin step of C1089-CONTINUOUS-REDUCTION
Theorem 3. The corner's excluded halfpoint is strictly owned by the same
actual B whose marker and inward point produced it. Only the stated
one-sided walls are supplied. Source translation only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1089.ContinuousOrigin
open S12 S12Pilot
set_option Elab.async false

theorem right_origin (W B K : OpenSquare)
    (side : 1<W.side) (same : W.side=K.side)
    (wall : ∀ x y,W.Inside x y → x≤2)
    (wallsK : ∀ x y,K.Inside x y → x≤2 ∧ y≤2)
    (marker : W.Inside (543/500) 0) (inner : W.Inside 1 (13/50))
    (cornerMarker : K.Inside (543/500) 1) (cornerPoint : K.Inside 1 1)
    (halfpoint : B.Inside (1/2) 1)
    (apartKB : ∀ x y,¬(K.Inside x y ∧ B.Inside x y))
    (apartKW : ∀ x y,¬(K.Inside x y ∧ W.Inside x y)) : W.Inside 1 0 := by
  let chartSquare (Q : OpenSquare) :=
    C1092RigidCharts.translate (C1092RigidCharts.opposite (C1092RigidCharts.swap Q)) (-2) (-2)
  have chart (Q : OpenSquare) (x y : ℝ) :
      (chartSquare Q).Inside x y↔Q.Inside (2-y) (2-x) := by
    dsimp only [chartSquare]
    rw [C1092RigidCharts.inside_translate,C1092RigidCharts.inside_opposite,
      C1092RigidCharts.inside_swap]
    congr 2 <;> ring
  have result := WallProfile.boundary_origin (chartSquare W) (chartSquare K)
    (457/500) (87/50) side same
    (by
      intro x y own
      have bound := wall _ _ ((chart _ _ _).mp own)
      linarith only [bound])
    (by
      intro x y own
      have bound := wallsK _ _ ((chart _ _ _).mp own)
      exact ⟨by linarith only [bound.2],by linarith only [bound.1]⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [chart]; exact marker)
    (by norm_num [chart]; exact inner)
    (by norm_num [chart]; exact cornerMarker)
    (by norm_num [chart]; exact cornerPoint)
    (by
      intro own
      have actual := (chart _ _ _).mp own
      norm_num at actual
      exact apartKB _ _ ⟨actual,halfpoint⟩)
    (by
      intro x y own
      exact apartKW _ _ ⟨(chart _ _ _).mp own.1,(chart _ _ _).mp own.2⟩)
  have actual := (chart _ _ _).mp result
  norm_num at actual
  exact actual

/-- The full local origin producer, with the halfpoint derived rather
than assumed. All five pairwise uses below refer to unchanged squares. -/
theorem right_origin_of_points (C W B K : OpenSquare)
    (sideW : 1<W.side) (sideB : 1<B.side) (sameWK : W.side=K.side)
    (wallW : ∀ x y,W.Inside x y → x≤2)
    (wallB : ∀ x y,B.Inside x y → y≤2)
    (wallsK : ∀ x y,K.Inside x y → x≤2 ∧ y≤2)
    (inward : C.Inside 0 (13/50))
    (markerW : W.Inside (543/500) 0) (innerW : W.Inside 1 (13/50))
    (markerB : B.Inside 0 (543/500)) (innerB : B.Inside (2/5) 1)
    (missingB : ¬B.Inside (-13/50) 1)
    (markerK : K.Inside (543/500) 1) (pointK : K.Inside 1 1)
    (apartBC : ∀ x y,¬(B.Inside x y ∧ C.Inside x y))
    (apartKB : ∀ x y,¬(K.Inside x y ∧ B.Inside x y))
    (apartKW : ∀ x y,¬(K.Inside x y ∧ W.Inside x y)) :
    B.Inside (14/25) 1 ∧ W.Inside 1 0 := by
  have reach := ContinuousReach.bottom_points B C sideB wallB markerB innerB missingB inward apartBC
  exact ⟨reach.1,right_origin W B K sideW sameWK wallW wallsK markerW innerW
    markerK pointK reach.2 apartKB apartKW⟩

#print axioms right_origin
#print axioms right_origin_of_points
end N12Compact.Completion.OtherCases.C1089.ContinuousOrigin
