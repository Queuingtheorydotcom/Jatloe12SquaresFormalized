import Compact.Bridge.C1092WallSymmetry.OwnerTransport

/-! The wall-center cuts and strict forced points move with the same actual owners. -/
namespace N12Compact.C1092WallSymmetry
open S12 S12Pilot C1092WallCycle
set_option Elab.async false

theorem wall_center_transport (g : Transform) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (k : Fin 4) :
    centerY (wallFrame (g.pullPacking p) k) =
      if wallFlip g k then 4-centerY (wallFrame p (wallAction g k))
      else centerY (wallFrame p (wallAction g k)) := by
  unfold wallFrame
  rw [wall_transport g p hf k]
  rcases g with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> fin_cases k <;>
    simp [localFrame,Transform.pull,wallFlip,wallAction,wallX,wallY,wallSwap]

private theorem wall_point_transport (g : Transform) (k : Fin 4) (b : Bool) (x y : ℝ) :
    g.apply (pointMap k x (branchY (if wallFlip g k then !b else b) y)).1
      (pointMap k x (branchY (if wallFlip g k then !b else b) y)).2 =
    pointMap (wallAction g k) x (branchY b y) := by
  rcases g with ⟨a,c,d⟩
  cases a <;> cases c <;> cases d <;> fin_cases k <;> cases b
  all_goals ext <;>
    simp [Transform.apply,pointMap,branchY,wallFlip,wallAction,wallX,wallY,wallSwap] <;> ring

theorem forced_point_transport (g : Transform) (b : WallBranch) (k : Fin 4) (i : Fin 12) :
    g.apply (forcedPoint k (branchAction g b k) i).1
      (forcedPoint k (branchAction g b k) i).2 =
    forcedPoint (wallAction g k) (b (wallAction g k)) i := by
  exact wall_point_transport g k (b (wallAction g k))
    (C1092WallPolynomial.targetX i) (C1092WallPolynomial.targetY i)

/-- The closed inequalities and all 48 strict point memberships transform
simultaneously. A center on the cut remains covered on either side. -/
theorem context_transport (g : Transform) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (b : WallBranch) (hb : WallContext p b) :
    WallContext (g.pullPacking p) (branchAction g b) := by
  intro k
  constructor
  · rw [wall_center_transport g p hf k]
    have cut := (hb (wallAction g k)).1
    cases hflip : wallFlip g k <;> cases hbit : b (wallAction g k) <;>
      simp [branchAction,hflip,hbit] at cut ⊢ <;> linarith only [cut]
  · intro i
    rw [wall_transport g p hf k,inside_pull,forced_point_transport]
    exact (hb (wallAction g k)).2 i

end N12Compact.C1092WallSymmetry
