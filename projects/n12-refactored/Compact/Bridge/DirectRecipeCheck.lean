import Compact.Bridge.DirectRecipeTable

/-! Numeric entry acceptance using only the already cached integer targets.
The original Entry.Check and all geometric conclusions remain unchanged.
Finite decisions explicitly traverse their given lists. -/

namespace N12Compact.DirectRecipeCheck
open IntegerSupport PlanarVertex PlanarVertexCheck PlanarVertexSparse DirectPoseCover

def StrictTargets (rows : List Row) : Prop :=
  ∀ row ∈ rows,
    row.strict = false ∨ (row.x = 0 ∧ row.y = 0 ∧ 0 < row.constant)

instance (rows : List Row) : Decidable (StrictTargets rows) :=
  List.decidableBAll _ rows

theorem strict_of_targets (root : Root) (rows : List Row)
    (exact_rows : rows = root.targetRows) (checked : StrictTargets rows) :
    root.strictOK := by
  cases result : root.result with
  | none => simp only [Root.strictOK, result]
  | some forms =>
      rw [Root.strictOK, result]
      intro f member
      apply checked f.row
      rw [exact_rows]
      simp only [Root.targetRows, result]
      exact List.mem_map.mpr ⟨f, member, rfl⟩

private def boxDecision (rows : List Row) : Decidable (BoxNormals rows) := by
  unfold BoxNormals
  letI : Decidable (∃ r ∈ rows, 0 < r.x ∧ r.y = 0) := List.decidableBEx _ rows
  letI : Decidable (∃ r ∈ rows, r.x < 0 ∧ r.y = 0) := List.decidableBEx _ rows
  letI : Decidable (∃ r ∈ rows, r.x = 0 ∧ 0 < r.y) := List.decidableBEx _ rows
  letI : Decidable (∃ r ∈ rows, r.x = 0 ∧ r.y < 0) := List.decidableBEx _ rows
  infer_instance

private def feasibleDecision (v : Vertex) (base : List Row)
    (forbidden : List (List Row)) : Decidable (v.Feasible base forbidden) := by
  unfold Vertex.Feasible
  letI : Decidable (∀ row ∈ base, 0 ≤ v.eval row) := List.decidableBAll _ base
  letI : DecidablePred (fun block : List Row => ¬(∀ row ∈ block, 0 < v.eval row)) :=
    fun block =>
      letI : Decidable (∀ row ∈ block, 0 < v.eval row) := List.decidableBAll _ block
      inferInstance
  letI : Decidable (∀ block ∈ forbidden, ¬(∀ row ∈ block, 0 < v.eval row)) :=
    List.decidableBAll _ forbidden
  infer_instance

private def pairDecision (base : List Row) (forbidden : List (List Row))
    (targets : List Row) (a b : Row) : Decidable (PairCheck base forbidden targets a b) := by
  unfold PairCheck
  letI := feasibleDecision (vertex a b) base forbidden
  letI : Decidable (∀ target ∈ targets, 0 ≤ (vertex a b).eval target) :=
    List.decidableBAll _ targets
  infer_instance

private def triangleDecision (test : Row → Row → Prop) [DecidableRel test] :
    (rows : List Row) → Decidable (triangle test rows)
  | [] => isTrue trivial
  | a :: rest =>
      letI := triangleDecision test rest
      letI : Decidable (∀ b ∈ rest, test a b) := List.decidableBAll _ rest
      inferInstanceAs (Decidable ((∀ b ∈ rest, test a b) ∧ triangle test rest))

def LiteralCheck {angleCount poseCount : Nat}
    {bank : DirectRecipeTable.Bank angleCount poseCount}
    {inside outside : List (ℚ × ℚ)} (entry : DirectRecipeTable.Entry bank inside outside) : Prop :=
  BoxNormals (entry.cached.base.map Form.row) ∧
  triangle (PairCheck (entry.cached.base.map Form.row)
    (entry.cached.forbidden.map (List.map Form.row)) entry.targets) entry.cached.active ∧
  StrictTargets entry.targets

instance {angleCount poseCount : Nat}
    {bank : DirectRecipeTable.Bank angleCount poseCount}
    {inside outside : List (ℚ × ℚ)} (entry : DirectRecipeTable.Entry bank inside outside) :
    Decidable (LiteralCheck entry) := by
  unfold LiteralCheck
  letI := boxDecision (entry.cached.base.map Form.row)
  letI : DecidableRel (PairCheck (entry.cached.base.map Form.row)
      (entry.cached.forbidden.map (List.map Form.row)) entry.targets) :=
    pairDecision _ _ _
  letI := triangleDecision (PairCheck (entry.cached.base.map Form.row)
    (entry.cached.forbidden.map (List.map Form.row)) entry.targets) entry.cached.active
  infer_instance

theorem LiteralCheck.toCheck {angleCount poseCount : Nat}
    {bank : DirectRecipeTable.Bank angleCount poseCount}
    {inside outside : List (ℚ × ℚ)} {entry : DirectRecipeTable.Entry bank inside outside}
    (checked : LiteralCheck entry) : entry.Check := by
  obtain ⟨box, numeric, strict⟩ := checked
  exact ⟨box, numeric, strict_of_targets _ entry.targets entry.targets_exact strict⟩

theorem all_checked {angleCount poseCount : Nat}
    {bank : DirectRecipeTable.Bank angleCount poseCount}
    {inside outside : List (ℚ × ℚ)}
    (entries : List (DirectRecipeTable.Entry bank inside outside))
    (checked : ∀ entry ∈ entries, LiteralCheck entry) :
    ∀ entry ∈ entries, entry.Check :=
  fun entry member => (checked entry member).toCheck

#print axioms LiteralCheck.toCheck
end N12Compact.DirectRecipeCheck
