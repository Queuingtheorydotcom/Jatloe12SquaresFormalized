import Compact.Core.PlanarVertexSparse

/-! Remove whole boundary lines before enumerating intersections.
A discarded line has one exact parallel-base certificate proving that no
point on it satisfies the closed base. This needs only one optional witness
per line, and excludes every pair involving that line at once. -/

set_option Elab.async false

namespace N12Compact.PlanarBoundaryFilter

open IntegerSupport PlanarVertex PlanarVertexCheck PlanarVertexSparse

structure LineExclusion where
  baseIndex : Nat
  scale : Int
  multiple : Int
  deriving DecidableEq

/-- The base row, after positive scaling, is parallel to the boundary row
and strictly negative on its zero line. The multiple may have either sign
so upper and lower compulsory bounds can both certify exclusion. -/
def LineExclusion.Check (hint : LineExclusion) (base : List Row)
    (boundary : Row) : Prop :=
  match base[hint.baseIndex]? with
  | none => False
  | some row =>
      0 < hint.scale ∧
      hint.scale * row.x = hint.multiple * boundary.x ∧
      hint.scale * row.y = hint.multiple * boundary.y ∧
      hint.scale * row.constant < hint.multiple * boundary.constant

instance (hint : LineExclusion) (base : List Row) (boundary : Row) :
    Decidable (hint.Check base boundary) := by
  unfold LineExclusion.Check
  cases base[hint.baseIndex]? <;> infer_instance

theorem LineExclusion.forces_negative (hint : LineExclusion) (base : List Row)
    (boundary : Row) (checked : hint.Check base boundary)
    (v : Vertex) (positive : 0 < v.denominator) (zero : v.eval boundary = 0) :
    ∃ row ∈ base, v.eval row < 0 := by
  cases hi : base[hint.baseIndex]? with
  | none => simp only [LineExclusion.Check, hi] at checked
  | some row =>
      have hc : 0 < hint.scale ∧
          hint.scale * row.x = hint.multiple * boundary.x ∧
          hint.scale * row.y = hint.multiple * boundary.y ∧
          hint.scale * row.constant < hint.multiple * boundary.constant := by
        simpa only [LineExclusion.Check, hi] using checked
      obtain ⟨hs, hx, hy, hk⟩ := hc
      have identity : hint.scale * v.eval row =
          hint.multiple * v.eval boundary + v.denominator *
            (hint.scale * row.constant - hint.multiple * boundary.constant) := by
        calc
          _ = v.x * (hint.scale * row.x) + v.y * (hint.scale * row.y) +
              v.denominator * (hint.scale * row.constant) := by
                dsimp [Vertex.eval]
                ring
          _ = _ := by rw [hx, hy]; dsimp [Vertex.eval]; ring
      have hn : hint.scale * v.eval row < 0 := by
        rw [identity, zero, mul_zero, zero_add]
        exact mul_neg_of_pos_of_neg positive (sub_neg.mpr hk)
      refine ⟨row, List.mem_of_getElem? hi, ?_⟩
      apply lt_of_not_ge
      intro hnonneg
      exact (not_lt_of_ge (mul_nonneg hs.le hnonneg)) hn

private theorem first_boundary_zero (a b : Row) : (vertex a b).eval a = 0 := by
  dsimp [Vertex.eval, vertex, det]
  ring

theorem LineExclusion.pairCheck (hint : LineExclusion) (base : List Row)
    (forbidden : List (List Row)) (targets : List Row) (a b : Row)
    (checked : hint.Check base a) : PairCheck base forbidden targets a b := by
  by_cases hd : det a b = 0
  · exact Or.inl hd
  · apply Or.inr
    intro feasible
    obtain ⟨row, hrow, negative⟩ := hint.forces_negative base a checked
      (vertex a b) (denominator_positive a b hd) (first_boundary_zero a b)
    exact ((not_lt_of_ge (feasible.1 row hrow)) negative).elim

/-- None retains a line; some certifies exclusion. The checked plan has
exactly one entry per original boundary, including retained lines. -/
def FilterCheck (base : List Row) : List Row → List (Option LineExclusion) → Prop
  | [], [] => True
  | _ :: rest, none :: plan => FilterCheck base rest plan
  | a :: rest, some hint :: plan => hint.Check base a ∧ FilterCheck base rest plan
  | _, _ => False

instance (base : List Row) (rows : List Row) (plan : List (Option LineExclusion)) :
    Decidable (FilterCheck base rows plan) := by
  induction rows generalizing plan with
  | nil => cases plan <;> unfold FilterCheck <;> infer_instance
  | cons a rest ih =>
      cases plan with
      | nil => unfold FilterCheck; infer_instance
      | cons hint plan =>
          letI := ih plan
          cases hint <;> unfold FilterCheck <;> infer_instance

def active : List Row → List (Option LineExclusion) → List Row
  | [], _ => []
  | _, [] => []
  | a :: rest, none :: plan => a :: active rest plan
  | _ :: rest, some _ :: plan => active rest plan

theorem FilterCheck.cover (base : List Row) (rows : List Row)
    (plan : List (Option LineExclusion)) (checked : FilterCheck base rows plan) :
    ∀ a ∈ rows, a ∈ active rows plan ∨ ∃ hint : LineExclusion, hint.Check base a := by
  induction rows generalizing plan with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons first rest ih =>
      cases plan with
      | nil => exact checked.elim
      | cons hint plan =>
          cases hint with
          | none =>
              intro a ha
              rcases List.mem_cons.mp ha with he | hr
              · apply Or.inl
                simpa only [active, he] using
                  (show first ∈ first :: active rest plan from List.mem_cons_self)
              · rcases ih plan checked a hr with kept | excluded
                · exact Or.inl (List.mem_cons_of_mem first kept)
                · exact Or.inr excluded
          | some hint =>
              obtain ⟨excluded, tail⟩ := checked
              intro a ha
              rcases List.mem_cons.mp ha with he | hr
              · exact Or.inr ⟨hint, by simpa only [he] using excluded⟩
              · exact ih plan tail a hr

/-- O(number of boundaries) line certificates followed by one unordered
check on the surviving lines. Target strictness and original source links
remain the responsibility of the unchanged DirectPoseCover bridge. -/
def Check (base : List Row) (forbidden : List (List Row)) (targets : List Row)
    (plan : List (Option LineExclusion)) : Prop :=
  let boundaries := (base ++ forbidden.flatten).dedup
  FilterCheck base boundaries plan ∧
    triangle (PairCheck base forbidden targets) (active boundaries plan)

instance (base : List Row) (forbidden : List (List Row)) (targets : List Row)
    (plan : List (Option LineExclusion)) : Decidable (Check base forbidden targets plan) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Check.toCheck {base : List Row} {forbidden : List (List Row)}
    {targets : List Row} {plan : List (Option LineExclusion)}
    (checked : Check base forbidden targets plan) :
    PlanarVertexCheck.Check base forbidden targets := by
  obtain ⟨filters, pairs⟩ := checked
  have coverage := FilterCheck.cover base _ plan filters
  have all := triangle_all _ (pairCheck_refl base forbidden targets)
    (pairCheck_swap base forbidden targets) _ pairs
  intro a ha b hb
  rcases coverage a ha with keptA | ⟨hintA, excludedA⟩
  · rcases coverage b hb with keptB | ⟨hintB, excludedB⟩
    · exact all a keptA b keptB
    · exact pairCheck_swap base forbidden targets b a
        (hintB.pairCheck base forbidden targets b a excludedB)
  · exact hintA.pairCheck base forbidden targets a b excludedA

#print axioms Check.toCheck
end N12Compact.PlanarBoundaryFilter
