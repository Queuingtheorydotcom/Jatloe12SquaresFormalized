import Compact.Core.SparseInteger

/-!
# Direct region DAG replay with persistent branch contexts

Each context record adds one row to an earlier context. A cut checks both
children, the exact strict complement, and the two context extensions. Empty
nodes use sparse integer certificates. Forbidden nodes cite a genuine
forbidden block whose rows are already present: no tautological Farkas proofs
are stored. Leaves retain the specified target rows.

All indexing is total. Bounds and local implications are explicit checks;
neither a missing record nor a malformed context can produce a contradiction
without the same soundness argument. No DAG is decoded into a RegionTree.
-/

namespace N12Compact.RegionDAG

open IntegerSupport SparseInteger

def opposite (row : Row) : Row :=
  ⟨-row.x, -row.y, -row.constant, !row.strict⟩

theorem opposite_holds (row : Row) (p : Fin 2 → ℝ) :
    (opposite row).Holds p ↔ ¬row.Holds p := by
  have he : (opposite row).eval p = -row.eval p := by
    simp [opposite, Row.eval]
    ring
  unfold Row.Holds
  rw [he]
  cases hs : row.strict <;> simp [opposite, hs]

structure Context (r : Nat) where
  parent : Nat
  row : Fin r
  depth : Nat
  deriving DecidableEq

/-- Index zero is the empty context. Depth bounds the lookup recursion; it is
checked whenever a context is extended. Prefixes remain shared records. -/
def contextRowsAt {r : Nat} (contexts : Nat → Context r) : Nat → Nat → List (Fin r)
  | 0, _ => []
  | depth + 1, index =>
      if index = 0 then [] else
        (contexts index).row :: contextRowsAt contexts depth (contexts index).parent

def contextRows {r : Nat} (contexts : Nat → Context r) (index : Nat) : List (Fin r) :=
  contextRowsAt contexts (contexts index).depth index

def Push {r : Nat} (contexts : Nat → Context r) (child parent : Nat) (row : Fin r) : Prop :=
  child ≠ 0 ∧ (contexts child).parent = parent ∧ (contexts child).row = row ∧
    (contexts child).depth = (contexts parent).depth + 1

instance {r : Nat} (contexts : Nat → Context r) (child parent : Nat) (row : Fin r) :
    Decidable (Push contexts child parent row) := inferInstanceAs (Decidable (_ ∧ _))

theorem push_rows {r : Nat} {contexts : Nat → Context r} {child parent : Nat}
    {row : Fin r} (h : Push contexts child parent row) :
    contextRows contexts child = row :: contextRows contexts parent := by
  rcases h with ⟨hn, hp, hr, hd⟩
  simp only [contextRows, hd, contextRowsAt, hn, ↓reduceIte, hp, hr]

def Included {r : Nat} (small large : List (Fin r)) : Prop :=
  ∀ row ∈ small, row ∈ large

instance {r : Nat} (small large : List (Fin r)) : Decidable (Included small large) :=
  inferInstanceAs (Decidable (∀ row ∈ small, row ∈ large))

inductive Kind (r : Nat) where
  | leaf (index : Nat)
  | empty (certificate : Certificate r)
  | forbidden (index : Nat)
  | cut (test complement : Fin r) (yes no : Nat)
  deriving DecidableEq

structure Node (r : Nat) where
  context : Nat
  kind : Kind r
  deriving DecidableEq

structure Program (r : Nat) where
  rows : Fin r → Row
  denominators : Fin r → Nat
  contexts : Nat → Context r
  nodes : Nat → Node r
  nodeCount : Nat
  leaves : Nat → List (Fin r)
  leafCount : Nat
  forbidden : Nat → List (Fin r)
  forbiddenCount : Nat

def Program.inputs {r : Nat} (program : Program r) (node : Nat) : List (Fin r) :=
  contextRows program.contexts (program.nodes node).context

def Program.NodeCheck {r : Nat} (program : Program r) (index : Nat) : Prop :=
  match (program.nodes index).kind with
  | .leaf leaf => leaf < program.leafCount ∧
      Included (program.leaves leaf) (program.inputs index)
  | .empty certificate => certificate.Check program.rows ⟨0, 0, 0, true⟩ ∧
      ∀ term ∈ certificate.terms, term.2 ∈ program.inputs index
  | .forbidden block => block < program.forbiddenCount ∧
      Included (program.forbidden block) (program.inputs index)
  | .cut test complement yes no =>
      yes < index ∧ no < index ∧ program.rows complement = opposite (program.rows test) ∧
      Push program.contexts (program.nodes yes).context (program.nodes index).context test ∧
      Push program.contexts (program.nodes no).context (program.nodes index).context complement

instance {r : Nat} (program : Program r) (index : Nat) :
    Decidable (program.NodeCheck index) := by
  unfold Program.NodeCheck
  cases (program.nodes index).kind <;> infer_instance

def Program.Check {r : Nat} (program : Program r) : Prop :=
  ∀ index ∈ List.range program.nodeCount, program.NodeCheck index

instance {r : Nat} (program : Program r) : Decidable program.Check :=
  inferInstanceAs (Decidable (∀ index ∈ List.range program.nodeCount, _))

/-- Every checked incoming point reaches a listed leaf. Both cut children
are mandatory, including equality boundaries through the strict complement. -/
theorem Program.sound {r : Nat} (program : Program r) (checked : program.Check)
    (p : Fin 2 → ℝ)
    (forbidden : ∀ b, b < program.forbiddenCount →
      ¬(∀ row ∈ program.forbidden b, (program.rows row).Holds p)) :
    ∀ index, index < program.nodeCount →
      (∀ row ∈ program.inputs index, (program.rows row).Holds p) →
      ∃ leaf, leaf < program.leafCount ∧
        ∀ row ∈ program.leaves leaf, (program.rows row).Holds p := by
  intro index
  induction index using Nat.strongRecOn with
  | ind index ih =>
      intro hi incoming
      have localCheck := checked index (List.mem_range.mpr hi)
      cases hk : (program.nodes index).kind with
      | leaf leaf =>
          simp only [NodeCheck, hk] at localCheck
          exact ⟨leaf, localCheck.1, fun row hr => incoming row (localCheck.2 row hr)⟩
      | empty certificate =>
          simp only [NodeCheck, hk] at localCheck
          exact (refutes localCheck.1 p
            (fun term ht => incoming term.2 (localCheck.2 term ht))).elim
      | forbidden block =>
          simp only [NodeCheck, hk] at localCheck
          exact (forbidden block localCheck.1
            (fun row hr => incoming row (localCheck.2 row hr))).elim
      | cut test complement yes no =>
          simp only [NodeCheck, hk] at localCheck
          obtain ⟨hy, hn, opposite_eq, pushYes, pushNo⟩ := localCheck
          by_cases testHolds : (program.rows test).Holds p
          · apply ih yes hy (Nat.lt_trans hy hi)
            have ctx := push_rows pushYes
            change contextRows program.contexts (program.nodes yes).context =
              test :: program.inputs index at ctx
            intro row hr
            rw [inputs, ctx] at hr
            rcases List.mem_cons.mp hr with he | hm
            · simpa only [he] using testHolds
            · exact incoming row hm
          · apply ih no hn (Nat.lt_trans hn hi)
            have complementHolds : (program.rows complement).Holds p := by
              rw [opposite_eq]
              exact (opposite_holds (program.rows test) p).mpr testHolds
            have ctx := push_rows pushNo
            change contextRows program.contexts (program.nodes no).context =
              complement :: program.inputs index at ctx
            intro row hr
            rw [inputs, ctx] at hr
            rcases List.mem_cons.mp hr with he | hm
            · simpa only [he] using complementHolds
            · exact incoming row hm

def Program.decode {r : Nat} (program : Program r) (refs : List (Fin r)) :
    List (S12.LinearConstraint 2) :=
  refs.map (fun i => (program.rows i).normalized (program.denominators i))

theorem Program.decode_holds_iff {r : Nat} (program : Program r)
    (positive : ∀ i, 0 < program.denominators i) (refs : List (Fin r))
    (p : Fin 2 → ℝ) :
    (∀ row ∈ program.decode refs, row.Holds p) ↔
      (∀ i ∈ refs, (program.rows i).Holds p) := by
  constructor
  · intro h i hi
    apply ((program.rows i).normalized_holds_iff _ (positive i) p).mp
    exact h _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · intro h row hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact ((program.rows i).normalized_holds_iff _ (positive i) p).mpr (h i hi)

/-- The same complete-cover theorem in the original region-row predicates. -/
theorem Program.normalized_sound {r : Nat} (program : Program r)
    (checked : program.Check) (positive : ∀ i, 0 < program.denominators i)
    (p : Fin 2 → ℝ)
    (forbidden : ∀ b, b < program.forbiddenCount →
      ¬(∀ row ∈ program.decode (program.forbidden b), row.Holds p))
    (root : Nat) (rootBound : root < program.nodeCount)
    (incoming : ∀ row ∈ program.decode (program.inputs root), row.Holds p) :
    ∃ leaf, leaf < program.leafCount ∧
      ∀ row ∈ program.decode (program.leaves leaf), row.Holds p := by
  obtain ⟨leaf, hl, hh⟩ := program.sound checked p
    (fun b hb h => forbidden b hb ((program.decode_holds_iff positive _ p).mpr h))
    root rootBound ((program.decode_holds_iff positive _ p).mp incoming)
  exact ⟨leaf, hl, (program.decode_holds_iff positive _ p).mpr hh⟩

#print axioms Program.normalized_sound

end N12Compact.RegionDAG
