import Compact.Core.PlanarVertexCheck

/-! Optional faster checks for the same continuous boundary theorem.
The first variant checks each unordered pair once and stores no new data.
The second permits one exact infeasibility witness per pair. Its recursive
shape checks every unordered pair; a missing entry cannot hide a vertex.
Neither variant changes the accepted geometric theorem or original root API. -/

set_option Elab.async false

namespace N12Compact.PlanarVertexSparse

open IntegerSupport PlanarVertex PlanarVertexCheck

private theorem det_swap (a b : Row) : det b a = -det a b := by
  dsimp [det]
  ring

private theorem sign_swap (a b : Row) (hd : det a b ≠ 0) :
    sign b a = -sign a b := by
  by_cases h : 0 ≤ det a b
  · have h' : ¬0 ≤ det b a := by rw [det_swap]; omega
    simp only [sign, if_pos h, if_neg h']
  · have h' : 0 ≤ det b a := by rw [det_swap]; omega
    simp only [sign, if_neg h, if_pos h']
    norm_num

theorem vertex_swap (a b : Row) (hd : det a b ≠ 0) :
    vertex b a = vertex a b := by
  unfold vertex
  rw [sign_swap a b hd, det_swap]
  congr 1 <;> ring

theorem pairCheck_refl (base : List Row) (forbidden : List (List Row))
    (targets : List Row) (a : Row) : PairCheck base forbidden targets a a := by
  apply Or.inl
  dsimp [det]
  ring

theorem pairCheck_swap (base : List Row) (forbidden : List (List Row))
    (targets : List Row) (a b : Row)
    (checked : PairCheck base forbidden targets a b) :
    PairCheck base forbidden targets b a := by
  by_cases hd : det a b = 0
  · exact Or.inl (by rw [det_swap, hd, neg_zero])
  · rcases checked with hz | checked
    · exact (hd hz).elim
    · exact Or.inr (by simpa only [vertex_swap a b hd] using checked)

/-- Strict upper triangle, excluding reflexive and reversed pairs. -/
def triangle (test : Row → Row → Prop) : List Row → Prop
  | [] => True
  | a :: rest => (∀ b ∈ rest, test a b) ∧ triangle test rest

instance (test : Row → Row → Prop) [DecidableRel test] (rows : List Row) :
    Decidable (triangle test rows) := by
  induction rows with
  | nil => exact isTrue trivial
  | cons a rest ih =>
      letI := ih
      unfold triangle
      infer_instance

theorem triangle_all (test : Row → Row → Prop)
    (refl : ∀ a, test a a) (symm : ∀ a b, test a b → test b a)
    (rows : List Row) : triangle test rows →
    ∀ a ∈ rows, ∀ b ∈ rows, test a b := by
  induction rows with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons first rest ih =>
      rintro ⟨head, tail⟩ a ha b hb
      rcases List.mem_cons.mp ha with hae | har
      · rcases List.mem_cons.mp hb with hbe | hbr
        · simpa only [hae, hbe] using refl first
        · simpa only [hae] using head b hbr
      · rcases List.mem_cons.mp hb with hbe | hbr
        · simpa only [hbe] using symm first a (head a har)
        · exact ih tail a har b hbr

/-- Same arithmetic test, half as many pair evaluations and no witness data. -/
def UnorderedCheck (base : List Row) (forbidden : List (List Row))
    (targets : List Row) : Prop :=
  triangle (PairCheck base forbidden targets) (base ++ forbidden.flatten).dedup

instance (base : List Row) (forbidden : List (List Row)) (targets : List Row) :
    Decidable (UnorderedCheck base forbidden targets) :=
  inferInstanceAs (Decidable (triangle _ _))

theorem UnorderedCheck.toCheck {base : List Row} {forbidden : List (List Row)}
    {targets : List Row} (checked : UnorderedCheck base forbidden targets) :
    PlanarVertexCheck.Check base forbidden targets :=
  triangle_all _ (pairCheck_refl base forbidden targets)
    (pairCheck_swap base forbidden targets) _ checked

inductive Witness where
  /-- One closed base inequality has a strictly negative value. -/
  | outsideBase (index : Nat)
  /-- Every face of one original open forbidden block is positive. -/
  | insideForbidden (index : Nat)
  /-- All target bounds hold, whether or not this vertex is feasible. -/
  | targetBounds
  deriving DecidableEq

def Witness.Check (hint : Witness) (v : Vertex) (base : List Row)
    (forbidden : List (List Row)) (targets : List Row) : Prop :=
  match hint with
  | .outsideBase i =>
      match base[i]? with
      | none => False
      | some row => v.eval row < 0
  | .insideForbidden i =>
      match forbidden[i]? with
      | none => False
      | some block => ∀ row ∈ block, 0 < v.eval row
  | .targetBounds => ∀ row ∈ targets, 0 ≤ v.eval row

instance (hint : Witness) (v : Vertex) (base : List Row)
    (forbidden : List (List Row)) (targets : List Row) :
    Decidable (hint.Check v base forbidden targets) := by
  cases hint with
  | outsideBase i =>
      change Decidable (match base[i]? with
        | none => False | some row => v.eval row < 0)
      cases base[i]? <;> infer_instance
  | insideForbidden i =>
      change Decidable (match forbidden[i]? with
        | none => False | some block => ∀ row ∈ block, 0 < v.eval row)
      cases forbidden[i]? <;> infer_instance
  | targetBounds =>
      change Decidable (∀ row ∈ targets, 0 ≤ v.eval row)
      infer_instance

theorem Witness.sound (hint : Witness) (v : Vertex) (base : List Row)
    (forbidden : List (List Row)) (targets : List Row)
    (checked : hint.Check v base forbidden targets)
    (feasible : v.Feasible base forbidden) :
    ∀ target ∈ targets, 0 ≤ v.eval target := by
  cases hint with
  | outsideBase i =>
      cases hi : base[i]? with
      | none => simp only [Witness.Check, hi] at checked
      | some row =>
          have hr : row ∈ base := List.mem_of_getElem? hi
          have hn : v.eval row < 0 := by simpa only [Witness.Check, hi] using checked
          exact (not_lt_of_ge (feasible.1 row hr) hn).elim
  | insideForbidden i =>
      cases hi : forbidden[i]? with
      | none => simp only [Witness.Check, hi] at checked
      | some block =>
          have hb : block ∈ forbidden := List.mem_of_getElem? hi
          have hp : ∀ row ∈ block, 0 < v.eval row := by
            simpa only [Witness.Check, hi] using checked
          exact (feasible.2 block hb hp).elim
  | targetBounds => exact checked

def PairWitnessCheck (base : List Row) (forbidden : List (List Row))
    (targets : List Row) (a b : Row) (hint : Witness) : Prop :=
  det a b = 0 ∨ hint.Check (vertex a b) base forbidden targets

instance (base : List Row) (forbidden : List (List Row)) (targets : List Row)
    (a b : Row) (hint : Witness) :
    Decidable (PairWitnessCheck base forbidden targets a b hint) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem PairWitnessCheck.sound {base : List Row} {forbidden : List (List Row)}
    {targets : List Row} {a b : Row} {hint : Witness}
    (checked : PairWitnessCheck base forbidden targets a b hint) :
    PairCheck base forbidden targets a b := by
  rcases checked with parallel | checked
  · exact Or.inl parallel
  · exact Or.inr (hint.sound _ _ _ _ checked)

def checkRow (base : List Row) (forbidden : List (List Row)) (targets : List Row)
    (a : Row) : List Row → List Witness → Prop
  | [], [] => True
  | b :: rest, hint :: hints =>
      PairWitnessCheck base forbidden targets a b hint ∧
        checkRow base forbidden targets a rest hints
  | _, _ => False

instance (base : List Row) (forbidden : List (List Row)) (targets : List Row)
    (a : Row) (rows : List Row) (hints : List Witness) :
    Decidable (checkRow base forbidden targets a rows hints) := by
  induction rows generalizing hints with
  | nil => cases hints <;> unfold checkRow <;> infer_instance
  | cons b rest ih =>
      cases hints with
      | nil => unfold checkRow; infer_instance
      | cons hint hints =>
          letI := ih hints
          unfold checkRow
          infer_instance

theorem checkRow_sound (base : List Row) (forbidden : List (List Row))
    (targets : List Row) (a : Row) (rows : List Row) (hints : List Witness) :
    checkRow base forbidden targets a rows hints →
      ∀ b ∈ rows, PairCheck base forbidden targets a b := by
  induction rows generalizing hints with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons b rest ih =>
      cases hints with
      | nil => exact False.elim
      | cons hint hints =>
          rintro ⟨first, tail⟩ q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact first.sound
          · exact ih hints tail q hq

def checkTriangle (base : List Row) (forbidden : List (List Row))
    (targets : List Row) : List Row → List (List Witness) → Prop
  | [], [] => True
  | a :: rest, hints :: plan =>
      checkRow base forbidden targets a rest hints ∧
        checkTriangle base forbidden targets rest plan
  | _, _ => False

instance (base : List Row) (forbidden : List (List Row)) (targets : List Row)
    (rows : List Row) (plan : List (List Witness)) :
    Decidable (checkTriangle base forbidden targets rows plan) := by
  induction rows generalizing plan with
  | nil => cases plan <;> unfold checkTriangle <;> infer_instance
  | cons a rest ih =>
      cases plan with
      | nil => unfold checkTriangle; infer_instance
      | cons hints plan =>
          letI := ih plan
          unfold checkTriangle
          infer_instance

theorem checkTriangle_sound (base : List Row) (forbidden : List (List Row))
    (targets : List Row) (rows : List Row) (plan : List (List Witness)) :
    checkTriangle base forbidden targets rows plan →
      triangle (PairCheck base forbidden targets) rows := by
  induction rows generalizing plan with
  | nil => exact fun _ => trivial
  | cons a rest ih =>
      cases plan with
      | nil => exact False.elim
      | cons hints plan =>
          rintro ⟨first, tail⟩
          exact ⟨checkRow_sound _ _ _ _ _ _ first, ih plan tail⟩

def SparseCheck (base : List Row) (forbidden : List (List Row))
    (targets : List Row) (plan : List (List Witness)) : Prop :=
  checkTriangle base forbidden targets (base ++ forbidden.flatten).dedup plan

instance (base : List Row) (forbidden : List (List Row)) (targets : List Row)
    (plan : List (List Witness)) : Decidable (SparseCheck base forbidden targets plan) :=
  inferInstanceAs (Decidable (checkTriangle _ _ _ _ _))

theorem SparseCheck.toCheck {base : List Row} {forbidden : List (List Row)}
    {targets : List Row} {plan : List (List Witness)}
    (checked : SparseCheck base forbidden targets plan) :
    PlanarVertexCheck.Check base forbidden targets :=
  UnorderedCheck.toCheck (checkTriangle_sound _ _ _ _ _ checked)

#print axioms UnorderedCheck.toCheck
#print axioms SparseCheck.toCheck
end N12Compact.PlanarVertexSparse
