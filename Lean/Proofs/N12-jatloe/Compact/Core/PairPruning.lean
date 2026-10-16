import Compact.Core.ReferenceAxis
import Compact.Core.RegionDAG
import S12.ContinuousPruning

/-!
Shared geometric meaning of an eight-axis, four-index overlap certificate.
All source-row and neighbor-row memberships are checked. A pruning block
must cover every neighbor leaf before it can exclude any actual center.
-/

set_option Elab.async false

namespace N12Compact.PairPruning

open S12 S12Pilot IntegerSupport

structure Support (r : Nat) where
  a₁ : Fin r
  a₂ : Fin r
  b₁ : Fin r
  b₂ : Fin r
  deriving DecidableEq

def direction (a b : ReferenceAxis.Reference) (i : Fin 8) : ReferenceAxis.Direction :=
  (ReferenceAxis.directions a b).get ⟨i.val, by
    simpa [ReferenceAxis.directions] using i.isLt⟩

def Support.Check {r : Nat} (rows : Fin r → Row)
    (aInputs bInputs : List (Fin r)) (a b : ReferenceAxis.Reference)
    (i : Fin 8) (w : Support r) : Prop :=
  w.a₁ ∈ aInputs ∧ w.a₂ ∈ aInputs ∧ w.b₁ ∈ bInputs ∧ w.b₂ ∈ bInputs ∧
  PairSupport.Check (rows w.a₁) (rows w.a₂) (rows w.b₁) (rows w.b₂)
    (ReferenceAxis.target a b (direction a b i))

instance {r : Nat} (rows : Fin r → Row) (aInputs bInputs : List (Fin r))
    (a b : ReferenceAxis.Reference) (i : Fin 8) (w : Support r) :
    Decidable (w.Check rows aInputs bInputs a b i) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Check {r : Nat} (rows : Fin r → Row) (aInputs bInputs : List (Fin r))
    (a b : ReferenceAxis.Reference) (witness : Fin 8 → Support r) : Prop :=
  ∀ i, (witness i).Check rows aInputs bInputs a b i

instance {r : Nat} (rows : Fin r → Row) (aInputs bInputs : List (Fin r))
    (a b : ReferenceAxis.Reference) (witness : Fin 8 → Support r) :
    Decidable (Check rows aInputs bInputs a b witness) :=
  inferInstanceAs (Decidable (∀ i, _))

theorem sound {r : Nat} (rows : Fin r → Row)
    (aInputs bInputs : List (Fin r)) (a b : ReferenceAxis.Reference)
    (ha : a.Valid) (hb : b.Valid) (hac : a.value.Check) (hbc : b.value.Check)
    (witness : Fin 8 → Support r) (checked : Check rows aInputs bInputs a b witness)
    (p q : Fin 2 → ℝ)
    (hp : ∀ i ∈ aInputs, (rows i).Holds p)
    (hq : ∀ i ∈ bInputs, (rows i).Holds q) :
    OverlapsAt (a.value.toSquare hac) (b.value.toSquare hbc)
      (p 0, p 1) (q 0, q 1) := by
  apply ReferenceAxis.overlap a b ha hb hac hbc p q
  intro n hn
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hn
  let j : Fin 8 := ⟨i.val, by simpa [ReferenceAxis.directions] using i.isLt⟩
  have he : direction a b j = n := by simpa [direction, j] using hi
  rw [← he]
  obtain ⟨h₁, h₂, h₃, h₄, hc⟩ := checked j
  exact PairSupport.sound hc p q (hp _ h₁) (hp _ h₂) (hq _ h₃) (hq _ h₄)

def inputRows {r : Nat} (rows : Fin r → Row) (denominators : Fin r → Nat)
    (indices : List (Fin r)) : RegionConstraints :=
  indices.map (fun i => (rows i).normalized (denominators i))

theorem inputs_hold {r : Nat} (rows : Fin r → Row) (denominators : Fin r → Nat)
    (positive : ∀ i, 0 < denominators i) (indices : List (Fin r)) (p : Fin 2 → ℝ)
    (h : ∀ row ∈ inputRows rows denominators indices, row.Holds p) :
    ∀ i ∈ indices, (rows i).Holds p := by
  intro i hi
  apply ((rows i).normalized_holds_iff (denominators i) (positive i) p).mp
  exact h _ (List.mem_map.mpr ⟨i, hi, rfl⟩)

/-- Actual source and neighbor squares overlap when all eight checked
support inequalities hold. The original inner-reference containments are
provided by the unchanged `PoseLeaf.Realizes` hypotheses. -/
theorem actual_overlap {r : Nat} (rows : Fin r → Row) (denominators : Fin r → Nat)
    (positive : ∀ i, 0 < denominators i) (block sourceRows neighborRows : List (Fin r))
    (source neighbor : PoseLeaf) (a b : ReferenceAxis.Reference)
    (ha : a.Valid) (hb : b.Valid)
    (haRef : a.value = source.angle.val.reference 1)
    (hbRef : b.value = neighbor.angle.val.reference 1)
    (haRows : source.inputs = inputRows rows denominators sourceRows)
    (hbRows : neighbor.inputs = inputRows rows denominators neighborRows)
    (witness : Fin 8 → Support r)
    (checked : Check rows (block ++ sourceRows) neighborRows a b witness)
    (q t : OpenSquare) (hq : source.Realizes q) (ht : neighbor.Realizes t)
    (hblock : ∀ i ∈ block, (rows i).Holds ![centerX q, centerY q]) :
    ∃ x y, q.Inside x y ∧ t.Inside x y := by
  have hac : a.value.Check := by
    rw [haRef]
    exact source.angle.val.reference_checked source.angle.property 1 (by norm_num)
  have hbc : b.value.Check := by
    rw [hbRef]
    exact neighbor.angle.val.reference_checked neighbor.angle.property 1 (by norm_num)
  have hs : ∀ i ∈ sourceRows, (rows i).Holds ![centerX q, centerY q] := by
    apply inputs_hold rows denominators positive sourceRows _
    rw [← haRows]
    exact hq.1
  have hn : ∀ i ∈ neighborRows, (rows i).Holds ![centerX t, centerY t] := by
    apply inputs_hold rows denominators positive neighborRows _
    rw [← hbRows]
    exact ht.1
  have overlap := sound rows (block ++ sourceRows) neighborRows a b ha hb hac hbc
    witness checked ![centerX q, centerY q] ![centerX t, centerY t]
    (by intro i hi; exact (List.mem_append.mp hi).elim (hblock i) (hs i)) hn
  obtain ⟨P, hPq, hPt⟩ := overlap
  refine ⟨P.1, P.2, hq.2 P ?_, ht.2 P ?_⟩
  · simpa only [haRef, Matrix.cons_val_zero, Matrix.cons_val_one] using hPq
  · simpa only [hbRef, Matrix.cons_val_zero, Matrix.cons_val_one] using hPt

/-- A block is excluded only after every possible neighbor leaf has a
checked certificate. The neighbor coverage premise is never narrowed. -/
theorem block_forbidden {r : Nat} (rows : Fin r → Row)
    (block : List (Fin r)) (neighbors : List PoseLeaf) (q t : OpenSquare)
    (covered : PoseCovered neighbors t)
    (every_neighbor : ∀ leaf ∈ neighbors, leaf.Realizes t →
      (∀ i ∈ block, (rows i).Holds ![centerX q, centerY q]) →
      ∃ x y, q.Inside x y ∧ t.Inside x y)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    ¬(∀ i ∈ block, (rows i).Holds ![centerX q, centerY q]) := by
  intro holds
  obtain ⟨leaf, member, realizes⟩ := covered
  obtain ⟨x, y, overlap⟩ := every_neighbor leaf member realizes holds
  exact disjoint x y overlap

/-- The first false block row identifies a surviving piece. Prefix rows
remain in its context, so existing outward-relaxation certificates apply
without weakening any of their hypotheses. -/
def outsidePieces {r : Nat} (complement : Fin r → Fin r) :
    List (Fin r) → List (Fin r) → List (List (Fin r))
  | [], _ => []
  | row :: rest, inputs =>
      (complement row :: inputs) :: outsidePieces complement rest (row :: inputs)

theorem outsidePieces_sound {r : Nat} (rows : Fin r → Row)
    (complement : Fin r → Fin r) (block inputs : List (Fin r))
    (exact_complement : ∀ i ∈ block, rows (complement i) = RegionDAG.opposite (rows i))
    (p : Fin 2 → ℝ) (incoming : ∀ i ∈ inputs, (rows i).Holds p)
    (forbidden : ¬(∀ i ∈ block, (rows i).Holds p)) :
    ∃ piece ∈ outsidePieces complement block inputs, ∀ i ∈ piece, (rows i).Holds p := by
  induction block generalizing inputs with
  | nil => exact (forbidden (by simp)).elim
  | cons row rest ih =>
      by_cases holds : (rows row).Holds p
      · have tail_forbidden : ¬(∀ i ∈ rest, (rows i).Holds p) := by
          intro all
          apply forbidden
          intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact holds
          · exact all i hi
        obtain ⟨piece, member, all⟩ := ih (row :: inputs)
          (fun i hi => exact_complement i (List.mem_cons_of_mem _ hi))
          (by intro i hi; rcases List.mem_cons.mp hi with rfl | hi
              · exact holds
              · exact incoming i hi)
          tail_forbidden
        exact ⟨piece, List.mem_cons_of_mem _ member, all⟩
      · refine ⟨complement row :: inputs, List.mem_cons_self, ?_⟩
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · rw [exact_complement row (List.mem_cons_self)]
          exact (RegionDAG.opposite_holds (rows row) p).mpr holds
        · exact incoming i hi

#print axioms actual_overlap
#print axioms block_forbidden
#print axioms outsidePieces_sound

end N12Compact.PairPruning
