import Compact.Cases.C898.ChordRadii
import Compact.Core.CoordinateBound

/-!
The vertical transition has two genuinely geometric ingredients: every
neighbor reaches the whole common window, and four long sections are
impossible. Its remaining pruning is just the complement of a closed interval.
There is no reconstructed region tree or four-dimensional linear certificate.
-/

namespace N12Compact.C898Chord
open S12 S12Pilot IntegerSupport CoordinateBound AngleSection C898Shared

noncomputable def poseRadius (i : Fin poseCount) : Radius := radiusFor (poseAngle i)

theorem pose_radius_checked (i : Fin poseCount) :
    (poseRadius i).Check (poses i).angle.val := radius_checked (poseAngle i)

theorem pose_row_holds {i : Fin poseCount} {q : OpenSquare}
    (h : (poses i).OrientedRealizes q) (r : Fin rowCount) (hr : r ∈ poseRows i) :
    (rows r).Holds ![centerX q, centerY q] := by
  apply ((rows r).normalized_holds_iff _ (positive_denominators r) _).mp
  exact h.1.1 _ (List.mem_map.mpr ⟨r, hr, rfl⟩)

structure Neighbor where
  pose : Fin poseCount
  lowerLeft : Fin rowCount
  lowerRight : Fin rowCount
  upperLeft : Fin rowCount
  upperRight : Fin rowCount
  deriving DecidableEq

def Neighbor.Check (w : Neighbor) (lo hi : ℚ) : Prop :=
  w.lowerLeft ∈ poseRows w.pose ∧ w.lowerRight ∈ poseRows w.pose ∧
  w.upperLeft ∈ poseRows w.pose ∧ w.upperRight ∈ poseRows w.pose ∧
  RowSupport.Check (rows w.lowerLeft) (rows w.lowerRight)
    (lower (hi - (poseRadius w.pose).radius) false) ∧
  RowSupport.Check (rows w.upperLeft) (rows w.upperRight)
    (upper (lo + (poseRadius w.pose).radius) false)

noncomputable instance (w : Neighbor) (lo hi : ℚ) : Decidable (w.Check lo hi) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Neighbor.sound (w : Neighbor) (lo hi : ℚ) (checked : w.Check lo hi)
    (q : OpenSquare) (ha : 1 < q.side) (h : (poses w.pose).OrientedRealizes q)
    (x : ℝ) (hx0 : (lo : ℝ) ≤ x) (hx1 : x ≤ (hi : ℝ)) : VerticalSection q x := by
  obtain ⟨hl0, hl1, hu0, hu1, hl, hu⟩ := checked
  have hl' := (holds_lower (hi - (poseRadius w.pose).radius) false
    ![centerX q, centerY q]).mp
    (RowSupport.sound hl _ (pose_row_holds h _ hl0) (pose_row_holds h _ hl1))
  have hu' := (holds_upper (lo + (poseRadius w.pose).radius) false
    ![centerX q, centerY q]).mp
    (RowSupport.sound hu _ (pose_row_holds h _ hu0) (pose_row_holds h _ hu1))
  simp only [Bool.false_eq_true, ↓reduceIte, Matrix.cons_val_zero] at hl' hu'
  push_cast at hl' hu'
  apply oriented_vertical (poses w.pose) (poseRadius w.pose)
    (pose_radius_checked w.pose) q ha h.2 x
  apply abs_le.mpr
  constructor <;> linarith

def NeighborCoverCheck (domain : List (Fin poseCount)) (records : List Neighbor) : Prop :=
  ∀ p ∈ domain, ∃ w ∈ records, w.pose = p

instance (domain : List (Fin poseCount)) (records : List Neighbor) :
    Decidable (NeighborCoverCheck domain records) := by
  unfold NeighborCoverCheck
  letI : DecidablePred (fun p => ∃ w ∈ records, w.pose = p) :=
    fun p => List.decidableBEx _ records
  exact List.decidableBAll _ domain

theorem neighbor_cover_sound (lo hi : ℚ) (domain : List (Fin poseCount))
    (records : List Neighbor) (covered : NeighborCoverCheck domain records)
    (checked : ∀ w ∈ records, w.Check lo hi) (q : OpenSquare) (ha : 1 < q.side)
    (h : OrientedPoseCovered (domain.map poses) q)
    (x : ℝ) (hx0 : (lo : ℝ) ≤ x) (hx1 : x ≤ (hi : ℝ)) : VerticalSection q x := by
  obtain ⟨p, hp, hh⟩ := h
  obtain ⟨i, hi', rfl⟩ := List.mem_map.mp hp
  obtain ⟨w, hw, he⟩ := covered i hi'
  exact w.sound lo hi (checked w hw) q ha (by simpa only [he] using hh) x hx0 hx1

inductive Branch where
  | keep (piece : Fin poseCount)
  | close (left right : Fin rowCount)
  deriving DecidableEq

def Branch.pieces : Branch → List (Fin poseCount)
  | .keep p => [p]
  | .close _ _ => []

def outsideRow (bound : ℚ) (high : Bool) : Row :=
  if high then lower bound true else upper bound true

def insideRow (bound : ℚ) (high : Bool) : Row :=
  if high then upper bound false else lower bound false

def Branch.Check (branch : Branch) (source : Fin poseCount) (bound : ℚ) (high : Bool) : Prop :=
  match branch with
  | .keep piece => poseAngle source = poseAngle piece ∧
      ∀ r ∈ poseRows piece, r ∈ poseRows source ∨ rows r = outsideRow bound high
  | .close left right => left ∈ poseRows source ∧ right ∈ poseRows source ∧
      RowSupport.Check (rows left) (rows right) (insideRow bound high)

noncomputable instance (branch : Branch) (source : Fin poseCount) (bound : ℚ) (high : Bool) :
    Decidable (branch.Check source bound high) := by
  cases branch with
  | keep piece =>
      unfold Branch.Check
      letI : Decidable (∀ r ∈ poseRows piece,
          r ∈ poseRows source ∨ rows r = outsideRow bound high) :=
        List.decidableBAll _ (poseRows piece)
      infer_instance
  | close left right => unfold Branch.Check; infer_instance

theorem Branch.sound (branch : Branch) (source : Fin poseCount) (bound : ℚ) (high : Bool)
    (checked : branch.Check source bound high) (q : OpenSquare)
    (hs : (poses source).OrientedRealizes q)
    (hout : (outsideRow bound high).Holds ![centerX q, centerY q]) :
    OrientedPoseCovered (branch.pieces.map poses) q := by
  cases branch with
  | keep piece =>
      refine ⟨poses piece, by simp [Branch.pieces], ?_⟩
      apply dictionary.transfer checked.1 positive_denominators q hs
      intro r hr
      rcases checked.2 r hr with h | h
      · exact pose_row_holds hs r h
      · change (rows r).Holds ![centerX q, centerY q]
        rw [h]
        exact hout
  | close left right =>
      obtain ⟨hl, hr, hc⟩ := checked
      have hin := RowSupport.sound hc _ (pose_row_holds hs left hl) (pose_row_holds hs right hr)
      exfalso
      cases high with
      | false =>
          have ho := (holds_upper bound true _).mp hout
          have hi := (holds_lower bound false _).mp hin
          exact (not_lt_of_ge hi) ho
      | true =>
          have ho := (holds_lower bound true _).mp hout
          have hi := (holds_upper bound false _).mp hin
          exact (not_lt_of_ge hi) ho

structure Plan where
  source : Fin poseCount
  low : Branch
  high : Branch
  deriving DecidableEq

def Plan.pieces (w : Plan) : List (Fin poseCount) := w.low.pieces ++ w.high.pieces

def Plan.Check (w : Plan) (lo hi : ℚ) : Prop :=
  w.low.Check w.source (lo - (poseRadius w.source).radius) false ∧
  w.high.Check w.source (hi + (poseRadius w.source).radius) true

noncomputable instance (w : Plan) (lo hi : ℚ) : Decidable (w.Check lo hi) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Plan.sound (w : Plan) (lo hi : ℚ) (ordered : lo ≤ hi)
    (checked : w.Check lo hi) (q : Fin 4 → OpenSquare)
    (ha : ∀ i, 1 < (q i).side) (hb : ∀ i, InsideContainer (q i))
    (hd : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (hs : (poses w.source).OrientedRealizes (q 0))
    (neighbors : ∀ x, (lo : ℝ) ≤ x → x ≤ (hi : ℝ) →
      ∀ i : Fin 3, VerticalSection (q i.succ) x) :
    OrientedPoseCovered (w.pieces.map poses) (q 0) := by
  have excluded := window_excludes lo hi (by exact_mod_cast ordered) q (poses w.source)
    (poseRadius w.source) (pose_radius_checked w.source) ha hb hd hs neighbors
  have pick : centerX (q 0) < ((lo - (poseRadius w.source).radius : ℚ) : ℝ) ∨
      ((hi + (poseRadius w.source).radius : ℚ) : ℝ) < centerX (q 0) := by
    push_cast
    by_contra h
    push_neg at h
    exact excluded h
  rcases pick with h | h
  · have hout := (holds_upper (lo - (poseRadius w.source).radius) true
      ![centerX (q 0), centerY (q 0)]).mpr h
    obtain ⟨p, hp, hh⟩ := w.low.sound w.source _ false checked.1 (q 0) hs hout
    exact ⟨p, by simpa only [Plan.pieces, List.map_append] using List.mem_append_left _ hp, hh⟩
  · have hout := (holds_lower (hi + (poseRadius w.source).radius) true
      ![centerX (q 0), centerY (q 0)]).mpr h
    obtain ⟨p, hp, hh⟩ := w.high.sound w.source _ true checked.2 (q 0) hs hout
    exact ⟨p, by simpa only [Plan.pieces, List.map_append] using List.mem_append_right _ hp, hh⟩

def PlansCoverCheck (sources targets : List (Fin poseCount)) (plans : List Plan) : Prop :=
  ∀ s ∈ sources, ∃ w ∈ plans, w.source = s ∧ ∀ p ∈ w.pieces, p ∈ targets

instance (sources targets : List (Fin poseCount)) (plans : List Plan) :
    Decidable (PlansCoverCheck sources targets plans) := by
  unfold PlansCoverCheck
  letI : DecidablePred (fun s => ∃ w ∈ plans,
      w.source = s ∧ ∀ p ∈ w.pieces, p ∈ targets) := fun s => by
    letI : DecidablePred (fun w : Plan =>
        w.source = s ∧ ∀ p ∈ w.pieces, p ∈ targets) := fun w => by
      letI : Decidable (∀ p ∈ w.pieces, p ∈ targets) :=
        List.decidableBAll _ w.pieces
      infer_instance
    exact List.decidableBEx _ plans
  exact List.decidableBAll _ sources

theorem plans_cover_sound (lo hi : ℚ) (ordered : lo ≤ hi)
    (sources targets : List (Fin poseCount)) (plans : List Plan)
    (covered : PlansCoverCheck sources targets plans) (checked : ∀ w ∈ plans, w.Check lo hi)
    (q : Fin 4 → OpenSquare) (ha : ∀ i, 1 < (q i).side)
    (hb : ∀ i, InsideContainer (q i))
    (hd : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (hs : OrientedPoseCovered (sources.map poses) (q 0))
    (neighbors : ∀ x, (lo : ℝ) ≤ x → x ≤ (hi : ℝ) →
      ∀ i : Fin 3, VerticalSection (q i.succ) x) :
    OrientedPoseCovered (targets.map poses) (q 0) := by
  obtain ⟨p, hp, hs⟩ := hs
  obtain ⟨s, hm, rfl⟩ := List.mem_map.mp hp
  obtain ⟨w, hw, he, hpieces⟩ := covered s hm
  obtain ⟨p, hp, hh⟩ := w.sound lo hi ordered (checked w hw) q ha hb hd
    (by simpa only [he] using hs) neighbors
  obtain ⟨i, hi', rfl⟩ := List.mem_map.mp hp
  exact ⟨poses i, List.mem_map.mpr ⟨i, hpieces i hi', rfl⟩, hh⟩

#print axioms plans_cover_sound
end N12Compact.C898Chord
