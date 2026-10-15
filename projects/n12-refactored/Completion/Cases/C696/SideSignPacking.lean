import Completion.Contracts
import Completion.Cases.C696.SideSign
import S12.LocalQuery
import Mathlib.Data.List.OfFn

/-!
Instantiate the returned C696 side-sign lemmas in the original normalized
packing. The exact auxiliary assignment remains an explicit premise; this
module does not assert its geometric necessity or exclude either residual
corner context. All contained and excluded points are derived from the original
marker and combined F/G ownership interfaces.
-/

namespace S12Completion.C696.SideSignPacking
open S12 S12Pilot

/-- The original twelve marker groups, in the saved C696 owner order. -/
def ownerMasks : Fin 12 → Nat :=
  ![1, 2, 12, 16, 32, 192, 256, 1024, 4096, 8192, 16384, 32768]

def family : Finset Nat :=
  {1, 2, 12, 16, 32, 192, 256, 1024, 4096, 8192, 16384, 32768}

theorem ownerMasks_mem : ∀ i, ownerMasks i ∈ family := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_family :
    ∀ r ∈ retainedRows, r.originalId = 696 → r.groups = family := by
  decide

/-- The returned assignment, using original F indices followed by G indices
offset by ten. Its necessity is deliberately not a theorem of this module. -/
def auxiliaryVector : Fin 12 → Finset Nat :=
  ![{2, 12}, {0, 10}, ∅, {7, 17}, {9, 19}, ∅,
    {4, 13}, {5, 16}, {1, 11}, {6, 15}, {8, 18}, {3, 14}]

noncomputable def owners (p : NormalizedPacking) (i : Fin 12) : OpenSquare :=
  p.square (ownerIndex p (ownerMasks i))

noncomputable def ownershipVector (p : NormalizedPacking) : List (Finset Nat) :=
  List.ofFn (fun i : Fin 12 => natCombinedOwners p (ownerIndex p (ownerMasks i)))

/-- Equality of exact strict auxiliary ownership, with no geometric premise. -/
def ExactAssignment (p : NormalizedPacking) : Prop :=
  ∀ i, natCombinedOwners p (ownerIndex p (ownerMasks i)) = auxiliaryVector i

theorem exactAssignment_of_vector (p : NormalizedPacking)
    (hv : ownershipVector p = List.ofFn auxiliaryVector) : ExactAssignment p :=
  congrFun (List.ofFn_injective hv)

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) :
    1 < (owners p i).side := by
  change 1 < (p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_le (p : NormalizedPacking) (i : Fin 12) :
    (owners p i).side ≤ 1001 / 1000 := by
  change (p.square _).side ≤ 1001 / 1000
  rw [p.congruent]
  exact p.side_le

private theorem contained (p : NormalizedPacking) (i : Fin 12) :
    InsideContainer (owners p i) := p.contained _

private theorem exactMarkers (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    ExactMarkers (owners p i) (maskSupport (ownerMasks i)) := by
  have he := ownerIndex_spec p (ownerMasks i) (by rw [hf]; exact ownerMasks_mem i)
  simpa only [owners, he] using coded_exact p (ownerIndex p (ownerMasks i))

private theorem exactAuxiliary (p : NormalizedPacking) (hv : ExactAssignment p)
    (i : Fin 12) : AuxExact (owners p i) 2 (auxiliaryVector i) := by
  simpa only [owners, hv i] using nat_combined_exact p (ownerIndex p (ownerMasks i))

private theorem inside_points (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (hv : ExactAssignment p) (i : Fin 12) :
    ∀ P ∈ queryInsidePoints (ownerMasks i) 2 (auxiliaryVector i),
      (owners p i).Inside P.1 P.2 :=
  query_inside_sound _ _ _ _ (side_gt p i) (side_le p i) (contained p i)
    (exactMarkers p hf i) (exactAuxiliary p hv i)

private theorem outside_points (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (hv : ExactAssignment p) (i : Fin 12) :
    ∀ P ∈ queryOutsidePoints (ownerMasks i) 2 (auxiliaryVector i),
      ¬ (owners p i).Inside P.1 P.2 :=
  query_outside_sound _ _ _ _ (exactMarkers p hf i) (exactAuxiliary p hv i)

private theorem lower_walls (p : NormalizedPacking) (i : Fin 12) :
    ∀ x y, (owners p i).Inside x y → 0 ≤ x ∧ 0 ≤ y := by
  intro x y hi
  have h := contained p i x y hi
  exact ⟨h.1, h.2.2.1⟩

private theorem upper_walls (p : NormalizedPacking) (i : Fin 12) :
    ∀ x y, (owners p i).Inside x y → x ≤ 4 ∧ y ≤ 4 := by
  intro x y hi
  have h := contained p i x y hi
  exact ⟨h.2.1, h.2.2.2⟩

/-- Actual C696 ownership implies the four strict signs. In the original
closed-cut convention these are sign 12: above, right, below, left. -/
theorem center_signs (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (hv : ExactAssignment p) :
    2 < centerY (owners p 8) ∧ 2 < centerX (owners p 9) ∧
      centerY (owners p 10) < 2 ∧ centerX (owners p 11) < 2 := by
  have hin := inside_points p hf hv
  have hout := outside_points p hf hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply c696_left_side_center_gt_two (owners p 8) (side_gt p 8) (lower_walls p 8)
    · simpa using hin 8 ((457 / 500, 2) : ℚ × ℚ) (by decide)
    · simpa using hin 8 ((1, 12 / 5) : ℚ × ℚ) (by decide)
    · simpa using hout 8 ((1, 87 / 50) : ℚ × ℚ) (by decide)
    · simpa using hout 8 ((87 / 50, 2) : ℚ × ℚ) (by decide)
  · apply c696_bottom_side_center_gt_two (owners p 9) (side_gt p 9) (lower_walls p 9)
    · simpa using hin 9 ((2, 457 / 500) : ℚ × ℚ) (by decide)
    · simpa using hin 9 ((12 / 5, 1) : ℚ × ℚ) (by decide)
    · simpa using hout 9 ((87 / 50, 1) : ℚ × ℚ) (by decide)
    · simpa using hout 9 ((2, 87 / 50) : ℚ × ℚ) (by decide)
  · apply c696_right_side_center_lt_two (owners p 10) (side_gt p 10) (upper_walls p 10)
    · simpa using hin 10 ((1543 / 500, 2) : ℚ × ℚ) (by decide)
    · simpa using hin 10 ((3, 8 / 5) : ℚ × ℚ) (by decide)
    · simpa using hout 10 ((3, 113 / 50) : ℚ × ℚ) (by decide)
    · simpa using hout 10 ((113 / 50, 2) : ℚ × ℚ) (by decide)
  · apply c696_top_side_center_lt_two (owners p 11) (side_gt p 11) (upper_walls p 11)
    · simpa using hin 11 ((2, 1543 / 500) : ℚ × ℚ) (by decide)
    · simpa using hin 11 ((8 / 5, 3) : ℚ × ℚ) (by decide)
    · simpa using hout 11 ((113 / 50, 3) : ℚ × ℚ) (by decide)
    · simpa using hout 11 ((2, 113 / 50) : ℚ × ℚ) (by decide)

theorem center_signs_of_vector (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family)
    (hv : ownershipVector p = List.ofFn auxiliaryVector) :
    2 < centerY (owners p 8) ∧ 2 < centerX (owners p 9) ∧
      centerY (owners p 10) < 2 ∧ centerX (owners p 11) < 2 :=
  center_signs p hf (exactAssignment_of_vector p hv)

/-- The same conclusion for every original retained row carrying ID 696. -/
theorem center_signs_of_row (r : S12.CoverRow) (hr : r ∈ retainedRows)
    (hid : r.originalId = 696) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = r.groups) (hv : ExactAssignment p) :
    2 < centerY (owners p 8) ∧ 2 < centerX (owners p 9) ∧
      centerY (owners p 10) < 2 ∧ centerX (owners p 11) < 2 :=
  center_signs p (hf.trans (row_family r hr hid)) hv

#print axioms center_signs
#print axioms center_signs_of_row
end S12Completion.C696.SideSignPacking
