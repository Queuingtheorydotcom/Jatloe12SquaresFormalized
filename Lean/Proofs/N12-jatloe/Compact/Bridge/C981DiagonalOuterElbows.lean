import Compact.Bridge.C981DoubleWallElbows
import Compact.Geometry.DiagonalOuterElbow

/-! Original representative rows 35 and 60. The northeast elbow owns
the outer top auxiliary instead of the inward right auxiliary. Its
diagonal wall, genuine foreign paired corner, and top owner force the
center, contradicting the opposite original elbow. Replay pending. -/
namespace N12Compact.C981DiagonalOuterElbows
open S12 S12Pilot S12Completion.C981
set_option Elab.async false

def transform : Transform := ⟨true,false,true⟩
def roles : Fin 4 → Fin 12 := ![5,9,2,10]
def insidePoints : Fin 4 → List (ℚ × ℚ)
  | 0 => [(2,113/50),(113/50,3),(47/20,47/20)]
  | 1 => [(1543/500,2),(3,12/5),(12/5,3)]
  | 2 => [(3,3)]
  | _ => [(87/50,3)]
def outsidePoints : List (ℚ × ℚ) := [(33/20,47/20)]

def Check (v : List (Finset Nat)) : Prop :=
  (∀ j, ∀ P∈insidePoints j, transform.applyRat P∈
    queryInsidePoints (ownerMasks (roles j)) 2 (v[(roles j).val]!)) ∧
  (∀ P∈outsidePoints, transform.applyRat P∈
    queryOutsidePoints (ownerMasks 5) 2 (v[5]!)) ∧
  C981DoubleWallElbows.PlacementCheck v 2

instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem excludes (v : List (Finset Nat)) (checked : Check v) : ExcludesVector v := by
  intro p hf hv
  let q : Fin 4 → OpenSquare := fun j => transform.pull (owners p (roles j))
  have aux (j : Fin 4) : AuxExact (owners p (roles j)) 2 (v[(roles j).val]!) := by
    have he := ownership_entry_at p v hv (roles j)
    simpa only [owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks (roles j)))
  have inside (j : Fin 4) (P : ℚ × ℚ) (member : P∈insidePoints j) :
      (q j).Inside P.1 P.2 := by
    apply (rat_inside_transform transform (owners p (roles j)) P).mpr
    exact query_inside_sound _ 2 _ _ (owners_side_gt p (roles j))
      (owners_side_le p (roles j)) (owners_contained p (roles j))
      (owners_markers p hf (roles j)) (aux j) _ (checked.1 j P member)
  have absent (P : ℚ × ℚ) (member : P∈outsidePoints) :
      ¬(q 0).Inside P.1 P.2 := by
    intro point
    have owned := aux 0
    simp only [roles,Matrix.cons_val_zero] at owned
    exact query_outside_sound _ 2 _ _ (owners_markers p hf 5) owned _
      (checked.2.1 P member) ((rat_inside_transform transform _ P).mp point)
  have side (j : Fin 4) : (q j).side=p.commonSide := by
    dsimp [q]
    rw [pull_same_side]
    exact p.congruent _
  have injective : Function.Injective roles := by decide +kernel
  have apart (j k : Fin 4) (different : j≠k) :
      ∀ x y, ¬((q j).Inside x y ∧ (q k).Inside x y) := by
    intro x y h
    exact owners_disjoint p hf (roles j) (roles k)
      (fun equal => different (injective equal)) _ _
      ⟨(inside_pull _ _ _ _).mp h.1,(inside_pull _ _ _ _).mp h.2⟩
  have point := DiagonalOuterElbow.point (q 0) (q 1) (q 3)
    (by rw [side 0]; exact p.side_gt_one) ((side 0).trans (side 1).symm)
    (by rw [side 1]; exact p.side_le)
    (by simpa using inside 0 (2,113/50) (by norm_num [insidePoints]))
    (by simpa using inside 0 (113/50,3) (by norm_num [insidePoints]))
    (by simpa using inside 0 (47/20,47/20) (by norm_num [insidePoints]))
    (by simpa using absent (33/20,47/20) (by norm_num [outsidePoints]))
    (by simpa using inside 1 (1543/500,2) (by norm_num [insidePoints]))
    (by simpa using inside 1 (3,12/5) (by norm_num [insidePoints]))
    (by simpa using inside 1 (12/5,3) (by norm_num [insidePoints]))
    (fun h => apart 1 2 (by decide) 3 3
      ⟨h,by simpa using inside 2 (3,3) (by norm_num [insidePoints])⟩)
    (by simpa using inside 3 (87/50,3) (by norm_num [insidePoints]))
    (apart 0 1 (by decide)) (apart 0 3 (by decide))
  have original : (owners p 5).Inside 2 2 := by
    have source := (rat_inside_transform transform (owners p (roles 0))
      ((2,2) : ℚ × ℚ)).mp point
    norm_num [roles,transform,Transform.applyRat] at source
    exact source
  have other : (owners p 7).Inside 2 2 := by
    simpa [C981DoubleWallElbows.placements] using
      C981DoubleWallElbows.center v 2 checked.2.2 p hf hv
  exact owners_disjoint p hf 5 7 (by decide) 2 2 ⟨original,other⟩

theorem representative35_checked : Check (representativeVectors[35]!) := by decide +kernel
theorem representative60_checked : Check (representativeVectors[60]!) := by decide +kernel

theorem representative35_excluded : ExcludesVector (representativeVectors[35]!) :=
  excludes _ representative35_checked
theorem representative60_excluded : ExcludesVector (representativeVectors[60]!) :=
  excludes _ representative60_checked

#print axioms representative35_excluded
#print axioms representative60_excluded
end N12Compact.C981DiagonalOuterElbows
