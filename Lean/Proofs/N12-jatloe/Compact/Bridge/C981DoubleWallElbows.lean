import Compact.Bridge.C981WallElbows
import Compact.Geometry.DoubleAuxWallCenter

/-! Whole original-vector exclusions using opposite actual elbows.
A double auxiliary wall retains its additional strict point and its
exact outer missing point. Each orientation is checked against the
original marker/auxiliary queries, never an archived assumed hull. -/
namespace N12Compact.C981DoubleWallElbows
open S12 S12Pilot S12Completion.C981
set_option Elab.async false

structure Placement where
  transform : Transform
  roles : Fin 3 → Fin 12
  double : Bool

def placements : Fin 4 → Placement := ![
  ⟨⟨false,false,true⟩, ![5,10,9], false⟩,
  ⟨⟨false,false,true⟩, ![5,10,9], true⟩,
  ⟨⟨false,true,false⟩, ![7,8,11], false⟩,
  ⟨⟨true,true,false⟩, ![7,11,8], true⟩]

def insidePoints (double : Bool) : Fin 3 → List (ℚ × ℚ)
  | 0 => [(2,113/50),(113/50,2),(47/20,47/20)]
  | 1 => if double then [(1543/500,2),(3,12/5),(3,87/50)]
      else [(1543/500,2),(3,12/5)]
  | _ => [(2,1543/500),(12/5,3)]
def outsidePoints (double : Bool) : Fin 3 → List (ℚ × ℚ)
  | 0 => [(47/20,33/20),(33/20,47/20)]
  | 1 => if double then [(3,8/5)] else [(3,87/50)]
  | _ => [(87/50,3)]

def PlacementCheck (v : List (Finset Nat)) (i : Fin 4) : Prop :=
  (∀ j, ∀ P ∈ insidePoints (placements i).double j, (placements i).transform.applyRat P ∈
    queryInsidePoints (ownerMasks ((placements i).roles j)) 2 (v[((placements i).roles j).val]!)) ∧
  (∀ j, ∀ P ∈ outsidePoints (placements i).double j, (placements i).transform.applyRat P ∈
    queryOutsidePoints (ownerMasks ((placements i).roles j)) 2 (v[((placements i).roles j).val]!))

instance (v : List (Finset Nat)) (i : Fin 4) : Decidable (PlacementCheck v i) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem center (v : List (Finset Nat)) (i : Fin 4) (checked : PlacementCheck v i)
    (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (hv : ownershipVector p = v) :
    (owners p ((placements i).roles 0)).Inside 2 2 := by
  let g := placements i
  let q : Fin 3 → OpenSquare := fun j => g.transform.pull (owners p (g.roles j))
  have aux (j : Fin 3) : AuxExact (owners p (g.roles j)) 2 (v[(g.roles j).val]!) := by
    have he := ownership_entry_at p v hv (g.roles j)
    simpa only [owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks (g.roles j)))
  have inside (j : Fin 3) (P : ℚ × ℚ) (hp : P ∈ insidePoints g.double j) :
      (q j).Inside P.1 P.2 := by
    apply (rat_inside_transform g.transform (owners p (g.roles j)) P).mpr
    exact query_inside_sound _ 2 _ _ (owners_side_gt p (g.roles j))
      (owners_side_le p (g.roles j)) (owners_contained p (g.roles j))
      (owners_markers p hf (g.roles j)) (aux j) _ (checked.1 j P hp)
  have outside (j : Fin 3) (P : ℚ × ℚ) (hp : P ∈ outsidePoints g.double j) :
      ¬ (q j).Inside P.1 P.2 := by
    intro h
    exact query_outside_sound _ 2 _ _ (owners_markers p hf (g.roles j))
      (aux j) _ (checked.2 j P hp) ((rat_inside_transform _ _ _).mp h)
  have side (j : Fin 3) : (q j).side=p.commonSide := by
    dsimp [q]
    rw [pull_same_side]
    exact p.congruent _
  have box (j : Fin 3) : InsideContainer (q j) :=
    container_transform _ _ (owners_contained p (g.roles j))
  have injective : Function.Injective g.roles := by
    dsimp [g]
    fin_cases i <;> decide +kernel
  have apart (j k : Fin 3) (hne : j ≠ k) :
      ∀ x y, ¬ ((q j).Inside x y ∧ (q k).Inside x y) := by
    intro x y h
    exact owners_disjoint p hf (g.roles j) (g.roles k)
      (fun eq => hne (injective eq)) _ _
      ⟨(inside_pull _ _ _ _).mp h.1,(inside_pull _ _ _ _).mp h.2⟩
  have ha : 1 < (q 0).side := by rw [side 0]; exact p.side_gt_one
  have hp := inside 0 (2,113/50) (by norm_num [insidePoints])
  have hq := inside 0 (113/50,2) (by norm_num [insidePoints])
  have hm := inside 0 (47/20,47/20) (by norm_num [insidePoints])
  have hg := outside 0 (47/20,33/20) (by norm_num [outsidePoints])
  have hb := outside 0 (33/20,47/20) (by norm_num [outsidePoints])
  have ht := inside 2 (2,1543/500) (by norm_num [insidePoints])
  have hh := inside 2 (12/5,3) (by norm_num [insidePoints])
  have hx := outside 2 (87/50,3) (by norm_num [outsidePoints])
  have point : (q 0).Inside 2 2 := by
    cases hd : g.double
    · exact CentralWallCenter.point (q 0) (q 1) (q 2) ha
        ((side 0).trans (side 1).symm) ((side 0).trans (side 2).symm) (box 1) (box 2)
        (by simpa using hp) (by simpa using hq) (by simpa using hm)
        (by simpa using hg) (by simpa using hb)
        (by simpa using inside 1 (1543/500,2) (by norm_num [insidePoints,hd]))
        (by simpa using inside 1 (3,12/5) (by norm_num [insidePoints,hd]))
        (by simpa using outside 1 (3,87/50) (by norm_num [outsidePoints,hd]))
        (by simpa using ht) (by simpa using hh) (by simpa using hx)
        (apart 0 1 (by decide)) (apart 0 2 (by decide))
    · exact DoubleAuxWallCenter.point (q 0) (q 1) (q 2) ha
        ((side 0).trans (side 1).symm) ((side 0).trans (side 2).symm) (box 1) (box 2)
        (by simpa using hp) (by simpa using hq) (by simpa using hm)
        (by simpa using hg) (by simpa using hb)
        (by simpa using inside 1 (1543/500,2) (by norm_num [insidePoints,hd]))
        (by simpa using inside 1 (3,12/5) (by norm_num [insidePoints,hd]))
        (by simpa using inside 1 (3,87/50) (by norm_num [insidePoints,hd]))
        (by simpa using outside 1 (3,8/5) (by norm_num [outsidePoints,hd]))
        (by simpa using ht) (by simpa using hh) (by simpa using hx)
        (apart 0 1 (by decide)) (apart 0 2 (by decide))
  have original := (rat_inside_transform g.transform (owners p (g.roles 0))
    ((2,2) : ℚ × ℚ)).mp point
  dsimp [g] at original ⊢
  fin_cases i <;> norm_num [placements,Transform.applyRat] at original ⊢ <;> exact original

def placementPairs : List (Fin 4 × Fin 4) := [(1,2),(1,3),(0,3)]
def Check (v : List (Finset Nat)) : Prop :=
  ∃ pair ∈ placementPairs, PlacementCheck v pair.1 ∧ PlacementCheck v pair.2
instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (∃ pair ∈ placementPairs, _))

theorem excludes (v : List (Finset Nat)) (checked : Check v) : ExcludesVector v := by
  intro p hf hv
  obtain ⟨pair,member,left,right⟩ := checked
  have different : (placements pair.1).roles 0 ≠ (placements pair.2).roles 0 := by
    simp only [placementPairs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide +kernel
  exact owners_disjoint p hf _ _ different 2 2
    ⟨center v pair.1 left p hf hv,center v pair.2 right p hf hv⟩

def coveredIds : List Nat := [1,20,21,23,51,112]
theorem covered_count : coveredIds.length = 6 := by decide +kernel
theorem covered_checked : ∀ i ∈ coveredIds, Check (representativeVectors[i]!) := by
  decide +kernel
theorem covered_excluded (i : Nat) (hi : i ∈ coveredIds) :
    ExcludesVector (representativeVectors[i]!) := excludes _ (covered_checked i hi)

#print axioms covered_excluded
end N12Compact.C981DoubleWallElbows
