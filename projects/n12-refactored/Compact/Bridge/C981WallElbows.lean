import Completion.Cases.C981.VectorData
import Compact.Geometry.CentralWallCenter

/-! Original C981 exclusions from both opposite elbow squares and their
actual four wall neighbors. Every geometric premise is bound to the
original query ownership; the continuous theorem covers all angles. -/
namespace N12Compact.C981WallElbows
open S12 S12Pilot S12Completion.C981
set_option Elab.async false

def transform : Fin 2 → Transform := ![⟨false,false,true⟩,⟨false,true,false⟩]
def roles : Fin 2 → Fin 3 → Fin 12 := ![![5,10,9],![7,8,11]]
def insidePoints : Fin 3 → List (ℚ × ℚ)
  | 0 => [(2,113/50),(113/50,2),(47/20,47/20)]
  | 1 => [(1543/500,2),(3,12/5)]
  | _ => [(2,1543/500),(12/5,3)]
def outsidePoints : Fin 3 → List (ℚ × ℚ)
  | 0 => [(47/20,33/20),(33/20,47/20)]
  | 1 => [(3,87/50)]
  | _ => [(87/50,3)]

def Check (v : List (Finset Nat)) : Prop :=
  (∀ i j, ∀ P ∈ insidePoints j, (transform i).applyRat P ∈
    queryInsidePoints (ownerMasks (roles i j)) 2 (v[(roles i j).val]!)) ∧
  (∀ i j, ∀ P ∈ outsidePoints j, (transform i).applyRat P ∈
    queryOutsidePoints (ownerMasks (roles i j)) 2 (v[(roles i j).val]!))

instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem center (v : List (Finset Nat)) (checked : Check v)
    (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (hv : ownershipVector p = v) (i : Fin 2) :
    (owners p (roles i 0)).Inside 2 2 := by
  let q : Fin 3 → OpenSquare := fun j => (transform i).pull (owners p (roles i j))
  have aux (j : Fin 3) : AuxExact (owners p (roles i j)) 2 (v[(roles i j).val]!) := by
    have he := ownership_entry_at p v hv (roles i j)
    simpa only [owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks (roles i j)))
  have inside (j : Fin 3) (P : ℚ × ℚ) (hp : P ∈ insidePoints j) :
      (q j).Inside P.1 P.2 := by
    apply (rat_inside_transform (transform i) (owners p (roles i j)) P).mpr
    exact query_inside_sound _ 2 _ _ (owners_side_gt p (roles i j))
      (owners_side_le p (roles i j)) (owners_contained p (roles i j))
      (owners_markers p hf (roles i j)) (aux j) _ (checked.1 i j P hp)
  have outside (j : Fin 3) (P : ℚ × ℚ) (hp : P ∈ outsidePoints j) :
      ¬ (q j).Inside P.1 P.2 := by
    intro h
    exact query_outside_sound _ 2 _ _ (owners_markers p hf (roles i j))
      (aux j) _ (checked.2 i j P hp) ((rat_inside_transform _ _ _).mp h)
  have side (j : Fin 3) : (q j).side=p.commonSide := by
    dsimp [q]
    rw [pull_same_side]
    exact p.congruent _
  have box (j : Fin 3) : InsideContainer (q j) :=
    container_transform _ _ (owners_contained p (roles i j))
  have injective : Function.Injective (roles i) := by fin_cases i <;> decide +kernel
  have apart (j k : Fin 3) (hne : j ≠ k) :
      ∀ x y, ¬ ((q j).Inside x y ∧ (q k).Inside x y) := by
    intro x y h
    exact owners_disjoint p hf (roles i j) (roles i k)
      (fun eq => hne (injective eq)) _ _
      ⟨(inside_pull _ _ _ _).mp h.1,(inside_pull _ _ _ _).mp h.2⟩
  have point := CentralWallCenter.point (q 0) (q 1) (q 2)
    (by rw [side 0]; exact p.side_gt_one) ((side 0).trans (side 1).symm)
    ((side 0).trans (side 2).symm) (box 1) (box 2)
    (by simpa using inside 0 (2,113/50) (by norm_num [insidePoints]))
    (by simpa using inside 0 (113/50,2) (by norm_num [insidePoints]))
    (by simpa using inside 0 (47/20,47/20) (by norm_num [insidePoints]))
    (by simpa using outside 0 (47/20,33/20) (by norm_num [outsidePoints]))
    (by simpa using outside 0 (33/20,47/20) (by norm_num [outsidePoints]))
    (by simpa using inside 1 (1543/500,2) (by norm_num [insidePoints]))
    (by simpa using inside 1 (3,12/5) (by norm_num [insidePoints]))
    (by simpa using outside 1 (3,87/50) (by norm_num [outsidePoints]))
    (by simpa using inside 2 (2,1543/500) (by norm_num [insidePoints]))
    (by simpa using inside 2 (12/5,3) (by norm_num [insidePoints]))
    (by simpa using outside 2 (87/50,3) (by norm_num [outsidePoints]))
    (apart 0 1 (by decide)) (apart 0 2 (by decide))
  have original := (rat_inside_transform (transform i) (owners p (roles i 0))
    ((2,2) : ℚ × ℚ)).mp point
  fin_cases i <;> norm_num [transform,Transform.applyRat] at original ⊢ <;> exact original

theorem excludes (v : List (Finset Nat)) (checked : Check v) : ExcludesVector v := by
  intro p hf hv
  have se : (owners p 5).Inside 2 2 := by simpa [roles] using center v checked p hf hv 0
  have nw : (owners p 7).Inside 2 2 := by simpa [roles] using center v checked p hf hv 1
  exact owners_disjoint p hf 5 7 (by decide) 2 2 ⟨se,nw⟩

def coveredIds : List Nat := [0,7,8,19,22,44,50,52,53,66,110,111,113,114,115,116]

theorem covered_count : coveredIds.length = 16 := by decide +kernel

theorem covered_checked : ∀ i ∈ coveredIds, Check (representativeVectors[i]!) := by
  decide +kernel

theorem covered_excluded (i : Nat) (hi : i ∈ coveredIds) :
    ExcludesVector (representativeVectors[i]!) := excludes _ (covered_checked i hi)

#print axioms covered_excluded
end N12Compact.C981WallElbows
