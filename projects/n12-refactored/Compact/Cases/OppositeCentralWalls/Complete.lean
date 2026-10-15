import Compact.Cases.OppositeCentralWalls.Ownership
import Compact.Geometry.CentralWallCenter

/-! Two reflected applications of one continuous three-square theorem
force opposite central squares to overlap at (2,2). All eight families
share this argument, without any orientation or vector enumeration. -/
namespace N12Compact.OppositeCentralWalls
open S12 S12Pilot
set_option Elab.async false

def transform : Fin 2 → Transform := ![⟨false,false,true⟩,⟨false,true,false⟩]
def roles : Fin 2 → Fin 3 → Fin 6 := ![![0,4,3],![1,2,5]]
def insidePoints : Fin 3 → List (ℚ × ℚ)
  | 0 => [(2,113/50),(113/50,2),(47/20,47/20)]
  | 1 => [(1543/500,2),(3,12/5)]
  | _ => [(2,1543/500),(12/5,3)]
def outsidePoints : Fin 3 → List (ℚ × ℚ)
  | 0 => [(47/20,33/20),(33/20,47/20)]
  | 1 => [(3,87/50)]
  | _ => [(87/50,3)]

private theorem inputs :
    (∀ i j, ∀ P ∈ insidePoints j, (transform i).applyRat P ∈
      queryInsidePoints (masks (roles i j)) 2 (owned (roles i j))) ∧
    (∀ i j, ∀ P ∈ outsidePoints j, (transform i).applyRat P ∈
      queryOutsidePoints (masks (roles i j)) 2 (owned (roles i j))) := by
  decide +kernel

theorem center (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) (i : Fin 2) :
    (owner p (roles i 0)).Inside 2 2 := by
  let q : Fin 3 → OpenSquare := fun j => (transform i).pull (owner p (roles i j))
  have qi (j : Fin 3) (P : ℚ × ℚ) (hp : P ∈ insidePoints j) :
      (q j).Inside P.1 P.2 := by
    apply (rat_inside_transform (transform i) (owner p (roles i j)) P).mpr
    exact inside v p hf (roles i j) _ (inputs.1 i j P hp)
  have qo (j : Fin 3) (P : ℚ × ℚ) (hp : P ∈ outsidePoints j) :
      ¬ (q j).Inside P.1 P.2 := by
    intro h
    exact outside v p hf (roles i j) _ (inputs.2 i j P hp)
      ((rat_inside_transform _ _ _).mp h)
  have side (j : Fin 3) : (q j).side=p.commonSide := by
    dsimp [q]
    rw [pull_same_side]
    exact p.congruent _
  have box (j : Fin 3) : InsideContainer (q j) :=
    container_transform _ _ (p.contained _)
  have injective : Function.Injective (roles i) := by fin_cases i <;> decide +kernel
  have qa (j k : Fin 3) (hne : j ≠ k) :
      ∀ x y, ¬ ((q j).Inside x y ∧ (q k).Inside x y) := by
    intro x y h
    exact apart v p hf (roles i j) (roles i k)
      (fun eq => hne (injective eq)) _ _
      ⟨(inside_pull _ _ _ _).mp h.1,(inside_pull _ _ _ _).mp h.2⟩
  have point := CentralWallCenter.point (q 0) (q 1) (q 2)
    (by rw [side 0]; exact p.side_gt_one) ((side 0).trans (side 1).symm)
    ((side 0).trans (side 2).symm) (box 1) (box 2)
    (by simpa using qi 0 (2,113/50) (by norm_num [insidePoints]))
    (by simpa using qi 0 (113/50,2) (by norm_num [insidePoints]))
    (by simpa using qi 0 (47/20,47/20) (by norm_num [insidePoints]))
    (by simpa using qo 0 (47/20,33/20) (by norm_num [outsidePoints]))
    (by simpa using qo 0 (33/20,47/20) (by norm_num [outsidePoints]))
    (by simpa using qi 1 (1543/500,2) (by norm_num [insidePoints]))
    (by simpa using qi 1 (3,12/5) (by norm_num [insidePoints]))
    (by simpa using qo 1 (3,87/50) (by norm_num [outsidePoints]))
    (by simpa using qi 2 (2,1543/500) (by norm_num [insidePoints]))
    (by simpa using qi 2 (12/5,3) (by norm_num [insidePoints]))
    (by simpa using qo 2 (87/50,3) (by norm_num [outsidePoints]))
    (qa 0 1 (by decide)) (qa 0 2 (by decide))
  have original := (rat_inside_transform (transform i) (owner p (roles i 0))
    ((2,2) : ℚ × ℚ)).mp point
  fin_cases i <;> norm_num [transform,Transform.applyRat] at original ⊢ <;> exact original

theorem impossible (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) : False := by
  have se : (owner p 0).Inside 2 2 := by simpa [roles] using center v p hf 0
  have nw : (owner p 1).Inside 2 2 := by simpa [roles] using center v p hf 1
  exact apart v p hf 0 1 (by decide) 2 2 ⟨se,nw⟩

#print axioms impossible
end N12Compact.OppositeCentralWalls
