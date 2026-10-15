import Compact.Geometry.FourSquareHighRight
import S12.Convex
import S12.CertifiedDomain

/-! Original-packing bridge for the higher-right family. The two right
endpoints are proved strictly inside through the original query semantics;
strict convexity supplies the higher point, without treating a saved closed
hull as an open interior certificate. -/
namespace N12Compact.FourSquareCaseHighRight
open S12 S12Pilot FourSquareAnchors

def insidePoints : Fin 4 → List (ℚ × ℚ)
  | 0 => [(2,113/50),(113/50,2),(47/20,47/20)]
  | 1 => [(33/20,47/20),(8/5,3),(87/50,3)]
  | 2 => [(457/500,2),(1,12/5)]
  | _ => [(3,113/50),(3,72/25)]

def outsidePoints : Fin 4 → List (ℚ × ℚ)
  | 0 => [(33/20,33/20),(47/20,33/20)]
  | 1 => [(1,1543/500),(2,1543/500)]
  | 2 => [(33/20,33/20)]
  | _ => []

structure Data where
  transform : Transform
  masks : Fin 4 → Nat
  owned : Fin 4 → Finset Nat
  leftBarrier : Nat

def Data.Check (d : Data) (family : Finset Nat) : Prop :=
  (∀ i, d.masks i ∈ family) ∧
  d.masks 0 ≠ d.masks 1 ∧ d.masks 0 ≠ d.masks 3 ∧
  d.masks 1 ≠ d.masks 2 ∧ d.masks 1 ≠ d.masks 3 ∧
  d.leftBarrier ∈ family ∧ d.masks 2 ≠ d.leftBarrier ∧
  (∀ i, ∀ P ∈ insidePoints i,
    d.transform.applyRat P ∈ queryInsidePoints (d.masks i) 2 (d.owned i)) ∧
  (∀ i, ∀ P ∈ outsidePoints i,
    d.transform.applyRat P ∈ queryOutsidePoints (d.masks i) 2 (d.owned i)) ∧
  d.transform.applyRat (19/25,187/100) ∈ seedPoints (maskSupport d.leftBarrier)

instance (d : Data) (family : Finset Nat) : Decidable (d.Check family) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem close {q : OpenSquare} {x y : ℝ} (h : q.Inside x y) :
    ClosedInside q x y := ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

theorem impossible_of_owned (d : Data) (family : Finset Nat) (hd : d.Check family)
    (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (forced : ∀ i, natCombinedOwners p (ownerIndex p (d.masks i)) = d.owned i) : False := by
  classical
  rcases hd with ⟨hmem, hab, har, hbl, hbr, hml, hdl, hi, ho, hsl⟩
  let q : Fin 4 → OpenSquare := fun i => d.transform.pull (p.square (ownerIndex p (d.masks i)))
  have hcode (i : Fin 4) : markerCode p (ownerIndex p (d.masks i)) = d.masks i :=
    ownerIndex_spec p _ (by rw [hf]; exact hmem i)
  have side (i : Fin 4) : (q i).side = p.commonSide := by
    exact (pull_same_side _ _).trans (p.congruent _)
  have box (i : Fin 4) : InsideContainer (q i) :=
    container_transform _ _ (p.contained _)
  have aux (i : Fin 4) : AuxExact (p.square (ownerIndex p (d.masks i))) 2 (d.owned i) := by
    have hh := nat_combined_exact p (ownerIndex p (d.masks i))
    simpa only [forced i] using hh
  have inside (i : Fin 4) (P : ℚ × ℚ) (hP : P ∈ insidePoints i) :
      (q i).Inside P.1 P.2 := by
    apply (rat_inside_transform _ _ _).mpr
    exact query_inside_sound _ 2 _ _
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained _)
      (by simpa only [hcode i] using coded_exact p (ownerIndex p (d.masks i)))
      (aux i) _ (hi i P hP)
  have outside (i : Fin 4) (P : ℚ × ℚ) (hP : P ∈ outsidePoints i) :
      ¬(q i).Inside P.1 P.2 := by
    intro hp
    exact query_outside_sound _ 2 _ _
      (by simpa only [hcode i] using coded_exact p (ownerIndex p (d.masks i)))
      (aux i) _ (ho i P hP) ((rat_inside_transform _ _ _).mp hp)
  have apart (i j : Fin 4) (hne : d.masks i ≠ d.masks j) :
      ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y) := by
    intro x y hp
    apply p.disjoint (ownerIndex p (d.masks i)) (ownerIndex p (d.masks j))
      (fun he => hne ((hcode i).symm.trans ((congrArg (markerCode p) he).trans (hcode j))))
      _ _ ⟨(inside_pull _ _ _ _).mp hp.1, (inside_pull _ _ _ _).mp hp.2⟩
  have barrier (i : Fin 4) (mask : Nat) (hm : mask ∈ family)
      (hne : d.masks i ≠ mask) (P : ℚ × ℚ)
      (hP : d.transform.applyRat P ∈ seedPoints (maskSupport mask)) :
      ¬(q i).Inside P.1 P.2 := by
    have hc := ownerIndex_spec p mask (by rw [hf]; exact hm)
    have hs := seed_points_sound (p.square (ownerIndex p mask))
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained _)
      _ (by simpa only [hc] using coded_exact p (ownerIndex p mask)) _ hP
    intro hp
    exact p.disjoint (ownerIndex p (d.masks i)) (ownerIndex p mask)
      (fun he => hne ((hcode i).symm.trans ((congrArg (markerCode p) he).trans hc)))
      _ _ ⟨(rat_inside_transform _ _ _).mp hp, hs⟩
  have rLow : (q 3).Inside 3 (113/50) := by
    simpa using inside 3 (3,113/50) (by norm_num [insidePoints, outsidePoints])
  have rUpper : (q 3).Inside 3 (72/25) := by
    simpa using inside 3 (3,72/25) (by norm_num [insidePoints, outsidePoints])
  have rTop : (q 3).Inside 3 (12/5) := by
    have hp := S12.inside_segment (q 3) 3 (113/50) 3 (72/25) (7/31)
      rLow rUpper (by norm_num) (by norm_num)
    norm_num at hp
    exact hp
  have rHigh : (q 3).Inside 3 (5/2) := by
    have hp := S12.inside_segment (q 3) 3 (113/50) 3 (72/25) (12/31)
      rLow rUpper (by norm_num) (by norm_num)
    norm_num at hp
    exact hp
  apply FourSquareHighRight.impossible (q 0) (q 1) (q 2) (q 3) ?_ rHigh
  refine {
    one_lt := by rw [side]; exact p.side_gt_one
    side_cap := by rw [side]; exact p.side_le
    sameA := (side 0).trans (side 1).symm
    sameL := (side 1).trans (side 2).symm
    sameR := (side 1).trans (side 3).symm
    boxB := box 1, boxL := box 2, boxR := box 3
    aP := ?_, aQ := ?_, aT := ?_, aF := ?_, aG := ?_
    bBottom := ?_, bTop := ?_, bTopRight := ?_
    bMissingLeft := ?_, bMissingRight := ?_
    lLeft := ?_, lTop := ?_, lMissingLow := ?_, lMissingRight := ?_
    rTop := close rTop
    ab := apart 0 1 hab, ar := apart 0 3 har
    bl := apart 1 2 hbl, br := apart 1 3 hbr }
  · simpa using close (inside 0 (2,113/50) (by norm_num [insidePoints, outsidePoints]))
  · simpa using close (inside 0 (113/50,2) (by norm_num [insidePoints, outsidePoints]))
  · simpa using close (inside 0 (47/20,47/20) (by norm_num [insidePoints, outsidePoints]))
  · simpa using outside 0 (33/20,33/20) (by norm_num [insidePoints, outsidePoints])
  · simpa using outside 0 (47/20,33/20) (by norm_num [insidePoints, outsidePoints])
  · simpa using close (inside 1 (33/20,47/20) (by norm_num [insidePoints, outsidePoints]))
  · simpa using close (inside 1 (8/5,3) (by norm_num [insidePoints, outsidePoints]))
  · simpa using close (inside 1 (87/50,3) (by norm_num [insidePoints, outsidePoints]))
  · simpa using outside 1 (1,1543/500) (by norm_num [insidePoints, outsidePoints])
  · simpa using outside 1 (2,1543/500) (by norm_num [insidePoints, outsidePoints])
  · simpa using close (inside 2 (457/500,2) (by norm_num [insidePoints, outsidePoints]))
  · simpa using close (inside 2 (1,12/5) (by norm_num [insidePoints, outsidePoints]))
  · simpa using barrier 2 d.leftBarrier hml hdl (19/25,187/100) hsl
  · simpa using outside 2 (33/20,33/20) (by norm_num [insidePoints, outsidePoints])

theorem impossible (d : Data) (family : Finset Nat) (hd : d.Check family)
    (forced : ∀ (p : NormalizedPacking), codedMarkerFamily p = family →
      ∀ i, natCombinedOwners p (ownerIndex p (d.masks i)) = d.owned i)
    (p : NormalizedPacking) (hf : codedMarkerFamily p = family) : False :=
  impossible_of_owned d family hd p hf (forced p hf)

#print axioms impossible
end N12Compact.FourSquareCaseHighRight
