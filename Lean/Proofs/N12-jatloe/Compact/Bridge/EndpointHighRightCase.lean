import Compact.Geometry.EndpointHighRight
import S12.CertifiedDomain
import S12.Convex

/-! Original-packing entry for the endpoint argument with a strict right
segment. Every endpoint is an actual marker, proved seed, or owned auxiliary
point; no saved hull or assumed high point enters the conclusion. -/
namespace N12Compact.EndpointHighRightCase
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

structure Data where
  transform : Transform
  masks : Fin 4 → Nat
  owned : Fin 4 → Finset Nat

def insidePoints : Fin 4 → List (ℚ × ℚ)
  | 0 => [(2,113/50),(113/50,2),(47/20,47/20)]
  | 1 => [(33/20,47/20),(87/50,2),(8/5,3)]
  | 2 => [(1,12/5)]
  | _ => [(3,113/50),(3,72/25)]

def outsidePoints : List (ℚ × ℚ) := [(33/20,33/20),(47/20,33/20)]

def Data.Check (d : Data) (family : Finset Nat) : Prop :=
  (∀ i, d.masks i ∈ family) ∧
  d.masks 0 ≠ d.masks 1 ∧ d.masks 0 ≠ d.masks 3 ∧
  d.masks 1 ≠ d.masks 2 ∧
  (∀ i, ∀ P ∈ insidePoints i, d.transform.applyRat P ∈
    queryInsidePoints (d.masks i) 2 (d.owned i)) ∧
  (∀ P ∈ outsidePoints, d.transform.applyRat P ∈
    queryOutsidePoints (d.masks 0) 2 (d.owned 0))

instance (d : Data) (family : Finset Nat) : Decidable (d.Check family) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem close {q : OpenSquare} {x y : ℝ} (hp : q.Inside x y) :
    ClosedInside q x y := ⟨hp.1.le,hp.2.1.le,hp.2.2.1.le,hp.2.2.2.le⟩

theorem impossible_actual (d : Data) (family : Finset Nat) (hd : d.Check family)
    (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (owned : ∀ i, natCombinedOwners p (ownerIndex p (d.masks i)) = d.owned i) : False := by
  obtain ⟨hmem,hab,har,hbl,hin,hout⟩ := hd
  let q : Fin 4 → OpenSquare := fun i =>
    d.transform.pull (p.square (ownerIndex p (d.masks i)))
  have code (i : Fin 4) : markerCode p (ownerIndex p (d.masks i)) = d.masks i :=
    ownerIndex_spec p _ (by rw [hf]; exact hmem i)
  have aux (i : Fin 4) :
      AuxExact (p.square (ownerIndex p (d.masks i))) 2 (d.owned i) := by
    simpa only [owned i] using nat_combined_exact p (ownerIndex p (d.masks i))
  have inside (i : Fin 4) (P : ℚ × ℚ) (hp : P ∈ insidePoints i) :
      (q i).Inside P.1 P.2 := by
    apply (rat_inside_transform _ _ _).mpr
    exact query_inside_sound _ 2 _ _
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained _)
      (by simpa only [code i] using coded_exact p (ownerIndex p (d.masks i)))
      (aux i) _ (hin i P hp)
  have outside (P : ℚ × ℚ) (hp : P ∈ outsidePoints) :
      ¬ (q 0).Inside P.1 P.2 := by
    intro hq
    exact query_outside_sound _ 2 _ _
      (by simpa only [code 0] using coded_exact p (ownerIndex p (d.masks 0)))
      (aux 0) _ (hout P hp) ((rat_inside_transform _ _ _).mp hq)
  have apart (i j : Fin 4) (hne : d.masks i ≠ d.masks j) :
      ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y) := by
    intro x y hp
    exact p.disjoint _ _
      (fun he => hne ((code i).symm.trans
        ((congrArg (markerCode p) he).trans (code j)))) _ _
      ⟨(inside_pull _ _ _ _).mp hp.1,(inside_pull _ _ _ _).mp hp.2⟩
  have side (i : Fin 4) : 1 < (q i).side := by
    simpa only [q,pull_same_side,p.congruent] using p.side_gt_one
  have rLow : (q 3).Inside 3 (113/50) := by
    simpa using inside 3 (3,113/50) (by norm_num [insidePoints])
  have rUpper : (q 3).Inside 3 (72/25) := by
    simpa using inside 3 (3,72/25) (by norm_num [insidePoints])
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
  apply EndpointHighRight.impossible (q 0) (q 1) (q 2) (q 3)
  refine {
    aSide := side 0, bSide := side 1
    aP := ?_, aQ := ?_, aT := ?_, aF := ?_, aG := ?_
    bMarker := ?_, bLow := ?_, bHigh := ?_, lQ := ?_
    rQ := close rTop, rHigh := rHigh
    ab := apart 0 1 hab, ar := apart 0 3 har, bl := apart 1 2 hbl }
  · simpa using close (inside 0 (2,113/50) (by norm_num [insidePoints]))
  · simpa using close (inside 0 (113/50,2) (by norm_num [insidePoints]))
  · simpa using close (inside 0 (47/20,47/20) (by norm_num [insidePoints]))
  · simpa using outside (33/20,33/20) (by norm_num [outsidePoints])
  · simpa using outside (47/20,33/20) (by norm_num [outsidePoints])
  · simpa using close (inside 1 (33/20,47/20) (by norm_num [insidePoints]))
  · simpa using inside 1 (87/50,2) (by norm_num [insidePoints])
  · simpa using inside 1 (8/5,3) (by norm_num [insidePoints])
  · simpa using close (inside 2 (1,12/5) (by norm_num [insidePoints]))

#print axioms impossible_actual
end N12Compact.EndpointHighRightCase
