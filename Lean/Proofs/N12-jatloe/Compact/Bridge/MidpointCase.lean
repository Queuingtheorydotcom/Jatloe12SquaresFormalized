import Compact.Geometry.MidpointRowTemplate
import S12.CertifiedDomain

/-! Original-packing entry for the unit-span midpoint contradiction.
The four complete owner sets may come from a finite global ownership choice.
They need not be independently forced across every packing in the family. -/
namespace N12Compact.MidpointCase
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

structure Data where
  transform : Transform
  masks : Fin 4 → Nat
  owned : Fin 4 → Finset Nat
  topX : ℚ

def insidePoints (d : Data) : Fin 4 → List (ℚ × ℚ)
  | 0 => [(2,113/50),(113/50,2),(47/20,47/20)]
  | 1 => [(33/20,47/20),(87/50,2),(d.topX,3)]
  | 2 => [(457/500,2),(1,12/5)]
  | _ => [(1543/500,2),(3,12/5)]

def outsidePoints : Fin 4 → List (ℚ × ℚ)
  | 0 => [(33/20,33/20),(47/20,33/20)]
  | 2 => [(1,87/50)]
  | 3 => [(3,87/50)]
  | _ => []

def Data.Check (d : Data) (family : Finset Nat) : Prop :=
  (∀ i, d.masks i ∈ family) ∧
  d.masks 0 ≠ d.masks 1 ∧ d.masks 0 ≠ d.masks 3 ∧
  d.masks 1 ≠ d.masks 2 ∧ d.masks 1 ≠ d.masks 3 ∧
  (∀ i, ∀ P ∈ insidePoints d i, d.transform.applyRat P ∈
    queryInsidePoints (d.masks i) 2 (d.owned i)) ∧
  (∀ i, ∀ P ∈ outsidePoints i, d.transform.applyRat P ∈
    queryOutsidePoints (d.masks i) 2 (d.owned i))

instance (d : Data) (family : Finset Nat) : Decidable (d.Check family) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem close {q : OpenSquare} {x y : ℝ} (hp : q.Inside x y) :
    ClosedInside q x y := ⟨hp.1.le,hp.2.1.le,hp.2.2.1.le,hp.2.2.2.le⟩

theorem impossible_actual (d : Data) (family : Finset Nat) (hd : d.Check family)
    (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (owned : ∀ i, natCombinedOwners p (ownerIndex p (d.masks i)) = d.owned i) : False := by
  obtain ⟨hmem,hab,har,hbl,hbr,hin,hout⟩ := hd
  let q : Fin 4 → OpenSquare := fun i =>
    d.transform.pull (p.square (ownerIndex p (d.masks i)))
  have code (i : Fin 4) : markerCode p (ownerIndex p (d.masks i)) = d.masks i :=
    ownerIndex_spec p _ (by rw [hf]; exact hmem i)
  have aux (i : Fin 4) :
      AuxExact (p.square (ownerIndex p (d.masks i))) 2 (d.owned i) := by
    simpa only [owned i] using nat_combined_exact p (ownerIndex p (d.masks i))
  have inside (i : Fin 4) (P : ℚ × ℚ) (hp : P ∈ insidePoints d i) :
      (q i).Inside P.1 P.2 := by
    apply (rat_inside_transform _ _ _).mpr
    exact query_inside_sound _ 2 _ _
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained _)
      (by simpa only [code i] using coded_exact p (ownerIndex p (d.masks i)))
      (aux i) _ (hin i P hp)
  have outside (i : Fin 4) (P : ℚ × ℚ) (hp : P ∈ outsidePoints i) :
      ¬ (q i).Inside P.1 P.2 := by
    intro hq
    exact query_outside_sound _ 2 _ _
      (by simpa only [code i] using coded_exact p (ownerIndex p (d.masks i)))
      (aux i) _ (hout i P hp) ((rat_inside_transform _ _ _).mp hq)
  have apart (i j : Fin 4) (hne : d.masks i ≠ d.masks j) :
      ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y) := by
    intro x y hp
    exact p.disjoint _ _
      (fun he => hne ((code i).symm.trans
        ((congrArg (markerCode p) he).trans (code j)))) _ _
      ⟨(inside_pull _ _ _ _).mp hp.1,(inside_pull _ _ _ _).mp hp.2⟩
  have side (i : Fin 4) : 1 < (q i).side := by
    simpa only [q,pull_same_side,p.congruent] using p.side_gt_one
  have box (i : Fin 4) : InsideContainer (q i) :=
    container_transform _ _ (p.contained _)
  apply MidpointRowTemplate.impossible (q 0) (q 1) (q 2) (q 3) d.topX
  refine {
    aSide := side 0, bSide := side 1, lSide := side 2, rSide := side 3
    bBox := box 1, lBox := box 2, rBox := box 3
    aP := ?_, aQ := ?_, aT := ?_, aF := ?_, aG := ?_
    bMarker := ?_, bLow := ?_, bHigh := ?_, lP := ?_, lQ := ?_
    lMissingLow := ?_, rP := ?_, rQ := ?_, rMissingLow := ?_
    ab := apart 0 1 hab, ar := apart 0 3 har
    bl := apart 1 2 hbl, br := apart 1 3 hbr }
  · simpa using close (inside 0 (2,113/50) (by norm_num [insidePoints]))
  · simpa using close (inside 0 (113/50,2) (by norm_num [insidePoints]))
  · simpa using close (inside 0 (47/20,47/20) (by norm_num [insidePoints]))
  · simpa using outside 0 (33/20,33/20) (by norm_num [outsidePoints])
  · simpa using outside 0 (47/20,33/20) (by norm_num [outsidePoints])
  · simpa using close (inside 1 (33/20,47/20) (by norm_num [insidePoints]))
  · simpa using inside 1 (87/50,2) (by norm_num [insidePoints])
  · simpa using inside 1 (d.topX,3) (by simp [insidePoints])
  · simpa using close (inside 2 (457/500,2) (by norm_num [insidePoints]))
  · simpa using close (inside 2 (1,12/5) (by norm_num [insidePoints]))
  · simpa using outside 2 (1,87/50) (by norm_num [outsidePoints])
  · simpa using close (inside 3 (1543/500,2) (by norm_num [insidePoints]))
  · simpa using close (inside 3 (3,12/5) (by norm_num [insidePoints]))
  · simpa using outside 3 (3,87/50) (by norm_num [outsidePoints])

#print axioms impossible_actual
end N12Compact.MidpointCase
