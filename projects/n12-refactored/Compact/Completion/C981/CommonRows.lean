import Compact.Completion.C981.CommonCycle
import Compact.Completion.C981.Crosspoint
import Compact.Completion.C981.WallAdvance
import Compact.Completion.C981.WallOrigin
import Compact.Completion.C981.Charts
import Compact.Geometry.WallLowerReach
import Compact.Bridge.C981DoubleWallElbows
import Completion.Cases.C981.VectorData

/-! Nine original common-cycle rows. Every derived point and whole
segment retains its actual owner. The original ordinary-center theorem
supplies the center; the new rigid charts supply the actual corner/top
ancestry without introducing a pose, orientation or ownership assumption. -/
namespace N12Compact.C981CompletionCommonRows

open S12 S12Pilot S12Completion.C981
set_option Elab.async false

def insidePoints : Fin 12 → List (ℚ × ℚ)
  | 1 => [(19/25,187/100)]
  | 3 => [(3,3)]
  | 4 => [(1,3)]
  | 6 => [(47/20,47/20),(113/50,3),(12/5,3)]
  | 7 => [(33/20,47/20),(2,113/50),(87/50,2)]
  | 8 => [(457/500,2),(1,113/50),(1,12/5)]
  | 10 => [(1543/500,2),(3,12/5)]
  | 11 => [(2,1543/500),(8/5,3),(87/50,3)]
  | _ => []

def outsidePoints : Fin 12 → List (ℚ × ℚ)
  | 7 => [(33/20,33/20)]
  | 8 => [(1,87/50)]
  | 10 => [(3,87/50),(113/50,2)]
  | _ => []

def Check (v : List (Finset Nat)) : Prop :=
  (∀ i, ∀ P ∈ insidePoints i, P ∈ queryInsidePoints (ownerMasks i) 2 (v[i.val]!)) ∧
  (∀ i, ∀ P ∈ outsidePoints i, P ∈ queryOutsidePoints (ownerMasks i) 2 (v[i.val]!)) ∧
  C981DoubleWallElbows.PlacementCheck v 2

instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem geometry (q : Fin 12 → OpenSquare)
    (side : ∀ i, 1 < (q i).side)
    (same : ∀ i j, (q i).side=(q j).side)
    (box : ∀ i, InsideContainer (q i))
    (inside : ∀ i, ∀ P ∈ insidePoints i, (q i).Inside (P.1 : ℝ) (P.2 : ℝ))
    (outside : ∀ i, ∀ P ∈ outsidePoints i, ¬ (q i).Inside (P.1 : ℝ) (P.2 : ℝ))
    (center : (q 7).Inside 2 2)
    (apart : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y)) :
    False := by
  have foreign (i j : Fin 12) (different : i ≠ j) (x y : ℝ)
      (point : (q j).Inside x y) : ¬ (q i).Inside x y := by
    intro own
    exact apart i j different x y ⟨own,point⟩
  have cMarker : (q 7).Inside (33/20) (47/20) := by
    simpa using inside 7 (33/20,47/20) (by norm_num [insidePoints])
  have bMarker : (q 6).Inside (47/20) (47/20) := by
    simpa using inside 6 (47/20,47/20) (by norm_num [insidePoints])
  have bLow : (q 6).Inside (113/50) 3 := by
    simpa using inside 6 (113/50,3) (by norm_num [insidePoints])
  have bHigh : (q 6).Inside (12/5) 3 := by
    simpa using inside 6 (12/5,3) (by norm_num [insidePoints])
  have cP : (q 7).Inside 2 (113/50) := by
    simpa using inside 7 (2,113/50) (by norm_num [insidePoints])
  have cQ : (q 7).Inside (87/50) 2 := by
    simpa using inside 7 (87/50,2) (by norm_num [insidePoints])
  have cMissing : ¬ (q 7).Inside (33/20) (33/20) := by
    simpa using outside 7 (33/20,33/20) (by norm_num [outsidePoints])
  have leftMarker : (q 8).Inside (457/500) 2 := by
    simpa using inside 8 (457/500,2) (by norm_num [insidePoints])
  have leftLow : (q 8).Inside 1 (113/50) := by
    simpa using inside 8 (1,113/50) (by norm_num [insidePoints])
  have leftHigh : (q 8).Inside 1 (12/5) := by
    simpa using inside 8 (1,12/5) (by norm_num [insidePoints])
  have leftMissing : ¬ (q 8).Inside 1 (87/50) := by
    simpa using outside 8 (1,87/50) (by norm_num [outsidePoints])
  have leftFar : (q 8).Inside 1 (14/5) :=
    C981CompletionWallAdvance.point (q 8) (side 8) (box 8) leftMarker leftHigh leftMissing
      (foreign 8 1 (by decide) _ _ (by simpa using inside 1 (19/25,187/100) (by norm_num [insidePoints])))
      (foreign 8 7 (by decide) _ _ cMarker)
  have leftSegment (y : ℝ) (lo : 113/50 ≤ y) (hi : y ≤ 14/5) : (q 8).Inside 1 y := by
    let t := (y-113/50)/(14/5-113/50)
    have tn : 0 ≤ t := div_nonneg (by linarith only [lo]) (by norm_num)
    have tu : t ≤ 1 := (div_le_iff₀ (by norm_num : (0:ℝ) < 14/5-113/50)).mpr
      (by linarith only [hi])
    have point := inside_segment (q 8) 1 (113/50) 1 (14/5) t leftLow leftFar tn tu
    convert point using 1 <;> dsimp [t] <;> ring
  have topMarker : (q 11).Inside 2 (1543/500) := by
    simpa using inside 11 (2,1543/500) (by norm_num [insidePoints])
  have topNear : (q 11).Inside (8/5) 3 := by
    simpa using inside 11 (8/5,3) (by norm_num [insidePoints])
  have topAnchor : (q 11).Inside (87/50) 3 := by
    simpa using inside 11 (87/50,3) (by norm_num [insidePoints])
  let topReachTransform : Transform := ⟨true,true,true⟩
  have topReachMarker : (topReachTransform.pull (q 11)).Inside (457/500) 2 := by
    apply (inside_pull topReachTransform (q 11) _ _).mpr
    convert topMarker using 1 <;> norm_num [topReachTransform,Transform.apply]
  have topReachHigh : (topReachTransform.pull (q 11)).Inside 1 (12/5) := by
    apply (inside_pull topReachTransform (q 11) _ _).mpr
    convert topNear using 1 <;> norm_num [topReachTransform,Transform.apply]
  have topReachLowMissing : ¬ (topReachTransform.pull (q 11)).Inside 1 (87/50) := by
    intro point
    have h := (inside_pull topReachTransform (q 11) _ _).mp point
    norm_num [topReachTransform,Transform.apply] at h
    exact foreign 11 6 (by decide) _ _ bLow h
  have topReachInwardMissing : ¬ (topReachTransform.pull (q 11)).Inside (87/50) 2 := by
    intro point
    have h := (inside_pull topReachTransform (q 11) _ _).mp point
    norm_num [topReachTransform,Transform.apply] at h
    exact foreign 11 7 (by decide) _ _ cP h
  have topFar : (q 11).Inside (36/25) 3 := by
    have point := WallLowerReach.point (topReachTransform.pull (q 11))
      (by simpa only [pull_same_side] using side 11)
      (container_transform _ _ (box 11)) topReachMarker topReachHigh
      topReachLowMissing topReachInwardMissing
    have h := (inside_pull topReachTransform (q 11) _ _).mp point
    norm_num [topReachTransform,Transform.apply] at h
    exact h
  have topMid : (q 11).Inside (3/2) 3 := by
    obtain ⟨a,b,c,d⟩ := topFar
    obtain ⟨e,f,g,h⟩ := topNear
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a,b,c,d,e,f,g,h]
  have cornerOrigin : (q 4).Inside 1 3 := by
    simpa using inside 4 (1,3) (by norm_num [insidePoints])
  have cornerFar : (q 4).Inside 1 (18/5) := by
    have origin : (C981CompletionCharts.corner (q 4)).Inside 0 0 := by
      apply (C981CompletionCharts.inside_corner _ _ _).mpr
      convert cornerOrigin using 1 <;> norm_num
    have missingLeft : ¬ (C981CompletionCharts.corner (q 4)).Inside (-(1/5)) 0 := by
      intro point
      have h := (C981CompletionCharts.inside_corner _ _ _).mp point
      norm_num at h
      exact foreign 4 8 (by decide) _ _ leftFar h
    have missingBelow : ¬ (C981CompletionCharts.corner (q 4)).Inside 0 (-(37/50)) := by
      intro point
      have h := (C981CompletionCharts.inside_corner _ _ _).mp point
      norm_num at h
      exact foreign 4 11 (by decide) _ _ topAnchor h
    have point := C981CompletionCornerAdvance.point (C981CompletionCharts.corner (q 4))
      (by simpa only [C981CompletionCharts.corner_side] using side 4)
      (C981CompletionCharts.corner_wall _ (box 4)) origin missingLeft missingBelow
    have h := (C981CompletionCharts.inside_corner _ _ _).mp point
    norm_num at h
    exact h
  have cornerSegment (z : ℝ) (lo : 0 ≤ z) (hi : z ≤ 3/5) : (q 4).Inside 1 (3+z) := by
    let t := z/(3/5)
    have tn : 0 ≤ t := div_nonneg lo (by norm_num)
    have tu : t ≤ 1 := (div_le_iff₀ (by norm_num : (0:ℝ) < 3/5)).mpr (by linarith only [hi])
    have point := inside_segment (q 4) 1 3 1 (18/5) t cornerOrigin cornerFar tn tu
    convert point using 1 <;> dsimp [t] <;> ring
  have topOrigin : (q 11).Inside 2 3 := by
    have north : (C981CompletionCharts.top (q 11)).Inside 0 (43/500) := by
      apply (C981CompletionCharts.inside_top _ _ _).mpr
      convert topMarker using 1 <;> norm_num
    have east : (C981CompletionCharts.top (q 11)).Inside (2/5) 0 := by
      apply (C981CompletionCharts.inside_top _ _ _).mpr
      convert topNear using 1 <;> norm_num
    have avoid : ∀ z : ℝ, 0 ≤ z → z ≤ 3/5 → ¬ (C981CompletionCharts.top (q 11)).Inside 1 z := by
      intro z lo hi point
      have h := (C981CompletionCharts.inside_top _ _ _).mp point
      norm_num at h
      exact foreign 11 4 (by decide) _ _ (cornerSegment z lo hi) h
    have point := C981CompletionWallOrigin.point (C981CompletionCharts.top (q 11))
      (by simpa only [C981CompletionCharts.top_side] using side 11)
      (C981CompletionCharts.top_wall _ (box 11)) north east avoid
    have h := (C981CompletionCharts.inside_top _ _ _).mp point
    norm_num at h
    exact h
  have north : (q 7).Inside 2 (5/2) := by
    have point := C981CompletionCrosspoint.point (pullX (q 7))
      (side 7)
      ((inside_pullX _ _ _).mpr (by convert cP using 1 <;> norm_num))
      ((inside_pullX _ _ _).mpr (by convert cQ using 1 <;> norm_num))
      ((inside_pullX _ _ _).mpr (by convert cMarker using 1 <;> norm_num))
      (fun h => cMissing (by have hp := (inside_pullX _ _ _).mp h; norm_num at hp; exact hp))
      (fun h => foreign 7 6 (by decide) _ _ bMarker
        (by have hp := (inside_pullX _ _ _).mp h; norm_num at hp; exact hp))
      (fun h => foreign 7 8 (by decide) _ _ leftHigh
        (by have hp := (inside_pullX _ _ _).mp h; norm_num at hp; exact hp))
      (fun h => foreign 7 8 (by decide) _ _ (leftSegment (5/2) (by norm_num) (by norm_num))
        (by have hp := (inside_pullX _ _ _).mp h; norm_num at hp; exact hp))
    have h := (inside_pullX _ _ _).mp point
    norm_num at h
    exact h
  let crossTransform : Transform := ⟨true,true,false⟩
  have west : (q 7).Inside (3/2) 2 := by
    have p' : (crossTransform.pull (q 7)).Inside 2 (113/50) := by
      apply (inside_pull crossTransform (q 7) _ _).mpr
      convert cQ using 1 <;> norm_num [crossTransform,Transform.apply]
    have q' : (crossTransform.pull (q 7)).Inside (113/50) 2 := by
      apply (inside_pull crossTransform (q 7) _ _).mpr
      convert cP using 1 <;> norm_num [crossTransform,Transform.apply]
    have m' : (crossTransform.pull (q 7)).Inside (47/20) (47/20) := by
      apply (inside_pull crossTransform (q 7) _ _).mpr
      convert cMarker using 1 <;> norm_num [crossTransform,Transform.apply]
    have g' : ¬ (crossTransform.pull (q 7)).Inside (47/20) (33/20) := by
      intro point
      have h := (inside_pull crossTransform (q 7) _ _).mp point
      norm_num [crossTransform,Transform.apply] at h
      exact foreign 7 6 (by decide) _ _ bMarker h
    have b' : ¬ (crossTransform.pull (q 7)).Inside (33/20) (47/20) := by
      intro point
      have h := (inside_pull crossTransform (q 7) _ _).mp point
      norm_num [crossTransform,Transform.apply] at h
      exact cMissing h
    have r0 : ¬ (crossTransform.pull (q 7)).Inside 3 (12/5) := by
      intro point
      have h := (inside_pull crossTransform (q 7) _ _).mp point
      norm_num [crossTransform,Transform.apply] at h
      exact foreign 7 11 (by decide) _ _ topNear h
    have r1 : ¬ (crossTransform.pull (q 7)).Inside 3 (5/2) := by
      intro point
      have h := (inside_pull crossTransform (q 7) _ _).mp point
      norm_num [crossTransform,Transform.apply] at h
      exact foreign 7 11 (by decide) _ _ topMid h
    have point := C981CompletionCrosspoint.point (crossTransform.pull (q 7))
      (by simpa only [pull_same_side] using side 7) p' q' m' g' b' r0 r1
    have h := (inside_pull crossTransform (q 7) _ _).mp point
    norm_num [crossTransform,Transform.apply] at h
    exact h
  have rightMarker : (q 10).Inside (1543/500) 2 := by
    simpa using inside 10 (1543/500,2) (by norm_num [insidePoints])
  have rightHigh : (q 10).Inside 3 (12/5) := by
    simpa using inside 10 (3,12/5) (by norm_num [insidePoints])
  have rightFar : (q 10).Inside 3 (64/25) := by
    have point := WallLowerReach.point (pullX (q 10)) (side 10) (container_pullX _ (box 10))
      ((inside_pullX _ _ _).mpr (by convert rightMarker using 1 <;> norm_num))
      ((inside_pullX _ _ _).mpr (by convert rightHigh using 1 <;> norm_num))
      (fun h => by
        have missing : ¬ (q 10).Inside 3 (87/50) := by
          simpa using outside 10 (3,87/50) (by norm_num [outsidePoints])
        have hp := (inside_pullX _ _ _).mp h
        norm_num at hp
        exact missing hp)
      (fun h => by
        have missing : ¬ (q 10).Inside (113/50) 2 := by
          simpa using outside 10 (113/50,2) (by norm_num [outsidePoints])
        have hp := (inside_pullX _ _ _).mp h
        norm_num at hp
        exact missing hp)
    have h := (inside_pullX _ _ _).mp point
    norm_num at h
    exact h
  have rightMid : (q 10).Inside 3 (5/2) := by
    obtain ⟨a,b,c,d⟩ := rightHigh
    obtain ⟨e,f,g,h⟩ := rightFar
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a,b,c,d,e,f,g,h]
  have cCut : (q 7).Inside 2 (12/5) := by
    obtain ⟨a,b,c,d⟩ := center
    obtain ⟨e,f,g,h⟩ := north
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a,b,c,d,e,f,g,h]
  apply C981CompletionCommonCycle.impossible (q 7) (q 6) (side 7) (same 7 6)
    center west north cMarker cMissing
    (fun y lo hi => foreign 7 8 (by decide) _ _ (leftSegment y lo hi)) bMarker bLow bHigh
    (foreign 6 7 (by decide) _ _ cCut) (foreign 6 11 (by decide) _ _ topOrigin)
    (foreign 6 10 (by decide) _ _ rightHigh)
    (foreign 6 3 (by decide) _ _ (by simpa using inside 3 (3,3) (by norm_num [insidePoints])))
    (foreign 6 10 (by decide) _ _ rightFar) (foreign 6 10 (by decide) _ _ rightMid)
    (foreign 6 11 (by decide) _ _ topMarker) (apart 7 6 (by decide))

theorem excludes (v : List (Finset Nat)) (checked : Check v) : ExcludesVector v := by
  intro p hf hv
  let q := owners p
  have aux (i : Fin 12) : AuxExact (q i) 2 (v[i.val]!) := by
    have he := ownership_entry_at p v hv i
    simpa only [q,owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks i))
  have inside (i : Fin 12) (P : ℚ × ℚ) (member : P ∈ insidePoints i) :
      (q i).Inside P.1 P.2 :=
    query_inside_sound _ 2 _ _ (owners_side_gt p i) (owners_side_le p i)
      (owners_contained p i) (owners_markers p hf i) (aux i) _ (checked.1 i P member)
  have outside (i : Fin 12) (P : ℚ × ℚ) (member : P ∈ outsidePoints i) :
      ¬ (q i).Inside P.1 P.2 :=
    query_outside_sound _ 2 _ _ (owners_markers p hf i) (aux i) _ (checked.2.1 i P member)
  have side (i : Fin 12) : 1 < (q i).side := owners_side_gt p i
  have same (i j : Fin 12) : (q i).side=(q j).side :=
    (p.congruent _).trans (p.congruent _).symm
  have box (i : Fin 12) : InsideContainer (q i) := owners_contained p i
  exact geometry q side same box inside outside
    (C981DoubleWallElbows.center v 2 checked.2.2 p hf hv)
    (fun i j different => owners_disjoint p hf i j different)

def coveredIds : List Nat := [2,28,30,34,37,41,43,69,103]

theorem checked : ∀ i ∈ coveredIds, Check (representativeVectors[i]!) := by decide +kernel

theorem covered_excluded (i : Nat) (member : i ∈ coveredIds) :
    ExcludesVector (representativeVectors[i]!) := excludes _ (checked i member)

#print axioms covered_excluded
end N12Compact.C981CompletionCommonRows
