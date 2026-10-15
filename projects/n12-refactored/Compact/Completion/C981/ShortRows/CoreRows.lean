import Compact.Completion.C981.ShortRows.CoreSqueeze
import Compact.Completion.C981.WallAdvance
import Completion.Cases.C981.VectorData
import S12.TransformFacts

/-! Whole original row 101. The four diamond points belong to owner 6.
Both neighboring sectors use original owners and their genuine corner,
singleton seed and advanced wall point. Coordinate interchange transports
all strict ownership and every boundary exclusion together. -/
namespace N12Compact.C981CompletionShortRows
open S12 S12Pilot S12Completion.C981 C977CornerCubic
set_option Elab.async false

def insidePoints : Fin 12 → List (ℚ × ℚ)
  | 0 => [(187/100,19/25)]
  | 1 => [(19/25,187/100)]
  | 2 => [(3,1)]
  | 4 => [(1,3)]
  | 5 => [(47/20,33/20),(3,87/50)]
  | 6 => [(47/20,47/20),(87/50,2),(2,87/50)]
  | 7 => [(33/20,47/20),(87/50,3)]
  | 8 => [(457/500,2),(1,12/5)]
  | 9 => [(2,457/500),(12/5,1)]
  | _ => []

def outsidePoints : Fin 12 → List (ℚ × ℚ)
  | 6 => [(33/20,47/20),(47/20,33/20)]
  | 8 => [(1,87/50)]
  | 9 => [(87/50,1)]
  | _ => []

def Check (v : List (Finset Nat)) : Prop :=
  (∀ i, ∀ P ∈ insidePoints i, P ∈ queryInsidePoints (ownerMasks i) 2 (v[i.val]!)) ∧
  (∀ i, ∀ P ∈ outsidePoints i, P ∈ queryOutsidePoints (ownerMasks i) 2 (v[i.val]!))

instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (_ ∧ _))

private noncomputable def swapFrame (A : OpenSquare) : OpenSquare where
  c := A.c
  s := -A.s
  loU := A.loV
  loV := A.loU
  side := A.side
  unit_normal := by nlinarith only [A.unit_normal]
  side_pos := A.side_pos

private theorem inside_swapFrame (A : OpenSquare) (x y : ℝ) :
    (swapFrame A).Inside x y ↔ A.Inside y x := by
  dsimp [swapFrame,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨a,b,c,d⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a,b,c,d]

theorem excludes (v : List (Finset Nat)) (checked : Check v) : ExcludesVector v := by
  intro p hf hv
  have aux (i : Fin 12) : AuxExact (owners p i) 2 (v[i.val]!) := by
    have he := ownership_entry_at p v hv i
    simpa only [owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks i))
  have inside (i : Fin 12) (P : ℚ × ℚ) (member : P ∈ insidePoints i) :
      (owners p i).Inside P.1 P.2 :=
    query_inside_sound _ 2 _ _ (owners_side_gt p i) (owners_side_le p i)
      (owners_contained p i) (owners_markers p hf i) (aux i) _ (checked.1 i P member)
  have outside (i : Fin 12) (P : ℚ × ℚ) (member : P ∈ outsidePoints i) :
      ¬ (owners p i).Inside P.1 P.2 :=
    query_outside_sound _ 2 _ _ (owners_markers p hf i) (aux i) _ (checked.2 i P member)
  have foreign (i j : Fin 12) (different : i ≠ j) (x y : ℝ)
      (point : (owners p j).Inside x y) : ¬ (owners p i).Inside x y := by
    intro own
    exact owners_disjoint p hf i j different x y ⟨own,point⟩
  have owner_side (i : Fin 12) : (owners p i).side=p.commonSide := p.congruent _
  have leftFar : (owners p 8).Inside 1 (14/5) := by
    apply C981CompletionWallAdvance.point (owners p 8) (owners_side_gt p 8) (owners_contained p 8)
    · simpa using inside 8 (457/500,2) (by norm_num [insidePoints])
    · simpa using inside 8 (1,12/5) (by norm_num [insidePoints])
    · simpa using outside 8 (1,87/50) (by norm_num [outsidePoints])
    · apply foreign 8 1 (by decide)
      simpa using inside 1 (19/25,187/100) (by norm_num [insidePoints])
    · apply foreign 8 7 (by decide)
      simpa using inside 7 (33/20,47/20) (by norm_num [insidePoints])
  have bottomFar : (owners p 9).Inside (14/5) 1 := by
    have point := C981CompletionWallAdvance.point (pullSwap (owners p 9))
      (by change 1 < (owners p 9).side; exact owners_side_gt p 9)
      (container_pullSwap _ (owners_contained p 9))
      ((inside_pullSwap _ _ _).mpr (by simpa using inside 9 (2,457/500) (by norm_num [insidePoints])))
      ((inside_pullSwap _ _ _).mpr (by simpa using inside 9 (12/5,1) (by norm_num [insidePoints])))
      (fun h => by
        have missing : ¬ (owners p 9).Inside (87/50) 1 := by
          simpa using outside 9 (87/50,1) (by norm_num [outsidePoints])
        exact missing ((inside_pullSwap _ _ _).mp h))
      (fun h => foreign 9 0 (by decide) _ _
        (by simpa using inside 0 (187/100,19/25) (by norm_num [insidePoints]))
        ((inside_pullSwap _ _ _).mp h))
      (fun h => foreign 9 5 (by decide) _ _
        (by simpa using inside 5 (47/20,33/20) (by norm_num [insidePoints]))
        ((inside_pullSwap _ _ _).mp h))
    exact (inside_pullSwap _ _ _).mp point
  obtain ⟨A,ac,canon,aside,ai,_⟩ := ClosedFrames.canonical_frame (owners p 6)
  have asame : A.side=p.commonSide := aside.trans (owner_side 6)
  have aside_gt : 1 < A.side := by rw [asame]; exact p.side_gt_one
  have left : A.Inside (87/50) 2 := (ai _ _).mpr
    (by simpa using inside 6 (87/50,2) (by norm_num [insidePoints]))
  have bottom : A.Inside 2 (87/50) := (ai _ _).mpr
    (by simpa using inside 6 (2,87/50) (by norm_num [insidePoints]))
  have marker : A.Inside (47/20) (47/20) := (ai _ _).mpr
    (by simpa using inside 6 (47/20,47/20) (by norm_num [insidePoints]))
  have nw : ¬ A.Inside (33/20) (47/20) := by
    intro h
    have missing : ¬ (owners p 6).Inside (33/20) (47/20) := by
      simpa using outside 6 (33/20,47/20) (by norm_num [outsidePoints])
    exact missing ((ai _ _).mp h)
  have se : ¬ A.Inside (47/20) (33/20) := by
    intro h
    have missing : ¬ (owners p 6).Inside (47/20) (33/20) := by
      simpa using outside 6 (47/20,33/20) (by norm_num [outsidePoints])
    exact missing ((ai _ _).mp h)
  by_cases positive : 0 ≤ A.s
  · obtain ⟨B,bc,bcanon,bside,bi,_⟩ := ClosedFrames.canonical_frame (owners p 5)
    apply C981CompletionShortSqueeze.impossible A B aside_gt
      (asame.trans (bside.trans (owner_side 5)).symm)
      ⟨positive,(abs_le.mp canon).2,A.unit_normal⟩ bc bcanon left bottom marker nw se
    · exact (bi _ _).mpr (by simpa using inside 5 (47/20,33/20) (by norm_num [insidePoints]))
    · exact (bi _ _).mpr (by simpa using inside 5 (3,87/50) (by norm_num [insidePoints]))
    · intro h
      exact foreign 5 2 (by decide) _ _
        (by simpa using inside 2 (3,1) (by norm_num [insidePoints])) ((bi _ _).mp h)
    · intro h
      exact foreign 5 9 (by decide) _ _ bottomFar ((bi _ _).mp h)
    · intro x y h
      exact owners_disjoint p hf 6 5 (by decide) x y ⟨(ai _ _).mp h.1,(bi _ _).mp h.2⟩
  · let D := swapFrame A
    obtain ⟨B,bc,bcanon,bside,bi,_⟩ := ClosedFrames.canonical_frame (pullSwap (owners p 7))
    have db : 1 < D.side := by simpa only [D,swapFrame] using aside_gt
    have dn : Normal D.c D.s := by
      dsimp [D,swapFrame,Normal]
      exact ⟨by linarith only [positive],by linarith only [(abs_le.mp canon).1],
        by nlinarith only [A.unit_normal]⟩
    have same : D.side=B.side := by
      change A.side=B.side
      have bsame : B.side=p.commonSide := bside.trans (owner_side 7)
      exact asame.trans bsame.symm
    apply C981CompletionShortSqueeze.impossible D B db same dn bc bcanon
    · exact (inside_swapFrame A _ _).mpr bottom
    · exact (inside_swapFrame A _ _).mpr left
    · exact (inside_swapFrame A _ _).mpr marker
    · exact fun h => se ((inside_swapFrame A _ _).mp h)
    · exact fun h => nw ((inside_swapFrame A _ _).mp h)
    · apply (bi _ _).mpr
      apply (inside_pullSwap _ _ _).mpr
      simpa using inside 7 (33/20,47/20) (by norm_num [insidePoints])
    · apply (bi _ _).mpr
      apply (inside_pullSwap _ _ _).mpr
      simpa using inside 7 (87/50,3) (by norm_num [insidePoints])
    · intro h
      exact foreign 7 4 (by decide) _ _
        (by simpa using inside 4 (1,3) (by norm_num [insidePoints]))
        ((inside_pullSwap _ _ _).mp ((bi _ _).mp h))
    · intro h
      exact foreign 7 8 (by decide) _ _ leftFar ((inside_pullSwap _ _ _).mp ((bi _ _).mp h))
    · intro x y h
      exact owners_disjoint p hf 6 7 (by decide) y x
        ⟨(ai _ _).mp ((inside_swapFrame A _ _).mp h.1),
          (inside_pullSwap _ _ _).mp ((bi _ _).mp h.2)⟩

def coveredIds : List Nat := [101]

theorem checked : ∀ i ∈ coveredIds, Check (representativeVectors[i]!) := by decide +kernel

theorem covered_excluded (i : Nat) (member : i ∈ coveredIds) :
    ExcludesVector (representativeVectors[i]!) := excludes _ (checked i member)

theorem representative101_excluded : ExcludesVector (representativeVectors[101]!) :=
  covered_excluded 101 (by simp [coveredIds])

#print axioms representative101_excluded
end N12Compact.C981CompletionShortRows
