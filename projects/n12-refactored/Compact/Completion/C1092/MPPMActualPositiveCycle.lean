import Compact.Completion.C1092.MPPMSteepPositiveThreeSquareActual

/-! The actual all-positive ordinary cycle, with the four printed scalar
inequalities isolated as a mathematical dependency. Every crosspoint,
origin and retaining angle entrance is produced from the actual squares.
No geometric support premise or ownership of an omitted point is added.
The final scalar proof is supplied separately. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualPositiveCycle
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C977CornerCubic C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
open C1092MPPMActualBoundaryOrigin C1092MPPMActualRetaining
open C1092MPPMSteepPositiveThreeSquare
set_option Elab.async false
noncomputable section

def ScalarProof : Prop := ∀ c s d t : ℝ,Normal c s→Normal d t→3/5≤s→
  ModesNonnegative c s d t

def PositiveFrames (p : NormalizedPacking) : Prop := ∀ i : Fin 4,
  ∃ C : OpenSquare,ActualFrame ((rotation i).pullPacking p) C ∧
    Normal C.c C.s ∧ 0<C.s

def Crosspoint (p : NormalizedPacking) : Prop := (owners p 4).Inside (3/2) 2
def Forward (p : NormalizedPacking) : Prop := (owners p 4).Inside (87/50) 2
def AllCrosspoints (p : NormalizedPacking) : Prop := ∀ i : Fin 4,
  Crosspoint ((rotation i).pullPacking p)

theorem PositiveFrames.rotated (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (positive : PositiveFrames p) (i : Fin 4) : PositiveFrames ((rotation i).pullPacking p) := by
  intro j
  obtain ⟨C,frame,cn,sp⟩ := positive (addSector i j)
  exact ⟨C,rotated_frame p hf i j C frame,cn,sp⟩

/-- The actual crosspoint is transported through both simultaneous
quarter turns. This uses the entire interior equivalence of one actual
square, not a relabeling of a finite point table. -/
theorem crosspoint_composed (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 4) (point : Crosspoint ((rotation (addSector i j)).pullPacking p)) :
    Crosspoint ((rotation j).pullPacking ((rotation i).pullPacking p)) := by
  let C := (owners ((rotation (addSector i j)).pullPacking p) 4).translated 2 2
  have old : ActualFrame ((rotation (addSector i j)).pullPacking p) C :=
    ⟨rfl,fun x y => inside_translated_iff _ 2 2 x y⟩
  have frame := rotated_frame p hf i j C old
  have own : C.Inside (-1/2) 0 := by
    apply (old.actual _ _).mpr
    norm_num
    exact point
  have original := (frame.actual _ _).mp own
  norm_num at original
  exact original

theorem AllCrosspoints.rotated (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (points : AllCrosspoints p) (i : Fin 4) : AllCrosspoints ((rotation i).pullPacking p) :=
  fun j => crosspoint_composed p hf i j (points (addSector i j))

theorem next_crosspoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (point : Crosspoint ((rotation 1).pullPacking p)) : (owners p 5).Inside 2 (3/2) := by
  change (owners ((rotation 1).pullPacking p) 4).Inside (3/2) 2 at point
  rw [owners_transport (rotation 1) p hf 4] at point
  norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullX] at point
  exact point

/-- Completed three-square reduction, with its only outstanding input
being the four explicit real scalar inequalities. All original geometric
data are produced in actual_input. -/
theorem positive_propagation_of_scalars (scalar : ScalarProof)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : ¬Forward p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c D.s) (tp : 0<D.s)
    (next : (owners p 5).Inside 2 (3/2)) : Crosspoint p := by
  apply Classical.byContradiction
  intro missing
  have caps := actual_missing_crosspoint_caps p hf hb h forward missing C frame cn sp
  have steep := (steep_sine cn caps.2).le
  exact impossible_of_modes C (C1092MMMPEndingAxes.clockwise D)
    ((owners p 9).translated 2 2)
    (actual_input p hf hb h forward missing C frame cn sp D dframe dn tp next)
    (scalar C.c C.s D.c D.s cn dn steep)

private theorem backward_cycle (P : Fin 4→Prop) (seed : ∃ i,P i)
    (step : ∀ i,P (addSector i 1)→P i) : ∀ i,P i := by
  obtain ⟨i,own⟩ := seed
  have first : P (addSector i 3) := step _ (by
    convert own using 1 <;> fin_cases i <;> rfl)
  have second : P (addSector i 2) := step _ (by
    convert first using 1 <;> fin_cases i <;> rfl)
  have third : P (addSector i 1) := step _ (by
    convert second using 1 <;> fin_cases i <;> rfl)
  intro j
  fin_cases i <;> fin_cases j <;>
    first | exact own | exact first | exact second | exact third

private theorem seed_exists (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (positive : PositiveFrames p) :
    ∃ i : Fin 4,Forward ((rotation i).pullPacking p) := by
  classical
  by_contra none
  have absent (i : Fin 4) : ¬Forward ((rotation i).pullPacking p) :=
    fun own => none ⟨i,own⟩
  have a := absent 0
  have b := absent 1
  have c := absent 2
  have d := absent 3
  change ¬(owners ((rotation 0).pullPacking p) 4).Inside (87/50) 2 at a
  change ¬(owners ((rotation 1).pullPacking p) 4).Inside (87/50) 2 at b
  change ¬(owners ((rotation 2).pullPacking p) 4).Inside (87/50) 2 at c
  change ¬(owners ((rotation 3).pullPacking p) 4).Inside (87/50) 2 at d
  rw [owners_transport (rotation 0) p hf 4] at a
  rw [owners_transport (rotation 1) p hf 4] at b
  rw [owners_transport (rotation 2) p hf 4] at c
  rw [owners_transport (rotation 3) p hf 4] at d
  norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullX,inside_pullY] at a b c d
  exact all_missing_positive_impossible p hf hb h ⟨a,b,c,d⟩
    (by intro i; obtain ⟨C,frame,normal,_⟩ := positive i; exact ⟨C,frame,normal⟩)

/-- A genuine retaining seed starts the backward propagation. A missing
forward point remains an omission from its indicated owner throughout.
At most three transfers visit all four distinct actual central owners. -/
theorem all_crosspoints_of_scalars (scalar : ScalarProof)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (positive : PositiveFrames p) :
    AllCrosspoints p := by
  have seed : ∃ i : Fin 4,Crosspoint ((rotation i).pullPacking p) := by
    obtain ⟨i,forward⟩ := seed_exists p hf hb h positive
    obtain ⟨C,frame,cn,sp⟩ := positive i
    exact ⟨i,C1092MPPMActualRetaining.forward_crosspoint ((rotation i).pullPacking p)
      (family_transport (rotation i) p hf) (rotation_context p hf hb i)
      (Ordinary.rotated p hf h i) forward C frame cn sp⟩
  apply backward_cycle (fun i => Crosspoint ((rotation i).pullPacking p)) seed
  intro i next
  let p' := (rotation i).pullPacking p
  have family' := family_transport (rotation i) p hf
  have context := rotation_context p hf hb i
  have ordinary := Ordinary.rotated p hf h i
  obtain ⟨C,frame,cn,sp⟩ := positive i
  by_cases forward : Forward p'
  · exact C1092MPPMActualRetaining.forward_crosspoint p' family' context ordinary
      forward C frame cn sp
  · obtain ⟨D,dframe,dn,tp⟩ := positive (addSector i 1)
    exact positive_propagation_of_scalars scalar p' family' context ordinary forward
      C frame cn sp D (rotated_frame p hf i 1 D dframe) dn tp
      (next_crosspoint p' family' (crosspoint_composed p hf i 1 next))

/-- With all four actual crosspoints, every sector supplies its own
next wall origin, for both forward memberships. The retaining branch
uses a genuine positive predecessor and the proved shallow corollary. -/
theorem bottom_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (positive : PositiveFrames p) (points : AllCrosspoints p) :
    (owners p 9).Inside 2 1 := by
  obtain ⟨C,frame0,cn,sp⟩ := positive 0
  have frame := original_frame p hf C frame0
  by_cases forward : Forward p
  · obtain ⟨W,wframe,wn,wp⟩ := positive 3
    exact (retaining_halfpoint_origin p hf hb h C frame cn sp W wframe wn wp forward
      (next_crosspoint p hf (points 1))).2.2
  · exact bottom_origin_of_missing p hf hb
      (C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
      h.southwest.1 h.southwest.2 forward

theorem left_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (positive : PositiveFrames p) (points : AllCrosspoints p) :
    (owners p 8).Inside 1 2 := by
  have own := bottom_origin ((rotation 3).pullPacking p)
    (family_transport (rotation 3) p hf) (rotation_context p hf hb 3)
    (Ordinary.rotated p hf h 3) (PositiveFrames.rotated p hf positive 3)
    (AllCrosspoints.rotated p hf points 3)
  rw [owners_transport (rotation 3) p hf 9] at own
  norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullY] at own
  exact own

/-- The final all-positive ordinary ending. Its only named dependency
is the separately proved four-mode scalar statement. Actual ordinary
pairs, origins, crosspoints, retaining ceilings and the four wall-center
comparisons are all obtained in this source chain. -/
theorem impossible_of_scalars (scalar : ScalarProof)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (positive : PositiveFrames p) : False := by
  have points := all_crosspoints_of_scalars scalar p hf hb h positive
  apply impossible_of_positive_entrance p hf hb h
  intro i
  let p' := (rotation i).pullPacking p
  have family' := family_transport (rotation i) p hf
  have context := rotation_context p hf hb i
  have ordinary := Ordinary.rotated p hf h i
  have positive' := PositiveFrames.rotated p hf positive i
  have points' := AllCrosspoints.rotated p hf points i
  obtain ⟨C,frame,cn,sp⟩ := positive i
  obtain ⟨W,wframe,wn,wp⟩ := positive' 3
  have next := next_crosspoint p' family' (points' 1)
  refine ⟨C,frame,cn,sp,left_origin p' family' context ordinary positive' points',next,?_⟩
  intro forward
  exact (retaining_shallow p' family' context ordinary C frame cn sp W wframe wn wp
    forward next).half.le

end
#print axioms positive_propagation_of_scalars
#print axioms all_crosspoints_of_scalars
#print axioms bottom_origin
#print axioms impossible_of_scalars
end N12Compact.C1092MPPMActualPositiveCycle
