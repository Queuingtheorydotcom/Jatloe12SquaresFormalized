import Compact.Completion.C1092.MPPMActualWallReduction
import Compact.Completion.C1092.MPPMPositiveSector
import Compact.Completion.C1092.MPPMMissingPositiveBoundEnvelopes
import Compact.Completion.C1092.MPPMWallOrderCycle

/-! The actual positive OOOO sector before the wall-order cancellation.
The ordinary pairs are retained as a named geometric producer: this file
does not substitute them for the inward/elbow cover. Original Q9 supplies
every point of the foreign bottom bar; original Q8 supplies its own origin.
The retaining half-angle ceiling and actual next crosspoint are explicit
upstream producers. All support faces used below are derived from points.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualPositiveOrder
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMOmissions C1092MPPMPositiveSeedsActual C977CornerCubic
open C1092WallProfileScalars C1092ShallowPositiveScalars
set_option Elab.async false
noncomputable section

structure Ordinary (p : NormalizedPacking) : Prop where
  southwest : (owners p 4).Inside 1 (87/50) ∧ (owners p 4).Inside 1 (8/5)
  southeast : (owners p 5).Inside (12/5) 1 ∧ (owners p 5).Inside (113/50) 1
  northeast : (owners p 6).Inside 3 (113/50) ∧ (owners p 6).Inside 3 (12/5)
  northwest : (owners p 7).Inside (8/5) 3 ∧ (owners p 7).Inside (87/50) 3

/-- Simultaneous original-packing quarter turns, in sector order Q4--Q7. -/
def rotation (i : Fin 4) : Transform :=
  ![⟨false,false,false⟩,⟨true,true,false⟩,⟨false,true,true⟩,⟨true,false,true⟩] i

theorem rotation_context (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (i : Fin 4) :
    WallContext ((rotation i).pullPacking p) mppm := by
  have action : branchAction (rotation i) mppm=mppm := by
    funext k
    fin_cases i <;> fin_cases k <;> rfl
  have context := context_transport (rotation i) p hf mppm hb
  rwa [action] at context

theorem Ordinary.rotated (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (h : Ordinary p) (i : Fin 4) : Ordinary ((rotation i).pullPacking p) := by
  constructor
  · rw [owners_transport (rotation i) p hf 4]
    fin_cases i <;>
      norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
        inside_pullSwap,inside_pullX,inside_pullY]
    · exact h.southwest
    · exact ⟨h.southeast.2,h.southeast.1⟩
    · exact h.northeast
    · exact ⟨h.northwest.2,h.northwest.1⟩
  · rw [owners_transport (rotation i) p hf 5]
    fin_cases i <;>
      norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
        inside_pullSwap,inside_pullX,inside_pullY]
    · exact h.southeast
    · exact ⟨h.northeast.2,h.northeast.1⟩
    · exact h.northwest
    · exact ⟨h.southwest.2,h.southwest.1⟩
  · rw [owners_transport (rotation i) p hf 6]
    fin_cases i <;>
      norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
        inside_pullSwap,inside_pullX,inside_pullY]
    · exact h.northeast
    · exact ⟨h.northwest.2,h.northwest.1⟩
    · exact h.southwest
    · exact ⟨h.southeast.2,h.southeast.1⟩
  · rw [owners_transport (rotation i) p hf 7]
    fin_cases i <;>
      norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
        inside_pullSwap,inside_pullX,inside_pullY]
    · exact h.northwest
    · exact ⟨h.southwest.2,h.southwest.1⟩
    · exact h.southeast
    · exact ⟨h.northeast.2,h.northeast.1⟩

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side :=
  (p.congruent _).trans (p.congruent _).symm

private theorem mark (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem far_points (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) :
    (owners p 8).Inside 1 (64/25) ∧ (owners p 9).Inside (36/25) 1 ∧
      (owners p 10).Inside 3 (36/25) ∧ (owners p 11).Inside (64/25) 3 :=
  C1092MPPMOrdinaryWallAdvance.all_far_no_omission p hf hb
    (C1092MPPMActualWallReduction.no_missing p hf hb)
    h.southwest.1 h.southeast.2 h.northeast.1 h.northwest.2

theorem bottom_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (x : ℝ) (low : 36/25≤x) (high : x≤87/50) : (owners p 9).Inside x 1 :=
  C1092MPPMOrdinaryWallAdvance.bottom_bar_no_omission p hf hb
    (C1092MPPMActualWallReduction.no_missing p hf hb) h.southeast.2 x low high

/-- The missing-positive boundary theorem receives its literal actual
point data. The preceding origin is strict in Q8, independently of Q4's
forward omission; its exclusion from Q4 is derived by actual disjointness. -/
theorem missing_data (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (leftOrigin : (owners p 8).Inside 1 2)
    (C : OpenSquare) (frame : ActualFrame p C) (normal : Normal C.c C.s) :
    C1092MPPMMissingPositiveBoundaries.Data C := by
  have input := missing_inputs p hf hb h.southwest.1 h.southwest.2 missing
    (far_points p hf hb h).2.1 C frame
  apply C1092MPPMMissingPositiveBoundaries.Data.of_inputs C normal input
  intro own
  have original := (frame.actual _ _).mp own
  norm_num at original
  exact owners_disjoint p hf 4 8 (by decide) _ _ ⟨original,leftOrigin⟩

/-- The exact far-bar exit used in the retaining sector. It is not a
new face hypothesis: the weak excluded point and the same square's upper
longitudinal cap force its lower transverse face. -/
theorem retaining_lower_v (C : OpenSquare) (side : 1<C.side)
    (normal : Normal C.c C.s)
    (marker : C.Inside (-7/20) (-7/20))
    (outer : C.Inside (-1) (-13/50))
    (cap : C.loU+C.side≤-C.s/2)
    (missing : ¬C.Inside (-14/25) (-1)) :
    (14/25)*C.s-C.c≤C.loV := by
  have bound := normal_bounds normal
  have cp : 0<C.c := by linarith only [bound.1]
  have short := (short_projections C (14/25) (1/2) (by norm_num)).2.1
  apply le_of_not_gt
  intro low
  apply missing
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [low,cap,side,short,marker.2.1,outer.2.2.2,
      cp,normal.1]

theorem retaining_data (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : (owners p 4).Inside (87/50) 2)
    (leftOrigin : (owners p 8).Inside 1 2)
    (next : (owners p 5).Inside 2 (3/2))
    (C : OpenSquare) (frame : ActualFrame p C) (normal : Normal C.c C.s)
    (positive : 0<C.s) (small : half C.c C.s≤1/4) :
    C1092ShallowWallOrder.Data C (half C.c C.s) := by
  have walls := C1092MPPMActualWallReduction.wall_pairs p hf hb
  have side : 1<C.side := by rw [frame.side]; exact side_gt p 4
  have previous : ¬(owners p 4).Inside 1 2 := fun own =>
    owners_disjoint p hf 4 8 (by decide) _ _ ⟨own,leftOrigin⟩
  have core := forward_core p hf walls.2.1.1 h.southwest.1 h.southwest.2
    forward previous C frame
  have faces := C1092MPPMPositiveCrosspointSeeds.forward_profile C side normal core
  have cap := (forward_halfpoint_and_origin p hf walls.2.1.1
    h.southwest.1 h.southwest.2 forward previous next C frame normal positive
    (by linarith only [small])).1
  have farMissing : ¬C.Inside (-14/25) (-1) := by
    intro own
    have original := (frame.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 4 9 (by decide) _ _
      ⟨original,(far_points p hf hb h).2.1⟩
  have lowV := retaining_lower_v C side normal core.marker core.ordinaryP cap farMissing
  have cp : 0<C.c := by linarith only [(normal_bounds normal).1]
  have qpos : 0<half C.c C.s := div_pos positive (by linarith only [cp])
  have q := quarter_data C.c C.s cp.le normal.1 normal.2.2
  have cosine : C.c=cosH (half C.c C.s) := by
    dsimp [cosH]
    apply (eq_div_iff (half_den_pos _).ne').mpr
    nlinarith only [q.2.2.2.1]
  have sine : C.s=sinH (half C.c C.s) := by
    dsimp [sinH]
    apply (eq_div_iff (half_den_pos _).ne').mpr
    nlinarith only [q.2.2.2.2]
  exact ⟨qpos,small,cosine,sine,normal,faces.lowerU,cap,lowV,faces.upperV,
    core.marker,core.ordinaryP⟩

/-- Literal original-wall order for a retained forward point. The two
extra upstream producers are its scalar half-angle ceiling and the next
actual crosspoint, both stated separately from derived support faces. -/
theorem retaining_order (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : (owners p 4).Inside (87/50) 2)
    (leftOrigin : (owners p 8).Inside 1 2)
    (next : (owners p 5).Inside 2 (3/2))
    (C : OpenSquare) (frame : ActualFrame p C) (normal : Normal C.c C.s)
    (positive : 0<C.s) (small : half C.c C.s≤1/4) :
    4<centerX (owners p 9)+centerY (owners p 8) := by
  let B := (owners p 9).translated 2 2
  let L := (owners p 8).translated 2 2
  have bActual (x y : ℝ) : B.Inside x y↔(owners p 9).Inside (2+x) (2+y) := by
    simpa only [add_comm] using inside_translated_iff (owners p 9) 2 2 x y
  have lActual (x y : ℝ) : L.Inside x y↔(owners p 8).Inside (2+x) (2+y) := by
    simpa only [add_comm] using inside_translated_iff (owners p 8) 2 2 x y
  have bm : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using mark p hf 9 13 (by decide +kernel)
  have lm : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using mark p hf 8 12 (by decide +kernel)
  have order := C1092ShallowWallOrder.order C B L (half C.c C.s)
    (by rw [frame.side]; exact side_gt p 4)
    (frame.side.trans (side_same p 4 9))
    (frame.side.trans (side_same p 4 8))
    (retaining_data p hf hb h forward leftOrigin next C frame normal positive small)
    (by apply (bActual _ _).mpr; norm_num; exact bm)
    (by apply (bActual _ _).mpr; norm_num; exact C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
    (by
      intro x y own
      have wall := (p.contained _ _ _ ((bActual _ _).mp own)).2.2.1
      linarith only [wall])
    (by apply (lActual _ _).mpr; norm_num; exact lm)
    (by apply (lActual _ _).mpr; norm_num; exact leftOrigin)
    (by
      intro x y own
      have wall := (p.contained _ _ _ ((lActual _ _).mp own)).1
      linarith only [wall])
    (fun x y both => owners_disjoint p hf 4 9 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(bActual _ _).mp both.2⟩)
    (fun x y both => owners_disjoint p hf 4 8 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(lActual _ _).mp both.2⟩)
  have centersB : centerX B=centerX (owners p 9)-2 := center_translate_x _ _ _
  have centersL : centerY L=centerY (owners p 8)-2 := center_translate_y _ _ _
  rw [centersB,centersL] at order
  linarith only [order]

/-- The missing-forward alternative has no incoming angle ceiling.
Both boundary envelopes are produced from its actual point ledger. -/
theorem missing_order (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (leftOrigin : (owners p 8).Inside 1 2)
    (C : OpenSquare) (frame : ActualFrame p C) (normal : Normal C.c C.s) :
    4<centerX (owners p 9)+centerY (owners p 8) := by
  let B := (owners p 9).translated 2 2
  let L := (owners p 8).translated 2 2
  have bActual (x y : ℝ) : B.Inside x y↔(owners p 9).Inside (2+x) (2+y) := by
    simpa only [add_comm] using inside_translated_iff (owners p 9) 2 2 x y
  have lActual (x y : ℝ) : L.Inside x y↔(owners p 8).Inside (2+x) (2+y) := by
    simpa only [add_comm] using inside_translated_iff (owners p 8) 2 2 x y
  have bm : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using mark p hf 9 13 (by decide +kernel)
  have lm : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using mark p hf 8 12 (by decide +kernel)
  have cap : C.side≤1001/1000 := by
    rw [frame.side]
    change (p.square _).side≤1001/1000
    rw [p.congruent]
    exact p.side_le
  have order := C1092MPPMMissingPositiveBoundaries.order C B L
    (by rw [frame.side]; exact side_gt p 4) cap
    (frame.side.trans (side_same p 4 9))
    (frame.side.trans (side_same p 4 8))
    (missing_data p hf hb h missing leftOrigin C frame normal)
    (by apply (bActual _ _).mpr; norm_num; exact bm)
    (by apply (bActual _ _).mpr; norm_num; exact C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
    (by
      intro x y own
      have wall := (p.contained _ _ _ ((bActual _ _).mp own)).2.2.1
      linarith only [wall])
    (by apply (lActual _ _).mpr; norm_num; exact lm)
    (by apply (lActual _ _).mpr; norm_num; exact leftOrigin)
    (by
      intro x y own
      have wall := (p.contained _ _ _ ((lActual _ _).mp own)).1
      linarith only [wall])
    (fun x y both => owners_disjoint p hf 4 9 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(bActual _ _).mp both.2⟩)
    (fun x y both => owners_disjoint p hf 4 8 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(lActual _ _).mp both.2⟩)
  have centersB : centerX B=centerX (owners p 9)-2 := center_translate_x _ _ _
  have centersL : centerY L=centerY (owners p 8)-2 := center_translate_y _ _ _
  rw [centersB,centersL] at order
  linarith only [order]

theorem sector_order (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (leftOrigin : (owners p 8).Inside 1 2)
    (next : (owners p 5).Inside 2 (3/2))
    (C : OpenSquare) (frame : ActualFrame p C) (normal : Normal C.c C.s)
    (positive : 0<C.s)
    (retainingSmall : (owners p 4).Inside (87/50) 2→half C.c C.s≤1/4) :
    4<centerX (owners p 9)+centerY (owners p 8) := by
  by_cases forward : (owners p 4).Inside (87/50) 2
  · exact retaining_order p hf hb h forward leftOrigin next C frame normal positive
      (retainingSmall forward)
  · exact missing_order p hf hb h forward leftOrigin C frame normal

structure MissingForward (p : NormalizedPacking) : Prop where
  southwest : ¬(owners p 4).Inside (87/50) 2
  southeast : ¬(owners p 5).Inside 2 (87/50)
  northeast : ¬(owners p 6).Inside (113/50) 2
  northwest : ¬(owners p 7).Inside 2 (113/50)

theorem missing_forward_rotated (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (h : MissingForward p) (i : Fin 4) :
    ¬(owners ((rotation i).pullPacking p) 4).Inside (87/50) 2 := by
  rw [owners_transport (rotation i) p hf 4]
  fin_cases i <;>
    norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX,inside_pullY]
  · exact h.southwest
  · exact h.southeast
  · exact h.northeast
  · exact h.northwest

/-- Every origin in the all-missing cycle is obtained from that same
central owner's strict outer halfpoint and its genuine paired corner. -/
theorem all_missing_origins (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (missing : MissingForward p) :
    (owners p 9).Inside 2 1 ∧ (owners p 10).Inside 3 2 ∧
      (owners p 11).Inside 2 3 ∧ (owners p 8).Inside 1 2 := by
  have origin (i : Fin 4) : (owners ((rotation i).pullPacking p) 9).Inside 2 1 := by
    have context := rotation_context p hf hb i
    have family' := family_transport (rotation i) p hf
    have ordinary := Ordinary.rotated p hf h i
    exact bottom_origin_of_missing ((rotation i).pullPacking p) family' context
      (C1092MPPMActualWallReduction.bottom_ordinary ((rotation i).pullPacking p) family' context)
      ordinary.southwest.1 ordinary.southwest.2 (missing_forward_rotated p hf missing i)
  have first := origin 0
  have second := origin 1
  have third := origin 2
  have fourth := origin 3
  rw [owners_transport (rotation 0) p hf 9] at first
  rw [owners_transport (rotation 1) p hf 9] at second
  rw [owners_transport (rotation 2) p hf 9] at third
  rw [owners_transport (rotation 3) p hf 9] at fourth
  norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullX,inside_pullY] at first second third fourth
  exact ⟨first,second,third,fourth⟩

theorem rotated_orders_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (orders : ∀ i : Fin 4,4<centerX (owners ((rotation i).pullPacking p) 9)+
      centerY (owners ((rotation i).pullPacking p) 8)) : False := by
  have order (i : Fin 4) : 0<(C1092MPPMWallOrderCycle.centerPairs (owners p) i).1+
      (C1092MPPMWallOrderCycle.centerPairs (owners p) i).2 := by
    have comparison := orders i
    rw [owners_transport (rotation i) p hf 9,owners_transport (rotation i) p hf 8] at comparison
    fin_cases i <;>
      norm_num [rotation,C1092MPPMWallOrderCycle.centerPairs,ownerAction,ownerSwap,
        ownerX,ownerY,Transform.pull,center_pullSwap_x,center_pullSwap_y,
        center_pullX_x,center_pullX_y,center_pullY_x,center_pullY_y] at comparison ⊢ <;>
      linarith only [comparison]
  have first := order 0
  have second := order 1
  have third := order 2
  have fourth := order 3
  dsimp [C1092MPPMWallOrderCycle.centerPairs] at first second third fourth
  linarith only [first,second,third,fourth]

/-- The all-missing positive cycle needs neither a crosspoint producer
nor a retaining angle ceiling. Its four actual origins are proved above. -/
theorem all_missing_positive_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (h : Ordinary p) (missing : MissingForward p)
    (positive : ∀ i : Fin 4,∃ C : OpenSquare,
      ActualFrame ((rotation i).pullPacking p) C ∧ Normal C.c C.s) : False := by
  have origins := all_missing_origins p hf hb h missing
  apply rotated_orders_impossible p hf
  intro i
  obtain ⟨C,frame,normal⟩ := positive i
  have left : (owners ((rotation i).pullPacking p) 8).Inside 1 2 := by
    rw [owners_transport (rotation i) p hf 8]
    fin_cases i <;>
      norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
        inside_pullSwap,inside_pullX,inside_pullY]
    · exact origins.2.2.2
    · exact origins.1
    · exact origins.2.1
    · exact origins.2.2.1
  exact missing_order ((rotation i).pullPacking p) (family_transport (rotation i) p hf)
    (rotation_context p hf hb i) (Ordinary.rotated p hf h i)
    (missing_forward_rotated p hf missing i) left C frame normal

/-- The exact original point/angle producers needed by the positive
sector join. No support face or desired wall-order conclusion is a field. -/
structure SectorEntrance (p : NormalizedPacking) (C : OpenSquare) : Prop where
  frame : ActualFrame p C
  normal : Normal C.c C.s
  positive : 0<C.s
  leftOrigin : (owners p 8).Inside 1 2
  next : (owners p 5).Inside 2 (3/2)
  retainingSmall : (owners p 4).Inside (87/50) 2→half C.c C.s≤1/4

/-- Four strict comparisons concern the same four original wall centers.
All mixed retained/omitted forward patterns are included. The entrance
still explicitly names its ordinary-pair, origin, crosspoint and scalar
producers; this is not an unconditional whole-family exclusion. -/
theorem impossible_of_positive_entrance (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (sectors : ∀ i : Fin 4,∃ C : OpenSquare,SectorEntrance ((rotation i).pullPacking p) C) :
    False := by
  apply rotated_orders_impossible p hf
  intro i
  obtain ⟨C,entrance⟩ := sectors i
  exact sector_order ((rotation i).pullPacking p)
    (family_transport (rotation i) p hf) (rotation_context p hf hb i)
    (Ordinary.rotated p hf h i) entrance.leftOrigin entrance.next C entrance.frame
    entrance.normal entrance.positive entrance.retainingSmall

end
#print axioms far_points
#print axioms missing_data
#print axioms retaining_order
#print axioms missing_order
#print axioms sector_order
#print axioms all_missing_positive_impossible
#print axioms impossible_of_positive_entrance
end N12Compact.C1092MPPMActualPositiveOrder
