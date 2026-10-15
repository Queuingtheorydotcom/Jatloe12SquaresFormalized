import Compact.Completion.C1092.MPPMAllNonpositiveActual
import Compact.Completion.C1092.MPPMOnePositiveActual
import Compact.Completion.C1092.MPPMNegativeMissingPositiveActual

/-! A fixed canonical frame for each of the four actual ordinary
central owners, together with their source-proved signed-cycle rules.
The indices choose simultaneous rigid sector motions. They enumerate
neither poses nor auxiliary ownership. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMOrdinaryCycle
open S12 S12Pilot C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual C1092MPPMActualRetaining
open C1092MPPMActualPositiveCycle C1092MPPMActualCrosspoints
set_option Elab.async false
noncomputable section

structure Frames (p : NormalizedPacking) where
  square : Fin 4→OpenSquare
  frame : ∀ i,ActualFrame ((rotation i).pullPacking p) (square i)
  canonical : ∀ i,|(square i).s|≤(square i).c

def Positive {p : NormalizedPacking} (d : Frames p) (i : Fin 4) : Prop :=
  0<(d.square i).s

def Retains (p : NormalizedPacking) (i : Fin 4) : Prop :=
  Forward ((rotation i).pullPacking p)

theorem Frames.positive_normal {p : NormalizedPacking} (d : Frames p) (i : Fin 4)
    (positive : Positive d i) : Normal (d.square i).c (d.square i).s :=
  ⟨positive.le,(abs_le.mp (d.canonical i)).2,(d.square i).unit_normal⟩

theorem Frames.nonpositive_normal {p : NormalizedPacking} (d : Frames p) (i : Fin 4)
    (nonpositive : ¬Positive d i) : Normal (d.square i).c (-(d.square i).s) :=
  ⟨by linarith only [le_of_not_gt nonpositive],
    by linarith only [(abs_le.mp (d.canonical i)).1],
    by nlinarith only [(d.square i).unit_normal]⟩

def Frames.rotated {p : NormalizedPacking} (d : Frames p)
    (hf : codedMarkerFamily p=family) (i : Fin 4) : Frames ((rotation i).pullPacking p) :=
  ⟨fun j => d.square (addSector i j),
    fun j => rotated_frame p hf i j _ (d.frame (addSector i j)),
    fun j => d.canonical (addSector i j)⟩

theorem Frames.exists (p : NormalizedPacking) : Nonempty (Frames p) := by
  classical
  have witnesses (i : Fin 4) : ∃ C : OpenSquare,
      ActualFrame ((rotation i).pullPacking p) C ∧ |C.s|≤C.c := by
    obtain ⟨C,frame,_,canonical⟩ := exists_canonical_frame ((rotation i).pullPacking p)
    exact ⟨C,frame,canonical⟩
  choose C frame canonical using witnesses
  exact ⟨⟨C,frame,canonical⟩⟩

theorem next_retained (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 4) (own : Retains p (addSector i 1)) :
    (owners ((rotation i).pullPacking p) 5).Inside 2 (87/50) :=
  (next_forward_iff _ (family_transport (rotation i) p hf)).mp (forward_composed p hf i 1 own)

theorem next_missing (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 4) (missing : ¬Retains p (addSector i 1)) :
    ¬(owners ((rotation i).pullPacking p) 5).Inside 2 (87/50) := by
  intro own
  exact missing ((forward_composed_iff p hf i 1).mpr
    ((next_forward_iff _ (family_transport (rotation i) p hf)).mpr own))

theorem previous_missing (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 4) (missing : ¬Retains p (addSector i 3)) :
    ¬(owners ((rotation i).pullPacking p) 7).Inside 2 (113/50) := by
  have previous : ¬Forward ((rotation 3).pullPacking ((rotation i).pullPacking p)) :=
    fun own => missing ((forward_composed_iff p hf i 3).mpr own)
  change ¬(owners ((rotation 3).pullPacking ((rotation i).pullPacking p)) 4).Inside (87/50) 2 at previous
  rw [owners_transport (rotation 3) ((rotation i).pullPacking p)
    (family_transport (rotation i) p hf) 4] at previous
  norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullY] at previous
  exact previous

theorem next_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 4) (point : Crosspoint ((rotation (addSector i 1)).pullPacking p)) :
    (owners ((rotation i).pullPacking p) 5).Inside 2 (3/2) :=
  next_crosspoint _ (family_transport (rotation i) p hf) (crosspoint_composed p hf i 1 point)

theorem opposite_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 4) (point : Crosspoint ((rotation (addSector i 2)).pullPacking p)) :
    (owners ((rotation i).pullPacking p) 6).Inside (5/2) 2 := by
  have own := crosspoint_composed p hf i 2 point
  change (owners ((rotation 2).pullPacking ((rotation i).pullPacking p)) 4).Inside (3/2) 2 at own
  rw [owners_transport (rotation 2) ((rotation i).pullPacking p)
    (family_transport (rotation i) p hf) 4] at own
  norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullX,inside_pullY] at own
  exact own

theorem Frames.positive_points (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (d : Frames p) :
    ∀ i,Positive d i→Crosspoint ((rotation i).pullPacking p) :=
  positive_crosspoints p hf hb h d.square d.frame d.canonical

/-- Every nonpositive-to-positive edge has exactly the stated strict
forward memberships. All four retaining/missing combinations are
handled by actual same-wall or retaining-edge arguments. -/
theorem signed_edge (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (d : Frames p) (i : Fin 4)
    (negative : ¬Positive d i) (positive : Positive d (addSector i 1)) :
    Retains p i ∧ ¬Retains p (addSector i 1) := by
  classical
  let p' := (rotation i).pullPacking p
  have family' := family_transport (rotation i) p hf
  have context := rotation_context p hf hb i
  have ordinary := Ordinary.rotated p hf h i
  have cn := d.nonpositive_normal i negative
  have dn := d.positive_normal (addSector i 1) positive
  have df := rotated_frame p hf i 1 _ (d.frame (addSector i 1))
  have current : Retains p i := by
    by_contra missing
    by_cases next : Retains p (addSector i 1)
    · exact C1092MPPMNegativeMissingPositiveActual.successor_retaining_impossible
        p' family' context ordinary (d.square i) (d.frame i) cn missing
        (d.square (addSector i 1)) df dn positive (next_retained p hf i next)
    · exact C1092MPPMPositiveMissingLeftCenter.negative_missing_successor_missing_impossible
        p' family' context ordinary (d.square i) (d.frame i) cn
        (d.square (addSector i 1)) df dn missing (next_missing p hf i next)
  refine ⟨current,?_⟩
  intro next
  exact C1092MPPMNegativeOwnedPositiveActual.retaining_edge_impossible
    p' family' context ordinary (d.square i) (d.frame i) cn current
    (d.square (addSector i 1)) df dn positive (next_retained p hf i next)

theorem adjacent_missing (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (d : Frames p) (i : Fin 4)
    (negative : ¬Positive d i) (nextNegative : ¬Positive d (addSector i 1))
    (missing : ¬Retains p i) (nextMissing : ¬Retains p (addSector i 1)) : False :=
  C1092MPPMMissingNegativeCenters.adjacent_missing_impossible ((rotation i).pullPacking p)
    (family_transport (rotation i) p hf) (rotation_context p hf hb i) (Ordinary.rotated p hf h i)
    (d.square i) (d.frame i) (d.nonpositive_normal i negative)
    (d.square (addSector i 1)) (rotated_frame p hf i 1 _ (d.frame (addSector i 1)))
    (d.nonpositive_normal (addSector i 1) nextNegative) missing (next_missing p hf i nextMissing)

theorem three_retaining (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (d : Frames p) (i : Fin 4)
    (negative : ¬Positive d i) (nextNegative : ¬Positive d (addSector i 1))
    (lastNegative : ¬Positive d (addSector i 2))
    (own : Retains p i) (nextOwn : Retains p (addSector i 1))
    (lastOwn : Retains p (addSector i 2)) : False :=
  C1092MPPMAllNonpositive.actual_three_retaining_impossible ((rotation i).pullPacking p)
    (family_transport (rotation i) p hf) (rotation_context p hf hb i) (Ordinary.rotated p hf h i)
    (d.square i) (d.frame i) (d.nonpositive_normal i negative)
    (d.square (addSector i 1)) (rotated_frame p hf i 1 _ (d.frame (addSector i 1)))
    (d.nonpositive_normal (addSector i 1) nextNegative)
    (d.square (addSector i 2)) (rotated_frame p hf i 2 _ (d.frame (addSector i 2)))
    (d.nonpositive_normal (addSector i 2) lastNegative) own
    (forward_composed p hf i 1 nextOwn) (forward_composed p hf i 2 lastOwn)

theorem positive_sandwich (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (d : Frames p) (i : Fin 4)
    (previousPositive : Positive d (addSector i 3)) (negative : ¬Positive d i)
    (positive : Positive d (addSector i 1))
    (own : Retains p i) (missing : ¬Retains p (addSector i 1)) : False :=
  C1092MPPMOnePositive.positive_sandwich_impossible ((rotation i).pullPacking p)
    (family_transport (rotation i) p hf) (rotation_context p hf hb i) (Ordinary.rotated p hf h i)
    (d.square i) (d.frame i) (d.nonpositive_normal i negative) own
    (d.square (addSector i 3)) (rotated_frame p hf i 3 _ (d.frame (addSector i 3)))
    (d.positive_normal (addSector i 3) previousPositive) previousPositive
    (d.square (addSector i 1)) (rotated_frame p hf i 1 _ (d.frame (addSector i 1)))
    (d.positive_normal (addSector i 1) positive) positive (next_missing p hf i missing)
    (next_point p hf i (d.positive_points p hf hb h _ positive))

theorem missing_before_positive (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (d : Frames p) (i : Fin 4)
    (previousNegative : ¬Positive d (addSector i 3)) (previousMissing : ¬Retains p (addSector i 3))
    (negative : ¬Positive d i) (own : Retains p i)
    (positive : Positive d (addSector i 1)) (missing : ¬Retains p (addSector i 1)) : False :=
  C1092MPPMOnePositive.missing_predecessor_positive_impossible ((rotation i).pullPacking p)
    (family_transport (rotation i) p hf) (rotation_context p hf hb i) (Ordinary.rotated p hf h i)
    (d.square i) (d.frame i) (d.nonpositive_normal i negative) own
    (d.square (addSector i 3)) (rotated_frame p hf i 3 _ (d.frame (addSector i 3)))
    (d.nonpositive_normal (addSector i 3) previousNegative) (previous_missing p hf i previousMissing)
    (d.square (addSector i 1)) (rotated_frame p hf i 1 _ (d.frame (addSector i 1)))
    (d.positive_normal (addSector i 1) positive) positive (next_missing p hf i missing)
    (next_point p hf i (d.positive_points p hf hb h _ positive))

theorem missing_before_retaining (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (d : Frames p) (i : Fin 4)
    (previousNegative : ¬Positive d (addSector i 3)) (previousMissing : ¬Retains p (addSector i 3))
    (negative : ¬Positive d i) (own : Retains p i)
    (nextNegative : ¬Positive d (addSector i 1)) (nextOwn : Retains p (addSector i 1))
    (lastPositive : Positive d (addSector i 2)) : False :=
  C1092MPPMOnePositive.missing_predecessor_retaining_impossible ((rotation i).pullPacking p)
    (family_transport (rotation i) p hf) (rotation_context p hf hb i) (Ordinary.rotated p hf h i)
    (d.square i) (d.frame i) (d.nonpositive_normal i negative) own
    (d.square (addSector i 3)) (rotated_frame p hf i 3 _ (d.frame (addSector i 3)))
    (d.nonpositive_normal (addSector i 3) previousNegative) (previous_missing p hf i previousMissing)
    (d.square (addSector i 1)) (rotated_frame p hf i 1 _ (d.frame (addSector i 1)))
    (d.nonpositive_normal (addSector i 1) nextNegative) (next_retained p hf i nextOwn)
    (opposite_point p hf i (d.positive_points p hf hb h _ lastPositive))

theorem positive_before_retaining (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (d : Frames p) (i : Fin 4)
    (previousPositive : Positive d (addSector i 3))
    (negative : ¬Positive d i) (own : Retains p i)
    (nextNegative : ¬Positive d (addSector i 1)) (nextOwn : Retains p (addSector i 1))
    (lastPositive : Positive d (addSector i 2)) : False :=
  C1092MPPMOnePositive.positive_predecessor_retaining_impossible ((rotation i).pullPacking p)
    (family_transport (rotation i) p hf) (rotation_context p hf hb i) (Ordinary.rotated p hf h i)
    (d.square i) (d.frame i) (d.nonpositive_normal i negative) own
    (d.square (addSector i 3)) (rotated_frame p hf i 3 _ (d.frame (addSector i 3)))
    (d.positive_normal (addSector i 3) previousPositive) previousPositive
    (d.square (addSector i 1)) (rotated_frame p hf i 1 _ (d.frame (addSector i 1)))
    (d.nonpositive_normal (addSector i 1) nextNegative) (next_retained p hf i nextOwn)
    (opposite_point p hf i (d.positive_points p hf hb h _ lastPositive))

end
#print axioms signed_edge
#print axioms missing_before_retaining
end N12Compact.C1092MPPMOrdinaryCycle
