import Compact.Completion.C1092.MPPMMissingNegativeProfile
import Compact.Completion.C1092.MPPMActualCentralOrigin
import Compact.Completion.CommonCases.UnitCircleChord

/-! Literal original weak and strong missing-negative profile adapters.
The complete excluded bar is in one actual Q9. The weak profile requires
no preceding-origin omission; the strong adapter names that omission
without assigning the origin any owner. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMMissingNegativeProfile
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C977CornerCubic C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
set_option Elab.async false
noncomputable section

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem mark (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem actual_core (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) : Core C := by
  have half := missing_halfpoint p hf hb h.southwest.1 h.southwest.2 missing
  have corner : (owners p 0).Inside 1 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 0
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · apply (frame.actual _ _).mpr
    norm_num
    simpa [marker] using mark p hf 4 8 (by decide +kernel)
  · apply (frame.actual _ _).mpr; norm_num; exact h.southwest.1
  · apply (frame.actual _ _).mpr; norm_num; exact h.southwest.2
  · apply (frame.actual _ _).mpr; norm_num; exact half
  · intro own
    have original := (frame.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 4 0 (by decide) _ _ ⟨original,corner⟩
  · intro own
    have original := (frame.actual _ _).mp own
    norm_num at original
    exact missing original
  · intro x low high own
    have original := (frame.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 4 9 (by decide) _ _
      ⟨original,bottom_bar p hf hb h (2+x) (by linarith only [low]) (by linarith only [high])⟩

theorem actual_weak (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s)) : WeakFaces C := by
  apply weak_profile C (by rw [frame.side]; exact side_gt p 4) cn
    (actual_core p hf hb h missing C frame)
  intro own
  have original := (frame.actual _ _).mp own
  norm_num at original
  have foreign : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using mark p hf 8 12 (by decide +kernel)
  exact owners_disjoint p hf 4 8 (by decide) _ _ ⟨original,foreign⟩

theorem actual_strong (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (previous : ¬(owners p 4).Inside 1 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s)) : StrongFaces C := by
  apply strong_profile C (by rw [frame.side]; exact side_gt p 4) cn
    (actual_core p hf hb h missing C frame)
  intro own
  have original := (frame.actual _ _).mp own
  norm_num at original
  exact previous original

/-- Exact large-sine consequence at the strong profile endpoint. This
uses one closed circle-support comparison, not angle samples. -/
theorem StrongFaces.sine_lower (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c (-C.s)) (h : StrongFaces C) : 252/373≤-C.s := by
  apply le_of_not_gt
  intro low
  have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
  have support := CommonCases.UnitCircleChord.increasing
    (c:=275/373) (s:=252/373) (d:=C.c) (t:=-C.s) (A:=11/25) (B:=1)
    (by norm_num) cp.le (by norm_num) cn.2.2 (by norm_num) cn.1 low.le
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at support
  linarith only [side,h.widthU,support]

end
#print axioms actual_core
#print axioms actual_weak
#print axioms actual_strong
#print axioms StrongFaces.sine_lower
end N12Compact.C1092MPPMMissingNegativeProfile
