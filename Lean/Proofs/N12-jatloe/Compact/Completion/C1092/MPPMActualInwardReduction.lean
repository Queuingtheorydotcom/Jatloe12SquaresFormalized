import Compact.Completion.C1092.MPPMActualInwardMissingEnds
import Compact.Completion.C1092.MPPMActualInwardFar
import Compact.Completion.C1092.MPPMActualInwardOIOI

/-! Exhaustive original-family inward reduction. Ordinary means actual
membership of the complete ordinary pair; the inward alternative is
used only after that pair has been excluded. Center and outer-G ties
are in the omitted branches. Every local support profile is produced
from the same original packing. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualInward
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMCentralCover C1092MPPMInwardFinal C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

theorem opposite_nonordinary (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) : ¬NorthOrdinary p := by
  intro ordinary
  by_cases center : (owners p 4).Inside 2 2
  · obtain ⟨C,c,cp,canonical⟩ := canonical_frame p 4
    have negative := centered_sign p hf hb inward nonordinary center C c canonical
    have cn : Normal C.c (-C.s) := ⟨by linarith only [negative],
      by simpa only [abs_of_neg negative] using canonical,by nlinarith only [C.unit_normal]⟩
    exact centered_far p hf hb inward nonordinary center ordinary.1 C c cn negative
  · have outer := missing_center_outer p hf hb inward nonordinary center
    exact missing_outer_far p hf hb inward nonordinary outer center ordinary.1

theorem opposite_inward (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) : NorthInward p := by
  rcases north_cover p hf hb with ordinary|north
  · exact False.elim (opposite_nonordinary p hf hb inward nonordinary ordinary)
  · exact north

theorem north_missing_outer (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : NorthInward p) (nonordinary : ¬NorthOrdinary p)
    (missing : ¬(owners p 6).Inside 2 2) : (owners p 6).Inside 3 (12/5) := by
  have inward' := (half_inward p hf).mpr inward
  have nonordinary' : ¬Ordinary (owners (halfTurn.pullPacking p) 4) :=
    fun own => nonordinary ((half_ordinary p hf).mp own)
  have missing' : ¬(owners (halfTurn.pullPacking p) 4).Inside 2 2 := by
    rw [half_inside p hf]
    norm_num [halfTurn,ownerAction,ownerSwap,ownerX,ownerY]
    exact missing
  have outer := missing_center_outer (halfTurn.pullPacking p) (family_transport halfTurn p hf)
    (half_context p hf hb) inward' nonordinary' missing'
  rw [half_inside p hf] at outer
  norm_num [halfTurn,ownerAction,ownerSwap,ownerX,ownerY] at outer
  exact outer

/-- A centered inward owner forces its opposite into the genuine
missing-center/G-owned profile and is then excluded by the first OIOI
ending. Its own outer G is never assumed. -/
theorem centered_nonordinary_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (center : (owners p 4).Inside 2 2) : False := by
  have north := opposite_inward p hf hb inward nonordinary
  have northNonordinary := opposite_nonordinary p hf hb inward nonordinary
  have northMissing : ¬(owners p 6).Inside 2 2 :=
    fun own => owners_disjoint p hf 4 6 (by decide) _ _ ⟨center,own⟩
  have outer := north_missing_outer p hf hb north northNonordinary northMissing
  obtain ⟨C,c,cp,canonical⟩ := canonical_frame p 4
  have negative := centered_sign p hf hb inward nonordinary center C c canonical
  have cn : Normal C.c (-C.s) := ⟨by linarith only [negative],
    by simpa only [abs_of_neg negative] using canonical,by nlinarith only [C.unit_normal]⟩
  exact centered_oioi p hf hb inward nonordinary center north northNonordinary outer C c cn negative

theorem nonordinary_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) : False := by
  by_cases center : (owners p 4).Inside 2 2
  · exact centered_nonordinary_impossible p hf hb inward nonordinary center
  · have outer := missing_center_outer p hf hb inward nonordinary center
    have north := opposite_inward p hf hb inward nonordinary
    have northNonordinary := opposite_nonordinary p hf hb inward nonordinary
    by_cases northCenter : (owners p 6).Inside 2 2
    · apply centered_nonordinary_impossible (halfTurn.pullPacking p)
        (family_transport halfTurn p hf) (half_context p hf hb)
        ((half_inward p hf).mpr north)
        (fun own => northNonordinary ((half_ordinary p hf).mp own))
      rw [half_inside p hf]
      norm_num [halfTurn,ownerAction,ownerSwap,ownerX,ownerY]
      exact northCenter
    · have northOuter := north_missing_outer p hf hb north northNonordinary northCenter
      exact opposed_missing_oioi p hf hb inward nonordinary outer center
        north northNonordinary northOuter northCenter

theorem southwest_ordinary (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) : Ordinary (owners p 4) := by
  by_contra missing
  rcases C1092MPPMActualNonordinary.ordinary_or_inward p hf hb with ordinary|inward
  · exact missing ordinary
  · exact nonordinary_impossible p hf hb inward missing

/-- All four original central owners have their actual ordinary pairs.
Each sector is proved by a simultaneous packing rotation, preserving
the complete mppm wall context and every original owner. -/
theorem ordinary (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) : C1092MPPMActualPositiveOrder.Ordinary p := by
  have sector (i : Fin 4) := southwest_ordinary
    ((C1092MPPMActualPositiveOrder.rotation i).pullPacking p)
    (family_transport _ p hf) (C1092MPPMActualPositiveOrder.rotation_context p hf hb i)
  have se := sector 1
  have ne := sector 2
  have nw := sector 3
  rw [owners_transport (C1092MPPMActualPositiveOrder.rotation 1) p hf 4] at se
  rw [owners_transport (C1092MPPMActualPositiveOrder.rotation 2) p hf 4] at ne
  rw [owners_transport (C1092MPPMActualPositiveOrder.rotation 3) p hf 4] at nw
  norm_num [Ordinary,C1092MPPMActualPositiveOrder.rotation,ownerAction,ownerSwap,ownerX,ownerY,
    Transform.pull,inside_pullSwap,inside_pullX,inside_pullY] at se ne nw
  exact ⟨southwest_ordinary p hf hb,⟨se.2,se.1⟩,ne,⟨nw.2,nw.1⟩⟩

end
#print axioms nonordinary_impossible
#print axioms ordinary
end N12Compact.C1092MPPMActualInward
