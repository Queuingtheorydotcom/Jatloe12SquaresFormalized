import Compact.Completion.C1092.MMMP.NortheastPositiveCentral
import Compact.Completion.C1092.MMMMNegativeNeighbor
import Compact.Geometry.ClosedFrames

/-! Full central-angle cover for the MMMP northeast sign. The actual paired
corner and wall marker replace any premature top-origin assumption. -/
namespace N12Compact.C1092MMMPNortheastSign
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

theorem nonpositive_impossible (C B : OpenSquare) (side : 1<C.side) (same : C.side=B.side)
    (bn : Normal B.c (-B.s))
    (origin : C.Inside 0 0) (left : C.Inside (-1/2) 0) (bottom : C.Inside 0 (-1/2))
    (central : C.Inside (-7/20) (-7/20))
    (missingG : ¬C.Inside (7/20) (-7/20)) (missingM : ¬C.Inside (-7/20) (7/20))
    (missingF : ¬C.Inside (-39/100) (-1))
    (marker : B.Inside (-7/20) (7/20))
    (H1 : B.Inside (-1) (13/50)) (H2 : B.Inside (-1) (2/5))
    (I : ¬B.Inside (-39/100) 0) (J : ¬B.Inside (-39/100) 1)
    (W : ¬B.Inside (-543/500) 0) (K : ¬B.Inside (-1) 1)
    (A : ¬B.Inside (-1/2) 0)
    (apart : ∀ x y, ¬(C.Inside x y ∧ B.Inside x y)) : False := by
  classical
  have sideB : 1<B.side := by rwa [←same]
  have faces := C1092MMMPNortheastNegativeFaces.faces B bn sideB marker H1 H2 I J W K A
  obtain ⟨R,rc,rs,rside,rinside,_⟩ := ClosedFrames.canonical_frame C
  have sideR : 1<R.side := by rwa [rside]
  have sameR : R.side=B.side := rside.trans same
  have originR := (rinside _ _).mpr origin
  have centralR := (rinside _ _).mpr central
  have missingR : ¬R.Inside (7/20) (-7/20) := fun own => missingG ((rinside _ _).mp own)
  have apartR : ∀ x y, ¬(R.Inside x y ∧ B.Inside x y) :=
    fun x y own => apart x y ⟨(rinside x y).mp own.1,own.2⟩
  by_cases sign : 0≤R.s
  · have dn : Normal R.c R.s := ⟨sign,by simpa only [abs_of_nonneg sign] using rs,R.unit_normal⟩
    exact C1092MMMPNortheastPositiveCentral.impossible R B sideR sameR dn bn originR
      ((rinside _ _).mpr left) centralR missingR
      (fun own => missingM ((rinside _ _).mp own))
      (fun own => missingF ((rinside _ _).mp own)) marker H2 faces apartR
  · have sn : R.s≤0 := by exact (lt_of_not_ge sign).le
    have dn : Normal R.c (-R.s) := ⟨by linarith only [sn],
      by simpa only [abs_of_nonpos sn] using rs,by nlinarith only [R.unit_normal]⟩
    exact C1092MMMMNegativeNeighbor.impossible_faces R B sideR sameR dn bn originR
      ((rinside _ _).mpr bottom) centralR missingR marker H2
      (by linarith only [faces.lowerU]) faces.upperU (by linarith only [faces.upperV]) apartR

/-- This is a local complete-sign theorem about the given actual square B.
It is not a whole MMMP BranchEnding. -/
theorem positive (C B : OpenSquare) (side : 1<C.side) (same : C.side=B.side)
    (bp : 0<B.c) (canonical : |B.s|≤B.c)
    (origin : C.Inside 0 0) (left : C.Inside (-1/2) 0) (bottom : C.Inside 0 (-1/2))
    (central : C.Inside (-7/20) (-7/20))
    (missingG : ¬C.Inside (7/20) (-7/20)) (missingM : ¬C.Inside (-7/20) (7/20))
    (missingF : ¬C.Inside (-39/100) (-1))
    (marker : B.Inside (-7/20) (7/20))
    (H1 : B.Inside (-1) (13/50)) (H2 : B.Inside (-1) (2/5))
    (I : ¬B.Inside (-39/100) 0) (J : ¬B.Inside (-39/100) 1)
    (W : ¬B.Inside (-543/500) 0) (K : ¬B.Inside (-1) 1)
    (A : ¬B.Inside (-1/2) 0)
    (apart : ∀ x y, ¬(C.Inside x y ∧ B.Inside x y)) : 0<B.s := by
  apply lt_of_not_ge
  intro sign
  have bn : Normal B.c (-B.s) := ⟨by linarith only [sign],
    by simpa only [abs_of_nonpos sign] using canonical,by nlinarith only [B.unit_normal]⟩
  exact nonpositive_impossible C B side same bn origin left bottom central
    missingG missingM missingF marker H1 H2 I J W K A apart

#print axioms nonpositive_impossible
#print axioms positive
end N12Compact.C1092MMMPNortheastSign
