import Compact.Completion.C1092.MMMP.TwoFifthsEntranceFloor
import Compact.Completion.C1092.MMMP.InwardOuterArmHalfpoint
import Compact.Completion.CommonCases.OriginalOwners

/-! Actual Q5 entrance for both truth values of G8. The old inward
chart is inverted by three physical quarter-turns, retaining its frame
components. The bar used in the closure-vertex proof is the whole
strict segment of the one original Q9, derived from its bottom origin.
No angle bound is transferred from the G8-absent branch to the owned one. -/
namespace N12Compact.C1092MMMPTwoFifthsEntrance
open S12 S12Pilot C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MMMPEntrance C1092MMMPOrigins
open C1092MMMPPointCore C1092MMMPEndingAxes
set_option Elab.async false

structure SoutheastActual (p : NormalizedPacking) (E : OpenSquare) : Prop where
  side : E.side=(owners p 5).side
  actual : ∀ x y,E.Inside x y↔(owners p 5).Inside (2+x) (2+y)
  normal : Normal E.c E.s
  positive : 0<E.s

private noncomputable def inverseChart (C : OpenSquare) : OpenSquare :=
  clockwise (clockwise (clockwise C))

private theorem inverse_inside (C : OpenSquare) (x y : ℝ) :
    (inverseChart C).Inside x y↔C.Inside (-y) x := by
  simp only [inverseChart,inside_clockwise,neg_neg]

private theorem inverse_actual (p : NormalizedPacking) (C : OpenSquare)
    (cp : C1092MMMPSoutheastSign.PositiveActual p C) :
    SoutheastActual p (inverseChart C) where
  side := cp.side
  actual := by
    intro x y
    rw [inverse_inside,cp.actual]
    simp only [sub_neg_eq_add]
  normal := cp.normal
  positive := cp.positive

private theorem missing_outer_small (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (near : (owners p 10).Inside 3 (87/50))
    (missing : ¬(owners p 5).Inside 3 (8/5))
    (C : OpenSquare) (cp : C1092MMMPSoutheastSign.PositiveActual p C) :
    C.s<21/100 ∧ 97/100<C.c := by
  have inward := C1092MMMPSoutheastSign.inward_pair p hf hb near
  have origin := C1092MMMPInwardOuterArmHalfpoint.bottom_origin_of_near p hf hb near
  have bottom := C1092MMMPBottomPair.pair p hf hb
  have mark : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  have bound := C1092MMMPPositiveInwardHalfangle.small_angle_of_bar C
    (by rw [cp.side]; exact side_gt p 5) cp.normal
    (by apply (cp.actual _ _).mpr; norm_num; exact mark)
    (by apply (cp.actual _ _).mpr; norm_num; exact inward.2)
    (by apply (cp.actual _ _).mpr; norm_num; exact inward.1)
    (by
      intro own
      have h := (cp.actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 5 7 (by decide) _ _ ⟨h,northwest_center p hf hb⟩)
    (by
      intro own
      have h := (cp.actual _ _).mp own
      norm_num at h
      exact missing h)
    (by
      intro y low high own
      have h := (cp.actual _ _).mp own
      norm_num at h
      have foreign : (owners p 9).Inside (2+y) 1 :=
        CommonCases.OriginalOwners.horizontal_segment _ _ _ _ _ origin bottom.1
          (by norm_num) (by linarith only [low]) (by linarith only [high])
      exact owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,foreign⟩)
  exact bound.2

theorem southeast_profile (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (near : (owners p 10).Inside 3 (87/50)) :
    ∃ E : OpenSquare,SoutheastActual p E ∧ C1092TwoFifths.Southeast E := by
  classical
  obtain ⟨C,cp⟩ := C1092MMMPSoutheastSign.exists_positive p hf hb near
  let E := inverseChart C
  have ep : SoutheastActual p E := inverse_actual p C cp
  have side : 1<E.side := by rw [ep.side]; exact side_gt p 5
  have cosine : 0<E.c := by linarith only [(normal_bounds ep.normal).1]
  have sine : 0<E.s := ep.positive
  have order : E.s≤E.c := ep.normal.2.1
  have inward := C1092MMMPSoutheastSign.inward_pair p hf hb near
  have marker : E.Inside (7/20) (-7/20) := by
    apply (ep.actual _ _).mpr
    norm_num
    simpa [S12.marker] using marker_point p hf 5 9 (by decide +kernel)
  have inner : E.Inside 0 (-13/50) := by
    apply (ep.actual _ _).mpr; norm_num; exact inward.1
  have forward : E.Inside (13/50) 0 := by
    apply (ep.actual _ _).mpr; norm_num; exact inward.2
  have missingOrigin : ¬E.Inside 0 0 := by
    intro own
    have h := (ep.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 5 7 (by decide) _ _ ⟨h,northwest_center p hf hb⟩
  have missingNear : ¬E.Inside 1 (-13/50) := by
    intro own
    have h := (ep.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨h,near⟩
  have missingSharp : ¬E.Inside (47/100) (3/25) := by
    intro own
    have h := (ep.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 5 6 (by decide) _ _ ⟨h,northeast_sharp p hf hb⟩
  have caps := southeast_caps E side cosine sine order marker inner forward
    missingOrigin missingNear
  let B := (owners p 9).translated 2 2
  have bar : ∀ x : ℝ,0≤x → x≤2/5 → B.Inside x (-1) := by
    intro x low high
    apply (inside_translated_iff _ _ _ _ _).mpr
    norm_num
    exact CommonCases.OriginalOwners.horizontal_segment _ _ _ _ _
      (C1092MMMPInwardOuterArmHalfpoint.bottom_origin_of_near p hf hb near)
      (C1092MMMPBottomPair.pair p hf hb).1 (by norm_num)
      (by linarith only [low]) (by linarith only [high])
  have apart : ∀ x y,¬(E.Inside x y ∧ B.Inside x y) := by
    intro x y own
    exact owners_disjoint p hf 5 9 (by decide) _ _
      ⟨(ep.actual x y).mp own.1,(inside_translated_iff _ _ _ _ _).mp own.2⟩
  refine ⟨E,ep,?_⟩
  by_cases outer : (owners p 5).Inside 3 (8/5)
  · have own : E.Inside 1 (-2/5) := by
      apply (ep.actual _ _).mpr; norm_num; exact outer
    have sharp := southeast_outer_cap E cosine sine order inner forward own missingSharp
    have floor := southeast_floor E B side cosine sine order sharp.2
      marker inner forward caps.1 caps.2 bar apart
    exact ⟨side,cosine,sine,
      southeast_outer_small E side cosine sine order caps.2 sharp.1 floor,
      inner,forward,caps.1,floor⟩
  · have bound := missing_outer_small p hf hb near outer C cp
    have small : E.s<21/100 := bound.1
    have close : 97/100<E.c := bound.2
    have floor := southeast_floor E B side cosine sine order
      (by linarith only [small]) marker inner forward caps.1 caps.2 bar apart
    exact ⟨side,cosine,sine,by linarith only [small,close],inner,forward,caps.1,floor⟩

#print axioms southeast_profile
end N12Compact.C1092MMMPTwoFifthsEntrance
