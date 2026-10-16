import Compact.Completion.C1092.TwoFifthsData
import Compact.Completion.C1092.MMMP.TopOrigin
import Compact.Completion.C1092.MMMP.NortheastActualSign
import Compact.Completion.C1092.MMMP.RightFar
import Compact.Completion.OtherCases.TopOnlyLeftPoint

/-! The unconditional northeast portion of the two-fifths entrance.
The four faces are those of the same actual Q6.  The sharp point is
NORTHEAST-LOWER-TIP Theorem 1, and the lower half-angle is TOP-CAP §3.
The upper half-angle is deliberately not asserted here: its two completed
W/E/N support arguments are separate producers. -/
namespace N12Compact.C1092MMMPTwoFifthsEntrance
open S12 S12Pilot C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MMMPEntrance C1092MMMPOrigins
open C1092MMMPPointCore Completion.OtherCases
set_option Elab.async false

structure NortheastCore (N : OpenSquare) : Prop where
  side : 1<N.side
  cosine : 0<N.c
  sine : 0<N.s
  canonical : N.s≤N.c
  halfLow : 1+N.c<4*N.s
  lowerU : (2/5)*N.s≤N.loU
  lowerV : (2/5)*N.c-N.s≤N.loV
  upperU : N.loU+N.side≤N.c+N.s
  upperV : N.loV+N.side≤N.c
  marker : N.Inside (7/20) (7/20)
  top : N.Inside (2/5) 1
  sharp : N.Inside (47/100) (3/25)

theorem northeast_faces (N : OpenSquare) (side : 1<N.side)
    (cp : 0<N.c) (sp : 0<N.s) (order : N.s≤N.c)
    (marker : N.Inside (7/20) (7/20))
    (nearTop : N.Inside (13/50) 1) (farTop : N.Inside (2/5) 1)
    (missingNear : ¬N.Inside 0 (13/50))
    (missingInner : ¬N.Inside 0 (2/5))
    (missingOrigin : ¬N.Inside 0 1) (missingCorner : ¬N.Inside 1 1)
    (missingRightNear : ¬N.Inside 1 (13/50))
    (missingRightFar : ¬N.Inside 1 (2/5)) : NortheastCore N := by
  have faces := TopOnlyLeftPoint.positive_faces N side cp sp.le order
    marker nearTop missingNear missingOrigin missingCorner missingRightNear
  have cu : N.c≤1 := by nlinarith only [N.unit_normal,sq_nonneg N.s,cp]
  have lowerU : (2/5)*N.s≤N.loU := by
    apply le_of_not_gt
    intro low
    apply missingInner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,marker.2.1,faces.2.2.2,side,nearTop.2.2.2,cp,sp,order,cu]
  have lowerV : (2/5)*N.c-N.s≤N.loV := by
    apply le_of_not_gt
    intro low
    apply missingRightFar
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,marker.1,lowerU,side,cu,farTop.2.2.2,cp,sp,order]
  have span : 1<(3/5)*N.c+N.s := by
    linarith only [lowerV,faces.2.2.2,side]
  have half := SharpPointScalars.half_lower N.c N.s (3/5) cp sp.le order
    N.unit_normal span
  have quarter : 1/4<C1092WallProfileScalars.half N.c N.s := by
    linarith only [half]
  have halfLow : 1+N.c<4*N.s := by
    have scaled := (lt_div_iff₀ (show 0<1+N.c by linarith only [cp])).mp quarter
    linarith only [scaled]
  have shortUV : (22/25)*N.c+(47/100)*N.s<1 := by
    nlinarith only [N.unit_normal,
      sq_nonneg ((47/100)*N.c-(22/25)*N.s),
      sq_nonneg ((22/25)*N.c+(47/100)*N.s-1)]
  have shortVU := CommonCases.OutwardScalars.increasing_projection
    N.c N.s (53/100) (22/25) cp sp.le order N.unit_normal
    (by norm_num) (by norm_num) (by norm_num)
  have sharp : N.Inside (47/100) (3/25) := by
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [faces.2.2.1,faces.2.2.2,lowerU,lowerV,
        side,shortUV,shortVU,cp,sp,order,cu]
  exact ⟨side,cp,sp,order,halfLow,lowerU,lowerV,
    faces.2.2.1,faces.2.2.2,marker,farTop,sharp⟩

theorem northeast_core (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (N : OpenSquare) (np : C1092MMMPNortheastActualSign.PositiveActual p N) :
    NortheastCore N := by
  have side : 1<N.side := by rw [np.side]; exact side_gt p 6
  have cp : 0<N.c := by linarith only [(normal_bounds np.normal).1]
  have mark : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have corner : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have inner : (owners p 7).Inside 2 (12/5) := by
    have h := inside_segment (owners p 7) 2 2 2 (5/2) (4/5)
      (northwest_center p hf hb) (northwest_north p hf hb) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  apply northeast_faces N side cp np.positive np.normal.2.1
  · apply (np.actual _ _).mpr; norm_num; exact mark
  · apply (np.actual _ _).mpr; norm_num; exact (northeast_pair p hf hb).2
  · apply (np.actual _ _).mpr; norm_num; exact (northeast_pair p hf hb).1
  · intro own
    have h := (np.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 6 7 (by decide) _ _ ⟨h,(northwest_pair p hf hb).1⟩
  · intro own
    have h := (np.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 6 7 (by decide) _ _ ⟨h,inner⟩
  · intro own
    have h := (np.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 6 11 (by decide) _ _ ⟨h,C1092MMMPTopOrigin.point p hf hb⟩
  · intro own
    have h := (np.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 6 2 (by decide) _ _ ⟨h,corner⟩
  · intro own
    have h := (np.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 6 10 (by decide) _ _ ⟨h,(wall_auxiliaries p hb).2.2.1⟩
  · intro own
    have h := (np.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 6 10 (by decide) _ _ ⟨h,C1092MMMPRightFar.point p hf hb⟩

/-- The literal new strict point, with no branch or extra point premise. -/
theorem northeast_sharp (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp) :
    (owners p 6).Inside (247/100) (53/25) := by
  obtain ⟨N,np⟩ := C1092MMMPNortheastActualSign.exists_positive p hf hb
  have h := (np.actual _ _).mp (northeast_core p hf hb N np).sharp
  norm_num at h
  exact h

theorem NortheastCore.complete {N : OpenSquare} (h : NortheastCore N)
    (halfHigh : 3*N.s≤1+N.c) : C1092TwoFifths.Northeast N :=
  ⟨h.side,h.cosine,h.sine,h.canonical,h.halfLow,halfHigh,h.lowerU,h.lowerV,
    h.upperU,h.upperV,h.marker,h.top,h.sharp⟩

#print axioms northeast_core
#print axioms northeast_sharp
end N12Compact.C1092MMMPTwoFifthsEntrance
