import Compact.Completion.C1092.MPPMPositiveOverlapScalars
import Compact.Completion.C1092.MPPMNonpositivePredecessor
import Compact.Completion.C1092.MMMP.NortheastNegativeFaces
import Compact.Completion.C1092.MMMMNegativeNeighbor
import Compact.Completion.C1092.RigidCharts
import S12.Convex

/-! The common point-only southeast calculation in the centered positive
chapters. No ordinary pair of C or preceding-origin omission is assumed.
The same actual C/E and all listed weak exclusions are retained. -/
namespace N12Compact.C1092MPPMCenteredPositive
open S12 S12Pilot C977CornerCubic C1092WallProfileScalars
set_option Elab.async false

structure Input (C E : OpenSquare) : Prop where
  marker : C.Inside (-7/20) (-7/20)
  northMarker : ¬C.Inside (-7/20) (7/20)
  center : C.Inside 0 0
  crosspoint : C.Inside (-1/2) 0
  inward : C.Inside 0 (-13/50)
  tip : C.Inside (-1/100) (-27/50)
  successorMarker : E.Inside (7/20) (-7/20)
  near : E.Inside (13/50) (-1)
  outer : E.Inside (2/5) (-1)
  halfpoint : E.Inside (1/2) (-1)
  shortWall : ¬E.Inside 1 (-39/100)
  bottomMarker : ¬E.Inside 0 (-543/500)
  corner : ¬E.Inside 1 (-1)
  rightOrigin : ¬E.Inside 1 0
  rightG : ¬E.Inside 1 (-2/5)
  apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)

theorem center_caps (C E : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (h : Input C E) :
    C.loU+C.side≤(7/20)*(C.c-C.s) ∧ C.loV+C.side≤(7/20)*(C.c+C.s) := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have capV : C.loV+C.side≤(7/20)*(C.c+C.s) := by
    apply le_of_not_gt; intro high; apply h.northMarker
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,h.marker.1,h.center.2.1,h.center.2.2.1,cp,cn.1,cn.2.1]
  refine ⟨?_,capV⟩
  apply le_of_not_gt; intro high
  have lowV : C.loV<-(7/20)*(C.c+C.s) := by
    linarith only [capV,side,cb.2.2.2.2.2]
  apply h.apart (7/20) (-7/20)
  refine ⟨⟨?_,?_,?_,?_⟩,h.successorMarker⟩ <;>
    linarith only [high,lowV,h.center.1,h.center.2.2.2,cp,cn.1,cn.2.1]

theorem lower_crosspoint (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (origin : C.Inside 0 0) (left : C.Inside (-1/2) 0)
    (cap : C.loV+C.side≤(7/20)*(C.c+C.s)) : C.Inside 0 (-1/2) := by
  have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
  have norm := C1092MPPMNonpositivePredecessor.norm_lt (17/20) (7/20)
    C.c C.s 1 C.unit_normal (by norm_num) (by norm_num)
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [origin.2.1,origin.2.2.2,left.1,cap,side,norm,cp,cn.1,cn.2.1]

theorem successor_negative (C E : OpenSquare) (side : 1<C.side)
    (same : C.side=E.side) (cn : Normal C.c C.s) (canonical : |E.s|≤E.c)
    (h : Input C E) : E.s<0 := by
  have bottom := lower_crosspoint C side cn h.center h.crosspoint (center_caps C E side cn h).2
  apply lt_of_not_ge
  intro sign
  let D := C1092RigidCharts.swap C
  let B := C1092RigidCharts.swap E
  have dActual (x y : ℝ) : D.Inside x y↔C.Inside y x := C1092RigidCharts.inside_swap C x y
  have bActual (x y : ℝ) : B.Inside x y↔E.Inside y x := C1092RigidCharts.inside_swap E x y
  have dn : Normal D.c (-D.s) := by
    change Normal C.c (-(-C.s)); simpa only [neg_neg] using cn
  have bn : Normal B.c (-B.s) := by
    change Normal E.c (-(-E.s))
    simpa only [neg_neg] using
      (show Normal E.c E.s from ⟨sign,by simpa only [abs_of_nonneg sign] using canonical,E.unit_normal⟩)
  have column : C.Inside 0 (-39/100) := by
    have point := inside_segment C 0 0 0 (-1/2) (39/50) h.center bottom (by norm_num) (by norm_num)
    norm_num at point
    exact point
  have faces := C1092MMMPNortheastNegativeFaces.faces B bn (by change 1<E.side; rwa [←same])
    ((bActual _ _).mpr h.successorMarker) ((bActual _ _).mpr h.near) ((bActual _ _).mpr h.outer)
    (fun own => h.apart _ _ ⟨column,(bActual _ _).mp own⟩)
    (fun own => h.shortWall ((bActual _ _).mp own))
    (fun own => h.bottomMarker ((bActual _ _).mp own))
    (fun own => h.corner ((bActual _ _).mp own))
    (fun own => h.apart _ _ ⟨bottom,(bActual _ _).mp own⟩)
  exact C1092MMMMNegativeNeighbor.impossible_faces D B side same dn bn
    ((dActual _ _).mpr h.center) ((dActual _ _).mpr h.crosspoint) ((dActual _ _).mpr h.marker)
    (fun own => h.northMarker ((dActual _ _).mp own))
    ((bActual _ _).mpr h.successorMarker) ((bActual _ _).mpr h.outer)
    (by linarith only [faces.lowerU]) faces.upperU (by linarith only [faces.upperV])
    (fun x y own => h.apart y x ⟨(dActual _ _).mp own.1,(bActual _ _).mp own.2⟩)

structure SuccessorFaces (E : OpenSquare) : Prop where
  lowerU : -(13/50)*E.s≤E.loU
  upperU : E.loU+E.side≤E.c-E.s
  lowerV : -(543/500)*E.c≤E.loV
  upperV : E.loV+E.side≤-E.s

theorem successor_faces (C E : OpenSquare) (side : 1<E.side)
    (en : Normal E.c (-E.s)) (h : Input C E) : SuccessorFaces E := by
  have eb := normal_bounds en
  have ep : 0<E.c := by linarith only [eb.1]
  have innerMissing : ¬E.Inside 0 (-13/50) := fun own => h.apart _ _ ⟨h.inward,own⟩
  have low : -(13/50)*E.s≤E.loU := by
    apply le_of_not_gt; intro low
    have highV : E.loV+E.side≤-(13/50)*E.c := by
      apply le_of_not_gt; intro high; apply innerMissing
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,high,h.successorMarker.2.1,h.outer.2.2.1,ep,en.1,en.2.1]
    have highU : E.loU+E.side≤E.c-E.s := by
      apply le_of_not_gt; intro high; apply h.corner
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [high,highV,side,h.outer.1,h.successorMarker.2.2.2,eb.2.1,ep,en.1,en.2.1]
    have lowU : -(543/500)*E.s≤E.loU := by
      apply le_of_not_gt; intro lowU; apply h.bottomMarker
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [lowU,highV,side,h.near.2.1,h.successorMarker.2.2.2,
          eb.2.1,ep,en.1,en.2.1]
    linarith only [lowU,highU,side,eb.2.1,en.1]
  have highV : E.loV+E.side≤-E.s := by
    apply le_of_not_gt; intro high
    have highU : E.loU+E.side≤E.c := by
      apply le_of_not_gt; intro highU; apply h.rightOrigin
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [highU,high,h.successorMarker.1,h.outer.2.2.1,ep,en.1,en.2.1]
    linarith only [low,highU,side,eb.2.1,en.1]
  have highU : E.loU+E.side≤E.c-E.s := by
    apply le_of_not_gt; intro high; apply h.corner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,highV,side,h.outer.1,h.successorMarker.2.2.2,eb.2.1,ep,en.1,en.2.1]
  have lowV : -(543/500)*E.c≤E.loV := by
    apply le_of_not_gt; intro low
    have lowU : -(543/500)*E.s≤E.loU := by
      apply le_of_not_gt; intro lowU; apply h.bottomMarker
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,lowU,h.near.2.1,h.successorMarker.2.2.2,ep,en.1,en.2.1]
    linarith only [lowU,highU,side,eb.2.1,en.1]
  exact ⟨low,highU,lowV,highV⟩

#print axioms successor_negative
#print axioms successor_faces
end N12Compact.C1092MPPMCenteredPositive
