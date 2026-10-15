import Compact.Geometry.CornerSingletonPair
import Compact.Geometry.LeftSingletonWallSeparation
import Compact.Geometry.CornerWallCycle
import Compact.Geometry.CornerWallMarkerShared
import Compact.Geometry.CornerWallMarkerMixed
import Compact.Geometry.CornerWallMarkerOtherMixed
import Compact.Geometry.CornerWallMarkerLongitudinalBounds
import Compact.Geometry.CornerWallMarkerNegativeLarge
import Compact.Geometry.CornerWallMarkerNegativeMixed

/-! Actual-square negative-wall cycle with genuine marker faces.
Every signed canonical L and every surviving separator are assembled
here. The outer angle order remains explicit: its missing-central-left-
point entrance is not yet proved from original packing assumptions.
Source only, uncompiled. -/
namespace N12Compact.CornerWallMarkerCycle

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds CornerWallCycleBounds

structure Data (O L W : OpenSquare) (t : ℝ) : Prop where
  on : Normal O.c O.s
  lc : 0<L.c
  canonical : |L.s|≤L.c
  wn : Normal W.c t
  ws : W.s=-t
  side : 1<L.side
  sameOL : O.side=L.side
  sameLW : L.side=W.side
  oBox : InsideContainer O
  lBox : InsideContainer L
  wBox : InsideContainer W
  oMarker : O.Inside 1 (457/500)
  oNear : O.Inside (28/25) 1
  oFar : O.Inside (187/100) (19/25)
  lMarker : L.Inside (457/500) 1
  corner : L.Inside 1 1
  lFar : L.Inside (19/25) (187/100)
  wMarker : W.Inside (457/500) 2
  oCap : O.loU+O.side≤2*O.c+(457/500)*O.s
  bottomFace : CornerWallMarkerMixedBounds.boundary O.c O.s<O.loV+O.side
  northwest : W.loU+W.side≤(33/20)*W.c-(47/20)*t
  top : W.loV+W.side≤(457/500)*t+3*W.c
  order : O.s≤t
  small : t≤3/5
  wide : 4/5≤W.c
  olApart : ∀ x y, ¬(O.Inside x y ∧ L.Inside x y)
  lwApart : ∀ x y, ¬(L.Inside x y ∧ W.Inside x y)

theorem positive_normal {O L W : OpenSquare} {t : ℝ}
    (data : Data O L W t) (sign : 0≤L.s) : Normal L.c L.s := by
  refine ⟨sign,?_,L.unit_normal⟩
  simpa only [abs_of_nonneg sign] using data.canonical

theorem negative_normal {O L W : OpenSquare} {t : ℝ}
    (data : Data O L W t) (sign : L.s≤0) : Normal L.c (-L.s) := by
  refine ⟨neg_nonneg.mpr sign,?_,?_⟩
  · simpa only [abs_of_nonpos sign] using data.canonical
  · nlinarith only [L.unit_normal]

theorem bottom_choices {O L W : OpenSquare} {t : ℝ} (data : Data O L W t) :
    O.loV+O.side≤lower L (-O.s) O.c ∨
      (0≤L.s ∧ upper O (-L.s) L.c≤L.loV) ∨
      (L.s<0 ∧ L.loU+L.side≤lower O L.c L.s) := by
  have ob := normal_bounds data.on
  have hc : 0<O.c := by linarith only [ob.1]
  rcases CornerSingletonPair.alternatives O L hc data.lc data.sameOL
      data.oMarker data.oNear data.oFar data.corner data.olApart with h | h
  · rcases h with h | h
    · left
      simpa only [(ownV O).2] using h.2
    · exact False.elim ((not_lt_of_ge data.on.1) h.1)
  · rcases h with h | h
    · right; left
      exact ⟨h.1,by simpa only [(ownV L).1] using h.2⟩
    · right; right
      exact ⟨h.1,by simpa only [(ownU L).2] using h.2⟩

theorem wall_choices {O L W : OpenSquare} {t : ℝ} (data : Data O L W t) :
    (L.c/4<L.s ∧ L.loU+L.side≤lower W L.c L.s) ∨
      L.loV+L.side≤lower W (-L.s) L.c ∨ upper L t W.c≤W.loV := by
  have wb := normal_bounds data.wn
  have hc : 0<W.c := by linarith only [wb.1]
  have sign : W.s≤0 := by rw [data.ws]; exact neg_nonpos.mpr data.wn.1
  have canonical : -W.c≤W.s := by rw [data.ws]; linarith only [data.wn.2.1]
  have h := LeftSingletonWallSeparation.negative_wall_alternatives L W
    data.lc data.canonical hc sign canonical data.sameLW data.side data.lBox
    data.lMarker data.corner data.lFar data.wMarker data.lwApart
  simpa only [data.ws,neg_neg] using h

theorem relaxed_bottom {O L W : OpenSquare} {t : ℝ} (data : Data O L W t) :
    bottom O.c O.s<O.loV+O.side := by
  have ob := normal_bounds data.on
  have cp : 0<O.c := by linarith only [ob.1]
  have gain : 0≤(43/500)*O.s^2/O.c :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg O.s)) cp.le
  have identity : CornerWallMarkerMixedBounds.boundary O.c O.s=
      bottom O.c O.s+(43/500)*O.s^2/O.c := by
    unfold CornerWallMarkerMixedBounds.boundary bottom
    ring
  linarith only [data.bottomFace,identity,gain]

theorem positive {O L W : OpenSquare} {t : ℝ}
    (data : Data O L W t) (sign : 0≤L.s) : False := by
  have ln := positive_normal data sign
  have looseTop : W.loV+W.side≤t+3*W.c := by
    linarith only [data.top,data.wn.1]
  have looseCap : O.loU+O.side≤2*O.c+O.s := by
    linarith only [data.oCap,data.on.1]
  have low := relaxed_bottom data
  rcases bottom_choices data with bottomAxis | leftAxis | backward
  · rcases wall_choices data with longitudinal | leftWall | wallAxis
    · apply CornerWallMarkerLongitudinal.bottom_axis_of_margin O L W t
        data.on ln data.wn data.ws data.side data.sameLW data.lBox low
        data.northwest data.top bottomAxis longitudinal.2
      exact CornerWallMarkerLongitudinalBounds.bottom_axis data.on data.wn ln
        data.order data.small data.wide
    · exact CornerWallMarkerMixed.sector O L W t data.on ln data.wn data.ws
        data.side data.sameLW data.lBox data.wBox data.lMarker data.bottomFace
        looseTop data.order data.small data.wide bottomAxis leftWall
    · exact CornerWallCycle.transverse_sector O L W t data.on data.wn data.ws
        data.lc data.canonical data.side data.sameLW data.lBox data.order
        low looseTop bottomAxis wallAxis
  · rcases wall_choices data with longitudinal | leftWall | wallAxis
    · apply CornerWallMarkerLongitudinal.singleton_axis_of_margin O L W t
        data.on ln data.wn data.ws data.side data.sameOL data.sameLW
        data.oBox data.lBox looseCap data.northwest data.top leftAxis.2 longitudinal.2
      exact CornerWallMarkerLongitudinalBounds.singleton_axis data.on data.wn ln
        data.order data.wide
    · exact CornerWallMarkerShared.sector O L W t data.on ln data.wn data.ws
        data.side data.sameOL data.sameLW data.oBox data.wBox data.oCap data.top
        data.order data.small data.wide leftAxis.2 leftWall
    · exact CornerWallMarkerOtherMixed.sector O L W t data.on ln data.wn data.ws
        data.side data.sameOL data.sameLW data.oBox data.lBox data.oCap data.top
        data.order data.small data.wide leftAxis.2 wallAxis
  · exact (not_lt_of_ge sign) backward.1

/-- The negative-L backward U alternative is closed by the actual
inner corner and original marker caps. Those premises themselves force
L's larger tilt, so no additional angle assumption is introduced. -/
theorem negative_backward {O L W : OpenSquare} {t : ℝ}
    (data : Data O L W t) (sign : L.s≤0)
    (ol : L.loU+L.side≤lower O L.c L.s) : False := by
  have ln := negative_normal data sign
  have ls : L.s=-(-L.s) := by ring
  rcases wall_choices data with longitudinal | leftWall | wallAxis
  · have positive : 0<L.s := lt_trans (div_pos data.lc (by norm_num)) longitudinal.1
    exact (not_lt_of_ge sign) positive
  · exact CornerWallMarkerNegativeLarge.left_axis O L W (-L.s) t
      data.on ln data.wn ls data.ws data.side data.sameOL data.sameLW
      data.oBox data.lBox data.oCap data.top data.order data.small data.wide
      data.corner data.wMarker (by simpa only [neg_neg] using ol) leftWall
  · exact CornerWallMarkerNegativeLarge.wall_axis O L W (-L.s) t
      data.on ln data.wn ls data.side data.sameOL data.sameLW
      data.oBox data.lBox data.oCap data.top data.order data.small data.wide
      data.corner (by simpa only [neg_neg] using ol) wallAxis

/-- The entire negative orientation of L, including the mixed-axis
case and the corner-forced backward alternatives. -/
theorem negative {O L W : OpenSquare} {t : ℝ}
    (data : Data O L W t) (sign : L.s<0) : False := by
  have ln := negative_normal data sign.le
  have ls : L.s=-(-L.s) := by ring
  have looseTop : W.loV+W.side≤t+3*W.c := by
    linarith only [data.top,data.wn.1]
  rcases bottom_choices data with bottomAxis | leftAxis | backward
  · rcases wall_choices data with longitudinal | leftWall | wallAxis
    · have positive : 0<L.s := lt_trans (div_pos data.lc (by norm_num)) longitudinal.1
      exact (not_lt_of_ge sign.le) positive
    · exact CornerWallMarkerNegativeMixed.sector O L W (-L.s) t
        data.on ln data.wn ls data.ws data.side data.sameLW data.lBox data.wBox
        data.bottomFace data.northwest data.top data.order data.small data.wide
        bottomAxis leftWall
    · exact CornerWallCycle.transverse_sector O L W t data.on data.wn data.ws
        data.lc data.canonical data.side data.sameLW data.lBox data.order
        (relaxed_bottom data) looseTop bottomAxis wallAxis
  · exact (not_lt_of_ge leftAxis.1) sign
  · exact negative_backward data sign.le backward.2

/-- Genuine-marker cycle closure for every canonical orientation of
the left singleton. The surrounding packing must still supply Data.order. -/
theorem impossible {O L W : OpenSquare} {t : ℝ}
    (data : Data O L W t) : False := by
  rcases le_or_gt 0 L.s with sign | sign
  · exact positive data sign
  · exact negative data sign

#print axioms impossible
end N12Compact.CornerWallMarkerCycle
