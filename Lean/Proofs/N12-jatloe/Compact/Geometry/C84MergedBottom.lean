import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! Three continuous exclusions for the original merged bottom/SE owner
of case84. Together with four elementary diameter exclusions, they replace
the missing historical seven-query G-domain certificate. The exact original
G-budget is needed to supply `missingG5`; no saved domain is assumed here.
Source only: this module has not yet been compiled. -/
namespace N12Compact.C84MergedBottom
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem zero (q : OpenSquare) (hc : 0<q.c)
    (canonical : |q.s|≤q.c) (size : q.side≤1001/1000)
    (marker : q.Inside (47/20) (33/20))
    (left : q.Inside 1 (8/5))
    (missing : ¬q.Inside (33/20) (33/20)) : False := by
  have signed := abs_le.mp canonical
  have lowerU : q.loU<q.c*(33/20)+q.s*(33/20) := by
    linarith only [left.1,signed.1,hc]
  have upperU : q.c*(33/20)+q.s*(33/20)<q.loU+q.side := by
    linarith only [marker.2.1,hc]
  by_cases negative : q.s≤0
  · exact missing ⟨lowerU,upperU,
      by linarith only [left.2.2.1,negative,hc],
      by linarith only [marker.2.2.2,negative]⟩
  have nonnegative : 0≤q.s := (lt_of_not_ge negative).le
  by_cases steep : q.c≤13*q.s
  · exact missing ⟨lowerU,upperU,
      by linarith only [marker.2.2.1,nonnegative],
      by linarith only [left.2.2.2,steep]⟩
  have narrow : 13*q.s≤q.c := (lt_of_not_ge steep).le
  have product := mul_nonneg (sub_nonneg.mpr narrow)
    (show 0≤q.c+13*q.s by positivity)
  have wide : 99/100≤q.c := by
    nlinarith only [product,q.unit_normal,hc]
  linarith only [marker.2.1,left.1,size,wide,nonnegative]

private theorem negative_corner (q : OpenSquare) (ha : 1<q.side)
    (hc : 0<q.c) (hs : q.s≤0) (canonical : -q.c≤q.s)
    (bottom : q.Inside 2 (457/500))
    (marker : q.Inside (47/20) (33/20))
    (cap : q.loU+q.side≤q.c*(113/50)+q.s)
    (missing : ¬q.Inside (33/20) (33/20)) : False := by
  have gap := (short_projections q (61/100) (-13/20) (by norm_num)).2.1
  apply missing
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [cap,gap,ha]
  · linarith only [marker.2.1,hc]
  · linarith only [bottom.2.2.1,canonical,hc]
  · linarith only [marker.2.2.2,hs]

private theorem two (q : OpenSquare) (ha : 1<q.side) (hc : 0<q.c)
    (canonical : |q.s|≤q.c)
    (bottom : q.Inside 2 (457/500))
    (marker : q.Inside (47/20) (33/20))
    (low : q.Inside (87/50) 1)
    (missing : ¬q.Inside (33/20) (33/20))
    (missingG5 : ¬q.Inside (113/50) 1) : False := by
  have signed := abs_le.mp canonical
  by_cases hs : 0≤q.s
  · have lowerU : q.loU<q.c*(113/50)+q.s := by
      linarith only [bottom.1,hc,hs]
    have upperU : q.c*(113/50)+q.s<q.loU+q.side := by
      linarith only [marker.2.1,hc,hs]
    have upperV : -q.s*(113/50)+q.c<q.loV+q.side := by
      linarith only [low.2.2.2,hs]
    have face : -q.s*(113/50)+q.c≤q.loV :=
      le_of_not_gt (fun h => missingG5 ⟨by linarith only [lowerU],
        by linarith only [upperU], by linarith only [h], by linarith only [upperV]⟩)
    have gap := (short_projections q (-61/100) (13/20) (by norm_num)).2.2.2
    apply missing
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [low.1,bottom.2.2.1,face,hc]
    · linarith only [marker.2.1,hc]
    · linarith only [low.2.2.1,hc,hs]
    · linarith only [face,gap,ha]
  · have nonpositive : q.s≤0 := (lt_of_not_ge hs).le
    have cap : q.loU+q.side≤q.c*(113/50)+q.s := by
      apply le_of_not_gt
      intro upperU
      apply missingG5
      refine ⟨?_,by linarith only [upperU],?_,?_⟩
      · linarith only [low.1,hc]
      · linarith only [bottom.2.2.1,hc,nonpositive]
      · linarith only [marker.2.2.2,hc,nonpositive]
    exact negative_corner q ha hc nonpositive signed.1 bottom marker cap missing

private theorem three (q : OpenSquare) (ha : 1<q.side) (hc : 0<q.c)
    (canonical : |q.s|≤q.c) (size : q.side≤1001/1000)
    (bottom : q.Inside 2 (457/500))
    (marker : q.Inside (47/20) (33/20))
    (high : q.Inside (87/50) 2)
    (missing : ¬q.Inside (33/20) (33/20))
    (missingG5 : ¬q.Inside (113/50) 1) : False := by
  have signed := abs_le.mp canonical
  by_cases hs : 0≤q.s
  · have c1 : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s]
    have s1 : q.s≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.c]
    have steep : q.c<2*q.s := by
      apply lt_of_not_ge
      intro narrow
      have product := mul_nonneg hs (sub_nonneg.mpr narrow)
      have defectProduct := mul_nonneg hs (sub_nonneg.mpr c1)
      have defect : 1-q.c≤q.s/4 := by
        apply le_of_not_gt
        intro failure
        have positive := mul_pos (sub_pos.mpr failure)
          (show 0<1+q.c by linarith only [hc])
        nlinarith only [positive,product,defectProduct,q.unit_normal]
      linarith only [high.2.2.2,bottom.2.2.1,size,defect,s1]
    apply missing
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [bottom.1,steep,hc]
    · linarith only [marker.2.1,hc]
    · linarith only [bottom.2.2.1,hc,hs]
    · linarith only [high.2.2.2,signed.2,hc]
  · have nonpositive : q.s≤0 := (lt_of_not_ge hs).le
    have cap : q.loU+q.side≤q.c*(113/50)+q.s := by
      apply le_of_not_gt
      intro upperU
      apply missingG5
      refine ⟨?_,by linarith only [upperU],?_,?_⟩
      · linarith only [high.1,hc,nonpositive]
      · linarith only [bottom.2.2.1,hc,nonpositive]
      · linarith only [high.2.2.2,signed.1,hc]
    exact negative_corner q ha hc nonpositive signed.1 bottom marker cap missing

/-- The three non-diameter G exclusions use the whole canonical arc.
The side cap and exact missing SW marker are original packing premises. -/
theorem forbidden (q : OpenSquare) (ha : 1<q.side) (size : q.side≤1001/1000)
    (bottom : q.Inside 2 (457/500))
    (marker : q.Inside (47/20) (33/20))
    (missing : ¬q.Inside (33/20) (33/20))
    (missingG5 : ¬q.Inside (113/50) 1) :
    ¬q.Inside 1 (8/5) ∧ ¬q.Inside (87/50) 1 ∧ ¬q.Inside (87/50) 2 := by
  obtain ⟨r,hc,canonical,side,inside,_⟩ := ClosedFrames.canonical_frame q
  have rside : 1<r.side := by simpa only [side] using ha
  have rcap : r.side≤1001/1000 := by simpa only [side] using size
  have rb := (inside _ _).mpr bottom
  have rm := (inside _ _).mpr marker
  have rn : ¬r.Inside (33/20) (33/20) := fun h => missing ((inside _ _).mp h)
  have rg : ¬r.Inside (113/50) 1 := fun h => missingG5 ((inside _ _).mp h)
  exact ⟨fun h => zero r hc canonical rcap rm ((inside _ _).mpr h) rn,
    fun h => two r rside hc canonical rb rm ((inside _ _).mpr h) rn rg,
    fun h => three r rside hc canonical rcap rb rm ((inside _ _).mpr h) rn rg⟩

/-- Once the actual G-budget chooses the inward right point, the merged
square must have a positive canonical frame. The other sign would force
the auxiliary point genuinely occupied by the bottom-right singleton. -/
theorem canonical_positive (q : OpenSquare) (ha : 1<q.side) (hc : 0<q.c)
    (canonical : |q.s|≤q.c)
    (bottom : q.Inside 2 (457/500))
    (marker : q.Inside (47/20) (33/20))
    (right : q.Inside (113/50) 2)
    (missingSW : ¬q.Inside (33/20) (33/20))
    (missingCorner : ¬q.Inside (12/5) 1) : 0<q.s := by
  apply lt_of_not_ge
  intro hs
  have signed := abs_le.mp canonical
  have lower : q.c*(33/20)+q.s*(33/20)≤q.loU := by
    apply le_of_not_gt
    intro hu
    apply missingSW
    refine ⟨hu,?_,?_,?_⟩
    · linarith only [marker.2.1,hc]
    · linarith only [bottom.2.2.1,signed.1,hc]
    · linarith only [right.2.2.2,hs,hc]
  have gap := (short_projections q (3/4) (-13/20) (by norm_num)).2.1
  apply missingCorner
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [right.1,hs,hc]
  · linarith only [lower,gap,ha]
  · linarith only [bottom.2.2.1,hs,hc]
  · linarith only [marker.2.2.2,signed.1,hc]

/-- The F4 point is a consequence of actual geometry, even though this
family permits two F points and the old singleSpec74 cannot be applied. -/
theorem inward (q : OpenSquare) (ha : 1<q.side)
    (bottom : q.Inside 2 (457/500))
    (marker : q.Inside (47/20) (33/20))
    (right : q.Inside (113/50) 2)
    (missingSW : ¬q.Inside (33/20) (33/20))
    (missingCorner : ¬q.Inside (12/5) 1) : q.Inside 2 (87/50) := by
  obtain ⟨r,hc,canonical,side,inside,_⟩ := ClosedFrames.canonical_frame q
  have rb := (inside _ _).mpr bottom
  have rm := (inside _ _).mpr marker
  have rr := (inside _ _).mpr right
  have rsw : ¬r.Inside (33/20) (33/20) := fun h => missingSW ((inside _ _).mp h)
  have rcorner : ¬r.Inside (12/5) 1 := fun h => missingCorner ((inside _ _).mp h)
  have hs := canonical_positive r (by simpa only [side] using ha)
    hc canonical rb rm rr rsw rcorner
  have signed := abs_le.mp canonical
  apply (inside _ _).mp
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [rb.1,hs]
  · linarith only [rm.2.1,signed.2,hc]
  · linarith only [rb.2.2.1,hc]
  · linarith only [rr.2.2.2,signed.2]

#print axioms forbidden
#print axioms inward
end N12Compact.C84MergedBottom
