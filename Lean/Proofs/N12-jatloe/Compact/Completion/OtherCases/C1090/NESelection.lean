import Compact.Completion.CommonCases.InwardPoint
import Compact.Completion.CommonCases.OutwardPoint
import Compact.Completion.OtherCases.InwardTopPoint
import Compact.Completion.OtherCases.OutwardBarPoint
import Compact.Completion.C1092.MixedSpan

/-! NE-SELECTION-LEMMA, using the original southeast/northeast squares.
The second duplicate uses the already available sharp common point
(2.525,2.125) in both squares. It does not assert that a differently
positioned 'stronger' point implies the chapter's point (2.50,2.04).
The whole actual bottom segment is retained in the sign lock and the
sharp outward-point theorem. No top square or container wall is assumed. -/
namespace N12Compact.Completion.OtherCases.C1090.NESelection
open S12 S12Pilot
set_option Elab.async false

structure Input (S E : OpenSquare) : Prop where
  sideS : 1<S.side
  sideE : 1<E.side
  apart : ∀ x y,¬(S.Inside x y ∧ E.Inside x y)
  markerS : S.Inside (47/20) (33/20)
  f8 : S.Inside 3 (87/50)
  g8 : S.Inside 3 (8/5)
  corner : ¬S.Inside 3 1
  cornerMarker : ¬S.Inside (1543/500) 1
  rightMarker : ¬S.Inside (1543/500) 2
  bottom : ∀ x : ℝ,113/50≤x → x≤14/5 → ¬S.Inside x 1
  markerE : E.Inside (47/20) (47/20)
  northwest : ¬E.Inside (33/20) (47/20)
  f9 : ¬E.Inside 3 (113/50)
  g9 : ¬E.Inside 3 (12/5)
  fCover : E.Inside 2 (113/50) ∨ E.Inside (12/5) 3
  gCover : E.Inside (113/50) 2 ∨ E.Inside (113/50) 3

/-- The sign is derived for the actual S whenever E owns G6. The
returned frame changes only face indexing, preserving the same S. -/
theorem negative_frame (S E : OpenSquare) (h : Input S E)
    (g6 : E.Inside (113/50) 2) :
    ∃ R : OpenSquare,0<R.c ∧ R.s<0 ∧ -R.s≤R.c ∧ R.side=S.side ∧
      (∀ x y,R.Inside x y↔S.Inside x y) := by
  obtain ⟨R,cp,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame S
  have side : 1<R.side := by simpa only [shape] using h.sideS
  have sign : R.s<0 := by
    apply lt_of_not_ge
    intro nonnegative
    exact C981CompletionOutwardAnchor.nonnegative_impossible R side cp nonnegative
      (by simpa only [abs_of_nonneg nonnegative] using canonical)
      ((inside _ _).mpr h.markerS) ((inside _ _).mpr h.g8)
      (fun own => h.corner ((inside _ _).mp own))
      (fun own => h.rightMarker ((inside _ _).mp own))
      (fun own => h.apart _ _ ⟨(inside _ _).mp own,g6⟩)
      (fun x low high own => h.bottom x low high ((inside _ _).mp own))
  exact ⟨R,cp,sign,by simpa only [abs_of_neg sign] using canonical,shape,inside⟩

/-- Both required duplicate points in the same actual outward square.
The reflection y↦4−y is applied to every owned/excluded datum. -/
theorem outward_points (S E : OpenSquare) (h : Input S E)
    (g6 : E.Inside (113/50) 2) :
    S.Inside (123/50) (201/100) ∧ S.Inside (101/40) (17/8) := by
  obtain ⟨R,cp,negative,order,shape,inside⟩ := negative_frame S E h g6
  have side : 1<R.side := by simpa only [shape] using h.sideS
  have reflectedSign : 0≤(pullY R).s := by change 0≤ -R.s; linarith only [negative]
  have reflectedOrder : (pullY R).s≤(pullY R).c := order
  have marker : (pullY R).Inside (47/20) (47/20) := by
    norm_num only [inside_pullY]
    exact (inside _ _).mpr h.markerS
  have outer : (pullY R).Inside 3 (113/50) := by
    norm_num only [inside_pullY]
    exact (inside _ _).mpr h.f8
  have missingG : ¬(pullY R).Inside (113/50) 2 := by
    norm_num only [inside_pullY]
    exact fun own => h.apart _ _ ⟨(inside _ _).mp own,g6⟩
  have missingR : ¬(pullY R).Inside (1543/500) 2 := by
    norm_num only [inside_pullY]
    exact fun own => h.rightMarker ((inside _ _).mp own)
  have missingP : ¬(pullY R).Inside 3 3 := by
    norm_num only [inside_pullY]
    exact fun own => h.corner ((inside _ _).mp own)
  have missingH : ¬(pullY R).Inside (1543/500) 3 := by
    norm_num only [inside_pullY]
    exact fun own => h.cornerMarker ((inside _ _).mp own)
  have segment (x : ℝ) (low : 113/50≤x) (high : x≤14/5) :
      ¬(pullY R).Inside x 3 := by
    norm_num only [inside_pullY]
    exact fun own => h.bottom x low high ((inside _ _).mp own)
  have first := CommonCases.OutwardPoint.positive_point_original (pullY R) side cp
    reflectedSign reflectedOrder marker outer missingG missingR
    (segment _ le_rfl (by norm_num)) (segment _ (by norm_num) le_rfl) missingP missingH
  have second := OutwardBarPoint.positive_point_original (pullY R) side cp
    reflectedSign reflectedOrder marker outer missingG missingR missingP missingH segment
  norm_num only [inside_pullY] at first second
  exact ⟨(inside _ _).mp first,(inside _ _).mp second⟩

theorem f7_of_g6 (S E : OpenSquare) (h : Input S E)
    (g6 : E.Inside (113/50) 2) : E.Inside (12/5) 3 := by
  by_contra missingF7
  have f5 := h.fCover.resolve_right missingF7
  have markerSExcluded : ¬E.Inside (47/20) (33/20) :=
    fun own => h.apart _ _ ⟨h.markerS,own⟩
  have point := CommonCases.InwardPoint.point_original (pullY E) h.sideE
    (by norm_num only [inside_pullY]; exact h.markerE)
    (by norm_num only [inside_pullY]; exact f5)
    (by norm_num only [inside_pullY]; exact g6)
    (by norm_num only [inside_pullY]; exact h.northwest)
    (by norm_num only [inside_pullY]; exact markerSExcluded)
    (by norm_num only [inside_pullY]; exact missingF7)
  norm_num only [inside_pullY] at point
  exact h.apart _ _ ⟨(outward_points S E h g6).1,point⟩

theorem g7 (S E : OpenSquare) (h : Input S E) : E.Inside (113/50) 3 := by
  by_contra missingG7
  have g6 := h.gCover.resolve_right missingG7
  have f7 := f7_of_g6 S E h g6
  by_cases f5 : E.Inside 2 (113/50)
  · have sharp := InwardTopPoint.point_original E h.sideE h.markerE f5 g6 f7
      missingG7 h.northwest (fun own => h.apart _ _ ⟨h.markerS,own⟩)
    exact h.apart _ _ ⟨(outward_points S E h g6).2,sharp⟩
  · -- The entire six-point obstruction is rotated, with the four
    -- exclusions kept in their literal actual positions.
    exact C1092MixedSpan.impossible (pullSwap (pullX E)) h.sideE
      (by norm_num only [inside_pullSwap,inside_pullX]; exact g6)
      (by norm_num only [inside_pullSwap,inside_pullX]; exact f7)
      (by norm_num only [inside_pullSwap,inside_pullX]; exact f5)
      (by norm_num only [inside_pullSwap,inside_pullX]; exact missingG7)
      (by norm_num only [inside_pullSwap,inside_pullX]; exact h.f9)
      (by norm_num only [inside_pullSwap,inside_pullX]; exact h.g9)

/-- NE-SELECTION-LEMMA, both conclusions and all contact alternatives.
Each side need only exceed one; congruence is not used by this proof. -/
theorem selection (S E : OpenSquare) (h : Input S E) :
    E.Inside (113/50) 3 ∧ (E.Inside (113/50) 2 → E.Inside (12/5) 3) :=
  ⟨g7 S E h,f7_of_g6 S E h⟩

#print axioms negative_frame
#print axioms selection
end N12Compact.Completion.OtherCases.C1090.NESelection
