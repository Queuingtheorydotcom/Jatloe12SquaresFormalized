import Completion.Cases.C977.MissingCornerPoints

namespace S12Completion.C977
open S12 S12Pilot
set_option maxHeartbeats 200000

/-- A contained missing-corner square cannot use the upper-U wall escape
    with this range of positive-frame cosine components. The estimate is
    uniform over the stated portion of the whole unit-normal arc. -/
theorem high_normal_wall_bound (c s : ℝ) (hc : 0 ≤ c) (hc48 : c ≤ 12 / 25)
    (hs : 0 ≤ s) (hn : c^2+s^2=1) :
    c^2+(457 / 500)*s^2+c*s ≤ c+s := by
  have hcsq := mul_nonneg hc (show 0 ≤ 12 / 25 - c by linarith only [hc48])
  have hcc : c^2 ≤ (12 / 25)^2 := by nlinarith only [hcsq, hc48]
  have hs1 : s ≤ 1 := by nlinarith only [hn, sq_nonneg c, sq_nonneg (s-1)]
  have hs87 : 87 / 100 ≤ s := by
    by_contra hh
    have hss := mul_nonneg hs (show 0 ≤ 87 / 100-s by linarith only [hh])
    nlinarith only [hn, hcc, hss, hh]
  have hsmul := mul_nonneg (show 0 ≤ 1-s by linarith only [hs1])
    (show 0 ≤ (27 / 50)*(1+s)-1 by linarith only [hs87])
  have hslow : 0 ≤ s-(1-(27 / 50)*c^2) := by nlinarith only [hsmul, hn]
  have hcomp := mul_nonneg (show 0 ≤ 1-c by linarith only [hc48]) hslow
  have hb : 0 ≤ (313 / 500)*(c+12 / 25)-
      (27 / 50)*(c^2+(12 / 25)*c+(12 / 25)^2) := by
    nlinarith only [hc, hcsq]
  have hpoly := mul_nonneg (show 0 ≤ 12 / 25-c by linarith only [hc48]) hb
  nlinarith only [hcomp, hpoly, hn]

/-- The lower-V wall escape forces a small cosine component. The exact
    rational cap follows from the unit-normal identity, without choosing
    an algebraic root or sampling orientations. -/
theorem lower_face_cos_bound (c s : ℝ) (hc : 0 < c) (hs : 0 ≤ s)
    (hn : c^2+s^2=1) (hlarge : 1 < s+(43 / 500)*c) :
    c < 43000 / 251849 := by
  have hc1 : c ≤ 1 := by nlinarith only [hn, sq_nonneg s, sq_nonneg (c-1)]
  have hfactor : 0 < s+1-(43 / 500)*c := by linarith only [hs, hc1]
  have hprod := mul_pos (show 0 < s+(43 / 500)*c-1 by linarith only [hlarge]) hfactor
  have hgap : 0 < c*(43000 / 251849-c) := by nlinarith only [hprod, hn]
  by_contra hh
  have hbad := mul_nonpos_of_nonneg_of_nonpos hc.le
    (show 43000 / 251849-c ≤ 0 by linarith only [hh])
  exact (not_lt_of_ge hbad) hgap
/-- The two surviving faces for the missing wall marker carry disjoint
    strict normal-component ranges. Face inequalities are closed so that
    square-boundary contact is retained. -/
def CornerBandAlternative (r : OpenSquare) : Prop :=
  (12 / 25 < r.c ∧ r.loU+r.side ≤ 2*r.c+(457 / 500)*r.s) ∨
  (r.c < 43000 / 251849 ∧ (457 / 500)*r.c-2*r.s ≤ r.loV)

/-- Both endpoints of the closed intervening normal range are impossible. -/
theorem CornerBandAlternative.cosine_gap (r : OpenSquare)
    (h : CornerBandAlternative r) :
    ¬(43000 / 251849 ≤ r.c ∧ r.c ≤ 12 / 25) := by
  rintro ⟨hlo, hhi⟩
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith

/-- Re-indexing preserves the square and both center coordinates. In the
    resulting positive frame, the corner lies beyond the upper-V face and
    the wall-marker alternatives exclude the intervening normal range. -/
def CanonicalCornerBounds (q : OpenSquare) : Prop :=
  ∃ r : OpenSquare,
    r.side=q.side ∧ centerX r=centerX q ∧ centerY r=centerY q ∧
    (∀ x y, r.Inside x y ↔ q.Inside x y) ∧
    0 < r.c ∧ 0 < r.s ∧ r.loV+r.side ≤ r.c-r.s ∧ CornerBandAlternative r

/-- The marker at (2,.914) can be missed only through upper U or lower V.
    In the former case the wall and corner inequalities force c>12/25;
    in the latter they force c<43000/251849. These are exhaustive for every
    legal orientation, and both endpoints of the excluded gap are covered. -/
theorem canonical_corner_bounds_of_anchors (q : OpenSquare) (ha : 1 < q.side)
    (hbox : InsideContainer q) (hA : q.Inside 1 (457 / 500))
    (hanchors : SingletonAnchors q) (hz : ¬q.Inside 1 1)
    (hM : ¬q.Inside 2 (457 / 500)) : CanonicalCornerBounds q := by
  classical
  obtain ⟨r, hc, hs, hside, hcx, hcy, hinside⟩ := exists_positive_frame q
  have hrA := (hinside 1 (457 / 500)).mpr hA
  have hrnear := (hinside (28 / 25) 1).mpr hanchors.near_point
  have hrz : ¬r.Inside 1 1 := fun hi => hz ((hinside 1 1).mp hi)
  have hrM : ¬r.Inside 2 (457 / 500) := fun hi => hM ((hinside 2 (457 / 500)).mp hi)
  have hra : 1 < r.side := by simpa only [hside] using ha
  have hrbox : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y := by
    intro x y hi
    have hw := hbox x y ((hinside x y).mp hi)
    exact ⟨hw.1, hw.2.2.1⟩
  have hwallY := (positive_frame_wall_bounds r hc hs hrbox).2
  have hywall : 0 ≤ r.s*r.loU+r.c*r.loV := by
    dsimp [centerY] at hwallY
    nlinarith only [hwallY]
  rcases hrA with ⟨hA0, hA1, hA2, hA3⟩
  rcases hrnear with ⟨hN0, hN1, hN2, hN3⟩
  have hz0 : r.loU < r.c+r.s := by nlinarith only [hA0, hs]
  have hz1 : r.c+r.s < r.loU+r.side := by nlinarith only [hN1, hc]
  have hz2 : r.loV < -r.s+r.c := by nlinarith only [hA2, hc]
  have hz3 : r.loV+r.side ≤ r.c-r.s := by
    by_contra hh
    apply hrz
    change InBands r.loU r.loV r.side _ _
    dsimp [InBands]
    exact ⟨by simpa using hz0, by simpa using hz1,
      by simpa using hz2, by linarith only [lt_of_not_ge hh]⟩
  have hcpos : 0 < r.c := by nlinarith only [hA3, hz3]
  have hspos : 0 < r.s := by nlinarith only [hN3, hz3]
  refine ⟨r, hside, hcx, hcy, hinside, hcpos, hspos, hz3, ?_⟩
  by_cases hMU : 2*r.c+(457 / 500)*r.s < r.loU+r.side
  · have hMV : (457 / 500)*r.c-2*r.s ≤ r.loV := by
      by_contra hh
      apply hrM
      change InBands r.loU r.loV r.side _ _
      dsimp [InBands]
      exact ⟨by nlinarith only [hA0, hc], by linarith only [hMU],
        by linarith only [lt_of_not_ge hh], by nlinarith only [hA3, hs]⟩
    have hlarge : 1 < r.s+(43 / 500)*r.c := by linarith only [hra, hz3, hMV]
    exact Or.inr ⟨lower_face_cos_bound r.c r.s hcpos hs r.unit_normal hlarge, hMV⟩
  · have hMU' : r.loU+r.side ≤ 2*r.c+(457 / 500)*r.s := le_of_not_gt hMU
    have hc48 : 12 / 25 < r.c := by
      by_contra hh
      have hnormal := high_normal_wall_bound r.c r.s hc (le_of_not_gt hh) hs r.unit_normal
      have hU := mul_nonneg hs (sub_nonneg.mpr hMU')
      have hV := mul_nonneg hc (sub_nonneg.mpr hz3)
      have hstrict := mul_pos (show 0 < r.side-1 by linarith only [hra])
        (show 0 < r.c+r.s by linarith only [hcpos, hspos])
      nlinarith only [hU, hV, hywall, hnormal, hstrict]
    exact Or.inl ⟨hc48, hMU'⟩

/-- A strengthened missing-corner owner acquires the same geometric bounds
    once the other bottom wall marker is known to be missing. -/
theorem canonical_corner_bounds (q : OpenSquare) (h : StrengthenedMissingCorner q)
    (hM : ¬q.Inside 2 (457 / 500)) : CanonicalCornerBounds q :=
  canonical_corner_bounds_of_anchors q h.entrance.side_gt_one h.entrance.contained
    h.entrance.marker_owned h.anchors h.entrance.corner_missing hM

/-- Exact code-1 ownership supplies the wall-marker exclusion required by
    the orientation reduction. -/
theorem code_one_missing_corner_bounds (p : S12.NormalizedPacking) (i : Fin 12)
    (hi : S12.markerCode p i = 1) (h : StrengthenedMissingCorner (p.square i)) :
    CanonicalCornerBounds (p.square i) := by
  have he := code_one_exact p i hi
  have hM : ¬S12.Owns (p.square i) 13 := by
    intro ho
    have hm : (13 : S12.Marker) = 0 := Finset.mem_singleton.mp ((he 13).mp ho)
    exact (by decide : (13 : S12.Marker) ≠ 0) hm
  apply canonical_corner_bounds _ h
  simpa [S12.Owns, S12.marker] using hM

/-- For code 2, the original left wall marker becomes the canonical bottom
    wall marker under transposition. The original labels remain unchanged. -/
theorem code_two_missing_corner_bounds (p : S12.NormalizedPacking) (i : Fin 12)
    (hi : S12.markerCode p i = 2)
    (h : StrengthenedMissingCorner (S12.pullSwap (p.square i))) :
    CanonicalCornerBounds (S12.pullSwap (p.square i)) := by
  have he := code_two_exact p i hi
  have hM : ¬S12.Owns (p.square i) 12 := by
    intro ho
    have hm : (12 : S12.Marker) = 1 := Finset.mem_singleton.mp ((he 12).mp ho)
    exact (by decide : (12 : S12.Marker) ≠ 1) hm
  apply canonical_corner_bounds _ h
  simpa [S12.Owns, S12.marker, S12.inside_pullSwap] using hM

/-- Every actual case-977 packing enters a strengthened root with the
    additional exact face and normal-component reduction. -/
theorem bounded_missing_corner_cover (p : S12.NormalizedPacking)
    (hf : S12.codedMarkerFamily p = family) :
    ∃ i j : Fin 12,
      S12.markerCode p i = 1 ∧ S12.markerCode p j = 2 ∧ i ≠ j ∧
      ((StrengthenedMissingCorner (p.square i) ∧ CanonicalCornerBounds (p.square i)) ∨
        ((p.square i).Inside 1 1 ∧
          StrengthenedMissingCorner (S12.pullSwap (p.square j)) ∧
          CanonicalCornerBounds (S12.pullSwap (p.square j)))) := by
  obtain ⟨i, j, hi, hj, hij, hroot⟩ := missing_corner_strengthening_cover p hf
  refine ⟨i, j, hi, hj, hij, ?_⟩
  rcases hroot with hroot | ⟨hpresent, hroot⟩
  · exact Or.inl ⟨hroot, code_one_missing_corner_bounds p i hi hroot⟩
  · exact Or.inr ⟨hpresent, hroot, code_two_missing_corner_bounds p j hj hroot⟩

/-- The bounded cover holds for every retained row bearing ID 977. -/
theorem retained_bounded_missing_corner_cover
    (r : S12.CoverRow) (hr : r ∈ S12.retainedRows) (hid : r.originalId = 977)
    (p : S12.NormalizedPacking) (hf : S12.codedMarkerFamily p = r.groups) :
    ∃ i j : Fin 12,
      S12.markerCode p i = 1 ∧ S12.markerCode p j = 2 ∧ i ≠ j ∧
      ((StrengthenedMissingCorner (p.square i) ∧ CanonicalCornerBounds (p.square i)) ∨
        ((p.square i).Inside 1 1 ∧
          StrengthenedMissingCorner (S12.pullSwap (p.square j)) ∧
          CanonicalCornerBounds (S12.pullSwap (p.square j)))) := by
  apply bounded_missing_corner_cover p
  exact hf.trans (row_family r hr hid)

end S12Completion.C977
