import Compact.Geometry.ABTransverse

/-! Actual separation of the left singleton and the left wall square.
Positive face frames may span the entire first quadrant. Four directed
axes remain; the two longitudinal alternatives carry necessary angle
bounds derived from the original points and the actual container wall. -/
namespace N12Compact.LeftSingletonWallSeparation

open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse

theorem alternatives (L W : OpenSquare)
    (lc : 0<L.c) (ls : 0≤L.s) (wc : 0<W.c) (ws : 0≤W.s)
    (same : L.side=W.side)
    (lMarker : L.Inside (457/500) 1) (wMarker : W.Inside (457/500) 2)
    (apart : ∀ x y, ¬ (L.Inside x y ∧ W.Inside x y)) :
    L.loU+L.side ≤ lower W L.c L.s ∨
      L.loV+L.side ≤ lower W (-L.s) L.c ∨
      upper L W.c W.s ≤ W.loU ∨
      upper L (-W.s) W.c ≤ W.loV := by
  have forwardU (c s : ℝ) (hs : 0≤s) (unit : c^2+s^2=1)
      (sep : upper L c s ≤ lower W c s ∨ upper W c s ≤ lower L c s) :
      upper L c s ≤ lower W c s := by
    rcases sep with forward | backward
    · exact forward
    · have l := strict_bounds L _ _ c s unit lMarker
      have w := strict_bounds W _ _ c s unit wMarker
      exfalso
      nlinarith only [backward,l.1,w.2,hs]
  have forwardV (c s : ℝ) (hc : 0<c) (unit : c^2+s^2=1)
      (sep : upper L (-s) c ≤ lower W (-s) c ∨
        upper W (-s) c ≤ lower L (-s) c) :
      upper L (-s) c ≤ lower W (-s) c := by
    rcases sep with forward | backward
    · exact forward
    · have vunit : (-s)^2+c^2=1 := by nlinarith only [unit]
      have l := strict_bounds L _ _ (-s) c vunit lMarker
      have w := strict_bounds W _ _ (-s) c vunit wMarker
      exfalso
      nlinarith only [backward,l.1,w.2,hc]
  have axes := CongruentSAT.faceSeparation_of_disjoint L W same apart
  change pairRadius L W ≤ |L.c*(centerX W-centerX L)+L.s*(centerY W-centerY L)| ∨
    pairRadius L W ≤ |-L.s*(centerX W-centerX L)+L.c*(centerY W-centerY L)| ∨
    pairRadius W L ≤ |W.c*(centerX W-centerX L)+W.s*(centerY W-centerY L)| ∨
    pairRadius W L ≤ |-W.s*(centerX W-centerX L)+W.c*(centerY W-centerY L)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius L nx ny+supportRadius W nx ny=R)
      (sep : R≤|nx*(centerX W-centerX L)+ny*(centerY W-centerY L)|) :=
    separated L W nx ny (by rwa [identity])
  rcases axes with lu | lv | wu | wv
  · left
    simpa only [(ownU L).2] using forwardU L.c L.s ls L.unit_normal
      (separateAxis _ _ _ (parallel_radius L W) lu)
  · right; left
    simpa only [(ownV L).2] using forwardV L.c L.s lc L.unit_normal
      (separateAxis _ _ _ (transverse_radius L W) lv)
  · have identity : supportRadius L W.c W.s+supportRadius W W.c W.s=pairRadius W L := by
      rw [add_comm]; exact parallel_radius W L
    right; right; left
    simpa only [(ownU W).1] using forwardU W.c W.s ws W.unit_normal
      (separateAxis _ _ _ identity wu)
  · have identity : supportRadius L (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W L := by
      rw [add_comm]; exact transverse_radius W L
    right; right; right
    simpa only [(ownV W).1] using forwardV W.c W.s wc W.unit_normal
      (separateAxis _ _ _ identity wv)

/-- A longitudinal separator on L's own axis requires a genuine positive
tilt. The bound uses its full width, actual left containment and far seed. -/
theorem singleton_tilt (L W : OpenSquare) (lc : 0<L.c) (ls : 0≤L.s)
    (side : 1<L.side) (box : InsideContainer L)
    (far : L.Inside (19/25) (187/100))
    (marker : W.Inside (457/500) 2)
    (sep : L.loU+L.side ≤ lower W L.c L.s) : L.c/4<L.s := by
  by_contra no
  have small : L.s≤L.c/4 := le_of_not_gt no
  have wall0 := (positive_frame_wall_bounds L lc.le ls
    (fun x y p => ⟨(box x y p).1,(box x y p).2.2.1⟩)).1
  have wall : L.s*(L.loV+L.side)≤L.c*L.loU := by
    dsimp [centerX] at wall0
    nlinarith only [wall0]
  have cBound : L.c≤1 := by
    nlinarith only [L.unit_normal,sq_nonneg L.s,sq_nonneg (L.c-1)]
  have cDefect := mul_nonneg lc.le (sub_nonneg.mpr cBound)
  have crossBound := mul_nonneg lc.le (sub_nonneg.mpr small)
  have squareBound := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤L.c/4+L.s by linarith only [lc,ls])
  have farBound := mul_le_mul_of_nonneg_left far.2.2.2.le ls
  have sideBound := mul_lt_mul_of_pos_left side lc
  have strictMarker := (strict_bounds W _ _ L.c L.s L.unit_normal marker).1
  have separation := mul_le_mul_of_nonneg_left sep lc.le
  have markerBound := mul_lt_mul_of_pos_left strictMarker lc
  have positive := sq_pos_of_pos lc
  nlinarith only [wall,cDefect,crossBound,squareBound,farBound,sideBound,
    separation,markerBound,positive]

/-- A longitudinal separator on W's own axis must tilt beyond the
horizontal difference between the two original corner/marker points. -/
theorem wall_tilt (L W : OpenSquare) (corner : L.Inside 1 1)
    (marker : W.Inside (457/500) 2)
    (sep : upper L W.c W.s≤W.loU) : (43/500)*W.c<W.s := by
  have l := (strict_bounds L _ _ W.c W.s W.unit_normal corner).2
  have w := marker.1
  nlinarith only [l,w,sep]

theorem guarded_alternatives (L W : OpenSquare)
    (lc : 0<L.c) (ls : 0≤L.s) (wc : 0<W.c) (ws : 0≤W.s)
    (same : L.side=W.side) (side : 1<L.side) (box : InsideContainer L)
    (lMarker : L.Inside (457/500) 1) (corner : L.Inside 1 1)
    (far : L.Inside (19/25) (187/100))
    (wMarker : W.Inside (457/500) 2)
    (apart : ∀ x y, ¬ (L.Inside x y ∧ W.Inside x y)) :
    (L.c/4<L.s ∧ L.loU+L.side ≤ lower W L.c L.s) ∨
      L.loV+L.side ≤ lower W (-L.s) L.c ∨
      ((43/500)*W.c<W.s ∧ upper L W.c W.s ≤ W.loU) ∨
      upper L (-W.s) W.c ≤ W.loV := by
  rcases alternatives L W lc ls wc ws same lMarker wMarker apart with h | h | h | h
  · exact Or.inl ⟨singleton_tilt L W lc ls side box far wMarker h,h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨wall_tilt L W corner wMarker h,h⟩))
  · exact Or.inr (Or.inr (Or.inr h))

/-- A negative canonical W cannot separate from L on its U axis at all.
The same is true on L's own U axis when L has a negative canonical frame.
Thus only one guarded positive-L mode and the two upward V modes remain. -/
theorem negative_wall_alternatives (L W : OpenSquare)
    (lc : 0<L.c) (lCanonical : |L.s|≤L.c)
    (wc : 0<W.c) (ws : W.s≤0) (wCanonical : -W.c≤W.s)
    (same : L.side=W.side) (side : 1<L.side) (box : InsideContainer L)
    (lMarker : L.Inside (457/500) 1) (corner : L.Inside 1 1)
    (far : L.Inside (19/25) (187/100))
    (wMarker : W.Inside (457/500) 2)
    (apart : ∀ x y, ¬ (L.Inside x y ∧ W.Inside x y)) :
    (L.c/4<L.s ∧ L.loU+L.side≤lower W L.c L.s) ∨
      L.loV+L.side≤lower W (-L.s) L.c ∨
      upper L (-W.s) W.c≤W.loV := by
  have negativeU (c s : ℝ) (hc : 0<c) (hs : s≤0) (canonical : -c≤s)
      (unit : c^2+s^2=1) :
      ¬ (upper L c s≤lower W c s ∨ upper W c s≤lower L c s) := by
    have k := strict_bounds L _ _ c s unit corner
    have f := strict_bounds L _ _ c s unit far
    have w := strict_bounds W _ _ c s unit wMarker
    rintro (h | h) <;> nlinarith only [h,k.2,f.1,w.1,w.2,hc,hs,canonical]
  have forwardV (c s : ℝ) (hc : 0<c) (unit : c^2+s^2=1)
      (sep : upper L (-s) c≤lower W (-s) c ∨
        upper W (-s) c≤lower L (-s) c) :
      upper L (-s) c≤lower W (-s) c := by
    rcases sep with h | h
    · exact h
    · have vunit : (-s)^2+c^2=1 := by nlinarith only [unit]
      have l := strict_bounds L _ _ (-s) c vunit lMarker
      have w := strict_bounds W _ _ (-s) c vunit wMarker
      exfalso
      nlinarith only [h,l.1,w.2,hc]
  have axes := CongruentSAT.faceSeparation_of_disjoint L W same apart
  change pairRadius L W ≤ |L.c*(centerX W-centerX L)+L.s*(centerY W-centerY L)| ∨
    pairRadius L W ≤ |-L.s*(centerX W-centerX L)+L.c*(centerY W-centerY L)| ∨
    pairRadius W L ≤ |W.c*(centerX W-centerX L)+W.s*(centerY W-centerY L)| ∨
    pairRadius W L ≤ |-W.s*(centerX W-centerX L)+W.c*(centerY W-centerY L)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius L nx ny+supportRadius W nx ny=R)
      (sep : R≤|nx*(centerX W-centerX L)+ny*(centerY W-centerY L)|) :=
    separated L W nx ny (by rwa [identity])
  rcases axes with lu | lv | wu | wv
  · have sep := separateAxis _ _ _ (parallel_radius L W) lu
    by_cases sign : 0≤L.s
    · rcases sep with h | h
      · have h' : L.loU+L.side≤lower W L.c L.s := by
          simpa only [(ownU L).2] using h
        exact Or.inl ⟨singleton_tilt L W lc sign side box far wMarker h',h'⟩
      · have l := strict_bounds L _ _ L.c L.s L.unit_normal lMarker
        have w := strict_bounds W _ _ L.c L.s L.unit_normal wMarker
        exfalso
        nlinarith only [h,l.1,w.2,sign]
    · exact False.elim (negativeU L.c L.s lc (le_of_lt (lt_of_not_ge sign))
        (abs_le.mp lCanonical).1 L.unit_normal sep)
  · right; left
    simpa only [(ownV L).2] using forwardV L.c L.s lc L.unit_normal
      (separateAxis _ _ _ (transverse_radius L W) lv)
  · have identity : supportRadius L W.c W.s+supportRadius W W.c W.s=pairRadius W L := by
      rw [add_comm]; exact parallel_radius W L
    exact False.elim (negativeU W.c W.s wc ws wCanonical W.unit_normal
      (separateAxis _ _ _ identity wu))
  · have identity : supportRadius L (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W L := by
      rw [add_comm]; exact transverse_radius W L
    right; right
    simpa only [(ownV W).1] using forwardV W.c W.s wc W.unit_normal
      (separateAxis _ _ _ identity wv)

end N12Compact.LeftSingletonWallSeparation
