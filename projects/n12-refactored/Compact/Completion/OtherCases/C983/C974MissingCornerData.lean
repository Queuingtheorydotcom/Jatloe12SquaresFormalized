import Compact.Completion.OtherCases.C983.C974LocalData
import Compact.Completion.OtherCases.WallProfile.VertexGeometry
import Compact.Geometry.ClosedFrames

/-! The point/face reductions of MISSING-CORNER-WALL-SIGN §§1.1, 3.1
and MISSING-CORNER-MIDPOINT §§1.1--1.3. All frame changes below retain
the same physical squares. The stronger missing-corner seed remains an
explicit input of C974LocalData; no unavailable historical source is used.
Source translation only; this module has not been replayed. -/
namespace N12Compact.Completion.OtherCases.C983.C974MissingCorner
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false
noncomputable section

structure Input (K W : OpenSquare) : Prop where
  sideLarge : 1<K.side
  sameSide : K.side=W.side
  wall : ∀ x y,K.Inside x y → -1≤y
  p : K.Inside 0 (-43/500)
  a : K.Inside (41/50) 0
  s : K.Inside (24/25) (-6/25)
  missing : ¬K.Inside 0 0
  o : W.Inside 1 0
  pw : W.Inside 1 (-43/500)
  r : W.Inside (9/5) 0
  missingM : ¬W.Inside (27/20) (13/20)
  missingC : ¬W.Inside 2 0
  missingF0 : ¬W.Inside 1 (1/2)
  missingF1 : ¬W.Inside 2 (1/2)
  apart : ∀ x y,¬(K.Inside x y ∧ W.Inside x y)

theorem Input.of_local {K W C : OpenSquare} (h : C974LocalData.Input K W C) :
    Input K W :=
  ⟨h.sideLarge,h.sameKW,h.lowerWall,h.markerK,h.pointK,h.seedK,h.missingK,
    h.originW,h.markerW,h.farW,h.missingMarker,
    fun own => h.apartWC _ _ ⟨own,h.corner⟩,h.missingMiddle,h.missingOuter,h.apartKW⟩

theorem Input.reframeK {K W R : OpenSquare} (h : Input K W)
    (shape : R.side=K.side) (same : ∀ x y,R.Inside x y↔K.Inside x y) : Input R W :=
  ⟨by simpa only [shape] using h.sideLarge,shape.trans h.sameSide,
    fun x y own => h.wall x y ((same x y).mp own),
    (same _ _).mpr h.p,(same _ _).mpr h.a,(same _ _).mpr h.s,
    fun own => h.missing ((same _ _).mp own),h.o,h.pw,h.r,
    h.missingM,h.missingC,h.missingF0,h.missingF1,
    fun x y own => h.apart x y ⟨(same x y).mp own.1,own.2⟩⟩

theorem Input.reframeW {K W R : OpenSquare} (h : Input K W)
    (shape : R.side=W.side) (same : ∀ x y,R.Inside x y↔W.Inside x y) : Input K R :=
  ⟨h.sideLarge,h.sameSide.trans shape.symm,h.wall,h.p,h.a,h.s,h.missing,
    (same _ _).mpr h.o,(same _ _).mpr h.pw,(same _ _).mpr h.r,
    fun own => h.missingM ((same _ _).mp own),
    fun own => h.missingC ((same _ _).mp own),
    fun own => h.missingF0 ((same _ _).mp own),
    fun own => h.missingF1 ((same _ _).mp own),
    fun x y own => h.apart x y ⟨own.1,(same x y).mp own.2⟩⟩

/-- The positive canonical case of WALL-SIGN §1.1; zero sine is ruled
out by the strict point A, not silently discarded. -/
theorem singleton_positive_cap (K W : OpenSquare) (h : Input K W)
    (cp : 0<K.c) (sn : 0≤K.s) : 0<K.s ∧ K.loV+K.side≤0 := by
  have p := h.p
  have a := h.a
  dsimp [OpenSquare.Inside,InBands] at p a
  have cap : K.loV+K.side≤0 := by
    by_contra no
    apply h.missing
    change K.loU<0 ∧ 0<K.loU+K.side ∧ K.loV<0 ∧ 0<K.loV+K.side
    refine ⟨?_,?_,?_,lt_of_not_ge no⟩ <;> linarith only [p.1,p.2.2.1,a.2.1,cp,sn]
  have positive : 0<K.s := by
    by_contra no
    have zero : K.s=0 := le_antisymm (le_of_not_gt no) sn
    rw [zero] at a
    linarith only [a.2.2.2,cap]
  exact ⟨positive,cap⟩

/-- The negative canonical case of §1.1, before physical reindexing. -/
theorem singleton_negative_cap (K W : OpenSquare) (h : Input K W)
    (cp : 0<K.c) (sn : K.s≤0) : K.s<0 ∧ 0≤K.loU := by
  have p := h.p
  have a := h.a
  dsimp [OpenSquare.Inside,InBands] at p a
  have cap : 0≤K.loU := by
    by_contra no
    apply h.missing
    change K.loU<0 ∧ 0<K.loU+K.side ∧ K.loV<0 ∧ 0<K.loV+K.side
    refine ⟨lt_of_not_ge no,?_,?_,?_⟩ <;> linarith only [p.2.2.1,a.2.1,a.2.2.2,cp,sn]
  have negative : K.s<0 := by
    by_contra no
    have zero : K.s=0 := le_antisymm sn (le_of_not_gt no)
    rw [zero] at p
    linarith only [p.1,cap]
  exact ⟨negative,cap⟩

/-- Every permitted K has a strictly positive quadrant frame with the
upper v face at most zero. No canonical order is claimed at this stage. -/
theorem singleton_quadrant (K W : OpenSquare) (h : Input K W) :
    ∃ R : OpenSquare, R.side=K.side ∧ (∀ x y,R.Inside x y↔K.Inside x y) ∧
      0<R.c ∧ 0<R.s ∧ R.loV+R.side≤0 := by
  obtain ⟨R,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame K
  have raw := h.reframeK shape same
  by_cases sign : 0≤R.s
  · have cap := singleton_positive_cap R W raw cp sign
    exact ⟨R,shape,same,cp,cap.1,cap.2⟩
  · have cap := singleton_negative_cap R W raw cp (le_of_not_ge sign)
    refine ⟨turnFrame R,by simpa only [turnFrame_side] using shape,?_,?_,cp,?_⟩
    · intro x y
      rw [turnFrame_inside]
      exact same x y
    · change 0< -R.s
      linarith only [cap.1]
    · change -R.loU-R.side+R.side≤0
      linarith only [cap.2]

/-- The genuine lower-wall limit at the lower-left band vertex. -/
theorem singleton_wall (K W : OpenSquare) (h : Input K W) :
    K.side*K.c-1≤K.s*K.loU+K.c*(K.loV+K.side) := by
  have endpoint : 0≤1+K.s*K.loU+K.c*K.loV := by
    apply affine_endpoint_nonnegative K.side (K.s+K.c) _ K.side_pos
    intro t positive small
    let u := K.loU+t
    let v := K.loV+t
    have own : K.Inside (K.c*u-K.s*v) (K.s*u+K.c*v) := by
      apply (inside_iff_rotated_box K _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp only [u,v,InBands]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [positive,small]
    have bound := h.wall _ _ own
    dsimp only [u,v] at bound
    nlinarith only [bound]
  nlinarith only [endpoint]

/-- WALL-SIGN §3.1, for the actual W in the untranslated local chart. -/
theorem wall_positive_caps (K W : OpenSquare) (h : Input K W)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c) :
    W.loU+W.side≤2*W.c ∧ W.loV+W.side≤W.c/2-W.s := by
  have o := h.o
  have p := h.pw
  have r := h.r
  dsimp [OpenSquare.Inside,InBands] at o p r
  have side : 1<W.side := by simpa only [←h.sameSide] using h.sideLarge
  have vCap : W.loV+W.side≤W.c/2-W.s := by
    by_contra no
    apply h.missingF0
    change W.loU<W.c+W.s/2 ∧ W.c+W.s/2<W.loU+W.side ∧
      W.loV< -W.s+W.c/2 ∧ -W.s+W.c/2<W.loV+W.side
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [p.1,r.2.1,o.2.2.1,cp,sn,order,no]
  have cAlternative : W.loU+W.side≤2*W.c ∨ -2*W.s≤W.loV := by
    by_cases first : W.loU+W.side≤2*W.c
    · exact Or.inl first
    · right
      by_contra second
      apply h.missingC
      change W.loU<2*W.c ∧ 2*W.c<W.loU+W.side ∧
        W.loV< -2*W.s ∧ -2*W.s<W.loV+W.side
      refine ⟨?_,lt_of_not_ge first,lt_of_not_ge second,?_⟩ <;>
        linarith only [r.1,o.2.2.2,cp,sn]
  rcases cAlternative with uCap | low
  · exact ⟨uCap,vCap⟩
  · have mAlternative : W.loU+W.side≤(27/20)*W.c+(13/20)*W.s ∨
        W.loV+W.side≤ -(27/20)*W.s+(13/20)*W.c := by
      by_cases first : W.loU+W.side≤(27/20)*W.c+(13/20)*W.s
      · exact Or.inl first
      · right
        by_contra second
        apply h.missingM
        refine ⟨?_,lt_of_not_ge first,?_,lt_of_not_ge second⟩ <;>
          dsimp [InBands] <;> linarith only [p.1,r.2.2.1,cp,sn]
    rcases mAlternative with highU | highV
    · exact ⟨by linarith only [highU,order],vCap⟩
    · have width : 1<(13/20)*(W.c+W.s) := by linarith only [side,low,highV]
      have bound : W.c+W.s≤3/2 := by
        nlinarith only [W.unit_normal,sq_nonneg (W.c-W.s)]
      linarith only [width,bound]

/-- MIDPOINT §1.2: the strict foreign seed forces W's positive angle
below arctan(2/3), including weak exterior contact at that seed. -/
theorem wall_positive_slope (K W : OpenSquare) (h : Input K W)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c) : 3*W.s<2*W.c := by
  have cap := wall_positive_caps K W h cp sn order
  have p := h.pw
  dsimp [OpenSquare.Inside,InBands] at p
  have outside : ¬W.Inside (24/25) (-6/25) := fun own => h.apart _ _ ⟨h.s,own⟩
  have side : 1<W.side := by simpa only [←h.sameSide] using h.sideLarge
  have cBound : W.c≤1 := by nlinarith only [W.unit_normal,sq_nonneg W.s,cp]
  have lower : (24/25)*W.c-(6/25)*W.s≤W.loU := by
    by_contra no
    apply outside
    refine ⟨lt_of_not_ge no,?_,?_,?_⟩ <;> dsimp [InBands]
    · linarith only [p.2.1,cp,sn]
    · have width : W.loV< -(24/25)*W.s-(6/25)*W.c := by
        linarith only [cap.2,side,cBound,sn]
      exact width
    · linarith only [p.2.2.2,cp,sn,order]
  have width : 1<(26/25)*W.c+(6/25)*W.s := by
    linarith only [side,lower,cap.1]
  by_contra no
  have steep : 2*W.c≤3*W.s := le_of_not_gt no
  have product := mul_nonneg (show 0≤3*W.s-2*W.c by linarith only [steep])
    (show 0≤(2544/625)*W.s+(344/625)*W.c by positivity)
  have identity : (324/25)*(W.c^2+W.s^2)-13*((26/25)*W.c+(6/25)*W.s)^2=
      (3*W.s-2*W.c)*((2544/625)*W.s+(344/625)*W.c) := by ring
  have square := mul_pos (sub_pos.mpr width)
    (show 0<(26/25)*W.c+(6/25)*W.s+1 by positivity)
  rw [W.unit_normal] at identity
  nlinarith only [product,identity,square]

end
#print axioms singleton_quadrant
#print axioms singleton_wall
#print axioms wall_positive_caps
#print axioms wall_positive_slope
end N12Compact.Completion.OtherCases.C983.C974MissingCorner
