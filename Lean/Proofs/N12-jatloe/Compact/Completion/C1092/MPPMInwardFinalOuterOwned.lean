import Compact.Completion.C1092.MPPMInwardFinalOuterOwnedScalars
import Compact.Completion.C1092.MPPMInwardFinalFloor
import Compact.Completion.C1092.MPPMInwardFinalCentered
import Compact.Geometry.ClosedFrames

/-! INWARD-OUTER-OWNED-ANGLE, Theorem 1 and Corollary 2. The whole
closed bottom segment is strict in one named foreign square B. In
particular its endpoint exits cannot be chosen independently.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardFinal
open S12 S12Pilot FourSquareAnchors C977CornerCubic C1092WallProfileScalars
set_option Elab.async false

structure OuterOwnedInput (C B : OpenSquare) : Prop where
  side : 1<C.side
  marker : C.Inside (-7/20) (-7/20)
  inner : C.Inside 0 (-13/50)
  forward : C.Inside (-13/50) 0
  outer : C.Inside (-1) (-2/5)
  origin : ¬C.Inside 0 0
  outerNear : ¬C.Inside (-1) (-13/50)
  bar : ∀ x : ℝ,-2/5≤x → x≤-13/50 → B.Inside x (-1)
  apart : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)

/-- The nonnegative sign obstruction does not use center omission. -/
theorem outer_nonnegative_impossible (C B : OpenSquare) (side : 1<C.side)
    (marker : C.Inside (-7/20) (-7/20)) (forward : C.Inside (-13/50) 0)
    (outer : C.Inside (-1) (-2/5)) (outerNear : ¬C.Inside (-1) (-13/50))
    (bar : ∀ x : ℝ,-2/5≤x → x≤-13/50 → B.Inside x (-1))
    (apart : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)) (cn : Normal C.c C.s) : False := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have upperV : C.loV+C.side≤C.s-(13/50)*C.c := by
    apply le_of_not_gt
    intro high
    apply outerNear
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [outer.1,forward.2.1,outer.2.2.1,high,cp,cn.1,cn.2.1]
  have lowerV : (2/5)*C.s-C.c≤C.loV := by
    apply le_of_not_gt
    intro low
    apply apart (-2/5) (-1)
    refine ⟨?_,bar _ le_rfl (by norm_num)⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [outer.1,marker.2.1,low,outer.2.2.2,cp,cn.1,cn.2.1]
  have width := (outer_short_width C.unit_normal).1
  linarith only [side,upperV,lowerV,width]

theorem outer_owned_negative (C B : OpenSquare) (h : OuterOwnedInput C B)
    (canonical : |C.s|≤C.c) : C.s<0 := by
  apply lt_of_not_ge
  intro nonnegative
  have cn : Normal C.c C.s := ⟨nonnegative,
    by simpa only [abs_of_nonneg nonnegative] using canonical,C.unit_normal⟩
  exact outer_nonnegative_impossible C B h.side h.marker h.forward h.outer h.outerNear h.bar h.apart cn

/-- All excluded endpoint faces are weak. The two alternatives at the
right endpoint include their distinct strict angle consequences. -/
theorem outer_owned_faces (C B : OpenSquare) (h : OuterOwnedInput C B)
    (cn : Normal C.c (-C.s)) (negative : C.s<0) :
    -C.c-(13/50)*C.s≤C.loU ∧ C.loV+C.side≤0 ∧
      -C.c+(2/5)*C.s≤C.loV ∧
      ((-C.c+(13/50)*C.s≤C.loV ∧ C.side≤C.c-(13/50)*C.s ∧
          half C.c (-C.s)<13/50) ∨
        (C.loU+C.side≤-(13/50)*C.c-C.s ∧ C.c< -2*C.s)) := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have upperV : C.loV+C.side≤0 := by
    apply le_of_not_gt
    intro high
    apply h.origin
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [h.forward.1,h.inner.2.1,h.marker.2.2.1,high,cp,cn.2.1,negative]
  have lowerU : -C.c-(13/50)*C.s≤C.loU := by
    apply le_of_not_gt
    intro low
    apply h.outerNear
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,h.marker.2.1,h.outer.2.2.1,h.inner.2.2.2,cp,cn.2.1,negative]
  have lowerV : -C.c+(2/5)*C.s≤C.loV := by
    apply le_of_not_gt
    intro low
    have upperU : -(2/5)*C.c-C.s<C.loU+C.side := by
      have width := (outer_short_width cn.2.2).2
      linarith only [lowerU,h.side,width]
    apply h.apart (-2/5) (-1)
    refine ⟨?_,h.bar _ le_rfl (by norm_num)⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [h.outer.1,upperU,low,h.outer.2.2.2,cp,cn.2.1,negative]
  refine ⟨lowerU,upperV,lowerV,?_⟩
  by_cases low : -C.c+(13/50)*C.s≤C.loV
  · have width : C.side≤C.c-(13/50)*C.s := by linarith only [low,upperV]
    exact Or.inl ⟨low,width,outer_lower_half cn (by linarith only [h.side,width])⟩
  · have cap : C.loU+C.side≤-(13/50)*C.c-C.s := by
      apply le_of_not_gt
      intro high
      apply h.apart (-13/50) (-1)
      refine ⟨?_,h.bar _ (by norm_num) le_rfl⟩
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [h.outer.1,high,low,h.inner.2.2.2,cp,cn.2.1,negative]
    refine Or.inr ⟨cap,?_⟩
    nlinarith only [outer_upper_slope cn (by linarith only [h.side,lowerU,cap])]

/-- The actual segment crossing rules out the entire bad arc, including
the equality at its algebraic endpoint. -/
theorem outer_owned_polynomial (C B : OpenSquare) (h : OuterOwnedInput C B)
    (cn : Normal C.c (-C.s)) (negative : C.s<0) :
    0<(half C.c (-C.s))^2-2*half C.c (-C.s)+12/25 := by
  have faces := outer_owned_faces C B h cn negative
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have sp : 0< -C.s := by linarith only [negative]
  let z := half C.c (-C.s)
  have zb := canonical_half_bounds cn
  have identities := outer_q_identity cn
  apply lt_of_not_ge
  intro bad
  rcases faces.2.2.2 with low|upper
  · nlinarith only [bad,low.2.2,sq_nonneg (z-13/50)]
  · let Q := 1-C.c-(13/50)*C.s
    have product := mul_nonpos_of_nonneg_of_nonpos zb.1 bad
    have scaled : 0≤(1+z^2)*(Q-z) := by
      dsimp [Q,z]
      nlinarith only [identities.1,product]
    have qlow : z≤Q := by
      have value := nonneg_of_mul_nonneg_right scaled
        (by nlinarith only [sq_nonneg z] : 0<1+z^2)
      linarith only [value]
    have qproduct := mul_nonneg sp.le (sub_nonneg.mpr qlow)
    have arc : 0≤C.c-C.s-1+C.c*C.s+(13/50)*C.s^2 := by
      dsimp [Q,z] at qproduct
      nlinarith only [identities.2,qproduct]
    let A := C.loU+C.side
    let Y := C.s*A+C.c*C.loV
    have first := mul_nonneg sp.le (sub_nonneg.mpr faces.1)
    have last := mul_nonneg cp.le
      (show 0≤-C.side-C.loV by linarith only [faces.2.1])
    have strict := mul_pos (sub_pos.mpr h.side)
      (show 0<C.c-C.s by linarith only [cp,negative])
    have below : Y< -1 := by
      dsimp [Y,A]
      nlinarith only [first,last,strict,arc]
    let xl := (C.loV+C.c)/(-C.s)
    let xr := (A+C.s)/C.c
    have xl_eq : xl*(-C.s)=C.loV+C.c := div_mul_cancel₀ _ sp.ne'
    have xr_eq : xr*C.c=A+C.s := div_mul_cancel₀ _ cp.ne'
    have xl_low : -2/5≤xl := by
      apply le_of_not_gt
      intro no
      have product := mul_neg_of_neg_of_pos (show xl+2/5<0 by linarith only [no]) sp
      nlinarith only [product,xl_eq,faces.2.2.1]
    have xr_high : xr≤-13/50 := by
      apply le_of_not_gt
      intro no
      have product := mul_pos (show 0<xr+13/50 by linarith only [no]) cp
      dsimp [A] at xr_eq
      nlinarith only [product,xr_eq,upper.1]
    have separation : xl<xr := by
      have identity : (-C.s)*C.c*(xr-xl)= -1-Y := by
        dsimp [Y]
        linear_combination (-C.s)*xr_eq-C.c*xl_eq-C.unit_normal
      have positive : 0<(-C.s)*C.c*(xr-xl) := by rw [identity]; linarith only [below]
      have unscaled := pos_of_mul_pos_right positive (mul_nonneg sp.le cp.le)
      linarith only [unscaled]
    let x := (xl+xr)/2
    have xlow : -2/5≤x := by dsimp [x]; linarith only [xl_low,separation]
    have xhigh : x≤-13/50 := by dsimp [x]; linarith only [xr_high,separation]
    have vlow : C.loV< -C.s*x-C.c := by
      have product := mul_pos sp (show 0<x-xl by dsimp [x]; linarith only [separation])
      nlinarith only [product,xl_eq]
    have uhigh : C.c*x-C.s<A := by
      have product := mul_pos cp (show 0<xr-x by dsimp [x]; linarith only [separation])
      nlinarith only [product,xr_eq]
    have firstBand := mul_nonneg cp.le (show 0≤x+2/5 by linarith only [xlow])
    have lastBand := mul_nonneg sp.le (show 0≤-13/50-x by linarith only [xhigh])
    apply h.apart x (-1)
    refine ⟨?_,h.bar x xlow xhigh⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      dsimp [A] at uhigh <;>
      nlinarith only [firstBand,lastBand,h.outer.1,h.inner.2.2.2,
        uhigh,vlow,cp,cn.2.1,negative]

/-- Raw physical profile producer for the outer-owned missing-center
branch. Nothing about the predecessor or successor is assumed here. -/
theorem outer_owned_profile (C B : OpenSquare) (h : OuterOwnedInput C B)
    (canonical : |C.s|≤C.c) :
    MissingProfile C ∧ half C.c (-C.s)<1-Real.sqrt 13/5 ∧
      half C.c (-C.s)<279/1000 := by
  have negative := outer_owned_negative C B h canonical
  have cn : Normal C.c (-C.s) := ⟨by linarith only [negative],
    by simpa only [abs_of_neg negative] using canonical,by nlinarith only [C.unit_normal]⟩
  have faces := outer_owned_faces C B h cn negative
  have angle := outer_angle_bounds cn (outer_owned_polynomial C B h cn negative)
  refine ⟨⟨h.side,cn,negative,angle.2.2.1,angle.2.2.2,h.marker,h.inner,
    h.forward,h.outer,faces.1,faces.2.2.1,faces.2.1,?_⟩,angle.1,angle.2.1⟩
  rcases faces.2.2.2 with low|high
  · exact Or.inl ⟨low.1,low.2.1⟩
  · exact Or.inr high.1

theorem outer_owned_halfpoint (C B : OpenSquare) (h : OuterOwnedInput C B)
    (canonical : |C.s|≤C.c) : C.Inside (-1) (-1/2) := by
  have profile := outer_owned_profile C B h canonical
  have p := profile.1
  have projection := outer_halfpoint_projection p.normal
    (show half C.c (-C.s)<1/3 by linarith only [profile.2.2])
  have cp : 0<C.c := by linarith only [p.close]
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [h.outer.1,h.marker.2.1,p.upperV,h.side,projection,
      h.outer.2.2.2,cp,p.normal.2.1,p.negative]

/-- Face reindexing, not a new owner: the theorem covers every original
orientation while preserving the exact strict interior of C. -/
theorem outer_owned_frame (C B : OpenSquare) (h : OuterOwnedInput C B) :
    ∃ D : OpenSquare,D.side=C.side ∧
      (∀ x y,D.Inside x y ↔ C.Inside x y) ∧ MissingProfile D ∧
      half D.c (-D.s)<1-Real.sqrt 13/5 ∧ C.Inside (-1) (-1/2) := by
  obtain ⟨D,cp,canonical,same,inside,closed⟩ := ClosedFrames.canonical_frame C
  have hd : OuterOwnedInput D B :=
    ⟨by simpa only [same] using h.side,
      (inside _ _).mpr h.marker,(inside _ _).mpr h.inner,
      (inside _ _).mpr h.forward,(inside _ _).mpr h.outer,
      fun own => h.origin ((inside _ _).mp own),
      fun own => h.outerNear ((inside _ _).mp own),h.bar,
      fun x y own => h.apart x y ⟨(inside x y).mp own.1,own.2⟩⟩
  have profile := outer_owned_profile D B hd canonical
  exact ⟨D,same,inside,profile.1,profile.2.1,
    (inside _ _).mp (outer_owned_halfpoint D B hd canonical)⟩

/-- The genuine paired corner transfer gives the actual bottom origin,
without assigning an owner to any omitted auxiliary. -/
theorem outer_owned_origin (C B K : OpenSquare) (h : OuterOwnedInput C B)
    (bottom : BottomCorner B K)
    (apart : ∀ x y,¬(C.Inside x y ∧ K.Inside x y)) : B.Inside 0 (-1) := by
  obtain ⟨D,same,inside,profile,angle,halfpoint⟩ := outer_owned_frame C B h
  exact bottom_origin C B K bottom halfpoint apart

/-- The literal Q4/Q9 chart. The actual bottom owner, including both
endpoints of its segment, is unchanged by translation. -/
theorem outer_owned_halfpoint_original (C B : OpenSquare) (side : 1<C.side)
    (marker : C.Inside (33/20) (33/20))
    (inner : C.Inside 2 (87/50)) (forward : C.Inside (87/50) 2)
    (outer : C.Inside 1 (8/5))
    (origin : ¬C.Inside 2 2) (outerNear : ¬C.Inside 1 (87/50))
    (bar : ∀ x : ℝ,8/5≤x → x≤87/50 → B.Inside x 1)
    (apart : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)) : C.Inside 1 (3/2) := by
  let C' := C.translated 2 2
  let B' := B.translated 2 2
  have ci (x y : ℝ) : C'.Inside x y ↔ C.Inside (2+x) (2+y) :=
    inside_translated_iff C 2 2 x y
  have bi (x y : ℝ) : B'.Inside x y ↔ B.Inside (2+x) (2+y) :=
    inside_translated_iff B 2 2 x y
  have h : OuterOwnedInput C' B' :=
    { side := side
      marker := by rw [ci]; norm_num; exact marker
      inner := by rw [ci]; norm_num; exact inner
      forward := by rw [ci]; norm_num; exact forward
      outer := by rw [ci]; norm_num; exact outer
      origin := by rw [ci]; norm_num; exact origin
      outerNear := by rw [ci]; norm_num; exact outerNear
      bar := by
        intro x low high
        rw [bi]
        norm_num
        exact bar _ (by linarith only [low]) (by linarith only [high])
      apart := fun x y own => apart _ _ ⟨(ci x y).mp own.1,(bi x y).mp own.2⟩ }
  obtain ⟨D,same,inside,profile,angle,halfpoint⟩ := outer_owned_frame C' B' h
  have actual := (ci (-1) (-1/2)).mp halfpoint
  norm_num at actual
  exact actual

#print axioms outer_owned_profile
#print axioms outer_owned_frame
#print axioms outer_owned_origin
#print axioms outer_owned_halfpoint_original
end N12Compact.C1092MPPMInwardFinal
