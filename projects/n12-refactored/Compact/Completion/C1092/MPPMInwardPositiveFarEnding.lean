import Compact.Completion.C1092.MPPMInwardPositiveFarFaces
import Compact.Completion.C1092.MPPMInwardPositiveFarScalars

/-! POSITIVE-MISSING-INWARD-FAR-ENDING. The small central arc uses
the two exact alternatives from one actual preceding-wall segment.
The large arc uses the simultaneous marker cap. All four actual C/E
normal sources are discharged; no opposite-owner type is assumed in
this raw local theorem. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardPositive
open S12 S12Pilot C977CornerCubic C1092WallProfileScalars C1092WholeSupports
set_option Elab.async false
noncomputable section

theorem far_target_support (C E L : OpenSquare) (h : PairInput C E)
    (en : Normal E.c (-E.s)) (small : half C.c C.s≤1/5)
    (far : ¬E.Inside 1 (-14/25))
    (marker : L.Inside (-543/500) 0) (seed : L.Inside (-1) (13/50))
    (apart : ∀ x y,¬(C.Inside x y ∧ L.Inside x y)) : E.loU<upper C E.c E.s := by
  have p := profile C h.source
  have e := negative_faces C E h en
  have large := (negative_far_faces C E h en far).2
  have cut := left_segment_alternatives C L h.source marker seed apart
  rcases cut with transverse|oblique
  · exact target_support_of_cap C E h en ((543/500)*C.s) transverse
      (FarScalars.transverse_target h.source.normal en small large.le)
  · let a := FarScalars.alpha C.c C.s
    let g := FarScalars.gamma C.c C.s
    let k := NegativeScalars.k C.c C.s E.c (-E.s)
    let l := NegativeScalars.ell C.c C.s E.c (-E.s)
    let D : ℝ := 7059/25000
    have cb := normal_bounds h.source.normal
    have eb := normal_bounds en
    have cp : 0<C.c := by linarith only [cb.1]
    have ap : 0<a := by dsimp [a,FarScalars.alpha]; linarith only [cp,h.source.normal.2.1]
    have gp : 0<g := by dsimp [g,FarScalars.gamma]; linarith only [cp,p.positive]
    have rel := NegativeScalars.relative h.source.normal p.strictOrder p.positive en
    have kp : 0<k := rel.1
    have lp : 0<l := rel.2.1
    have coefficient : k*g-l*a=(43/500)*E.c+(13/50)*E.s := by
      dsimp [k,l,g,a,NegativeScalars.k,NegativeScalars.ell,FarScalars.alpha,FarScalars.gamma]
      linear_combination ((43/500)*E.c+(13/50)*E.s)*C.unit_normal
    have negative : k*g-l*a<0 := by linarith only [coefficient,large,eb.2.1]
    have first := mul_nonneg (neg_nonneg.mpr negative.le)
      (show 0≤-C.loU-C.side by linarith only [p.upperU])
    have second := mul_nonneg lp.le
      (show 0≤a*C.loU-g*(C.loV+C.side)+D by
        dsimp [a,g,D,FarScalars.alpha,FarScalars.gamma]
        linarith only [oblique])
    have capU : E.loU≤E.c-E.s-C.side := by linarith only [e.upperU,h.same]
    have last := mul_nonneg gp.le (sub_nonneg.mpr capU)
    have reserve := mul_pos (sub_pos.mpr h.source.side)
      (show 0<g+l*(a+g) by positivity)
    have scalar := FarScalars.oblique_target h.source.normal en small large.le
    change 0<g*(1-E.c+E.s)+l*FarScalars.L0 C.c C.s at scalar
    have formula := C1092TwoFifths.Support.upper_pos_neg C E.c E.s k (-l)
      (by dsimp [k,NegativeScalars.k]; ring) (by dsimp [l,NegativeScalars.ell]; ring)
      kp.le (neg_nonpos.mpr lp.le)
    have identity : g*(upper C E.c E.s-E.loU)=
        (k*g-l*a)*(C.loU+C.side)+l*(a*C.loU-g*(C.loV+C.side)+D)+
        (C.side-1)*(g+l*(a+g))+g*(1-E.c+E.s)+l*FarScalars.L0 C.c C.s+
        g*(E.c-E.s-C.side-E.loU) := by
      rw [formula]
      dsimp [FarScalars.L0,D,a,g]
      ring
    have positive : 0<g*(upper C E.c E.s-E.loU) := by
      nlinarith only [identity,first,second,last,reserve,scalar]
    have result := pos_of_mul_pos_right positive gp.le
    linarith only [result]

/-- Both strict endpoints of the entire preceding-wall segment stay
in one actual L. The right far point is a genuine omission from E. -/
theorem far_impossible (C E L : OpenSquare) (h : PairInput C E)
    (canonical : |E.s|≤E.c) (far : ¬E.Inside 1 (-14/25))
    (marker : L.Inside (-543/500) 0) (seed : L.Inside (-1) (13/50))
    (apart : ∀ x y,¬(C.Inside x y ∧ L.Inside x y)) : False := by
  have p := profile C h.source
  have negative := successor_negative C E h canonical
  have en : Normal E.c (-E.s) :=
    ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using canonical,
      by nlinarith only [E.unit_normal]⟩
  apply impossible_of_target C E h en
  by_cases small : half C.c C.s≤1/5
  · exact far_target_support C E L h en small far marker seed apart
  · exact target_support_of_cap C E h en ((7/20)*(C.c+C.s)) p.upperV
      (NegativeScalars.marker_target h.source.normal en (le_of_lt (lt_of_not_ge small)) p.halfSmall.le)

end
#print axioms far_target_support
#print axioms far_impossible
end N12Compact.C1092MPPMInwardPositive
