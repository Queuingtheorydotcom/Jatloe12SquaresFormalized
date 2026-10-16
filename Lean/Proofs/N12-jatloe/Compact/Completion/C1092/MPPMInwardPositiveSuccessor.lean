import Compact.Completion.C1092.MPPMInwardPositiveSuccessorFaces

/-! Complete same-square successor sign comparison for positive
missing-center inward C. Strict anchor cones remove five of the eight
signed face sources. Both relative-angle orders remain in the downward
comparisons. The extra foreign corner-marker datum is explicit in
PairInput and comes from the original paired corner in the application. -/
namespace N12Compact.C1092MPPMInwardPositive
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports SuccessorScalars
set_option Elab.async false
noncomputable section

private theorem axes (C E : OpenSquare) (h : PairInput C E) (en : Normal E.c E.s)
    (f : NonnegativeFaces E) :
    (C.loU+C.side≤lower E C.c C.s ∧ 0<delta C.c C.s E.c E.s) ∨
      upper C C.s (-C.c)≤lower E C.s (-C.c) ∨
      upper C E.s (-E.c)≤-(E.loV+E.side) := by
  have p := profile C h.source
  have cp : 0<C.c := by linarith only [(normal_bounds h.source.normal).1]
  have dp : 0<E.c := by linarith only [(normal_bounds en).1]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower E nx ny) : 0<nx ∧ 0<nx/2-(37/50)*ny := by
    have a := (strict_bounds C _ _ nx ny unit h.source.marker).2
    have b := (strict_bounds E _ _ nx ny unit h.recipient.successorMarker).1
    have c := (strict_bounds C _ _ nx ny unit h.source.inner).2
    have d := (strict_bounds E _ _ nx ny unit h.halfpoint).1
    constructor <;> linarith only [a,b,c,d,sep]
  rcases C1092MPPMSteepPositiveThreeSquare.signed_axes C E h.same h.apart
      with a|b|c|d|e|f'|g|j
  · have direction := (cone _ _ C.unit_normal a).2
    have first := mul_pos cp
      (show 0<E.s-(3/4)*E.c by linarith only [f.large,f.cosine])
    have last := mul_nonneg dp.le
      (show 0≤(3/4)*C.c-C.s by linarith only [direction,cp])
    refine Or.inl ⟨by simpa only [(ownU C).2] using a,?_⟩
    dsimp [delta]
    nlinarith only [first,last]
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) b).1
    exact False.elim (by linarith only [no,cp])
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) c).1
    exact False.elim (by linarith only [no,p.positive])
  · exact Or.inr (Or.inl d)
  · have no := (cone _ _ E.unit_normal e).2
    exact False.elim (by linarith only [no,f.large,f.cosine])
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) f').1
    exact False.elim (by linarith only [no,dp])
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) g).1
    exact False.elim (by linarith only [no,f.large])
  · have formula : lower E E.s (-E.c)=-(E.loV+E.side) := by
      have neg := C1092TwoFifths.Support.lower_neg E (-E.s) E.c
      simpa only [neg_neg,(ownV E).2] using neg
    exact Or.inr (Or.inr (by simpa only [formula] using j))

theorem nonnegative_successor_impossible (C E : OpenSquare) (h : PairInput C E)
    (en : Normal E.c E.s) : False := by
  have p := profile C h.source
  have f := nonnegative_faces C E h en
  let K := k C.c C.s E.c E.s
  let z := delta C.c C.s E.c E.s
  have rel := relative h.source.normal en
  have kp : 0<K := rel.1
  have capU : E.loU≤E.c-(2/5)*E.s-C.side := by linarith only [f.upperU,h.same]
  have capV : C.loV≤(7/20)*(C.c+C.s)-C.side := by linarith only [p.upperV]
  have lowerA : C.side-C.c-(2/5)*C.s≤C.loU+C.side := by linarith only [p.lowerU]
  have markerD : -(7/20)*(E.c+E.s)<E.loV+E.side := by
    linarith only [h.recipient.successorMarker.2.2.2]
  have sourceUp : upper C C.s (-C.c)= -C.loV := by
    have neg := C1092TwoFifths.Support.upper_neg C (-C.s) C.c
    simpa only [neg_neg,(ownV C).1] using neg
  rcases axes C E h en f with current|downward|target
  · have zp : 0<z := current.2
    have formula := lower_pn E C.c C.s K (-z)
      (by dsimp [K,k]) (by dsimp [z,delta]; ring) kp.le (neg_nonpos.mpr zp.le)
    have first := mul_le_mul_of_nonneg_left capU kp.le
    have last := mul_lt_mul_of_pos_left markerD zp
    have margin := source_margin h.source.normal en f.large
    have strict := mul_pos (sub_pos.mpr h.source.side)
      (show 0<1+K by linarith only [kp])
    rw [←h.same] at formula last
    dsimp [K,z] at formula first last strict
    nlinarith only [current.1,formula,first,last,margin,strict,lowerA]
  · have margin := downward_margin h.source.normal en
    have strict := h.source.side
    have last := mul_lt_mul_of_pos_left markerD kp
    by_cases order : 0≤z
    · have formula : lower E C.s (-C.c)=(-z)*(E.loU+E.side)-K*(E.loV+E.side) := by
        rw [(formulas E C.s (-C.c)).1,
          show C.s*E.c+(-C.c)*E.s= -z by dsimp [z,delta]; ring,
          show -C.s*E.s+(-C.c)*E.c= -K by dsimp [K,k]; ring,
          min_eq_left (neg_nonpos.mpr order),min_eq_left (neg_nonpos.mpr kp.le)]
        ring
      have markerJ : 0≤E.loU+E.side := by
        linarith only [h.recipient.successorMarker.2.1,en.2.1]
      have first := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr order) markerJ
      dsimp [K,z] at formula first last
      rw [sourceUp,formula] at downward
      nlinarith only [downward,first,last,margin,strict,p.upperV]
    · have zn : z≤0 := (lt_of_not_ge order).le
      have formula := lower_pn E C.s (-C.c) (-z) (-K)
        (by dsimp [z,delta]; ring) (by dsimp [K,k]; ring)
        (neg_nonneg.mpr zn) (neg_nonpos.mpr kp.le)
      have first := mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr zn)
        (show E.loU≤0 by linarith only [capU,(normal_bounds en).2.1,en.1,h.source.side])
      dsimp [K,z] at formula first last
      rw [sourceUp,formula] at downward
      nlinarith only [downward,first,last,margin,strict,p.upperV]
  · have upper := mul_le_mul_of_nonneg_left capV kp.le
    by_cases order : 0≤z
    · have formula := C1092TwoFifths.Support.upper_pos_neg C E.s (-E.c) z (-K)
        (by dsimp [z,delta]; ring) (by dsimp [K,k]; ring) order (neg_nonpos.mpr kp.le)
      have first := mul_le_mul_of_nonneg_left lowerA order
      have margin := target_after h.source.normal en
      have strict := mul_pos (sub_pos.mpr h.source.side)
        (show 0<1+z+K by linarith only [kp,order])
      rw [←h.same] at target
      dsimp [K,z] at formula first upper strict
      nlinarith only [target,formula,first,upper,margin,strict,f.lowerV]
    · have zn : z≤0 := (lt_of_not_ge order).le
      have formula := C1092TwoFifths.Support.upper_neg_neg C E.s (-E.c) z (-K)
        (by dsimp [z,delta]; ring) (by dsimp [K,k]; ring) zn (neg_nonpos.mpr kp.le)
      have first := mul_nonneg (neg_nonneg.mpr zn)
        (show 0≤-C.side-C.loU by linarith only [p.upperU])
      have margin := target_before h.source.normal en zn
      have strict := mul_pos (sub_pos.mpr h.source.side)
        (show 0<1-z+K by linarith only [kp,zn])
      rw [←h.same] at target
      dsimp [K,z] at formula first upper strict
      nlinarith only [target,formula,first,upper,margin,strict,f.lowerV,zn]

/-- This canonical representative is strictly negative, including the
zero and positive diagonal endpoints in the rejected alternative. -/
theorem successor_negative (C E : OpenSquare) (h : PairInput C E) (canonical : |E.s|≤E.c) :
    E.s<0 := by
  apply lt_of_not_ge
  intro nonnegative
  exact nonnegative_successor_impossible C E h
    ⟨nonnegative,by simpa only [abs_of_nonneg nonnegative] using canonical,E.unit_normal⟩

end
#print axioms nonnegative_successor_impossible
#print axioms successor_negative
end N12Compact.C1092MPPMInwardPositive
