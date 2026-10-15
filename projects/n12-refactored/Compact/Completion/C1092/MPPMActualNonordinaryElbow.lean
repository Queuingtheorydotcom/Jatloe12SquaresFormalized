import Compact.Completion.C1092.MPPMActualNonordinaryScalars

/-! ELBOW-EXCLUSION Lemma 1 and Theorem 3, with their literal local
points.  The negative successor orientation remains the conclusion of
the separate all-angle successor theorem, not an assumed original-case
fact.  The final local theorem eliminates every actual face separator. -/
namespace N12Compact.C1092MPPMActualNonordinary
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092TwoFifths.Support
set_option Elab.async false

structure SuccessorFaces (E : OpenSquare) : Prop where
  lowerU : -(1/2)*E.s≤E.loU
  upperU : E.loU+E.side≤E.c-E.s
  lowerV : -(543/500)*E.c≤E.loV
  upperV : E.loV+E.side≤-E.s-(2/5)*E.c

/-- Every exit is weak. In particular the corner's diagonal-band tie
retains strictness from its actual marker. -/
theorem successor_faces (E : OpenSquare) (side : 1<E.side)
    (en : Normal E.c (-E.s))
    (M : E.Inside (7/20) (-7/20))
    (A : E.Inside (13/50) (-1)) (B : E.Inside (2/5) (-1))
    (G : ¬E.Inside 1 (-2/5)) (K : ¬E.Inside 1 (-1))
    (R : ¬E.Inside 0 (-543/500)) (X : ¬E.Inside 0 (-1/2)) :
    SuccessorFaces E := by
  have eb := normal_bounds en
  have cp : 0<E.c := by linarith only [eb.1]
  have lowerU : -(1/2)*E.s≤E.loU := by
    apply le_of_not_gt
    intro low
    apply X
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,B.2.1,M.2.2.2,A.2.2.1,cp,en.1,en.2.1]
  have upperV : E.loV+E.side≤-E.s-(2/5)*E.c := by
    apply le_of_not_gt
    intro high
    apply G
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,M.1,A.2.2.1,lowerU,side,eb.2.1,cp,en.1]
  have cornerLow : E.loV< -E.s-E.c := by
    linarith only [upperV,side,eb.2.1]
  have upperU : E.loU+E.side≤E.c-E.s := by
    apply le_of_not_gt
    intro high
    apply K
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,B.1,M.2.2.2,cornerLow,cp,en.1,en.2.1]
  have lowerV : -(543/500)*E.c≤E.loV := by
    apply le_of_not_gt
    intro low
    apply R
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,B.2.1,A.2.2.2,upperU,side,eb.2.1,cp,en.1,en.2.1]
  exact ⟨lowerU,upperU,lowerV,upperV⟩

theorem successor_axes (C E : OpenSquare) (same : C.side=E.side)
    (cp : 0<C.c) (sp : 0<C.s) (dp : 0<E.c) (tn : E.s≤0)
    (M : C.Inside (-7/20) (-7/20)) (N : E.Inside (7/20) (-7/20))
    (apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)) :
    C.loU+C.side≤lower E C.c C.s ∨
      upper C C.s (-C.c)≤lower E C.s (-C.c) ∨
      upper C E.c E.s≤E.loU ∨ upper C (-E.s) E.c≤E.loV := by
  have choices := CongruentSAT.faceSeparation_of_disjoint C E same apart
  change pairRadius C E≤|C.c*(centerX E-centerX C)+C.s*(centerY E-centerY C)| ∨
    pairRadius C E≤|-C.s*(centerX E-centerX C)+C.c*(centerY E-centerY C)| ∨
    pairRadius E C≤|E.c*(centerX E-centerX C)+E.s*(centerY E-centerY C)| ∨
    pairRadius E C≤|-E.s*(centerX E-centerX C)+E.c*(centerY E-centerY C)| at choices
  have split (nx ny radius : ℝ)
      (eq : supportRadius C nx ny+supportRadius E nx ny=radius)
      (sep : radius≤|nx*(centerX E-centerX C)+ny*(centerY E-centerY C)|) :=
    separated C E nx ny (by rwa [eq])
  have rightward (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower E nx ny) : 0<nx := by
    have first := (strict_bounds C _ _ nx ny unit M).2
    have last := (strict_bounds E _ _ nx ny unit N).1
    linarith only [first,last,sep]
  rcases choices with cu|cv|eu|ev
  · rcases split _ _ _ (parallel_radius C E) cu with direct|back
    · exact Or.inl (by simpa only [(ownU C).2] using direct)
    · have no := rightward (-C.c) (-C.s) (by nlinarith only [C.unit_normal])
        (reverse C E _ _ back)
      exact False.elim (by linarith only [no,cp])
  · rcases split _ _ _ (transverse_radius C E) cv with direct|back
    · have no := rightward (-C.s) C.c (by nlinarith only [C.unit_normal]) direct
      exact False.elim (by linarith only [no,sp])
    · right; left
      simpa only [neg_neg] using reverse C E _ _ back
  · have radius : supportRadius C E.c E.s+supportRadius E E.c E.s=pairRadius E C := by
      rw [add_comm]; exact parallel_radius E C
    rcases split _ _ _ radius eu with direct|back
    · right; right; left
      simpa only [(ownU E).1] using direct
    · have no := rightward (-E.c) (-E.s) (by nlinarith only [E.unit_normal])
        (reverse C E _ _ back)
      exact False.elim (by linarith only [no,dp])
  · have radius : supportRadius C (-E.s) E.c+supportRadius E (-E.s) E.c=pairRadius E C := by
      rw [add_comm]; exact transverse_radius E C
    rcases split _ _ _ radius ev with direct|back
    · right; right; right
      simpa only [(ownV E).1] using direct
    · have no := rightward E.s (-E.c) (by nlinarith only [E.unit_normal])
        (by simpa only [neg_neg] using reverse C E _ _ back)
      exact False.elim (by linarith only [no,tn])

/-- Theorem 3 of the supplied elbow-exclusion chapter. The preceding
wall origin is an actual omission from C. No far-wall point or segment
is silently introduced, and E's frame is allowed the closed endpoint. -/
theorem origin_impossible (C E : OpenSquare)
    (side : 1<C.side) (same : C.side=E.side) (h : C1092ElbowProfile.Profile C)
    (en : Normal E.c (-E.s))
    (cM : C.Inside (-7/20) (-7/20)) (cP : C.Inside (-1) (-13/50))
    (cQ : C.Inside (-13/50) 0) (missing : ¬C.Inside (-1) 0)
    (M : E.Inside (7/20) (-7/20))
    (A : E.Inside (13/50) (-1)) (B : E.Inside (2/5) (-1))
    (G : ¬E.Inside 1 (-2/5)) (K : ¬E.Inside 1 (-1))
    (R : ¬E.Inside 0 (-543/500))
    (apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)) : False := by
  have cp : 0<C.c := by linarith only [h.cosine]
  have dp : 0<E.c := by linarith only [(normal_bounds en).1]
  have e := successor_faces E (by simpa only [←same] using side) en M A B G K R
    (fun own => apart 0 (-1/2) ⟨h.crosspoint,own⟩)
  have cap : C.loV+C.side≤C.s := by
    apply le_of_not_gt
    intro high
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,cP.1,cP.2.2.1,cQ.2.1,cp,h.sinePositive]
  let k := C.c*E.c+C.s*E.s
  let l := -C.c*E.s+C.s*E.c
  have rel := relative_bounds C.c C.s E.c (-E.s) h.normal en h.cosine h.sinePositive h.sine
  have kp : 0<k := by dsimp [k]; nlinarith only [rel.1]
  have lp : 0<l := by dsimp [l]; nlinarith only [rel.2.1]
  have strict := mul_pos (sub_pos.mpr side)
    (show 0<1+k+l by linarith only [kp,lp])
  have choices := successor_axes C E same cp h.sinePositive dp
    (by linarith only [en.1]) cM M apart
  rcases choices with own|transverse|neighbor|neighborV
  · have formula := lower_nn E C.c C.s k l
      (by dsimp [k]; ring) (by dsimp [l]; ring) kp.le lp.le
    have first := mul_nonneg kp.le
      (show 0≤E.c-E.s-C.side-E.loU by linarith only [e.upperU,same])
    have last := mul_nonneg lp.le
      (show 0≤-E.s-(2/5)*E.c-C.side-E.loV by linarith only [e.upperV,same])
    have margin := source_longitudinal C.c C.s E.c (-E.s) h.normal en cp h.sinePositive
    dsimp [k,l] at formula first last strict
    nlinarith only [own,formula,first,last,strict,h.lowerU,margin]
  · have formula := lower_pn E C.s (-C.c) l (-k)
      (by dsimp [l]; ring) (by dsimp [k]; ring) lp.le (by linarith only [kp])
    rw [←same] at formula
    have ownV : upper C C.s (-C.c)= -C.loV := by
      simpa only [neg_neg,(ABTransverse.ownV C).1] using
        upper_neg C (-C.s) C.c
    have first := mul_nonneg lp.le
      (show 0≤E.c-E.s-C.side-E.loU by linarith only [e.upperU,same])
    have last := mul_nonneg kp.le
      (show 0≤E.loV+(543/500)*E.c by linarith only [e.lowerV])
    have margin := source_transverse C.c C.s E.c (-E.s) h.normal en h.cosine h.sinePositive h.sine
    dsimp [k,l] at formula first last strict
    nlinarith only [transverse,formula,ownV,first,last,strict,cap,margin,same]
  · have formula := upper_pos_neg C E.c E.s k (-l)
      (by dsimp [k]; ring) (by dsimp [l]; ring) kp.le (by linarith only [lp])
    have first := mul_nonneg kp.le
      (show 0≤C.loU+C.c+(2/5)*C.s by linarith only [h.lowerU])
    have last := mul_nonneg lp.le
      (show 0≤C.s-C.side-C.loV by linarith only [cap])
    have margin := successor_longitudinal C.c C.s E.c (-E.s)
      h.normal en cp h.sinePositive h.halfSmall
    dsimp [k,l] at formula first last strict
    nlinarith only [neighbor,formula,first,last,strict,e.upperU,margin,same]
  · have formula := upper_pos_pos C (-E.s) E.c l k
      (by dsimp [l]; ring) (by dsimp [k]; ring) lp.le kp.le
    have first := mul_nonneg lp.le
      (show 0≤C.loU+C.c+(2/5)*C.s by linarith only [h.lowerU])
    have last := mul_nonneg kp.le
      (show 0≤C.loV+C.c-(2/5)*C.s by linarith only [h.lowerV])
    have margin := successor_transverse C.c C.s E.c (-E.s)
      h.normal en h.cosine h.sinePositive h.sine
    dsimp [k,l] at formula first last strict
    nlinarith only [neighborV,formula,first,last,strict,e.upperV,margin,same]

#print axioms successor_faces
#print axioms origin_impossible
end N12Compact.C1092MPPMActualNonordinary
