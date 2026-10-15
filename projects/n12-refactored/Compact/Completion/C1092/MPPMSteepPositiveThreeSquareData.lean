import Compact.Completion.C1092.MPPMCrosspointSupportScalars
import Compact.Completion.C1092.WholeSupports
import Compact.Completion.C1092.TwoFifthsSupport
import Compact.Completion.C1092.ShallowBoundarySupport

/-! Literal three-square input and the complete directed normal sources
in STEEP-POSITIVE-THREE-SQUARE-REDUCTION, sections 1--2. The boundary
square is arbitrary; its first-quadrant reframe will be chosen only once.
All point hypotheses are strict and every separating face remains weak.
Source only: no compiler or replay was run. -/
namespace N12Compact.C1092MPPMSteepPositiveThreeSquare
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092MPPMCrosspointSupport
open C1092TwoFifths.Support
set_option Elab.async false
noncomputable section

structure Input (C E B : OpenSquare) : Prop where
  side : 1<C.side
  sameE : C.side=E.side
  sameB : C.side=B.side
  central : Normal C.c C.s
  recipient : Normal E.c E.s
  steep : 3/5≤C.s
  lowerU : -C.c-C.s≤C.loU
  upperU : C.loU+C.side≤-C.c/2
  upperV : C.loV+C.side≤(543/500)*C.s
  markerC : C.Inside (-7/20) (-7/20)
  ordinaryC : C.Inside (-1) (-13/50)
  upperE : E.loU+E.side≤E.c-(14/25)*E.s
  bottomE : E.Inside (2/5) (-1)
  crosspointE : E.Inside 0 (-1/2)
  markerB : B.Inside 0 (-543/500)
  outerB : B.Inside (-2/5) (-1)
  originB : B.Inside 0 (-1)
  wall : ∀ x y,B.Inside x y→-2≤y
  apartC : ∀ x y,¬(B.Inside x y ∧ C.Inside x y)
  apartE : ∀ x y,¬(B.Inside x y ∧ E.Inside x y)

/-- The complete signed actual face alternatives, before using anchors.
The displayed normal always points from the first square to the second. -/
theorem signed_axes (B Q : OpenSquare) (same : B.side=Q.side)
    (apart : ∀ x y,¬(B.Inside x y ∧ Q.Inside x y)) :
    upper B B.c B.s≤lower Q B.c B.s ∨
    upper B (-B.c) (-B.s)≤lower Q (-B.c) (-B.s) ∨
    upper B (-B.s) B.c≤lower Q (-B.s) B.c ∨
    upper B B.s (-B.c)≤lower Q B.s (-B.c) ∨
    upper B Q.c Q.s≤lower Q Q.c Q.s ∨
    upper B (-Q.c) (-Q.s)≤lower Q (-Q.c) (-Q.s) ∨
    upper B (-Q.s) Q.c≤lower Q (-Q.s) Q.c ∨
    upper B Q.s (-Q.c)≤lower Q Q.s (-Q.c) := by
  have axes := CongruentSAT.faceSeparation_of_disjoint B Q same apart
  change pairRadius B Q≤|B.c*(centerX Q-centerX B)+B.s*(centerY Q-centerY B)| ∨
    pairRadius B Q≤|-B.s*(centerX Q-centerX B)+B.c*(centerY Q-centerY B)| ∨
    pairRadius Q B≤|Q.c*(centerX Q-centerX B)+Q.s*(centerY Q-centerY B)| ∨
    pairRadius Q B≤|-Q.s*(centerX Q-centerX B)+Q.c*(centerY Q-centerY B)| at axes
  have split (nx ny radius : ℝ)
      (eq : supportRadius B nx ny+supportRadius Q nx ny=radius)
      (sep : radius≤|nx*(centerX Q-centerX B)+ny*(centerY Q-centerY B)|) :=
    separated B Q nx ny (by rwa [eq])
  rcases axes with bu|bv|qu|qv
  · rcases split _ _ _ (parallel_radius B Q) bu with direct|back
    · exact Or.inl direct
    · exact Or.inr (Or.inl (reverse B Q _ _ back))
  · rcases split _ _ _ (transverse_radius B Q) bv with direct|back
    · exact Or.inr (Or.inr (Or.inl direct))
    · have result := reverse B Q _ _ back
      exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [neg_neg] using result))))
  · have radius : supportRadius B Q.c Q.s+supportRadius Q Q.c Q.s=pairRadius Q B := by
      rw [add_comm]; exact parallel_radius Q B
    rcases split _ _ _ radius qu with direct|back
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl direct))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (reverse B Q _ _ back))))))
  · have radius : supportRadius B (-Q.s) Q.c+supportRadius Q (-Q.s) Q.c=pairRadius Q B := by
      rw [add_comm]; exact transverse_radius Q B
    rcases split _ _ _ radius qv with direct|back
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl direct))))))
    · have result := reverse B Q _ _ back
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (by simpa only [neg_neg] using result)))))))

theorem anchor_cone (C B : OpenSquare)
    (markerC : C.Inside (-7/20) (-7/20)) (ordinaryC : C.Inside (-1) (-13/50))
    (markerB : B.Inside 0 (-543/500)) (outerB : B.Inside (-2/5) (-1))
    (nx ny : ℝ) (unit : nx^2+ny^2=1)
    (sep : upper B nx ny≤lower C nx ny) :
    0<ny ∧ nx<(413/500)*ny := by
  have p := (strict_bounds C _ _ nx ny unit ordinaryC).1
  have b := (strict_bounds B _ _ nx ny unit markerB).2
  have m := (strict_bounds C _ _ nx ny unit markerC).1
  have f := (strict_bounds B _ _ nx ny unit outerB).2
  constructor <;> linarith only [p,b,m,f,sep]

theorem central_cone (C E B : OpenSquare) (h : Input C E B)
    (nx ny : ℝ) (unit : nx^2+ny^2=1)
    (sep : upper B nx ny≤lower C nx ny) :
    0<ny ∧ nx<(413/500)*ny :=
  anchor_cone C B h.markerC h.ordinaryC h.markerB h.outerB nx ny unit sep

theorem recipient_cone (C E B : OpenSquare) (h : Input C E B)
    (nx ny : ℝ) (unit : nx^2+ny^2=1)
    (sep : upper B nx ny≤lower E nx ny) : 0<nx ∧ 0<ny := by
  have b := (strict_bounds E _ _ nx ny unit h.bottomE).1
  have y := (strict_bounds E _ _ nx ny unit h.crosspointE).1
  have o := (strict_bounds B _ _ nx ny unit h.originB).2
  constructor <;> linarith only [b,y,o,sep]

/-- The stronger omitted-crosspoint face A<=-c/2 makes the manuscript's
northeast exclusion derivative-free. Its two coefficient bounds are
strict throughout the closed canonical sector. -/
theorem northeast_of_faces (C B : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (sp : 0<C.s)
    (upperU : C.loU+C.side≤-C.c/2)
    (upperV : C.loV+C.side≤(543/500)*C.s)
    (markerC : C.Inside (-7/20) (-7/20)) (ordinaryC : C.Inside (-1) (-13/50))
    (markerB : B.Inside 0 (-543/500)) (outerB : B.Inside (-2/5) (-1))
    (nx ny : ℝ) (unit : nx^2+ny^2=1) (xn : 0≤nx) (yn : 0≤ny) :
    ¬upper B nx ny≤lower C nx ny := by
  intro sep
  have cone := anchor_cone C B markerC ordinaryC markerB outerB nx ny unit sep
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  let u := nx*C.c+ny*C.s
  let v := -nx*C.s+ny*C.c
  have un : 0≤u := by dsimp [u]; positivity
  have vp : 0<v := by
    have order := mul_le_mul_of_nonneg_left cn.2.1 cone.1.le
    have margin := mul_pos sp
      (show 0<ny-nx by linarith only [cone.1,cone.2])
    dsimp [v]
    nlinarith only [order,margin]
  have formula := lower_nn C nx ny u v rfl rfl un vp.le
  have upper := mul_le_mul_of_nonneg_left upperU un
  have transverse := mul_le_mul_of_nonneg_left upperV vp.le
  have sideWeight := mul_nonneg (sub_nonneg.mpr side.le)
    (show 0≤u+v by linarith only [un,vp])
  have coefficientX : -(1/10)-C.c+C.s-(293/500)*C.s^2<0 := by
    nlinarith only [cn.2.1,sq_nonneg C.s]
  have product := mul_nonneg
    (show 0≤C.c+C.s-1 by linarith only [cb.2.2.2.2.1])
    (show 0≤(17/7)-(C.c+C.s+1) by linarith only [cb.2.2.2.2.2])
  have arc : (14/17)*C.c*C.s≤C.c+C.s-1 := by
    nlinarith only [product,cn.2.2]
  have cs := mul_pos cp sp
  have coefficientY : 1-C.c-C.s+(293/500)*C.c*C.s<0 := by
    nlinarith only [arc,cs]
  have first := mul_nonpos_of_nonneg_of_nonpos xn coefficientX.le
  have last := mul_neg_of_pos_of_neg cone.1 coefficientY
  have identity : u*(-C.c/2-1)+v*((543/500)*C.s-1)+
      (2/5)*nx+ny=
      nx*(-(1/10)-C.c+C.s-(293/500)*C.s^2)+
        ny*(1-C.c-C.s+(293/500)*C.c*C.s) := by
    dsimp [u,v]
    linear_combination -(nx/2)*cn.2.2
  have foreign := (strict_bounds B _ _ nx ny unit outerB).2
  nlinarith only [formula,upper,transverse,sideWeight,first,last,identity,foreign,sep]

theorem northeast_impossible (C E B : OpenSquare) (h : Input C E B)
    (nx ny : ℝ) (unit : nx^2+ny^2=1) (xn : 0≤nx) (yn : 0≤ny) :
    ¬upper B nx ny≤lower C nx ny :=
  northeast_of_faces C B h.side h.central (by linarith only [h.steep])
    h.upperU h.upperV h.markerC h.ordinaryC h.markerB h.outerB nx ny unit xn yn

/-- All eight actual signed sources reduce to C's upward transverse
normal or the boundary's northwest normal. Coordinate endpoints survive
only when their strict anchor cone permits them. -/
theorem central_sources (C E B : OpenSquare) (h : Input C E B)
    (bn : Quarter B.c B.s) :
    upper B (-C.s) C.c≤C.loV ∨ upper B (-B.s) B.c≤lower C (-B.s) B.c := by
  have cb := normal_bounds h.central
  have bc := B.unit_normal
  have cc := C.unit_normal
  have cone := central_cone C E B h
  rcases signed_axes B C h.sameB.symm h.apartC with a|b|c|d|e|f|g|j
  · exact False.elim (northeast_impossible C E B h _ _ bc bn.cosine bn.sine a)
  · have no := (cone _ _ (by nlinarith only [bc]) b).1
    exact False.elim (by linarith only [no,bn.sine])
  · exact Or.inr c
  · have no := (cone _ _ (by nlinarith only [bc]) d).1
    exact False.elim (by linarith only [no,bn.cosine])
  · have no := (cone _ _ cc e).2
    exact False.elim (by linarith only [no,h.central.2.1,cb.1])
  · have no := (cone _ _ (by nlinarith only [cc]) f).1
    exact False.elim (by linarith only [no,h.central.1])
  · exact Or.inl (by simpa only [(ownV C).1] using g)
  · have no := (cone _ _ (by nlinarith only [cc]) j).1
    exact False.elim (by linarith only [no,cb.1])

theorem recipient_sources (C E B : OpenSquare) (h : Input C E B)
    (bn : Quarter B.c B.s) :
    upper B E.c E.s≤E.loU ∨ upper B B.c B.s≤lower E B.c B.s := by
  have eb := normal_bounds h.recipient
  have bc := B.unit_normal
  have ec := E.unit_normal
  have cone := recipient_cone C E B h
  rcases signed_axes B E (h.sameB.symm.trans h.sameE) h.apartE with a|b|c|d|e|f|g|j
  · exact Or.inr a
  · have no := (cone _ _ (by nlinarith only [bc]) b).1
    exact False.elim (by linarith only [no,bn.cosine])
  · have no := (cone _ _ (by nlinarith only [bc]) c).1
    exact False.elim (by linarith only [no,bn.sine])
  · have no := (cone _ _ (by nlinarith only [bc]) d).2
    exact False.elim (by linarith only [no,bn.cosine])
  · exact Or.inl (by simpa only [(ownU E).1] using e)
  · have no := (cone _ _ (by nlinarith only [ec]) f).1
    exact False.elim (by linarith only [no,eb.1])
  · have no := (cone _ _ (by nlinarith only [ec]) g).1
    exact False.elim (by linarith only [no,h.recipient.1])
  · have no := (cone _ _ (by nlinarith only [ec]) j).2
    exact False.elim (by linarith only [no,eb.1])

end
#print axioms central_sources
#print axioms recipient_sources
end N12Compact.C1092MPPMSteepPositiveThreeSquare
