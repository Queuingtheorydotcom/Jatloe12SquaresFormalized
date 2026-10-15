import Compact.Completion.OtherCases.C983.MergedCenterF5
import Compact.Completion.OtherCases.C983.LeftOrigin
import Compact.Completion.OtherCases.WallProfile.VertexGeometry
import Compact.Completion.C981.SupportForms

/-! Source translation of §§1–3 of `C983-F4-MERGED-CENTER.md` in the
2026-10-13 handoff. Coordinates in `Input` are translated by (-2,-2).

The actual singleton corner (1,1) is an explicit premise of `actual_input`.
Its manuscript proof is in `C983-F4-LEFT-ORIGIN-AND-CORNER-ROOT.md`, §4;
it is not inferred here from the auxiliary ownership table. The resulting
missing-center reduction is not yet the positive-sector contradiction of
§§4–7, and this file does not assert an unconditional merged-center theorem.
No compiler replay has been performed for this translation. -/
namespace N12Compact.Completion.OtherCases.C983.F4MergedCenter
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false
noncomputable section

/-- The exact actual-square prerequisites displayed in manuscript §1. -/
structure Input (W K : OpenSquare) : Prop where
  sideLarge : 1<W.side
  sideSmall : W.side≤1001/1000
  sameSide : W.side=K.side
  south : W.Inside (-7/20) (-7/20)
  north : W.Inside (-7/20) (7/20)
  inner : W.Inside 0 (-13/50)
  west : W.Inside (-13/50) 0
  corner : K.Inside (-1) (-1)
  auxiliary : K.Inside (-1) (-13/50)
  seed : K.Inside (-31/25) (-13/100)
  marker : K.Inside (-543/500) (-1)
  missingLeft : ¬W.Inside (-1) 0
  missingMarker : ¬K.Inside (-1) (-543/500)
  leftWall : ∀ x y, K.Inside x y → -2≤x
  apart : ∀ x y, ¬(K.Inside x y ∧ W.Inside x y)

/-- All manuscript prerequisites except its separately proved singleton
corner are already available from the actual C983 entrance. -/
theorem actual_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) (corner : (owners p 1).Inside 1 1) :
    Input ((owners p 7).translated 2 2) ((owners p 1).translated 2 2) := by
  have south : (owners p 7).Inside (33/20) (33/20) := by
    have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have north : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have inner : (owners p 7).Inside 2 (87/50) := by
    have h := auxiliary_inside p 7 4 (by decide +kernel) f4
    simpa [auxPoints,fPoints,gPoints] using h
  have west : (owners p 7).Inside (87/50) 2 := by
    have h := auxiliary_inside p 7 13 (by decide +kernel) (merged_g3 p hf)
    simpa [auxPoints,fPoints,gPoints] using h
  have auxiliary : (owners p 1).Inside 1 (87/50) := by
    have h := seed_inside p hf 1 (1,87/50) (by decide +kernel)
    norm_num at h
    exact h
  have seed : (owners p 1).Inside (19/25) (187/100) := by
    have h := seed_inside p hf 1 (19/25,187/100) (by decide +kernel)
    norm_num at h
    exact h
  have marker : (owners p 1).Inside (457/500) 1 := by
    have h := seed_inside p hf 1 (457/500,1) (by decide +kernel)
    norm_num at h
    exact h
  have foreign : (owners p 0).Inside 1 (457/500) := by
    have h := seed_inside p hf 0 (1,457/500) (by decide +kernel)
    norm_num at h
    exact h
  have left := left_origin_of_top_g7 p hf (f4_top p hf f4).1
    (f4_northeast_g7 p hf f4)
  refine ⟨owners_side p 7,owners_cap p 7,owners_same_side p 7 1,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · norm_num only [inside_translated_iff]; exact south
  · norm_num only [inside_translated_iff]; exact north
  · norm_num only [inside_translated_iff]; exact inner
  · norm_num only [inside_translated_iff]; exact west
  · norm_num only [inside_translated_iff]; exact corner
  · norm_num only [inside_translated_iff]; exact auxiliary
  · norm_num only [inside_translated_iff]; exact seed
  · norm_num only [inside_translated_iff]; exact marker
  · norm_num only [inside_translated_iff]
    exact fun h => owners_apart p hf 7 8 (by decide +kernel) _ _ ⟨h,left⟩
  · norm_num only [inside_translated_iff]
    exact fun h => owners_apart p hf 1 0 (by decide +kernel) _ _ ⟨h,foreign⟩
  · intro x y h
    have original := (inside_translated_iff _ _ _ _ _).mp h
    have bound := (owners_contained p 1 (x+2) (y+2) original).1
    linarith only [bound]
  · intro x y both
    exact owners_apart p hf 1 7 (by decide +kernel) (x+2) (y+2)
      ⟨(inside_translated_iff _ _ _ _ _).mp both.1,
        (inside_translated_iff _ _ _ _ _).mp both.2⟩

/-- Equation (1), the upper transverse cap, and the slope bound (2). -/
theorem missing_faces (W K : OpenSquare) (h : Input W K)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c)
    (missing : ¬W.Inside 0 0) :
    W.loU+W.side≤0 ∧ W.loU< -1 ∧ W.loV+W.side≤W.s ∧
      (7/13)*W.c<W.s := by
  have cSmall : W.c≤1 := by nlinarith only [W.unit_normal,sq_nonneg W.s,cp]
  have p := h.south
  have q := h.north
  have f := h.inner
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,zero_add,add_zero] at p q f
  have uCap : W.loU+W.side≤0 := by
    apply le_of_not_gt
    intro positive
    apply missing
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,zero_add,add_zero]
    exact ⟨by linarith only [p.1,cp,sn],positive,
      by linarith only [f.2.2.1,cp],by linarith only [q.2.2.2,cp,sn]⟩
  have uLow : W.loU< -1 := by linarith only [uCap,h.sideLarge]
  have vCap : W.loV+W.side≤W.s := by
    apply le_of_not_gt
    intro high
    apply h.missingLeft
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,add_zero,mul_neg,mul_one]
    refine ⟨?_,?_,?_,high⟩
    · linarith only [uLow,cSmall]
    · linarith only [f.2.1,cp,sn,order]
    · linarith only [p.2.2.1,cp,sn]
  exact ⟨uCap,uLow,vCap,by linarith only [q.2.2.2,vCap]⟩

/-- The actual singleton owns the complete bar used in §2, including
its endpoints. -/
theorem singleton_bar (W K : OpenSquare) (h : Input W K) :
    ∀ y : ℝ,-1≤y → y≤ -13/50 → K.Inside (-1) y :=
  WallProfile.vertical_owned K (-1) (-1) (-13/50) (by norm_num)
    h.corner h.auxiliary

/-- The strict/closed crossing in manuscript §2. No closure point is
silently treated as a strict owner. -/
theorem no_left_vertex (W K : OpenSquare) (h : Input W K) (x y : ℝ)
    (closed : ClosedInside W x y) (left : x< -1)
    (low : -1<y) (high : y< -13/50) : False := by
  let t := (-1-x)/(-7/20-x)
  have denominator : 0< -7/20-x := by linarith only [left]
  have positive : 0<t := div_pos (by linarith only [left]) denominator
  have small : t<1 := (div_lt_one denominator).mpr (by linarith)
  have identity : t*(-7/20-x)= -1-x := div_mul_cancel₀ _ denominator.ne'
  have point := WallProfile.strict_closed_segment W x y (-7/20) (-7/20) t
    closed h.south positive small
  have xIdentity : (1-t)*x+t*(-7/20)= -1 := by nlinarith only [identity]
  rw [xIdentity] at point
  have weight : 0<1-t := sub_pos.mpr small
  have lower : -1≤(1-t)*y+t*(-7/20) := by
    have first := mul_pos weight (sub_pos.mpr low)
    nlinarith only [first,positive]
  have upper : (1-t)*y+t*(-7/20)≤ -13/50 := by
    have first := mul_pos weight (sub_pos.mpr high)
    nlinarith only [first,positive]
  exact h.apart _ _ ⟨singleton_bar W K h _ lower upper,point⟩

/-- The alternative that A=(-1,-.26) leaves W through its upper v face
is exactly the closed-vertex/bar contradiction (3)–(6). -/
theorem auxiliary_not_upper (W K : OpenSquare) (h : Input W K)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c)
    (missing : ¬W.Inside 0 0)
    (cap : W.loV+W.side≤W.s-(13/50)*W.c) : False := by
  obtain ⟨uCap,uLow,vCap,slope⟩ := missing_faces W K h cp sn order missing
  have f := h.inner
  have q := h.north
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,zero_add,add_zero] at f q
  have steep : (61/65)*W.c<W.s := by linarith only [cap,q.2.2.2]
  have cSmall : W.c≤1 := by nlinarith only [W.unit_normal,sq_nonneg W.s,cp]
  have cLarge : 7/10<W.c := by
    have squares : W.s^2≤W.c^2 := (sq_le_sq₀ sn cp.le).mpr order
    nlinarith only [W.unit_normal,squares,cp]
  have sLarge : 13/20<W.s := by linarith only [steep,cLarge]
  have sumLarge : 27/20<W.c+W.s := by linarith only [cLarge,sLarge]
  have sSquare : W.s^2≤1/2 := by
    have squares : W.s^2≤W.c^2 := (sq_le_sq₀ sn cp.le).mpr order
    nlinarith only [W.unit_normal,squares]
  have cSquare : 1/2≤W.c^2 := by nlinarith only [W.unit_normal,sSquare]
  have sSmall : W.s<5/7 := by nlinarith only [sSquare,sn]
  let U := W.loU
  let H := W.loV+W.side
  let x := W.c*U-W.s*H
  let y := W.s*U+W.c*H
  have closed : ClosedInside W x y := by
    exact WallProfile.vertex W U H ⟨le_rfl,by dsimp [U]; linarith only [W.side_pos]⟩
      ⟨by dsimp [H]; linarith only [W.side_pos],le_rfl⟩
  have hLarge : (7/20)*(W.c+W.s)<H := by
    dsimp only [H]
    linarith only [q.2.2.2]
  have xLeft : x< -1 := by
    have first := mul_pos cp (show 0< -1-U by dsimp [U]; linarith only [uLow])
    have second := mul_pos (show 0<W.s by linarith only [sLarge])
      (sub_pos.mpr hLarge)
    have third := mul_pos (show 0<W.s-13/20 by linarith only [sLarge])
      (show 0<W.c+W.s by linarith only [cp,sn])
    dsimp only [x]
    nlinarith only [first,second,third,cLarge,sumLarge]
  have yHigh : y< -13/50 := by
    have first := mul_pos (show 0<W.s by linarith only [sLarge])
      (show 0< -1-U by dsimp [U]; linarith only [uLow])
    have second := mul_nonneg cp.le (show 0≤W.s-(13/50)*W.c-H by
      dsimp [H]; linarith only [cap])
    have half : 0<W.s-(13/50)*(1+W.c) := by linarith only [sLarge,cSmall]
    have halfProduct := mul_pos (mul_pos (show 0<W.s by linarith only [sLarge])
      (show 0<W.s by linarith only [sLarge])) half
    have identity : (1+W.c)*(W.s*(1-W.c)-(13/50)*W.s^2)=
        W.s^2*(W.s-(13/50)*(1+W.c)) := by
      linear_combination -W.s*W.unit_normal
    have margin : 0<W.s*(1-W.c)-(13/50)*W.s^2 := by
      have positive : 0<(1+W.c)*(W.s*(1-W.c)-(13/50)*W.s^2) := by
        rw [identity]
        exact halfProduct
      exact (mul_pos_iff_of_pos_left (show 0<1+W.c by linarith only [cp])).mp positive
    dsimp only [y]
    nlinarith only [first,second,margin,W.unit_normal]
  have yLow : -1<y := by
    have first := mul_pos (show 0<W.s by linarith only [sLarge])
      (show 0<U+(13/50)*W.s+W.side by dsimp [U]; linarith only [f.2.1])
    have second := mul_pos cp (sub_pos.mpr hLarge)
    have sideBound := mul_nonneg sn (sub_nonneg.mpr h.sideSmall)
    have product := mul_nonneg cp.le sn
    dsimp only [y]
    nlinarith only [first,second,sideBound,sSmall,sSquare,cSquare,product]
  exact no_left_vertex W K h x y closed xLeft yLow yHigh

/-- The surviving lower-u exit of the foreign singleton anchor. This
is the conclusion preceding the half-angle interval (7). -/
theorem auxiliary_lower (W K : OpenSquare) (h : Input W K)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c)
    (missing : ¬W.Inside 0 0) :
    -W.c-(13/50)*W.s≤W.loU ∧ 1<W.c+(13/50)*W.s := by
  have p := h.south
  have f := h.inner
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,zero_add,add_zero] at p f
  have missingA : ¬W.Inside (-1) (-13/50) := fun own =>
    h.apart _ _ ⟨h.auxiliary,own⟩
  have lower : -W.c-(13/50)*W.s≤W.loU := by
    apply le_of_not_gt
    intro low
    have cap : W.loV+W.side≤W.s-(13/50)*W.c := by
      apply le_of_not_gt
      intro high
      apply missingA
      simp only [OpenSquare.Inside,InBands]
      refine ⟨by linarith only [low],?_,?_,by linarith only [high]⟩
      · linarith only [f.2.1,cp]
      · linarith only [p.2.2.1,cp,sn]
    exact auxiliary_not_upper W K h cp sn order missing cap
  have uCap := (missing_faces W K h cp sn order missing).1
  exact ⟨lower,by linarith only [lower,uCap,h.sideLarge]⟩

/-- The two strict actual-point differences in (9). -/
theorem separator_cone (W K : OpenSquare) (h : Input W K)
    (nx ny : ℝ) (unit : nx^2+ny^2=1)
    (separate : upper K nx ny≤lower W nx ny) : 0<nx ∧ 0<nx+ny := by
  have kA := (strict_bounds K _ _ nx ny unit h.auxiliary).2
  have wF := (strict_bounds W _ _ nx ny unit h.inner).1
  have kE := (strict_bounds K _ _ nx ny unit h.corner).2
  have wP := (strict_bounds W _ _ nx ny unit h.south).1
  constructor <;> linarith only [kA,wF,kE,wP,separate]

/-- The precise half-angle interval (7), with the coarse consequences
(8) used by the manuscript's subsequent support comparisons. -/
theorem angle_window (W K : OpenSquare) (h : Input W K)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c)
    (missing : ¬W.Inside 0 0) :
    let z := W.s/(1+W.c)
    1/4<z ∧ z<13/50 ∧ W.s*z=1-W.c ∧
      87/100<W.c ∧ 47/100<W.s ∧ W.s<49/100 ∧
      27/20<W.c+W.s ∧ 19/50<W.c-W.s := by
  dsimp only
  let z := W.s/(1+W.c)
  have slope := (missing_faces W K h cp sn order missing).2.2.2
  have reach := (auxiliary_lower W K h cp sn order missing).2
  have sp : 0<W.s := by linarith only [slope,cp]
  have denominator : 0<1+W.c := by linarith only [cp]
  have zp : 0<z := div_pos sp denominator
  have relation : z*(1+W.c)=W.s := div_mul_cancel₀ _ denominator.ne'
  have squared := congrArg (fun x : ℝ => x^2) relation
  have cProduct : (1+W.c)*(W.c*(1+z^2)-(1-z^2))=0 := by
    nlinarith only [squared,W.unit_normal]
  have cIdentity : W.c*(1+z^2)=1-z^2 := by
    have := (mul_eq_zero.mp cProduct).resolve_left denominator.ne'
    linarith only [this]
  have rIdentity : W.s*(1+z^2)=2*z := by
    calc
      W.s*(1+z^2)=z*((1+W.c)*(1+z^2)) := by rw [←relation]; ring
      _=z*2 := by congr 1; nlinarith only [cIdentity]
      _=2*z := by ring
  have shortIdentity : W.s*z=1-W.c := by
    have weighted := congrArg (fun x : ℝ => z*x) relation
    nlinarith only [weighted,cIdentity]
  have halfLower : 1/4<z := by
    apply lt_of_not_ge
    intro low
    have square : z^2≤1/16 := by
      have bound := (sq_le_sq₀ zp.le (show (0:ℝ)≤1/4 by norm_num)).mpr low
      norm_num at bound
      exact bound
    have weight := mul_pos (show 0<13*W.s-7*W.c by linarith only [slope])
      (show 0<1+z^2 by positivity)
    nlinarith only [weight,cIdentity,rIdentity,square,low]
  have halfUpper : z<13/50 := by
    have product : W.s*z<W.s*(13/50) := by
      nlinarith only [shortIdentity,reach]
    exact (mul_lt_mul_left sp).mp product
  have halfSquare : z^2<(13/50)^2 := (sq_lt_sq₀ zp.le (by norm_num)).mpr halfUpper
  have cosineExact : 2331/2669<W.c := by
    have weighted := mul_pos denominator (sub_pos.mpr halfSquare)
    nlinarith only [weighted,cIdentity]
  have cosine : 87/100<W.c := by linarith only [cosineExact]
  have sineLower : 47/100<W.s := by
    apply lt_of_not_ge
    intro low
    have weighted := mul_pos denominator (sub_pos.mpr halfLower)
    have cBound : W.c<22/25 := by nlinarith only [weighted,relation,low]
    have csq := (sq_lt_sq₀ cp.le (show (0:ℝ)≤22/25 by norm_num)).mpr cBound
    have rsq := (sq_le_sq₀ sp.le (show (0:ℝ)≤47/100 by norm_num)).mpr low
    nlinarith only [csq,rsq,W.unit_normal]
  have sineUpper : W.s<49/100 := by
    have csq := (sq_lt_sq₀ (show (0:ℝ)≤2331/2669 by norm_num) cp.le).mpr cosineExact
    nlinarith only [csq,W.unit_normal,sp]
  have sum : 27/20<W.c+W.s := by
    apply lt_of_not_ge
    intro low
    have cBound : W.c≤27/20-W.s := by linarith only [low]
    have csq := (sq_le_sq₀ cp.le (show 0≤27/20-W.s by linarith only [cBound,cp])).mpr cBound
    have interval := mul_nonneg (sub_nonneg.mpr sineLower.le)
      (sub_nonneg.mpr sineUpper.le)
    nlinarith only [csq,interval,W.unit_normal,sineLower]
  have difference : 19/50<W.c-W.s := by linarith only [cosineExact,sineUpper]
  exact ⟨halfLower,halfUpper,shortIdentity,cosine,sineLower,sineUpper,sum,difference⟩

end
#print axioms actual_input
#print axioms auxiliary_lower
#print axioms angle_window
end N12Compact.Completion.OtherCases.C983.F4MergedCenter
