import Compact.Completion.C1092.MPPMNegativeForwardFaces

/-! Full local Theorem 2 of NEGATIVE-FORWARD-POSITIVE-H. The eight
oriented actual face axes reduce to three support comparisons. The real
whole foreign bar is used only through its proved geometric floor.
Neither potentially reassigned inner point is an exclusion premise.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMNegativeForward
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open Completion.OtherCases
set_option Elab.async false

theorem axes (C E B : OpenSquare) (h : Input C E B) :
    C.loU+C.side≤lower E C.c C.s ∨
      upper C E.c E.s≤E.loU ∨ upper C E.s (-E.c)≤-(E.loV+E.side) := by
  have cb := C977CornerCubic.normal_bounds h.sourceNormal
  have eb := C977CornerCubic.normal_bounds h.targetNormal
  have cp : 0<C.c := by linarith only [cb.1]
  have ep : 0<E.c := by linarith only [eb.1]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower E nx ny) : 0<nx ∧ 0<nx-ny := by
    have cm := (strict_bounds C _ _ nx ny unit h.source).2
    have em := (strict_bounds E _ _ nx ny unit h.target).1
    have ct := (strict_bounds C _ _ nx ny unit h.forward).2
    have ei := (strict_bounds E _ _ nx ny unit h.inner).1
    constructor <;> linarith only [cm,em,ct,ei,sep]
  have reverse (nx ny : ℝ) (sep : upper E nx ny≤lower C nx ny) :
      upper C (-nx) (-ny)≤lower E (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have choices := CongruentSAT.faceSeparation_of_disjoint C E h.same h.apart
  change pairRadius C E≤|C.c*(centerX E-centerX C)+C.s*(centerY E-centerY C)| ∨
    pairRadius C E≤|-C.s*(centerX E-centerX C)+C.c*(centerY E-centerY C)| ∨
    pairRadius E C≤|E.c*(centerX E-centerX C)+E.s*(centerY E-centerY C)| ∨
    pairRadius E C≤|-E.s*(centerX E-centerX C)+E.c*(centerY E-centerY C)| at choices
  have separate (nx ny R : ℝ)
      (radius : supportRadius C nx ny+supportRadius E nx ny=R)
      (sep : R≤|nx*(centerX E-centerX C)+ny*(centerY E-centerY C)|) :=
    separated C E nx ny (by rwa [radius])
  rcases choices with cu | cv | eu | ev
  · rcases separate _ _ _ (parallel_radius C E) cu with forward | backward
    · exact Or.inl (by simpa only [(ownU C).2] using forward)
    · have failed := (cone (-C.c) (-C.s) (by nlinarith only [C.unit_normal])
        (reverse _ _ backward)).1
      linarith only [failed,cp]
  · rcases separate _ _ _ (transverse_radius C E) cv with forward | backward
    · have failed := (cone (-C.s) C.c (by nlinarith only [C.unit_normal]) forward).2
      linarith only [failed,h.sourceNormal.2.1]
    · have failed := (cone C.s (-C.c) (by nlinarith only [C.unit_normal])
        (by simpa only [neg_neg] using reverse _ _ backward)).1
      linarith only [failed,h.sourceNormal.1]
  · have radius : supportRadius C E.c E.s+supportRadius E E.c E.s=pairRadius E C := by
      rw [add_comm]
      exact parallel_radius E C
    rcases separate _ _ _ radius eu with forward | backward
    · exact Or.inr (Or.inl (by simpa only [(ownU E).1] using forward))
    · have failed := (cone (-E.c) (-E.s) (by nlinarith only [E.unit_normal])
        (reverse _ _ backward)).1
      linarith only [failed,ep]
  · have radius : supportRadius C (-E.s) E.c+supportRadius E (-E.s) E.c=pairRadius E C := by
      rw [add_comm]
      exact transverse_radius E C
    rcases separate _ _ _ radius ev with forward | backward
    · have failed := (cone (-E.s) E.c (by nlinarith only [E.unit_normal]) forward).1
      linarith only [failed,h.targetNormal.1]
    · right; right
      have reflected := reverse _ _ backward
      have lowerIdentity : lower E E.s (-E.c)=-(E.loV+E.side) := by
        calc
          lower E E.s (-E.c)=lower E (-(-E.s)) (-E.c) := by rw [neg_neg]
          _= -upper E (-E.s) E.c := WallProfile.lower_neg E (-E.s) E.c
          _= -(E.loV+E.side) := by rw [(ownV E).2]
      simpa only [neg_neg,lowerIdentity] using reflected

/-- The bar clearance gives a strictly positive support gap on E's
longitudinal axis. The exact polynomial form avoids dividing by the
source half-angle or requiring any successor angle ceiling. -/
theorem target_support (C E B : OpenSquare) (h : Input C E B)
    (f : SourceProfile C) : -(13/50)*E.s<upper C E.c E.s := by
  let c := C.c
  let s := -C.s
  let d := E.c
  let t := E.s
  let k := c*d-s*t
  let l := c*t+s*d
  have cp : 0<c := by dsimp only [c]; linarith only [f.close]
  have sp : 0<s := f.negative
  have dp : 0<d := by
    dsimp only [d]
    linarith only [(C977CornerCubic.normal_bounds h.targetNormal).1]
  have tn : 0≤t := h.targetNormal.1
  have order : t≤d := h.targetNormal.2.1
  have cs : 0<c-s := by dsimp only [c,s]; linarith only [f.close,f.small]
  have kp : 0<k := by
    have first := mul_pos dp cs
    have last := mul_nonneg sp.le (sub_nonneg.mpr order)
    dsimp only [k]
    nlinarith only [first,last]
  have lp : 0<l := by
    have first := mul_pos sp dp
    have last := mul_nonneg cp.le tn
    dsimp only [l]
    nlinarith only [first,last]
  have cu : E.c*C.c+E.s*C.s=k := by dsimp only [c,s,d,t,k]; ring
  have cv : -E.c*C.s+E.s*C.c=l := by dsimp only [c,s,d,t,l]; ring
  have support : upper C E.c E.s=
      d*centerX C+t*centerY C+C.side*(k+l)/2 := by
    dsimp only [upper,supportRadius]
    rw [cu,cv,abs_of_nonneg kp.le,abs_of_nonneg lp.le]
    dsimp only [d,t]
    ring
  have floor := center_floor C E B h f
  change -1+C.side*(c+s)/2<centerY C at floor
  have coordinate : c*centerX C-s*centerY C=C.loU+C.side/2 := by
    have original := (center_coordinates C).1
    dsimp only [c,s]
    linarith only [original]
  have low : 0≤d*(C.loU+c) := mul_nonneg dp.le
    (by dsimp only [c]; linarith only [f.lowerU])
  have raised := mul_pos lp (sub_pos.mpr floor)
  have coefficient : 0<l*(c+s)+d+c*(k+l) := by positivity
  have excess := mul_pos (sub_pos.mpr h.side) coefficient
  have unit : c^2+s^2=1 := h.sourceNormal.2.2
  have identity : -c*d-l+(l*(c+s)+d+c*(k+l))/2=
      (1-c)*(d*(1-s)-c*t) := by
    dsimp only [k,l]
    linear_combination (d/2)*unit
  have first := mul_pos (mul_pos (show 0<1-c by exact sub_pos.mpr f.strictCosine) dp)
    (show 0<1-s by dsimp only [s]; linarith only [f.small])
  have second := mul_nonneg (mul_nonneg cp.le tn)
    (show 0≤c-37/50 by dsimp only [c]; linarith only [f.close])
  have supportScaled := congrArg (fun z : ℝ => c*z) support
  have coordinateScaled := congrArg (fun z : ℝ => d*z) coordinate
  have scaled : 0<c*(upper C E.c E.s+(13/50)*t) := by
    nlinarith only [supportScaled,coordinateScaled,low,raised,excess,identity,first,second]
  apply lt_of_not_ge
  intro lowSupport
  have bad := mul_nonpos_of_nonneg_of_nonpos cp.le
    (show upper C E.c E.s+(13/50)*t≤0 by dsimp only [t]; linarith only [lowSupport])
  linarith only [scaled,bad]

/-- A nonpositive retaining ordinary predecessor supplies the positive
successor halfpoint for every canonical successor angle. The whole bar
is strict in B; B is never replaced by an assumed global half-plane. -/
theorem point (C E B : OpenSquare) (h : Input C E B) : E.Inside (1/2) (-1) := by
  have f := source_profile C E B h
  let c := C.c
  let s := -C.s
  let d := E.c
  let t := E.s
  let k := c*d-s*t
  let l := c*t+s*d
  have cp : 0<c := by dsimp only [c]; linarith only [f.close]
  have sp : 0<s := f.negative
  have dp : 0<d := by
    dsimp only [d]
    linarith only [(C977CornerCubic.normal_bounds h.targetNormal).1]
  have tn : 0≤t := h.targetNormal.1
  have order : t≤d := h.targetNormal.2.1
  have cs : 0<c-s := by dsimp only [c,s]; linarith only [f.close,f.small]
  have kp : 0<k := by
    have first := mul_pos dp cs
    have last := mul_nonneg sp.le (sub_nonneg.mpr order)
    dsimp only [k]
    nlinarith only [first,last]
  have lp : 0<l := by
    have first := mul_pos sp dp
    have last := mul_nonneg cp.le tn
    dsimp only [l]
    nlinarith only [first,last]
  by_contra missing
  have lowerBound := target_lower C E B h missing
  have targetLow : -d-t/2≤E.loV := lowerBound
  have sourceLow : -c≤C.loU := f.lowerU
  have sourceHigh : C.loV+C.side≤(7/20)*(c-s) := by
    dsimp only [c,s]
    linarith only [f.upperV]
  have anchor : E.loU < -(13/50)*t := by dsimp only [t]; linarith only [h.inner.1]
  rcases axes C E B h with sourceAxis | targetAxis | transverseAxis
  · have eu : C.c*E.c+C.s*E.s=k := by dsimp only [c,s,d,t,k]; ring
    have ev : -C.c*E.s+C.s*E.c= -l := by dsimp only [c,s,d,t,l]; ring
    have support : lower E C.c C.s=k*E.loU-l*(E.loV+C.side) := by
      have result := C1092WholeSupports.lower_pn E C.c C.s k (-l) eu ev
        kp.le (neg_nonpos.mpr lp.le)
      rw [←h.same] at result
      convert result using 1 <;> ring
    rw [support] at sourceAxis
    have first := mul_lt_mul_of_pos_left anchor kp
    have last := mul_le_mul_of_nonneg_left targetLow lp.le
    have margin := longitudinal_margin h.sourceNormal h.targetNormal
    change 0≤1+l-c-l*d-l*t/2+(13/50)*k*t at margin
    have excess := mul_pos (sub_pos.mpr h.side) (show 0<1+l by linarith only [lp])
    nlinarith only [sourceAxis,sourceLow,first,last,margin,excess]
  · have support := target_support C E B h f
    change -(13/50)*t<upper C E.c E.s at support
    linarith only [support,targetAxis,anchor]
  · have cu : E.s*C.c+(-E.c)*C.s=l := by dsimp only [c,s,d,t,l]; ring
    have cv : -E.s*C.s+(-E.c)*C.c= -k := by dsimp only [c,s,d,t,k]; ring
    have support : upper C E.s (-E.c)=l*(C.loU+C.side)-k*C.loV := by
      rw [(C1092WholeSupports.formulas C E.s (-E.c)).2,cu,cv,
        max_eq_left lp.le,max_eq_right (neg_nonpos.mpr kp.le)]
      ring
    rw [support,←h.same] at transverseAxis
    have first := mul_le_mul_of_nonneg_left sourceLow lp.le
    have last := mul_le_mul_of_nonneg_left sourceHigh kp.le
    have margin := transverse_margin h.sourceNormal h.targetNormal f.close f.small
    change 0<1+k+l-d-t/2-l*c-(7/20)*k*(c-s) at margin
    have excess := mul_pos (sub_pos.mpr h.side)
      (show 0<1+k+l by linarith only [kp,lp])
    nlinarith only [transverseAxis,targetLow,first,last,margin,excess]

#print axioms point
end N12Compact.C1092MPPMNegativeForward
