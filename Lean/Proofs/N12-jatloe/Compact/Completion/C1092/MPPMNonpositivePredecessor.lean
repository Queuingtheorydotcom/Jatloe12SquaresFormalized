import Compact.Completion.C1092.MPPMNonpositivePredecessorScalars
import Compact.Completion.C1092.MPPMOrdinaryNegativeHalfpoint
import Compact.Completion.C1092.MPPMMissingPositiveFaces
import Compact.Completion.OtherCases.WallProfile.VertexGeometry

/-! Completed local producer behind ORDINARY-NEGATIVE-HALFPOINT Corollary 2.
The actual predecessor may have either canonical sign and may own or omit
its forward point. Positive forward and missing predecessors share the
three exact support comparisons from MIXED-NEGATIVE-H and
POSITIVE-MISSING-NEGATIVE-H. Negative missing predecessors use only the
elementary cap part of MISSING-NEGATIVE-WALL-ORDER Lemma 1.

Coordinates are translated by (-2,-2) from the original SW/SE pair.
All points remain in their actual source or target square; foreign points
are absences, never assigned an owner here. The original-owner adapter
must supply the literal point inputs below. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMNonpositivePredecessor
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse
open C1092MPPMOrdinaryNegativeHalfpoint
open Completion.OtherCases
set_option Elab.async false

structure PositiveRegimes (C : OpenSquare) : Prop where
  upper : C.loV+C.side≤C.s+(13/50)*C.c
  cases : -C.c-C.s≤C.loU ∨
    (-(543/500)*C.c≤C.loU ∧ 99/100<C.c ∧ C.s<9/100) ∨
    (C.loV+C.side≤(543/500)*C.s ∧ -(13/50)*C.c<C.loU+C.side ∧
      49/50<C.c ∧ C.s<9/50)

theorem positive_axes (C E : OpenSquare) (same : C.side=E.side)
    (cf : Frame C.c C.s) (ef : Frame E.c (-E.s))
    (source : C.Inside (-7/20) (-7/20))
    (target : E.Inside (7/20) (-7/20))
    (bar : E.Inside (13/50) (-1))
    (apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)) :
    C.loU+C.side≤lower E C.c C.s ∨
      -C.loV≤lower E C.s (-C.c) ∨ upper C E.c E.s≤E.loU := by
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (separation : upper C nx ny≤lower E nx ny) : 0<nx := by
    have a := (strict_bounds C _ _ nx ny unit source).2
    have b := (strict_bounds E _ _ nx ny unit target).1
    linarith only [a,b,separation]
  have reverse (nx ny : ℝ) (separation : upper E nx ny≤lower C nx ny) :
      upper C (-nx) (-ny)≤lower E (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [separation]
  have axes := CongruentSAT.faceSeparation_of_disjoint C E same apart
  change pairRadius C E≤|C.c*(centerX E-centerX C)+C.s*(centerY E-centerY C)| ∨
    pairRadius C E≤|-C.s*(centerX E-centerX C)+C.c*(centerY E-centerY C)| ∨
    pairRadius E C≤|E.c*(centerX E-centerX C)+E.s*(centerY E-centerY C)| ∨
    pairRadius E C≤|-E.s*(centerX E-centerX C)+E.c*(centerY E-centerY C)| at axes
  have separate (nx ny R : ℝ)
      (radius : supportRadius C nx ny+supportRadius E nx ny=R)
      (axis : R≤|nx*(centerX E-centerX C)+ny*(centerY E-centerY C)|) :=
    separated C E nx ny (by rwa [radius])
  rcases axes with cu | cv | eu | ev
  · rcases separate _ _ _ (parallel_radius C E) cu with f | r
    · left; simpa only [(ownU C).2] using f
    · have bad := cone (-C.c) (-C.s) (by nlinarith only [C.unit_normal]) (reverse _ _ r)
      linarith only [bad,cf.positive]
  · rcases separate _ _ _ (transverse_radius C E) cv with f | r
    · have bad := cone (-C.s) C.c (by nlinarith only [C.unit_normal]) f
      linarith only [bad,cf.nonnegative]
    · right; left
      have reflected := reverse _ _ r
      have support : upper C C.s (-C.c)= -C.loV := by
        simpa only [neg_neg,(ownV C).1] using WallProfile.upper_neg C (-C.s) C.c
      simpa only [neg_neg,support] using reflected
  · have radius : supportRadius C E.c E.s+supportRadius E E.c E.s=pairRadius E C := by
      rw [add_comm]; exact parallel_radius E C
    rcases separate _ _ _ radius eu with f | r
    · right; right; simpa only [(ownU E).1] using f
    · have bad := cone (-E.c) (-E.s) (by nlinarith only [E.unit_normal]) (reverse _ _ r)
      linarith only [bad,ef.positive]
  · have radius : supportRadius C (-E.s) E.c+supportRadius E (-E.s) E.c=pairRadius E C := by
      rw [add_comm]; exact transverse_radius E C
    rcases separate _ _ _ radius ev with f | r
    · have unit : (-E.s)^2+E.c^2=1 := by nlinarith only [E.unit_normal]
      have a := (strict_bounds C _ _ (-E.s) E.c unit source).2
      have b := (strict_bounds E _ _ (-E.s) E.c unit bar).1
      linarith only [a,b,f,ef.positive,ef.ordered]
    · have bad := cone E.s (-E.c) (by nlinarith only [E.unit_normal])
        (by simpa only [neg_neg] using reverse _ _ r)
      linarith only [bad,ef.nonnegative]

/-- Shared whole-square support proof. The regimes themselves are produced
from literal owned and omitted points below. -/
theorem positive_point (C E : OpenSquare) (side : 1<C.side) (same : C.side=E.side)
    (cf : Frame C.c C.s) (ef : Frame E.c (-E.s))
    (source : C.Inside (-7/20) (-7/20)) (data : PositiveRegimes C)
    (target : E.Inside (7/20) (-7/20))
    (bar0 : E.Inside (13/50) (-1)) (bar1 : E.Inside (2/5) (-1))
    (inner : E.Inside 0 (-13/50))
    (apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)) : E.Inside (1/2) (-1) := by
  let c := C.c
  let s := C.s
  let d := E.c
  let t := -E.s
  let k := c*d-s*t
  let l := c*t+s*d
  have kn : 0≤k := (relative c s d t cf ef).1
  have ln : 0≤l := (relative c s d t cf ef).2
  have low : E.loV<(13/50)*t-d := by dsimp [d,t]; linarith only [bar0.2.2.1]
  have high : -(13/50)*d<E.loV+C.side := by dsimp [d]; linarith only [inner.2.2.2,same]
  have cap : C.loV+C.side≤s+(13/50)*c := data.upper
  by_contra missing
  have upper : E.loU+C.side≤d/2+t := by
    have h := missing_face E ef target bar1 missing
    dsimp [d,t]; linarith only [h,same]
  have ku : C.c*E.c+C.s*E.s=k := by dsimp [c,s,d,t,k]; ring
  have lu : -C.c*E.s+C.s*E.c=l := by dsimp [c,s,d,t,l]; ring
  have kl : E.c*C.c+E.s*C.s=k := by dsimp [c,s,d,t,k]; ring
  have ll : -E.c*C.s+E.s*C.c= -l := by dsimp [c,s,d,t,l]; ring
  have sourceSupport : lower E C.c C.s=k*E.loU+l*E.loV :=
    C1092WholeSupports.lower_nn E C.c C.s k l ku lu kn ln
  have transverseSupport : lower E C.s (-C.c)=l*E.loU-k*(E.loV+C.side) := by
    have h := C1092WholeSupports.lower_pn E C.s (-C.c) l (-k)
      (by dsimp [c,s,d,t,l]; ring) (by dsimp [c,s,d,t,k]; ring) ln (neg_nonpos.mpr kn)
    simpa only [←same,neg_mul,sub_eq_add_neg] using h
  have targetSupport : ABTransverse.upper C E.c E.s=k*(C.loU+C.side)-l*C.loV := by
    rw [(C1092WholeSupports.formulas C E.c E.s).2,kl,ll,
      max_eq_left kn,max_eq_right (neg_nonpos.mpr ln)]
    ring
  have upperK := mul_le_mul_of_nonneg_left upper kn
  have upperL := mul_le_mul_of_nonneg_left upper ln
  have lowL := mul_le_mul_of_nonneg_left low.le ln
  have highK := mul_le_mul_of_nonneg_left high.le kn
  have capL := mul_le_mul_of_nonneg_left cap ln
  have sourceIdentity : k*(d/2+t)+l*((13/50)*t-d)=c/2-s-(6/25)*l*t := by
    dsimp [k,l]
    linear_combination (c/2-s)*ef.unit
  have transverseIdentity : s+(13/50)*c+l*(d/2+t)+k*((13/50)*d)=
      (63/50)*c+(3/2)*s-k*((37/50)*d-t/2) := by
    dsimp [k,l]
    linear_combination (c+s/2)*ef.unit
  have strictK := mul_pos (sub_pos.mpr side) (show 0<1+k by linarith only [kn])
  have strictL := mul_pos (sub_pos.mpr side) (show 0<1+l by linarith only [ln])
  have strictBoth := mul_pos (sub_pos.mpr side) (show 0<1+k+l by linarith only [kn,ln])
  have axes := positive_axes C E same cf ef source target bar0 apart
  rcases axes with sourceAxis | transverseAxis | targetAxis
  · rw [sourceSupport] at sourceAxis
    rcases data.cases with first | second | third
    · have margin := first_source c s d t cf ef
      have margin : (3/2)*c-(6/25)*l*t<1+k := by dsimp [k,l]; linarith only [margin]
      nlinarith only [sourceAxis,upperK,lowL,sourceIdentity,first,margin,strictK]
    · have margin := second_source c s d t cf ef second.2.1 second.2.2
      have margin : (793/500)*c-s-(6/25)*l*t<1+k := by dsimp [k,l]; linarith only [margin]
      nlinarith only [sourceAxis,upperK,lowL,sourceIdentity,second.1,margin,strictK]
    · have margin := third_source c s d t cf ef
      change (19/25)*c-s-(6/25)*l*t<k at margin
      have sideK := mul_nonneg (sub_nonneg.mpr side.le) kn
      nlinarith only [sourceAxis,upperK,lowL,sourceIdentity,third.2.1,margin,sideK]
  · rw [transverseSupport] at transverseAxis
    have margin := transverse c s d t cf ef
    have margin : (63/50)*c+(3/2)*s-k*((37/50)*d-t/2)<1+l := by
      dsimp [k,l]
      linarith only [margin]
    nlinarith only [transverseAxis,upperL,highK,cap,transverseIdentity,margin,strictL]
  · rw [targetSupport] at targetAxis
    rcases data.cases with first | second | third
    · have weighted := mul_le_mul_of_nonneg_left first kn
      have identity : d/2+t+k*(c+s)+l*(s+(13/50)*c)=(3/2)*d+(63/50)*c*l := by
        dsimp [k,l]
        linear_combination (d-t)*C.unit_normal
      have margin := first_target c s d t cf ef
      change (3/2)*d+(63/50)*c*l<1+k+l at margin
      nlinarith only [targetAxis,upper,weighted,capL,identity,margin,strictBoth]
    · have weighted := mul_le_mul_of_nonneg_left second.1 kn
      have identity : d/2+t+(543/500)*k*c+l*(s+(13/50)*c)=
          (793/500)*d+t+l*((13/50)*c-(43/500)*s) := by
        dsimp [k,l]
        linear_combination (543/500)*d*C.unit_normal
      have margin := second_target c s d t cf ef second.2.1 second.2.2
      change (793/500)*d+t+l*((13/50)*c-(43/500)*s)<1+k+l at margin
      nlinarith only [targetAxis,upper,weighted,capL,identity,margin,strictBoth]
    · have capSmall := mul_le_mul_of_nonneg_left third.1 ln
      have lowerJ := mul_le_mul_of_nonneg_left third.2.1.le kn
      have identity : d/2+t+(13/50)*k*c+(543/500)*l*s=
          (19/25)*d+t+(413/500)*l*s := by
        dsimp [k,l]
        linear_combination (13/50)*d*C.unit_normal
      have margin := third_target c s d t cf ef third.2.2.1 third.2.2.2
      have margin : (19/25)*d+t+(413/500)*l*s<1+l := by
        dsimp [l]
        linarith only [margin]
      nlinarith only [targetAxis,upper,capSmall,lowerJ,identity,margin,strictL]

/-- All three regimes of the positive forward-owned predecessor follow
from the actual excluded corner, preceding wall marker and wall endpoint. -/
theorem positive_forward_regimes (C : OpenSquare) (side : 1<C.side)
    (cf : Frame C.c C.s)
    (marker : C.Inside (-7/20) (-7/20))
    (ordinary : C.Inside (-1) (-13/50)) (bar : C.Inside (-1) (-2/5))
    (forward : C.Inside (-13/50) 0)
    (corner : ¬C.Inside (-1) (-1)) (wall : ¬C.Inside (-543/500) 0)
    (wallF : ¬C.Inside (-1) (13/50)) : PositiveRegimes C := by
  have cb := CommonCases.CanonicalScalars.bounds C.c C.s cf.positive cf.nonnegative cf.ordered cf.unit
  have upper : C.loV+C.side≤C.s+(13/50)*C.c := by
    apply le_of_not_gt; intro high; apply wallF
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,ordinary.1,ordinary.2.2.1,forward.2.1,
        cf.positive,cf.nonnegative,cf.ordered]
  refine ⟨upper,?_⟩
  by_cases first : -C.c-C.s≤C.loU
  · exact Or.inl first
  have cornerV : C.s-C.c≤C.loV := by
    apply le_of_not_gt; intro low; apply corner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [first,low,marker.2.1,bar.2.2.2,cf.positive,cf.nonnegative,cf.ordered]
  by_cases wallU : -(543/500)*C.c≤C.loU
  · have slope : C.s<(43/500)*C.c := by linarith only [wallU,first]
    have sh : C.s<9/100 := by linarith only [slope,cb.2.1]
    have square := mul_pos (sub_pos.mpr sh) (show 0<9/100+C.s by linarith only [cf.nonnegative])
    have cl : 99/100<C.c := by
      by_contra no
      have bad := mul_nonneg (show 0≤99/100-C.c by linarith only [no])
        (show 0≤99/100+C.c by linarith only [cf.positive])
      nlinarith only [cf.unit,square,bad]
    exact Or.inr (Or.inl ⟨wallU,cl,sh⟩)
  · have wallV : C.loV+C.side≤(543/500)*C.s := by
      apply le_of_not_gt; intro high; apply wall
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [wallU,high,forward.2.1,bar.2.2.1,cf.positive,cf.nonnegative]
    have thin : 1<C.c+(43/500)*C.s := by linarith only [cornerV,wallV,side]
    have sp : 0<C.s := by linarith only [thin,cb.2.1]
    have product := mul_pos (show 0<C.c+(43/500)*C.s-1 by linarith only [thin])
      (show 0<C.c+1 by linarith only [cf.positive])
    have identity : (C.c+(43/500)*C.s-1)*(C.c+1)=
        C.s*((43/500)*(1+C.c)-C.s) := by linear_combination cf.unit
    rw [identity] at product
    have gap : 0<(43/500)*(1+C.c)-C.s := by
      by_contra no
      have bad := mul_nonpos_of_nonneg_of_nonpos sp.le (le_of_not_gt no)
      linarith only [product,bad]
    have sh : C.s<9/50 := by linarith only [gap,cb.2.1]
    have square := mul_pos (sub_pos.mpr sh) (show 0<9/50+C.s by linarith only [sp])
    have cl : 49/50<C.c := by
      by_contra no
      have bad := mul_nonneg (show 0≤49/50-C.c by linarith only [no])
        (show 0≤49/50+C.c by linarith only [cf.positive])
      nlinarith only [cf.unit,square,bad]
    have j : -(13/50)*C.c<C.loU+C.side := by linarith only [forward.2.1]
    exact Or.inr (Or.inr ⟨wallV,j,cl,sh⟩)

/-- The negative missing-forward cap step does not need a preceding
origin, a wall-center inequality, or any replacement support hypothesis. -/
theorem negative_missing_caps (C : OpenSquare) (side : 1<C.side)
    (cf : Frame C.c (-C.s))
    (marker : C.Inside (-7/20) (-7/20))
    (ordinary : C.Inside (-1) (-13/50)) (bar : C.Inside (-1) (-2/5))
    (halfpoint : C.Inside (-1) (-1/2))
    (corner : ¬C.Inside (-1) (-1)) (wall : ¬C.Inside (-543/500) 0)
    (forward : ¬C.Inside (-13/50) 0) :
    -(543/500)*C.c≤C.loU ∧ C.loV+C.side≤(7/20)*(C.c+C.s) := by
  have cb := CommonCases.CanonicalScalars.bounds C.c (-C.s) cf.positive cf.nonnegative cf.ordered cf.unit
  have cornerV : C.s-C.c≤C.loV := by
    apply le_of_not_gt; intro low; apply corner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,halfpoint.1,marker.2.1,bar.2.2.2,
        cf.positive,cf.nonnegative,cf.ordered]
  have lower : -(543/500)*C.c≤C.loU := by
    apply le_of_not_gt; intro low
    have upper : C.loV+C.side≤(543/500)*C.s := by
      apply le_of_not_gt; intro high; apply wall
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,high,ordinary.2.1,bar.2.2.1,
          cf.positive,cf.nonnegative,cf.ordered]
    linarith only [cornerV,upper,side,cb.2.1,cf.nonnegative]
  have upper : C.loV+C.side≤(13/50)*C.s := by
    apply le_of_not_gt; intro high
    have capU : C.loU+C.side≤-(13/50)*C.c := by
      apply le_of_not_gt; intro highU; apply forward
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [high,highU,ordinary.1,ordinary.2.2.1,
          cf.positive,cf.nonnegative,cf.ordered]
    linarith only [capU,lower,side,cb.2.1]
  exact ⟨lower,by linarith only [upper,cf.nonnegative,cf.ordered]⟩

/-- Raw ordinary predecessor data. The conditional missing-forward
package contains only strict points and absences, with existing original
packing producers. In particular it contains no final face caps. -/
structure Inputs (C E : OpenSquare) : Prop where
  source : C.Inside (-7/20) (-7/20)
  ordinary : C.Inside (-1) (-13/50)
  bar : C.Inside (-1) (-2/5)
  corner : ¬C.Inside (-1) (-1)
  wall : ¬C.Inside (-543/500) 0
  northwest : ¬C.Inside (-7/20) (7/20)
  wallF : ¬C.Inside (-1) (13/50)
  missing : ¬C.Inside (-13/50) 0 → C1092MPPMMissingPositiveFaces.Inputs C
  target : E.Inside (7/20) (-7/20)
  bar0 : E.Inside (13/50) (-1)
  bar1 : E.Inside (2/5) (-1)
  inner : E.Inside 0 (-13/50)
  apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)

/-- Full raw local producer for ORDINARY-NEGATIVE-HALFPOINT Corollary 2.
The successor is nonpositive. Every canonical predecessor sign and both
forward ownership alternatives are covered, including all endpoints. -/
theorem point (C E : OpenSquare) (side : 1<C.side) (same : C.side=E.side)
    (cp : 0<C.c) (co : |C.s|≤C.c)
    (ep : 0<E.c) (en : E.s≤0) (eo : -E.s≤E.c)
    (h : Inputs C E) : E.Inside (1/2) (-1) := by
  have ef := negative_frame E ep en eo
  by_cases sn : C.s≤0
  · have cf := negative_frame C cp sn (by simpa only [abs_of_nonpos sn] using co)
    have caps : -(543/500)*C.c≤C.loU ∧ C.loV+C.side≤(7/20)*(C.c+C.s) := by
      by_cases forward : C.Inside (-13/50) 0
      · exact forward_owned_caps C cf h.ordinary h.bar forward h.wall h.northwest
      · exact negative_missing_caps C side cf h.source h.ordinary h.bar
          (h.missing forward).halfpoint h.corner h.wall forward
    exact C1092MPPMOrdinaryNegativeHalfpoint.point C E side same cp sn cf.ordered
      ep en eo h.source caps.1 caps.2 h.target h.bar0 h.bar1 h.inner h.apart
  · have sp : 0<C.s := lt_of_not_ge sn
    have order : C.s≤C.c := by simpa only [abs_of_pos sp] using co
    have cf : Frame C.c C.s := ⟨cp,sp.le,order,C.unit_normal⟩
    have regimes : PositiveRegimes C := by
      by_cases forward : C.Inside (-13/50) 0
      · exact positive_forward_regimes C side cf h.source h.ordinary h.bar forward h.corner h.wall h.wallF
      · have profile := C1092MPPMMissingPositiveFaces.profile C side
          (show C977CornerCubic.Normal C.c C.s from ⟨sp.le,order,C.unit_normal⟩) (h.missing forward)
        exact ⟨by linarith only [profile.upperV,order,cp],Or.inl profile.lowerU⟩
    exact positive_point C E side same cf ef h.source regimes h.target h.bar0 h.bar1 h.inner h.apart

#print axioms point
end N12Compact.C1092MPPMNonpositivePredecessor
