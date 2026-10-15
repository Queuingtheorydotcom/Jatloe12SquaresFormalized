import Compact.Completion.FiniteCases.C972NortheastPositiveFaces
import Compact.Completion.FiniteCases.C972NortheastPositiveScalars

/-! The two remaining positive actual central squares cannot separate.
Every longitudinal direction is excluded by strict anchors. The two
transverse directions are exhausted over both relative-angle orders,
using the actual southeast floor and the derived northeast upper face. -/
namespace N12Compact.FiniteCases.C972Local
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
open C977CornerCubic N12Compact.Completion.OtherCases
set_option Elab.async false

structure PositivePairInput (E N : OpenSquare) : Prop where
  side : 1<E.side
  same : E.side=N.side
  sourceNormal : Normal E.c E.s
  targetNormal : Normal N.c N.s
  targetPositive : 0<N.s
  sourceFaces : C983.F4SoutheastSignSupports.Data E
  sourceCenter : E.Inside 0 0
  sourceOuter : E.Inside 1 (-13/50)
  sourceFloor : -E.s-E.c/2≤E.loV
  targetMarker : N.Inside (7/20) (7/20)
  targetOrigin : N.Inside 0 1
  targetFaces : PositiveNorth N
  apart : ∀ x y,¬(E.Inside x y ∧ N.Inside x y)

private theorem upper_pp (q : OpenSquare) (nx ny : ℝ)
    (first : 0≤nx*q.c+ny*q.s) (last : 0≤ -nx*q.s+ny*q.c) :
    upper q nx ny=(nx*q.c+ny*q.s)*(q.loU+q.side)+
      (-nx*q.s+ny*q.c)*(q.loV+q.side) := by
  rw [C981CompletionSupportForms.upper_in_bands,abs_of_nonneg first,abs_of_nonneg last]
  ring

private theorem upper_np (q : OpenSquare) (nx ny : ℝ)
    (first : nx*q.c+ny*q.s≤0) (last : 0≤ -nx*q.s+ny*q.c) :
    upper q nx ny=(nx*q.c+ny*q.s)*q.loU+
      (-nx*q.s+ny*q.c)*(q.loV+q.side) := by
  rw [C981CompletionSupportForms.upper_in_bands,abs_of_nonpos first,abs_of_nonneg last]
  ring

private theorem lower_pp (q : OpenSquare) (nx ny : ℝ)
    (first : 0≤nx*q.c+ny*q.s) (last : 0≤ -nx*q.s+ny*q.c) :
    lower q nx ny=(nx*q.c+ny*q.s)*q.loU+(-nx*q.s+ny*q.c)*q.loV := by
  rw [C981CompletionSupportForms.lower_in_bands,abs_of_nonneg first,abs_of_nonneg last]
  ring

private theorem lower_np (q : OpenSquare) (nx ny : ℝ)
    (first : nx*q.c+ny*q.s≤0) (last : 0≤ -nx*q.s+ny*q.c) :
    lower q nx ny=(nx*q.c+ny*q.s)*(q.loU+q.side)+(-nx*q.s+ny*q.c)*q.loV := by
  rw [C981CompletionSupportForms.lower_in_bands,abs_of_nonpos first,abs_of_nonneg last]
  ring

private theorem upper_self_v (q : OpenSquare) : upper q (-q.s) q.c=q.loV+q.side := by
  have first : (-q.s)*q.c+q.c*q.s=0 := by ring
  have last : -(-q.s)*q.s+q.c*q.c=1 := by nlinarith only [q.unit_normal]
  rw [C981CompletionSupportForms.upper_in_bands,first,last]
  norm_num <;> ring

private theorem lower_self_v (q : OpenSquare) : lower q (-q.s) q.c=q.loV := by
  have first : (-q.s)*q.c+q.c*q.s=0 := by ring
  have last : -(-q.s)*q.s+q.c*q.c=1 := by nlinarith only [q.unit_normal]
  rw [C981CompletionSupportForms.lower_in_bands,first,last]
  norm_num <;> ring

theorem positive_pair_impossible (E N : OpenSquare) (h : PositivePairInput E N) : False := by
  let alpha := E.c*N.c+E.s*N.s
  let beta := E.c*N.s-E.s*N.c
  let H0 := 1-E.s-E.c/2
  let A0 := E.c-(13/50)*E.s
  let cap := (543/500)*N.c-1
  have cb := normal_bounds h.sourceNormal
  have db := normal_bounds h.targetNormal
  have cp : 0<E.c := by linarith only [h.sourceFaces.cosine]
  have dp : 0<N.c := by linarith only [db.1]
  have sideN : 1<N.side := by rw [←h.same]; exact h.side
  have ap : 0<alpha := by
    have first := mul_pos cp dp
    have last := mul_nonneg h.sourceNormal.1 h.targetNormal.1
    dsimp only [alpha]
    nlinarith only [first,last]
  have lowU : E.loU<0 := by linarith only [h.sourceFaces.lowerU,h.sourceFaces.cosineUpper]
  have highU : A0<E.loU+E.side := by dsimp only [A0]; linarith only [h.sourceOuter.2.1]
  have highV : H0<E.loV+E.side := by dsimp only [H0]; linarith only [h.sourceFloor,h.side]
  have hpositive : 0<H0 := by dsimp only [H0]; linarith only [h.sourceFaces.sineUpper,cb.2.1]
  have capV : N.loV<cap := by dsimp only [cap]; linarith only [h.targetFaces.upperV,sideN]
  have lowerA : 1+(13/50)*N.s<N.loU+N.side := by
    linarith only [h.targetFaces.lowerU,sideN]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper E nx ny≤lower N nx ny) : 0<ny := by
    have first := (strict_bounds E 0 0 nx ny unit h.sourceCenter).2
    have last := (strict_bounds N 0 1 nx ny unit h.targetOrigin).1
    linarith only [first,last,sep]
  have reverse (nx ny : ℝ) (sep : upper N nx ny≤lower E nx ny) :
      upper E (-nx) (-ny)≤lower N (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have noEU (sep : upper E E.c E.s≤lower N E.c E.s ∨
      upper N E.c E.s≤lower E E.c E.s) : False := by
    rcases sep with forward | backward
    · have first := (strict_bounds E 1 (-13/50) E.c E.s E.unit_normal h.sourceOuter).2
      have last := (strict_bounds N 0 1 E.c E.s E.unit_normal h.targetOrigin).1
      linarith only [first,last,forward,h.sourceFaces.cosine,h.sourceFaces.sineUpper]
    · have sign := cone (-E.c) (-E.s)
        (by simpa only [neg_sq] using E.unit_normal) (reverse _ _ backward)
      linarith only [sign,h.sourceFaces.sine]
  have noNU (sep : upper E N.c N.s≤lower N N.c N.s ∨
      upper N N.c N.s≤lower E N.c N.s) : False := by
    rcases sep with forward | backward
    · have first := (strict_bounds E 1 (-13/50) N.c N.s N.unit_normal h.sourceOuter).2
      have last := (strict_bounds N (7/20) (7/20) N.c N.s N.unit_normal h.targetMarker).1
      linarith only [first,last,forward,dp,h.targetNormal.1,h.targetNormal.2.1]
    · have sign := cone (-N.c) (-N.s)
        (by simpa only [neg_sq] using N.unit_normal) (reverse _ _ backward)
      linarith only [sign,h.targetPositive]
  have noEV (sep : upper E (-E.s) E.c≤lower N (-E.s) E.c ∨
      upper N (-E.s) E.c≤lower E (-E.s) E.c) : False := by
    rcases sep with forward | backward
    · rw [upper_self_v] at forward
      by_cases order : 0≤beta
      · have formula := lower_pp N (-E.s) E.c
          (by dsimp only [beta] at order; nlinarith only [order])
          (by dsimp only [alpha] at ap; nlinarith only [ap])
        have first := mul_nonneg order
          (show 0<(7/20)*(N.c+N.s)-N.loU by linarith only [h.targetMarker.1]).le
        have last := mul_pos ap (sub_pos.mpr capV)
        have margin := NortheastPositiveScalars.source_axis_steeper h.sourceNormal h.targetNormal
        have identity : H0-beta*((7/20)*(N.c+N.s))-alpha*cap=
            1-E.c*NortheastPositiveScalars.Aplus N.c N.s-
              E.s*NortheastPositiveScalars.Bplus N.c N.s := by
          dsimp only [H0,beta,alpha,cap,NortheastPositiveScalars.Aplus,
            NortheastPositiveScalars.Bplus]
          linear_combination (-(543/500)*E.c+(7/20)*E.s)*N.unit_normal
        dsimp only [alpha,beta,H0,cap] at formula first last identity highV capV
        nlinarith only [formula,first,last,margin,identity,forward,highV]
      · have negative : beta≤0 := le_of_not_ge order
        have relation := NortheastPositiveScalars.relative_order h.sourceNormal h.targetNormal
          (by dsimp only [beta] at negative; linarith only [negative])
        have formula := lower_np N (-E.s) E.c
          (by dsimp only [beta] at negative; nlinarith only [negative])
          (by dsimp only [alpha] at ap; nlinarith only [ap])
        have first := mul_nonneg (neg_nonneg.mpr negative)
          (sub_nonneg.mpr lowerA.le)
        have last := mul_pos ap (sub_pos.mpr capV)
        have margin := NortheastPositiveScalars.source_axis_shallower
          h.sourceNormal h.targetNormal h.targetPositive relation.2
        have identity : H0-beta*(1+(13/50)*N.s)-alpha*cap=
            1-E.c*NortheastPositiveScalars.Aminus N.c N.s-
              E.s*NortheastPositiveScalars.Bminus N.c N.s := by
          dsimp only [H0,beta,alpha,cap,NortheastPositiveScalars.Aminus,
            NortheastPositiveScalars.Bminus]
          linear_combination -(543/500)*E.c*N.unit_normal
        dsimp only [alpha,beta,H0,cap] at formula first last identity highV capV
        nlinarith only [formula,first,last,margin,identity,forward,highV]
    · have sign := cone E.s (-E.c) (by nlinarith only [E.unit_normal])
        (by simpa only [neg_neg] using reverse _ _ backward)
      linarith only [sign,cp]
  have noNV (sep : upper E (-N.s) N.c≤lower N (-N.s) N.c ∨
      upper N (-N.s) N.c≤lower E (-N.s) N.c) : False := by
    rcases sep with forward | backward
    · rw [lower_self_v] at forward
      by_cases order : 0≤beta
      · have relation := NortheastPositiveScalars.relative_order h.targetNormal h.sourceNormal
          (by dsimp only [beta] at order; linarith only [order])
        have formula := upper_np E (-N.s) N.c
          (by dsimp only [beta] at order; nlinarith only [order])
          (by dsimp only [alpha] at ap; nlinarith only [ap])
        have first := mul_nonneg order (neg_nonneg.mpr lowU.le)
        have last := mul_pos ap (sub_pos.mpr highV)
        have cosine := NortheastPositiveScalars.alpha_lower h.sourceNormal h.targetNormal relation.1
        have alphaWeight := mul_nonneg
          (show 0≤alpha-N.c by dsimp only [alpha]; linarith only [cosine]) hpositive.le
        have floorWeight := mul_nonneg dp.le
          (show 0≤H0-(1/2-N.s) by dsimp only [H0]; linarith only [relation.1,cb.2.1])
        have projection := NortheastPositiveScalars.right_projection h.targetNormal
        dsimp only [alpha,beta,H0] at first last alphaWeight floorWeight
        dsimp only [cap] at capV
        nlinarith only [formula,first,last,alphaWeight,floorWeight,projection,capV,forward]
      · have negative : beta≤0 := le_of_not_ge order
        have relation := NortheastPositiveScalars.relative_order h.sourceNormal h.targetNormal
          (by dsimp only [beta] at negative; linarith only [negative])
        have formula := upper_pp E (-N.s) N.c
          (by dsimp only [beta] at negative; nlinarith only [negative])
          (by dsimp only [alpha] at ap; nlinarith only [ap])
        have first := mul_nonneg (neg_nonneg.mpr negative) (sub_nonneg.mpr highU.le)
        have last := mul_pos ap (sub_pos.mpr highV)
        have margin := NortheastPositiveScalars.north_axis_shallower
          h.sourceNormal h.targetNormal h.sourceFaces.cosine h.sourceFaces.sineUpper relation.1
        have identity : (-beta)*A0+alpha*H0-cap=
            1-N.c*NortheastPositiveScalars.P E.c E.s-
              N.s*NortheastPositiveScalars.Q E.c E.s := by
          dsimp only [beta,A0,alpha,H0,cap,NortheastPositiveScalars.P,NortheastPositiveScalars.Q]
          linear_combination (-(13/50)*N.c-N.s)*E.unit_normal
        dsimp only [alpha,beta,A0,H0,cap] at formula first last identity capV
        nlinarith only [formula,first,last,margin,identity,capV,forward]
    · have sign := cone N.s (-N.c) (by nlinarith only [N.unit_normal])
        (by simpa only [neg_neg] using reverse _ _ backward)
      linarith only [sign,dp]
  have axes := CongruentSAT.faceSeparation_of_disjoint E N h.same h.apart
  change pairRadius E N≤|E.c*(centerX N-centerX E)+E.s*(centerY N-centerY E)| ∨
    pairRadius E N≤|-E.s*(centerX N-centerX E)+E.c*(centerY N-centerY E)| ∨
    pairRadius N E≤|N.c*(centerX N-centerX E)+N.s*(centerY N-centerY E)| ∨
    pairRadius N E≤|-N.s*(centerX N-centerX E)+N.c*(centerY N-centerY E)| at axes
  have separate (nx ny radius : ℝ)
      (eq : supportRadius E nx ny+supportRadius N nx ny=radius)
      (axis : radius≤|nx*(centerX N-centerX E)+ny*(centerY N-centerY E)|) :=
    separated E N nx ny (by rwa [eq])
  rcases axes with eu | ev | nu | nv
  · exact noEU (separate _ _ _ (parallel_radius E N) eu)
  · exact noEV (separate _ _ _ (transverse_radius E N) ev)
  · have radius : supportRadius E N.c N.s+supportRadius N N.c N.s=pairRadius N E := by
      rw [add_comm]; exact parallel_radius N E
    exact noNU (separate _ _ _ radius nu)
  · have radius : supportRadius E (-N.s) N.c+supportRadius N (-N.s) N.c=pairRadius N E := by
      rw [add_comm]; exact transverse_radius N E
    exact noNV (separate _ _ _ radius nv)

end N12Compact.FiniteCases.C972Local

namespace N12Compact.FiniteCases.C972
open S12 S12Pilot C977CornerCubic
set_option Elab.async false
noncomputable section

theorem family_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : False := by
  obtain ⟨E,eShape,eActual,en,ep⟩ :=
    exists_positive_southeast p hf (southeast_missing_halfpoint p hf)
  obtain ⟨N,nShape,nActual,nn,np⟩ := exists_positive_northeast p hf
  have data := southeast_support_profile p hf (southeast_missing_halfpoint p hf)
    E eShape eActual (by linarith only [(normal_bounds en).1])
    (by simpa only [abs_of_nonneg en.1] using en.2.1)
  exact C972Local.positive_pair_impossible E N {
    side := by rw [eShape]; exact side p 6
    same := eShape.trans ((same p 6 7).trans nShape.symm)
    sourceNormal := en
    targetNormal := nn
    targetPositive := np
    sourceFaces := data
    sourceCenter := by apply (eActual _ _).mpr; norm_num; exact southeast_center p hf
    sourceOuter := by apply (eActual _ _).mpr; norm_num; exact (fixed p hf).southeastF8
    sourceFloor := southeast_lower_face p hf E eShape eActual en
    targetMarker := by apply (nActual _ _).mpr; norm_num; exact (fixed p hf).northeastMarker
    targetOrigin := by apply (nActual _ _).mpr; norm_num; exact northeast_origin p hf
    targetFaces := northeast_positive_faces p hf N nShape nActual nn
    apart := by
      intro x y both
      exact apart p hf 6 7 (by decide) _ _ ⟨(eActual _ _).mp both.1,(nActual _ _).mp both.2⟩ }

end
#print axioms family_impossible
end N12Compact.FiniteCases.C972
