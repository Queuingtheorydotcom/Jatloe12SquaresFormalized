import Compact.Completion.FiniteCases.C972NortheastSignScalars
import Compact.Completion.FiniteCases.C972ResidualFaces
import Compact.Completion.OtherCases.SupportBands

/-! The genuine remaining C972 northeast square has positive canonical
sine. The entire nonpositive sector is excluded by its actual origin,
the actual positive southeast square, and the two markers of the paired
northeast corner. No absent top marker is made into a top-wall square. -/
namespace N12Compact.FiniteCases.C972Local
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
open C977CornerCubic N12Compact.Completion.OtherCases
set_option Elab.async false

structure NegativeNorth (N : OpenSquare) : Prop where
  lowerU : (543/500)*N.s≤N.loU
  lowerV : (13/50)*N.c≤N.loV
  upperV : N.loV+N.side≤N.c-N.s
  positiveU : 0<N.loU+N.side

theorem negative_north_faces (N : OpenSquare) (side : 1<N.side)
    (normal : Normal N.c (-N.s))
    (marker : N.Inside (7/20) (7/20)) (origin : N.Inside 0 1)
    (inner : ¬N.Inside 0 (13/50)) (top : ¬N.Inside 0 (543/500))
    (corner : ¬N.Inside 1 1) (upperCorner : ¬N.Inside 1 (543/500)) :
    NegativeNorth N := by
  let r := -N.s
  have rn : 0≤r := normal.1
  have order : r≤N.c := normal.2.1
  have signed : N.s= -r := by dsimp only [r]; ring
  have unit : N.c^2+r^2=1 := normal.2.2
  have bounds := normal_bounds normal
  have cp : 0<N.c := by linarith only [bounds.1]
  have m := marker
  have o := origin
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,
    mul_one,zero_add] at m o
  have lowerV : (13/50)*N.c≤N.loV := by
    apply le_of_not_gt
    intro low
    apply inner
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_add]
    refine ⟨?_,?_,by nlinarith only [low],?_⟩ <;> linarith only [o.1,m.2.1,o.2.2.2,cp,rn,order]
  have lowerU : -(543/500)*r≤N.loU := by
    apply le_of_not_gt
    intro low
    have upperV : N.loV+N.side≤(543/500)*N.c := by
      apply le_of_not_gt
      intro high
      apply top
      simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_add]
      refine ⟨?_,?_,?_,by nlinarith only [high]⟩ <;> linarith only [low,o.2.1,m.2.2.1,cp,rn,order]
    linarith only [lowerV,upperV,side,bounds.2.1]
  have upperCornerFace : N.loV+N.side≤r+(543/500)*N.c := by
    apply le_of_not_gt
    intro high
    apply upperCorner
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one]
    refine ⟨?_,?_,?_,by nlinarith only [high]⟩ <;>
      linarith only [o.1,lowerU,side,bounds.2.1,m.2.2.1,cp,rn,order]
  have sine : 87/500<r := by
    linarith only [lowerV,upperCornerFace,side,bounds.2.1]
  have squareUpper : N.c≤1-r^2/2 := by nlinarith only [unit,sq_nonneg (N.c-1)]
  have product := mul_pos (show 0<r by linarith only [sine])
    (show 0<r-43/250 by linarith only [sine])
  have short : N.c+(43/500)*r<1 := by nlinarith only [squareUpper,product]
  have upperV : N.loV+N.side≤N.c+r := by
    apply le_of_not_gt
    intro high
    apply corner
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one]
    refine ⟨?_,?_,?_,by nlinarith only [high]⟩ <;> linarith only [o.1,lowerU,side,short,m.2.2.1,cp,rn]
  have sineCap : r≤5/7 := by linarith only [order,bounds.2.2.2.2.2]
  refine ⟨?_,lowerV,?_,?_⟩
  · rw [signed]; linarith only [lowerU]
  · rw [signed]; linarith only [upperV]
  · linarith only [lowerU,side,sineCap]

structure NortheastSignInput (E N : OpenSquare) : Prop where
  side : 1<E.side
  same : E.side=N.side
  sourceNormal : Normal E.c E.s
  positive : 0<E.s
  cosine : 4/5<E.c
  sine : E.s<1/2
  outer : E.Inside 1 (-13/50)
  center : E.Inside 0 0
  floor : -E.s-E.c/2≤E.loV
  targetNormal : Normal N.c (-N.s)
  targetMarker : N.Inside (7/20) (7/20)
  targetOrigin : N.Inside 0 1
  inner : ¬N.Inside 0 (13/50)
  top : ¬N.Inside 0 (543/500)
  corner : ¬N.Inside 1 1
  upperCorner : ¬N.Inside 1 (543/500)
  apart : ∀ x y,¬(E.Inside x y ∧ N.Inside x y)

private theorem upper_pp (q : OpenSquare) (nx ny : ℝ)
    (first : 0≤nx*q.c+ny*q.s) (last : 0≤ -nx*q.s+ny*q.c) :
    upper q nx ny=(nx*q.c+ny*q.s)*(q.loU+q.side)+
      (-nx*q.s+ny*q.c)*(q.loV+q.side) := by
  rw [C981CompletionSupportForms.upper_in_bands,abs_of_nonneg first,abs_of_nonneg last]
  ring

private theorem lower_np (q : OpenSquare) (nx ny : ℝ)
    (first : nx*q.c+ny*q.s≤0) (last : 0≤ -nx*q.s+ny*q.c) :
    lower q nx ny=(nx*q.c+ny*q.s)*(q.loU+q.side)+
      (-nx*q.s+ny*q.c)*q.loV := by
  rw [C981CompletionSupportForms.lower_in_bands,abs_of_nonpos first,abs_of_nonneg last]
  ring

theorem northeast_negative_impossible (E N : OpenSquare)
    (h : NortheastSignInput E N) : False := by
  let r := -N.s
  let j := r*E.c+N.c*E.s
  let k := N.c*E.c-r*E.s
  have signed : N.s= -r := by dsimp only [r]; ring
  have normal : Normal N.c r := h.targetNormal
  have bounds := normal_bounds normal
  have cp : 0<E.c := by linarith only [h.cosine]
  have dp : 0<N.c := by linarith only [bounds.1]
  have sideN : 1<N.side := by rw [←h.same]; exact h.side
  have n := negative_north_faces N sideN h.targetNormal h.targetMarker h.targetOrigin
    h.inner h.top h.corner h.upperCorner
  have jp : 0<j := by
    have first := mul_nonneg normal.1 cp.le
    have last := mul_pos dp h.positive
    dsimp only [j]
    nlinarith only [first,last]
  have kp : 0<k := by
    have first := mul_pos dp (show 0<E.c-E.s by linarith only [h.cosine,h.sine])
    have last := mul_nonneg h.sourceNormal.1 (sub_nonneg.mpr normal.2.1)
    dsimp only [k]
    nlinarith only [first,last]
  have highU : E.c-(13/50)*E.s<E.loU+E.side := by
    linarith only [h.outer.2.1]
  have highV : 1-E.s-E.c/2<E.loV+E.side := by linarith only [h.floor,h.side]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper E nx ny≤lower N nx ny) : 0<ny := by
    have first := (strict_bounds E 0 0 nx ny unit h.center).2
    have last := (strict_bounds N 0 1 nx ny unit h.targetOrigin).1
    linarith only [first,last,sep]
  have reverse (nx ny : ℝ) (sep : upper N nx ny≤lower E nx ny) :
      upper E (-nx) (-ny)≤lower N (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have noEU (sep : upper E E.c E.s≤lower N E.c E.s ∨
      upper N E.c E.s≤lower E E.c E.s) : False := by
    rcases sep with forward | backward
    · have first := (strict_bounds E 1 (-13/50) E.c E.s E.unit_normal h.outer).2
      have last := (strict_bounds N 0 1 E.c E.s E.unit_normal h.targetOrigin).1
      linarith only [first,last,forward,h.cosine,h.sine]
    · have sign := cone (-E.c) (-E.s)
        (by simpa only [neg_sq] using E.unit_normal) (reverse _ _ backward)
      linarith only [sign,h.positive]
  have noNU (sep : upper E N.c N.s≤lower N N.c N.s ∨
      upper N N.c N.s≤lower E N.c N.s) : False := by
    rcases sep with forward | backward
    · have sign := cone N.c N.s N.unit_normal forward
      linarith only [sign,h.targetNormal.1]
    · have axis := reverse _ _ backward
      have strict := (strict_bounds E 0 0 (-N.c) (-N.s)
        (by simpa only [neg_sq] using N.unit_normal) h.center).2
      have vertex := WallProfile.vertex N (N.loU+N.side) N.loV
        ⟨by linarith only [N.side_pos],le_rfl⟩
        ⟨le_rfl,by linarith only [N.side_pos]⟩
      have closed := (closed_bounds N _ _ (-N.c) (-N.s) vertex).1
      have identity : (-N.c)*(N.c*(N.loU+N.side)-N.s*N.loV)+
          (-N.s)*(N.s*(N.loU+N.side)+N.c*N.loV)= -(N.loU+N.side) := by
        linear_combination -(N.loU+N.side)*N.unit_normal
      rw [identity] at closed
      linarith only [strict,closed,axis,n.positiveU]
  have noNV (sep : upper E (-N.s) N.c≤lower N (-N.s) N.c ∨
      upper N (-N.s) N.c≤lower E (-N.s) N.c) : False := by
    have unit : (-N.s)^2+N.c^2=1 := by nlinarith only [N.unit_normal]
    rcases sep with forward | backward
    · have formula := upper_pp E (-N.s) N.c
        (by dsimp only [j,r] at jp; nlinarith only [jp])
        (by dsimp only [k,r] at kp; nlinarith only [kp])
      have first := mul_pos jp (sub_pos.mpr highU)
      have last := mul_pos kp (sub_pos.mpr highV)
      have margin := NortheastScalars.north_transverse h.sourceNormal normal h.cosine h.sine
      have identity : j*(E.c-(13/50)*E.s)+k*(1-E.s-E.c/2)-
          (7/20)*(N.c+r)=
          N.c*(E.c-61/100-(6/25)*E.c^2)+
            r*(13/20-E.s+(6/25)*E.c*E.s) := by
        dsimp only [j,k]
        linear_combination (r-(13/50)*N.c)*E.unit_normal
      have point := (strict_bounds N (7/20) (7/20) (-N.s) N.c unit h.targetMarker).1
      dsimp only [j,k,r] at first last identity margin
      nlinarith only [formula,first,last,identity,margin,point,forward]
    · have opposite := reverse _ _ backward
      have sign := cone N.s (-N.c) (by nlinarith only [N.unit_normal])
        (by simpa only [neg_neg] using opposite)
      linarith only [sign,dp]
  have noEV (sep : upper E (-E.s) E.c≤lower N (-E.s) E.c ∨
      upper N (-E.s) E.c≤lower E (-E.s) E.c) : False := by
    have unit : (-E.s)^2+E.c^2=1 := by nlinarith only [E.unit_normal]
    rcases sep with forward | backward
    · have formula := lower_np N (-E.s) E.c
        (by rw [signed]; dsimp only [j] at jp; nlinarith only [jp])
        (by rw [signed]; dsimp only [k] at kp; nlinarith only [kp])
      have first := mul_pos jp
        (show 0<N.loU+N.side-(1-(543/500)*r) by
          have lower := n.lowerU
          rw [signed] at lower
          linarith only [lower,sideN])
      have last := mul_pos kp
        (show 0<(7/20)*(N.c+r)-N.loV by
          have marker := h.targetMarker.2.2.1
          rw [signed] at marker
          linarith only [marker])
      have margin := NortheastScalars.source_transverse h.sourceNormal normal
      have identity : 1-E.s-E.c/2+j*(1-(543/500)*r)-
          (7/20)*k*(N.c+r)=1-E.c*NortheastScalars.A N.c r-
            E.s*NortheastScalars.B N.c r := by
        dsimp only [j,k,NortheastScalars.A,NortheastScalars.B]
        linear_combination -(7/20)*E.c*normal.2.2
      have vertex := WallProfile.vertex E E.loU (E.loV+E.side)
        ⟨le_rfl,by linarith only [E.side_pos]⟩
        ⟨by linarith only [E.side_pos],le_rfl⟩
      have closed := (closed_bounds E _ _ (-E.s) E.c vertex).2
      have own : (-E.s)*(E.c*E.loU-E.s*(E.loV+E.side))+
          E.c*(E.s*E.loU+E.c*(E.loV+E.side))=E.loV+E.side := by
        linear_combination (E.loV+E.side)*E.unit_normal
      rw [own] at closed
      rw [signed] at formula
      dsimp only [j,k,r] at formula first last identity margin
      nlinarith only [formula,first,last,identity,margin,highV,closed,forward]
    · have sign := cone E.s (-E.c) (by nlinarith only [E.unit_normal])
        (by simpa only [neg_neg] using reverse _ _ backward)
      linarith only [sign,cp]
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

theorem southeast_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside 2 2 := by
  obtain ⟨E,shape,actual,normal,positive⟩ :=
    exists_positive_southeast p hf (southeast_missing_halfpoint p hf)
  have data := southeast_support_profile p hf (southeast_missing_halfpoint p hf)
    E shape actual (by linarith only [(normal_bounds normal).1])
    (by simpa only [abs_of_nonneg normal.1] using normal.2.1)
  have height := southeast_height_positive p hf E shape actual normal
  have own : E.Inside 0 0 := by
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [data.lowerU,data.cosineUpper,data.upperU,data.cosine,
        data.lowerV,data.sine,data.upperV,height]
  convert (actual _ _).mp own using 1 <;> norm_num

theorem northeast_positive (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (N : OpenSquare) (shape : N.side=(owners p 7).side)
    (actual : ∀ x y,N.Inside x y↔(owners p 7).Inside (2+x) (2+y))
    (cp : 0<N.c) (canonical : |N.s|≤N.c) : 0<N.s := by
  apply lt_of_not_ge
  intro nonpositive
  obtain ⟨E,eShape,eActual,en,positive⟩ :=
    exists_positive_southeast p hf (southeast_missing_halfpoint p hf)
  have data := southeast_support_profile p hf (southeast_missing_halfpoint p hf)
    E eShape eActual (by linarith only [(normal_bounds en).1])
    (by simpa only [abs_of_nonneg en.1] using en.2.1)
  have input : C972Local.NortheastSignInput E N := {
    side := by rw [eShape]; exact side p 6
    same := eShape.trans ((same p 6 7).trans shape.symm)
    sourceNormal := en
    positive := positive
    cosine := data.cosine
    sine := data.sineUpper
    outer := by apply (eActual _ _).mpr; norm_num; exact (fixed p hf).southeastF8
    center := by apply (eActual _ _).mpr; norm_num; exact southeast_center p hf
    floor := southeast_lower_face p hf E eShape eActual en
    targetNormal := ⟨by linarith only [nonpositive],
      by simpa only [abs_of_nonpos nonpositive] using canonical,
      by nlinarith only [N.unit_normal]⟩
    targetMarker := by apply (actual _ _).mpr; norm_num; exact (fixed p hf).northeastMarker
    targetOrigin := by apply (actual _ _).mpr; norm_num; exact northeast_origin p hf
    inner := by
      intro own
      apply northeast_missing_f5 p hf
      convert (actual _ _).mp own using 1 <;> norm_num
    top := by
      intro own
      apply missing_top p hf 7
      convert (actual _ _).mp own using 1 <;> norm_num
    corner := by
      intro own
      exact apart p hf 7 3 (by decide) _ _
        ⟨by convert (actual _ _).mp own using 1 <;> norm_num,(fixed p hf).northeastCorner⟩
    upperCorner := by
      intro own
      have marker := seed p hf 3 (3,1543/500) (by decide +kernel)
      exact apart p hf 7 3 (by decide) _ _
        ⟨by convert (actual _ _).mp own using 1,by norm_num at marker ⊢; exact marker⟩
    apart := by
      intro x y both
      exact apart p hf 6 7 (by decide) _ _ ⟨(eActual _ _).mp both.1,(actual _ _).mp both.2⟩ }
  exact C972Local.northeast_negative_impossible E N input

theorem exists_positive_northeast (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ∃ N : OpenSquare,N.side=(owners p 7).side ∧
      (∀ x y,N.Inside x y↔(owners p 7).Inside (2+x) (2+y)) ∧
        Normal N.c N.s ∧ 0<N.s := by
  obtain ⟨N,cp,canonical,shape,inside,_⟩ :=
    ClosedFrames.canonical_frame ((owners p 7).translated 2 2)
  have actual (x y : ℝ) : N.Inside x y↔(owners p 7).Inside (2+x) (2+y) :=
    (inside x y).trans (inside_translated_iff _ _ _ _ _)
  have shape' : N.side=(owners p 7).side := shape
  have positive := northeast_positive p hf N shape' actual cp canonical
  exact ⟨N,shape',actual,⟨positive.le,
    by simpa only [abs_of_pos positive] using canonical,N.unit_normal⟩,positive⟩

end
#print axioms southeast_center
#print axioms northeast_positive
#print axioms exists_positive_northeast
end N12Compact.FiniteCases.C972
