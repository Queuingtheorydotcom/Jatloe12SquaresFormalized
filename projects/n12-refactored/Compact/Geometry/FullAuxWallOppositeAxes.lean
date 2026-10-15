import Compact.Geometry.FullAuxWallLowerCorner
import Compact.Completion.C981.SupportForms

/-! Exhaustive separation of a narrow escaping northeast elbow from an
opposite square in a negative canonical frame. All four SAT axes and both
directions are retained before elimination. The resulting two-offset cut
is a consequence of the original squares, not an assumed selector. -/
namespace N12Compact.FullAuxWallOppositeAxes

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977ChainBridge C981CompletionSupportForms
set_option Elab.async false

private theorem opposite_u_impossible (A D : OpenSquare) (S : ℝ)
    (hc : 0<A.c) (hs : 0<A.s) (narrow : 4*A.s≤A.c)
    (p : A.Inside 2 (113/50)) (high : A.Inside (5/2) 3)
    (ds : D.s=-S) (dc : 0<D.c) (dS : 0≤S) (canonical : S≤D.c)
    (center : D.Inside 2 2)
    (axis : D.loU+D.side≤lower A D.c D.s) : False := by
  let α := A.c*D.c-A.s*S
  let β := A.c*S+A.s*D.c
  let e := A.loU-2*(A.c+A.s)
  let h := A.loV+A.side-2*(A.c-A.s)
  have ap : 0<α := by
    have first := mul_pos dc (show 0<A.c-A.s by linarith only [narrow,hs])
    have second := mul_nonneg hs.le (sub_nonneg.mpr canonical)
    dsimp [α]
    nlinarith only [first,second]
  have bp : 0<β := by
    have first := mul_nonneg hc.le dS
    have second := mul_pos hs dc
    dsimp [β]
    linarith only [first,second]
  have offset : e<(13/50)*A.s := by dsimp [e]; linarith only [p.1]
  have height : A.c-A.s/2<h := by dsimp [h]; linarith only [high.2.2.2]
  have first := mul_lt_mul_of_pos_left offset ap
  have second := mul_lt_mul_of_pos_left height bp
  have width : 0<(37/50)*A.c-A.s/2 := by linarith only [narrow,hs]
  have negative := mul_pos (mul_pos dc hs) width
  have nonnegative : 0≤S*(A.c^2-A.c*A.s/2+(13/50)*A.s^2) := by
    have product := mul_nonneg hc.le
      (show 0≤A.c-A.s/2 by linarith only [narrow,hs])
    apply mul_nonneg dS
    nlinarith only [product,sq_nonneg A.s]
  have scalarIdentity :
      (13/50)*A.s*α-β*(A.c-A.s/2)=
        -D.c*A.s*((37/50)*A.c-A.s/2)-
          S*(A.c^2-A.c*A.s/2+(13/50)*A.s^2) := by
    dsimp [α,β]
    ring
  have scalar : α*e-β*h<0 := by
    calc
      _ < α*((13/50)*A.s)-β*(A.c-A.s/2) := sub_lt_sub first second
      _ = (13/50)*A.s*α-β*(A.c-A.s/2) := by ring
      _ < 0 := by
        rw [scalarIdentity]
        nlinarith only [negative,nonnegative]
  have support : lower A D.c D.s=α*A.loU-β*(A.loV+A.side) := by
    rw [ds,lower_in_bands]
    have u : D.c*A.c+(-S)*A.s=α := by dsimp [α]; ring
    have v : -D.c*A.s+(-S)*A.c=-β := by dsimp [β]; ring
    rw [u,v,abs_of_nonneg ap.le,abs_of_nonpos (neg_nonpos.mpr bp.le)]
    ring
  have identity : lower A D.c D.s-2*(D.c-S)=α*e-β*h := by
    rw [support]
    dsimp [e,h,α,β]
    linear_combination (2*(D.c-S))*A.unit_normal
  have strict := center.2.1
  rw [ds] at strict
  nlinarith only [axis,strict,identity,scalar]

/-- All disjointness alternatives reduce to separation on the narrow
elbow's U face. The opposite square's true center and southwest marker
are enough; no guessed opposite-angle enclosure is required. -/
theorem separation (A D : OpenSquare) (S : ℝ)
    (ha : 1<A.side) (same : A.side=D.side)
    (hc : 0<A.c) (hs : 0<A.s) (narrow : 4*A.s≤A.c)
    (p : A.Inside 2 (113/50)) (m : A.Inside (47/20) (47/20))
    (high : A.Inside (5/2) 3)
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (ds : D.s=-S) (dc : 0<D.c) (dS : 0≤S) (canonical : S≤D.c)
    (marker : D.Inside (33/20) (33/20)) (center : D.Inside 2 2)
    (apart : ∀ x y, ¬(A.Inside x y ∧ D.Inside x y)) :
    upper D A.c A.s≤A.loU := by
  have acs : 0<A.c-A.s := by linarith only [narrow,hs]
  have aUnit : (-A.s)^2+A.c^2=1 := by nlinarith only [A.unit_normal]
  have dUnit : (-D.s)^2+D.c^2=1 := by nlinarith only [D.unit_normal]
  have forward (nx ny : ℝ) (unit : nx^2+ny^2=1) (direction : 0≤nx+ny)
      (sep : upper D nx ny≤lower A nx ny ∨ upper A nx ny≤lower D nx ny) :
      upper D nx ny≤lower A nx ny := by
    rcases sep with yes | no
    · exact yes
    · have low := strict_bounds D _ _ nx ny unit marker
      have high := strict_bounds A _ _ nx ny unit m
      exfalso
      nlinarith only [low.1,high.2,no,direction]
  have ownVImpossible (axis : upper D (-A.s) A.c≤A.loV) : False := by
    have own := strict_bounds D _ _ (-A.s) A.c aUnit center
    have cosine : A.c≤1 := by
      nlinarith only [A.unit_normal,sq_nonneg A.s,hc]
    nlinarith only [axis,own.2,top,ha,cosine,hs]
  have axes := CongruentSAT.faceSeparation_of_disjoint D A same.symm
    (fun x y h => apart x y ⟨h.2,h.1⟩)
  change pairRadius D A≤|D.c*(centerX A-centerX D)+D.s*(centerY A-centerY D)| ∨
    pairRadius D A≤|-D.s*(centerX A-centerX D)+D.c*(centerY A-centerY D)| ∨
    pairRadius A D≤|A.c*(centerX A-centerX D)+A.s*(centerY A-centerY D)| ∨
    pairRadius A D≤|-A.s*(centerX A-centerX D)+A.c*(centerY A-centerY D)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius D nx ny+supportRadius A nx ny=R)
      (sep : R≤|nx*(centerX A-centerX D)+ny*(centerY A-centerY D)|) :=
    separated D A nx ny (by rwa [identity])
  rcases axes with du | dv | au | av
  · have selected := forward D.c D.s D.unit_normal
      (by rw [ds]; linarith only [canonical])
      (separateAxis _ _ _ (parallel_radius D A) du)
    have own : D.loU+D.side≤lower A D.c D.s := by
      simpa only [(ownU D).2] using selected
    exact False.elim (opposite_u_impossible A D S hc hs narrow p high
      ds dc dS canonical center own)
  · have selected := forward (-D.s) D.c dUnit
      (by rw [ds]; linarith only [dc,dS])
      (separateAxis _ _ _ (transverse_radius D A) dv)
    have own : D.loV+D.side≤lower A (-D.s) D.c := by
      simpa only [(ownV D).2] using selected
    exact False.elim (FullAuxWallLowerCorner.opposite_v_impossible A D S
      ha hc hs narrow p top ds dc dS canonical center own)
  · have identity : supportRadius D A.c A.s+supportRadius A A.c A.s=
        pairRadius A D := by rw [add_comm]; exact parallel_radius A D
    have selected := forward A.c A.s A.unit_normal
      (by linarith only [hc,hs]) (separateAxis _ _ _ identity au)
    simpa only [(ownU A).1] using selected
  · have identity : supportRadius D (-A.s) A.c+supportRadius A (-A.s) A.c=
        pairRadius A D := by rw [add_comm]; exact transverse_radius A D
    have selected := forward (-A.s) A.c aUnit
      (by linarith only [acs]) (separateAxis _ _ _ identity av)
    have own : upper D (-A.s) A.c≤A.loV := by
      simpa only [(ownV A).1] using selected
    exact False.elim (ownVImpossible own)

/-- The actual opposite square's two upper-face offsets satisfy the
strict cut. Both offsets are measured from its strictly owned center. -/
theorem cut (A D : OpenSquare) (S : ℝ)
    (ha : 1<A.side) (same : A.side=D.side)
    (hc : 0<A.c) (hs : 0<A.s) (narrow : 4*A.s≤A.c)
    (p : A.Inside 2 (113/50)) (m : A.Inside (47/20) (47/20))
    (high : A.Inside (5/2) 3)
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (ds : D.s=-S) (dc : 0<D.c) (dS : 0≤S) (canonical : S≤D.c)
    (marker : D.Inside (33/20) (33/20)) (center : D.Inside 2 2)
    (apart : ∀ x y, ¬(A.Inside x y ∧ D.Inside x y)) :
    (A.c*D.c-A.s*S)*(D.loU+D.side-2*(D.c-S))+
      (A.c*S+A.s*D.c)*(D.loV+D.side-2*(D.c+S))<(13/50)*A.s := by
  have selected := separation A D S ha same hc hs narrow p m high top
    ds dc dS canonical marker center apart
  let α := A.c*D.c-A.s*S
  let β := A.c*S+A.s*D.c
  have ap : 0≤α := by
    have first := mul_nonneg dc.le
      (show 0≤A.c-A.s by linarith only [narrow,hs])
    have second := mul_nonneg hs.le (sub_nonneg.mpr canonical)
    dsimp [α]
    nlinarith only [first,second]
  have bp : 0≤β := by dsimp [β]; positivity
  have support : upper D A.c A.s=
      α*(D.loU+D.side)+β*(D.loV+D.side) := by
    rw [upper_in_bands,ds]
    have u : A.c*D.c+A.s*(-S)=α := by dsimp [α]; ring
    have v : -A.c*(-S)+A.s*D.c=β := by dsimp [β]; ring
    rw [u,v,abs_of_nonneg ap,abs_of_nonneg bp]
    ring
  have normal : D.c^2+S^2=1 := by
    have unit := D.unit_normal
    rw [ds] at unit
    nlinarith only [unit]
  have identity :
      α*(D.loU+D.side-2*(D.c-S))+β*(D.loV+D.side-2*(D.c+S))=
        upper D A.c A.s-2*(A.c+A.s) := by
    rw [support]
    dsimp [α,β]
    linear_combination (-2*(A.c+A.s))*normal
  change α*(D.loU+D.side-2*(D.c-S))+β*(D.loV+D.side-2*(D.c+S))<(13/50)*A.s
  rw [identity]
  linarith only [selected,p.1]

#print axioms separation
#print axioms cut
end N12Compact.FullAuxWallOppositeAxes
