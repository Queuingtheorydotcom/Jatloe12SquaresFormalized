import Compact.Geometry.PositiveBottomWallCentralAxis

/-! The positive bottom wall's own transverse separator is incompatible
with a central-neighbor-owned incoming axis. The actual lower central
crosspoint is retained, so the central square may have either sign. -/
namespace N12Compact.PositiveBottomWallNeighborAxis

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem margin {c t d r : ℝ} (bn : Normal c t) (dn : Normal d r) :
    d*((-r*c-d*t)*(2*c-(3/2)*t+1)+(d*c-r*t)*(2*c+3*t-1))-
      d+2*d*r+(457/500)*r^2≤0 := by
  have bb := normal_bounds bn
  have db := normal_bounds dn
  have dc := sub_nonneg.mpr bb.2.1
  have dd := sub_nonneg.mpr db.2.1
  have arc : 0≤c+2*t-1 := by linarith only [bb.2.2.2.2.1,bn.1]
  have endpoint := mul_nonneg dc arc
  let A := 2-t^2/2+c*t-c-t
  have aBound : A≤1 := by
    dsimp [A]
    nlinarith only [endpoint,bn.2.2]
  have defect := mul_nonneg dc
    (show 0≤(3/5)*c-2/5 by linarith only [bb.1])
  have delta : 1-c≤(3/5)*t^2 := by nlinarith only [defect,bn.2.2]
  have small : t≤5/7 := by linarith only [bn.2.1,bb.2.2.2.2.2]
  have cosineWeight := mul_nonneg bn.1
    (show 0≤c-7/10 by linarith only [bb.1])
  let E := t^2+c*t/2+c-t
  have eBound : 53/100≤E := by
    dsimp [E]
    nlinarith only [delta,small,cosineWeight,sq_nonneg t]
  have dDefect := mul_nonneg dd
    (show 0≤(3/5)*d-2/5 by linarith only [db.1])
  have dBound : (2/5)*r^2≤d*(1-d) := by
    nlinarith only [dDefect,dn.2.2]
  have dr : 0≤d*r := mul_nonneg (by linarith only [db.1]) dn.1
  have first := mul_nonneg (sq_nonneg d) (sub_nonneg.mpr aBound)
  have second := mul_nonneg dr (sub_nonneg.mpr eBound)
  have order := mul_nonneg dn.1 (sub_nonneg.mpr dn.2.1)
  have identity :
      d*((-r*c-d*t)*(2*c-(3/2)*t+1)+(d*c-r*t)*(2*c+3*t-1))-
        d+2*d*r+(457/500)*r^2=
      d^2*A-d-d*r*E+(457/500)*r^2 := by
    dsimp [A,E]
    linear_combination (2*d^2-2*d*r)*bn.2.2
  nlinarith only [identity,first,second,dBound,order,dr]

/-- The scalar endpoint needs only the genuine lower-U entrance. This
form also applies when another incoming axis forces that entrance. -/
theorem of_entry (D B : OpenSquare) (t : ℝ)
    (dn : Normal D.c D.s) (bn : Normal B.c t) (bs : B.s=-t)
    (same : D.side=B.side) (side : 1<D.side)
    (box : InsideContainer D) (marker : D.Inside 2 (457/500))
    (cap : B.loV+B.side≤2*B.c+3*t)
    (entry : 2*B.c-(3/2)*t≤B.loU)
    (outgoing : D.loV+D.side≤lower B (-D.s) D.c) : False := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0<D.c := by linarith only [db.1]
  have bc : 0≤B.c := by linarith only [bb.1]
  have wall : 0≤D.s*D.loU+D.c*D.loV := by
    have lower : ∀ x y, D.Inside x y→0≤x ∧ 0≤y := by
      intro x y h
      have contained := box x y h
      exact ⟨contained.1,contained.2.2.1⟩
    have boundary := (positive_frame_wall_bounds D dp.le dn.1 lower).2
    dsimp [centerY] at boundary
    nlinarith only [boundary]
  let J := -D.s*B.c-D.c*t
  let L := D.c*B.c-D.s*t
  have jn : J≤0 := by
    have first := mul_nonneg dn.1 bc
    have last := mul_nonneg dp.le bn.1
    dsimp [J]; nlinarith only [first,last]
  have lp : 0≤L := by
    have first := mul_nonneg dp.le (sub_nonneg.mpr bn.2.1)
    have last := mul_nonneg bn.1 (sub_nonneg.mpr dn.2.1)
    dsimp [L]; nlinarith only [first,last]
  have formula : lower B (-D.s) D.c=J*(B.loU+B.side)+L*B.loV := by
    rw [lower_in_bands,bs]
    have u : (-D.s)*B.c+D.c*(-t)=J := by dsimp [J]; ring
    have v : -(-D.s)*(-t)+D.c*B.c=L := by dsimp [L]; ring
    rw [u,v,abs_of_nonpos jn,abs_of_nonneg lp]; ring
  have upperWeight := mul_nonneg (neg_nonneg.mpr jn) (sub_nonneg.mpr entry)
  have lowerWeight := mul_nonneg lp (sub_nonneg.mpr cap)
  have first := mul_nonneg dp.le upperWeight
  have last := mul_nonneg dp.le lowerWeight
  have markerWeight := mul_nonneg dn.1
    (show 0≤2*D.c+(457/500)*D.s-D.loU by linarith only [marker.1])
  have width := mul_pos (sub_pos.mpr side)
    (mul_pos dp (show 0<1+L-J by linarith only [lp,jn]))
  have scalar := margin bn dn
  have identity : D.c*(lower B (-D.s) D.c-(D.loV+D.side))=
      (D.c*(J*(2*B.c-(3/2)*t+1)+L*(2*B.c+3*t-1))-
        D.c+2*D.c*D.s+(457/500)*D.s^2)-
      D.c*((-J)*(B.loU-(2*B.c-(3/2)*t)))-
      D.c*(L*(2*B.c+3*t-(B.loV+B.side)))-
      (D.s*D.loU+D.c*D.loV)-
      D.s*(2*D.c+(457/500)*D.s-D.loU)-
      (D.side-1)*D.c*(1+L-J) := by
    rw [formula,←same]
    ring
  have order := mul_nonneg dp.le (sub_nonneg.mpr outgoing)
  dsimp [J,L] at identity first last width ⊢
  nlinarith only [identity,first,last,wall,markerWeight,width,scalar,order]

/-- This whole separator is independent of A's orientation. Its strict
incoming support comes from the original point A(2,1.5). -/
theorem impossible (A D B : OpenSquare) (t : ℝ)
    (dn : Normal D.c D.s) (bn : Normal B.c t) (bs : B.s=-t)
    (same : D.side=B.side) (side : 1<D.side)
    (box : InsideContainer D) (marker : D.Inside 2 (457/500))
    (low : A.Inside 2 (3/2))
    (cap : B.loV+B.side≤2*B.c+3*t)
    (incoming : upper A B.c B.s≤B.loU)
    (outgoing : D.loV+D.side≤lower B (-D.s) D.c) : False := by
  have strict := strict_bounds A _ _ B.c (-t)
    (by nlinarith only [bn.2.2]) low
  rw [bs] at incoming
  have entry : 2*B.c-(3/2)*t≤B.loU := by linarith only [strict.2,incoming]
  exact of_entry D B t dn bn bs same side box marker cap entry outgoing

#print axioms of_entry
#print axioms impossible
end N12Compact.PositiveBottomWallNeighborAxis
