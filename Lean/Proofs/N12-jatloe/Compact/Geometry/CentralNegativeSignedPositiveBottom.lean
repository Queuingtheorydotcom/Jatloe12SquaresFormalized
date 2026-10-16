import Compact.Geometry.CentralNegativePositiveBottom
import Compact.Geometry.PositiveBottomWallNeighborAxis

/-! The negative incoming central arc is controlled by three exact
support directions: horizontal, the neighbor's own U axis, and the
negative diagonal. The two linear cones retain their shared endpoints.
No orientation sampling or extra packing premise is used. -/
namespace N12Compact.CentralNegativeSignedPositiveBottom

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem diagonal_margin {c t d r : ℝ} (bn : Normal c t) (dn : Normal d r) :
    d*((d-r)*(2*c+3*t-1)+(-r*c-d*t)*(2*c+1/2))-
      (c+t)*(d-2*d*r-(457/500)*r^2)≤0 := by
  have bb := normal_bounds bn
  have db := normal_bounds dn
  have cp : 0≤c := by linarith only [bb.1]
  have dp : 0≤d := by linarith only [db.1]
  let A := c+(3/2)*t-1-2*c*t
  let E := 1-t-c/2-2*c^2
  have first := mul_nonneg bn.1
    (show 0≤(3/2)*c-1 by linarith only [bb.1])
  have last := mul_nonneg (sub_nonneg.mpr bb.2.1)
    (show 0≤1-t/2 by linarith only [bb.2.2.2.1])
  have aBound : A≤0 := by dsimp [A]; nlinarith only [first,last]
  have endpoint := mul_nonneg (sub_nonneg.mpr bn.2.1)
    (show 0≤c+t-1/4 by linarith only [bb.2.2.2.2.1])
  have eBound : E≤-(3/4)*(c+t) := by
    dsimp [E]; nlinarith only [endpoint,bn.2.2]
  have defect := mul_nonneg (sub_nonneg.mpr db.2.1)
    (show 0≤(3/5)*d-2/5 by linarith only [db.1])
  have dBound : (2/5)*r^2≤d*(1-d) := by
    nlinarith only [defect,dn.2.2]
  have sumPos : 0≤c+t := add_nonneg cp bn.1
  have firstWeight := mul_nonneg (sq_nonneg d) (neg_nonneg.mpr aBound)
  have nextWeight := mul_nonneg sumPos (sub_nonneg.mpr dBound)
  have lastWeight := mul_nonneg (mul_nonneg dp dn.1) (sub_nonneg.mpr eBound)
  have order := mul_nonneg dn.1 (sub_nonneg.mpr dn.2.1)
  have remainder : 0≤(3/4)*d*r-(257/500)*r^2 := by
    nlinarith only [order,sq_nonneg r]
  have remainderWeight := mul_nonneg sumPos remainder
  have identity : d*((d-r)*(2*c+3*t-1)+(-r*c-d*t)*(2*c+1/2))-
      (c+t)*(d-2*d*r-(457/500)*r^2)=
      d^2*A+(d^2-d)*(c+t)+d*r*E+(457/500)*r^2*(c+t) := by
    dsimp [A,E]; ring
  nlinarith only [identity,firstWeight,nextWeight,lastWeight,remainderWeight]

/-- The final endpoint uses the full positive bottom wall and the
actual negative neighbor. The marker and bottom containment give the
required wall support, including the diagonal equality orientation. -/
theorem diagonal_impossible (D B : OpenSquare) (t : ℝ)
    (bn : Normal B.c t) (dn : Normal D.c D.s) (signed : B.s=-t)
    (side : 1<B.side) (dSide : 1≤D.side)
    (box : InsideContainer D) (marker : D.Inside 2 (457/500))
    (cap : B.loV+B.side≤2*B.c+3*t)
    (incoming : 1/2<lower B 1 (-1))
    (outgoing : D.loV+D.side≤lower B (-D.s) D.c) : False := by
  have bb := normal_bounds bn
  have db := normal_bounds dn
  have bc : 0<B.c := by linarith only [bb.1]
  have dc : 0<D.c := by linarith only [db.1]
  have wall : 0≤D.s*D.loU+D.c*D.loV := by
    have lower : ∀ x y, D.Inside x y→0≤x ∧ 0≤y := by
      intro x y h
      have contained := box x y h
      exact ⟨contained.1,contained.2.2.1⟩
    have boundary := (positive_frame_wall_bounds D dc.le dn.1 lower).2
    dsimp [centerY] at boundary
    nlinarith only [boundary]
  have markerWeight := mul_nonneg dn.1
    (show 0≤2*D.c+(457/500)*D.s-D.loU by linarith only [marker.1])
  have sideWeight := mul_nonneg dc.le (sub_nonneg.mpr dSide)
  have wallSupport : D.c-2*D.c*D.s-(457/500)*D.s^2≤
      D.c*(D.loV+D.side) := by nlinarith only [wall,markerWeight,sideWeight]
  let K := B.c+t
  let H := t-B.c
  let J := -D.s*B.c-D.c*t
  let L := D.c*B.c-D.s*t
  let Z := D.c-D.s
  let G := Z-J*(K-H)
  have kp : 0≤K := by dsimp [K]; exact add_nonneg bc.le bn.1
  have hn : H≤0 := by dsimp [H]; linarith only [bn.2.1]
  have jn : J≤0 := by
    have first := mul_nonneg dn.1 bc.le
    have last := mul_nonneg dc.le bn.1
    dsimp [J]; nlinarith only [first,last]
  have lp : 0≤L := by
    have first := mul_nonneg bc.le (sub_nonneg.mpr dn.2.1)
    have last := mul_nonneg dn.1 (sub_nonneg.mpr bn.2.1)
    dsimp [L]; nlinarith only [first,last]
  have zp : 0≤Z := by dsimp [Z]; exact sub_nonneg.mpr dn.2.1
  have gp : 0<G := by
    have order := mul_nonneg (sub_nonneg.mpr bn.2.1) (add_nonneg bc.le bn.1)
    have square : 0≤2*B.c^2-1 := by nlinarith only [order,bn.2.2]
    have first := mul_nonneg dn.1 square
    have last := mul_nonneg (mul_nonneg dc.le bc.le) bn.1
    dsimp [G,Z,J,K,H]
    nlinarith only [first,last,dc]
  have centralFormula : lower B 1 (-1)=K*B.loU+H*(B.loV+B.side) := by
    rw [lower_in_bands,signed]
    have u : 1*B.c+(-1)*(-t)=K := by dsimp [K]; ring
    have v : -1*(-t)+(-1)*B.c=H := by dsimp [H]; ring
    rw [u,v,abs_of_nonneg kp,abs_of_nonpos hn]; ring
  have wallFormula : lower B (-D.s) D.c=J*(B.loU+B.side)+L*B.loV := by
    rw [lower_in_bands,signed]
    have u : (-D.s)*B.c+D.c*(-t)=J := by dsimp [J]; ring
    have v : -(-D.s)*(-t)+D.c*B.c=L := by dsimp [L]; ring
    rw [u,v,abs_of_nonpos jn,abs_of_nonneg lp]; ring
  have centralWeight := mul_nonneg (neg_nonneg.mpr jn)
    (show 0≤lower B 1 (-1)-1/2 by linarith only [incoming])
  have wallWeight := mul_nonneg kp (sub_nonneg.mpr outgoing)
  have topWeight := mul_nonneg zp (sub_nonneg.mpr cap)
  have width := mul_pos (sub_pos.mpr side) gp
  have identity : (-J)*(K*B.loU+H*(B.loV+B.side))+
      K*(J*(B.loU+B.side)+L*B.loV)=Z*B.loV+J*(K-H)*B.side := by
    dsimp [J,K,H,L,Z]
    linear_combination (D.c-D.s)*B.loV*bn.2.2
  have pressure : 0<Z*(2*B.c+3*t-1)+J*(K-H)+J/2-K*(D.loV+D.side) := by
    dsimp [G] at width
    rw [centralFormula] at centralWeight
    rw [wallFormula] at wallWeight
    nlinarith only [centralFormula,wallFormula,centralWeight,wallWeight,topWeight,width,identity]
  have scaled := mul_pos dc pressure
  have floorWeight := mul_nonneg kp (sub_nonneg.mpr wallSupport)
  have margin := diagonal_margin bn dn
  dsimp [Z,J,K,H] at scaled floorWeight
  nlinarith only [scaled,floorWeight,margin]

/-- The negative canonical arc has just three endpoints because the
neighbor's support is linear on either side of its own normal. -/
theorem endpoint_bound (B : OpenSquare) (t : ℝ) {C S : ℝ}
    (an : Normal C S) (bn : Normal B.c t) (signed : B.s=-t)
    (horizontal : lower B 1 0≤2)
    (own : B.loU≤2*B.c-(3/2)*t)
    (diagonal : lower B 1 (-1)≤1/2) :
    lower B C (-S)≤2*C-(3/2)*S := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have cp : 0<C := by linarith only [ab.1]
  have bc : 0<B.c := by linarith only [bb.1]
  let K := C*B.c+S*t
  let H := C*t-S*B.c
  have kp : 0≤K := by
    dsimp [K]
    exact add_nonneg (mul_nonneg cp.le bc.le) (mul_nonneg an.1 bn.1)
  have horizontalFormula : lower B 1 0=B.c*B.loU+t*B.loV := by
    rw [lower_in_bands,signed]
    have u : 1*B.c+0*(-t)=B.c := by ring
    have v : -1*(-t)+0*B.c=t := by ring
    rw [u,v,abs_of_nonneg bc.le,abs_of_nonneg bn.1]
    ring
  have diagonalFormula : lower B 1 (-1)=
      (B.c+t)*B.loU+(t-B.c)*(B.loV+B.side) := by
    rw [lower_in_bands,signed]
    have u : 1*B.c+(-1)*(-t)=B.c+t := by ring
    have v : -1*(-t)+(-1)*B.c=t-B.c := by ring
    rw [u,v,abs_of_nonneg (add_nonneg bc.le bn.1),
      abs_of_nonpos (by linarith only [bn.2.1] : t-B.c≤0)]
    ring
  by_cases positive : 0≤H
  · have formula : lower B C (-S)=K*B.loU+H*B.loV := by
      rw [lower_in_bands,signed]
      have u : C*B.c+(-S)*(-t)=K := by dsimp [K]; ring
      have v : -C*(-t)+(-S)*B.c=H := by dsimp [H]; ring
      rw [u,v,abs_of_nonneg kp,abs_of_nonneg positive]; ring
    by_cases tilt : 0<t
    · have first := mul_nonneg positive (sub_nonneg.mpr horizontal)
      have last := mul_nonneg an.1 (sub_nonneg.mpr own)
      have identity : t*lower B C (-S)=H*lower B 1 0+S*B.loU := by
        rw [formula,horizontalFormula]; dsimp [K,H]
        linear_combination S*B.loU*bn.2.2
      have scaled : t*(lower B C (-S)-(2*C-(3/2)*S))≤0 := by
        dsimp [H] at first
        nlinarith only [identity,first,last]
      have gap := nonpos_of_mul_nonpos_right scaled tilt
      linarith only [gap]
    · have zero : t=0 := by linarith only [tilt,bn.1]
      have sine : S=0 := by
        dsimp [H] at positive
        rw [zero, mul_zero, zero_sub] at positive
        have nonpositive : S ≤ 0 :=
          nonpos_of_mul_nonpos_left (by linarith only [positive] : S * B.c ≤ 0) bc
        exact le_antisymm nonpositive an.1
      have weight := mul_nonneg cp.le (sub_nonneg.mpr horizontal)
      have identity : lower B C (-S)=C*lower B 1 0 := by
        rw [formula,horizontalFormula]
        dsimp [K,H]
        rw [zero,sine]
        ring
      rw [identity,sine]
      nlinarith only [weight]
  · have negative : H<0 := lt_of_not_ge positive
    have hn : H≤0 := negative.le
    have formula : lower B C (-S)=K*B.loU+H*(B.loV+B.side) := by
      rw [lower_in_bands,signed]
      have u : C*B.c+(-S)*(-t)=K := by dsimp [K]; ring
      have v : -C*(-t)+(-S)*B.c=H := by dsimp [H]; ring
      rw [u,v,abs_of_nonneg kp,abs_of_nonpos hn]; ring
    have gap : 0<B.c-t := by
      have weight := mul_nonneg bc.le (sub_nonneg.mpr an.2.1)
      dsimp [H] at negative
      nlinarith only [negative,weight,bn.2.1,cp]
    have first := mul_nonneg (sub_nonneg.mpr an.2.1) (sub_nonneg.mpr own)
    have last := mul_nonneg (neg_nonneg.mpr hn) (sub_nonneg.mpr diagonal)
    have identity : (B.c-t)*lower B C (-S)=
        (C-S)*B.loU-H*lower B 1 (-1) := by
      rw [formula,diagonalFormula]
      dsimp [K,H]
      linear_combination (C-S)*B.loU*bn.2.2
    have scaled : (B.c-t)*(lower B C (-S)-(2*C-(3/2)*S))≤0 := by
      dsimp [H] at last
      nlinarith only [identity,first,last]
    have result := nonpos_of_mul_nonpos_right scaled gap
    linarith only [result]

/-- Both signs of the incoming central square now use the same actual
wall contradiction; this theorem supplies the negative sign. -/
theorem impossible (D B : OpenSquare) (t : ℝ) {C S : ℝ}
    (an : Normal C S) (bn : Normal B.c t) (dn : Normal D.c D.s)
    (signed : B.s=-t) (same : D.side=B.side) (side : 1<D.side)
    (box : InsideContainer D) (marker : D.Inside 2 (457/500))
    (cap : B.loV+B.side≤2*B.c+3*t)
    (incoming : 2*C-(3/2)*S<lower B C (-S))
    (outgoing : D.loV+D.side≤lower B (-D.s) D.c) : False := by
  have bSide : 1<B.side := by simpa only [same] using side
  have horizontal : lower B 1 0≤2 := by
    apply le_of_not_gt
    intro high
    exact CentralNegativePositiveBottom.impossible D B t (C := 1) (S := 0)
      (by norm_num [Normal]) bn dn signed bSide side.le box marker cap
      (by simpa only [add_zero,mul_one] using high) outgoing
  have own : B.loU≤2*B.c-(3/2)*t := by
    apply le_of_not_gt
    intro high
    exact PositiveBottomWallNeighborAxis.of_entry D B t dn bn signed same side
      box marker cap high.le outgoing
  have diagonal : lower B 1 (-1)≤1/2 := by
    apply le_of_not_gt
    intro high
    exact diagonal_impossible D B t bn dn signed bSide side.le box marker cap high outgoing
  have result := endpoint_bound B t an bn signed horizontal own diagonal
  linarith only [result,incoming]

#print axioms impossible
end N12Compact.CentralNegativeSignedPositiveBottom
