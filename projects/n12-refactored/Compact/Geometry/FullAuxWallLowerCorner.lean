import Compact.Geometry.FullAuxWallEscape

/-! A genuine consequence of the escaping elbow's complete face strip.
The quadratic cosine deficit is retained; dropping it creates a spurious
near-diagonal opposite-square sector. No additional wall premise is used. -/
namespace N12Compact.FullAuxWallLowerCorner
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

theorem scalar (c s e v : ℝ) (hc : 0 < c) (hs : 0 < s)
    (unit : c^2+s^2=1) (narrow : 4*s≤c)
    (offset : e<(13/50)*s) (height : v<c-1-(2/5)*s) :
    s*e+c*v<0 ∧ (c+s)*e+(c-s)*v<0 := by
  have cu : c≤1 := by nlinarith only [unit,sq_nonneg s,hc]
  have orderProduct := mul_nonneg (sub_nonneg.mpr narrow)
    (show 0≤c+4*s by linarith only [hc,hs])
  have cl : (24/25 : ℝ)≤c := by
    apply le_of_not_gt
    intro contrary
    have product := mul_nonneg (sub_nonneg.mpr contrary.le)
      (show 0≤(24/25 : ℝ)+c by linarith only [hc])
    nlinarith only [unit,orderProduct,product]
  have deficitProduct := mul_nonneg (sub_nonneg.mpr cu)
    (show 0≤c-(1/2 : ℝ) by linarith only [cl])
  have deficit : 1-c≤(2/3)*s^2 := by
    nlinarith only [deficitProduct,unit]
  have cs : 0<c*s := mul_pos hc hs
  have dyBound := add_lt_add
    (mul_lt_mul_of_pos_left offset hs)
    (mul_lt_mul_of_pos_left height hc)
  have dy : s*e+c*v<0 := by
    nlinarith only [dyBound,unit,deficit,cs,sq_nonneg s]
  have sumPositive : 0<c+s := by linarith only [hc,hs]
  have differencePositive : 0<c-s := by linarith only [narrow,hs]
  have sumBound := add_lt_add
    (mul_lt_mul_of_pos_left offset sumPositive)
    (mul_lt_mul_of_pos_left height differencePositive)
  have narrowProduct := mul_nonneg hs.le (sub_nonneg.mpr narrow)
  have cosineProduct := mul_nonneg hs.le (sub_nonneg.mpr cl)
  have sum : (c+s)*e+(c-s)*v<0 := by
    nlinarith only [sumBound,unit,deficit,narrowProduct,cosineProduct,hs]
  exact ⟨dy,sum⟩

/-- Every nonnegative normal above the diagonal has negative projection on
the lower-left displacement; all signed opposite-square V axes are covered. -/
theorem projection (c s e v C S : ℝ) (hc : 0<c) (hs : 0<s)
    (unit : c^2+s^2=1) (narrow : 4*s≤c)
    (offset : e<(13/50)*s) (height : v<c-1-(2/5)*s)
    (hC : 0<C) (hS : 0≤S) (canonical : S≤C) :
    (c*S+s*C)*e+(c*C-s*S)*v<0 := by
  have bounds := scalar c s e v hc hs unit narrow offset height
  have identity : (c*S+s*C)*e+(c*C-s*S)*v =
      S*((c+s)*e+(c-s)*v)+(C-S)*(s*e+c*v) := by ring
  rw [identity]
  by_cases positive : 0<S
  · exact add_neg_of_neg_of_nonpos
      (mul_neg_of_pos_of_neg positive bounds.2)
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr canonical) bounds.1.le)
  · have zero : S=0 := by linarith only [hS,positive]
    simpa only [zero,zero_mul,zero_add,sub_zero] using
      (mul_neg_of_pos_of_neg hC bounds.1)

/-- The actual elbow's lower support is below the strict center of every
opposite square with a negative canonical frame. This eliminates that
square's forward V separator without assuming a small opposite angle. -/
theorem opposite_v_impossible (A D : OpenSquare) (S : ℝ)
    (ha : 1<A.side) (hc : 0<A.c) (hs : 0<A.s) (narrow : 4*A.s≤A.c)
    (p : A.Inside 2 (113/50))
    (top : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (ds : D.s=-S) (dc : 0<D.c) (dS : 0≤S) (canonical : S≤D.c)
    (center : D.Inside 2 2)
    (axis : D.loV+D.side≤lower A (-D.s) D.c) : False := by
  let e := A.loU-2*(A.c+A.s)
  let v := A.loV-2*(A.c-A.s)
  have offset : e<(13/50)*A.s := by
    dsimp [e]; linarith only [p.1]
  have height : v<A.c-1-(2/5)*A.s := by
    dsimp [v]; linarith only [top,ha]
  have result := projection A.c A.s e v D.c S hc hs A.unit_normal narrow
    offset height dc dS canonical
  have k : 0≤A.c*S+A.s*D.c :=
    add_nonneg (mul_nonneg hc.le dS) (mul_nonneg hs.le dc.le)
  have alpha : 0≤A.c*D.c-A.s*S := by
    have first := mul_nonneg (show 0≤A.c-A.s by linarith only [narrow,hs]) dc.le
    have second := mul_nonneg hs.le (sub_nonneg.mpr canonical)
    nlinarith only [first,second]
  have support : lower A S D.c=
      (A.c*S+A.s*D.c)*A.loU+(A.c*D.c-A.s*S)*A.loV := by
    dsimp [lower,supportRadius,centerX,centerY]
    rw [abs_of_nonneg (show 0≤S*A.c+D.c*A.s by nlinarith only [k]),
      abs_of_nonneg (show 0≤-S*A.s+D.c*A.c by nlinarith only [alpha])]
    ring
  have identity : lower A S D.c-2*(S+D.c)=
      (A.c*S+A.s*D.c)*e+(A.c*D.c-A.s*S)*v := by
    rw [support]
    dsimp [e,v]
    calc
      _ = (A.c*S+A.s*D.c)*(A.loU-2*(A.c+A.s))+
          (A.c*D.c-A.s*S)*(A.loV-2*(A.c-A.s))+
          2*(S+D.c)*(A.c^2+A.s^2-1) := by ring
      _ = _ := by rw [A.unit_normal]; ring
  rw [ds,neg_neg] at axis
  have strict := center.2.2.2
  rw [ds,neg_neg] at strict
  nlinarith only [axis,strict,identity,result]

#print axioms scalar
#print axioms projection
#print axioms opposite_v_impossible
end N12Compact.FullAuxWallLowerCorner
