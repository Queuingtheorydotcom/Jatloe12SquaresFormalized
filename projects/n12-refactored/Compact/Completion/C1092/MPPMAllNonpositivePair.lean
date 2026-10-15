import Compact.Completion.C1092.MPPMAllNonpositiveProfiles
import Compact.Completion.C1092.MPPMAllNonpositiveTripleScalars
import Compact.Completion.C1092.MPPMOrdinaryNegativeHalfpointFaces

/-! ALL-NEGATIVE-MIXED-FORWARD-ENDING section 3. Both longitudinal
normals, in both relative angle orders, are rejected for the same two
physical squares. The recipient's strict rightmost-vertex clearance is
the separately proved consequence of its own actual foreign whole bar. -/
namespace N12Compact.C1092MPPMAllNonpositive
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C977CornerSectorBounds C1092WholeSupports
set_option Elab.async false
noncomputable section

theorem pair_impossible (C E : OpenSquare) (h : Core C)
    (close : 873/1000<C.c) (e : ClearedSuccessor E)
    (same : C.side=E.side) (marker : E.Inside (7/20) (-7/20))
    (ordinary : E.Inside (13/50) (-1))
    (apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)) : False := by
  have f := faces C h
  let c := C.c
  let s := -C.s
  let d := E.c
  let t := -E.s
  let a := C.side
  let A := C.loU+C.side
  let V := C.loV
  let H := C.loV+C.side
  let L := E.loU
  let K := E.loV
  let J := E.loU+E.side
  let D := E.loV+E.side
  let k := c*d+s*t
  let z := c*t-s*d
  have cn : Normal c s := h.normal
  have en : Normal d t := e.normal
  have cp : 0<c := by linarith only [(normal_bounds cn).1]
  have dp : 0<d := by linarith only [(normal_bounds en).1]
  have sp : 0<s := neg_pos.mpr f.negative
  have tp : 0<t := neg_pos.mpr e.negative
  have kp : 0<k := by
    have first := mul_pos cp dp
    have last := mul_pos sp tp
    dsimp only [k]
    linarith only [first,last]
  have side : 1<a := h.side
  have AD : a-c≤A := by dsimp only [a,c,A]; linarith only [f.lowerU]
  have DD : a-d≤D := by dsimp only [a,d,D]; rw [same]; linarith only [e.lowerV]
  have Hhigh : H≤(7/20)*(c-s) := f.upperV
  have Hlow : -(13/50)*s≤H := by
    dsimp only [s,H]
    linarith only [h.forward.2.2.2]
  have VH : V=H-a := by dsimp only [V,H,a]; ring
  have LJ : L=J-a := by dsimp only [L,J,a]; rw [same]; ring
  have KD : K=D-a := by dsimp only [K,D,a]; rw [same]; ring
  have vertex : d*J+t*D<1 := e.vertex
  have mixed : d*z-k*t= -s := by
    dsimp only [k,z]
    linear_combination -s*en.2.2
  have recipientCap : d*L<1+t*d-a*(d+t) := by
    have weighted := mul_le_mul_of_nonneg_left DD tp.le
    nlinarith only [vertex,weighted,LJ]
  have Gidentity : d*TripleScalars.G d t=(1-d)*(1-t) := by
    dsimp only [TripleScalars.G]
    field_simp [dp.ne']
  have cu : C.c*E.c+C.s*E.s=k := by dsimp only [c,s,d,t,k]; ring
  have cv : -C.c*E.s+C.s*E.c=z := by dsimp only [c,s,d,t,z]; ring
  have eu : E.c*C.c+E.s*C.s=k := by dsimp only [c,s,d,t,k]; ring
  have ev : -E.c*C.s+E.s*C.c= -z := by dsimp only [c,s,d,t,z]; ring
  have cf : C1092MPPMOrdinaryNegativeHalfpoint.Frame C.c (-C.s) :=
    ⟨cp,cn.1,cn.2.1,cn.2.2⟩
  have ef : C1092MPPMOrdinaryNegativeHalfpoint.Frame E.c (-E.s) :=
    ⟨dp,en.1,en.2.1,en.2.2⟩
  rcases C1092MPPMOrdinaryNegativeHalfpoint.axes C E same cf ef
      h.marker marker ordinary apart with current|recipient
  · change A≤lower E C.c C.s at current
    have sourceFloor := mul_le_mul_of_nonneg_left AD dp.le
    have weightedVertex := mul_lt_mul_of_pos_left vertex kp
    have weightedD := mul_le_mul_of_nonneg_left DD sp.le
    rcases le_total z 0 with before|after
    · have formula : lower E C.c C.s=k*L+z*D :=
        lower_pn E C.c C.s k z cu cv kp.le before
      have identity : d*(k*L+z*D)=k*(d*J+t*D)-s*D-a*d*k := by
        rw [LJ]
        linear_combination D*mixed
      have margin := TripleScalars.source_before cn en sp tp before
      change 0<d*(1-c)+(1-d)*(s-k) at margin
      have excess := mul_pos (sub_pos.mpr side)
        (show 0<d+s+d*k by nlinarith only [dp,sp,mul_pos dp kp])
      rw [formula] at current
      have scaled := mul_le_mul_of_nonneg_left current dp.le
      nlinarith only [scaled,sourceFloor,weightedVertex,weightedD,identity,margin,excess]
    · have formula : lower E C.c C.s=k*L+z*K :=
        lower_nn E C.c C.s k z cu cv kp.le after
      have identity : d*(k*L+z*K)=k*(d*J+t*D)-s*D-a*d*(k+z) := by
        rw [LJ,KD]
        linear_combination D*mixed
      have margin := TripleScalars.source_after cn en sp tp after
      change 0<d*(1-c)+(1-d)*(s-k)+d*z at margin
      have excess := mul_pos (sub_pos.mpr side)
        (show 0<d+s+d*(k+z) by nlinarith only [dp,sp,mul_pos dp kp,mul_nonneg dp.le after])
      rw [formula] at current
      have scaled := mul_le_mul_of_nonneg_left current dp.le
      nlinarith only [scaled,sourceFloor,weightedVertex,weightedD,identity,margin,excess]
  · change upper C E.c E.s≤L at recipient
    have first := mul_le_mul_of_nonneg_left AD kp.le
    rcases le_total z 0 with before|after
    · have formula : upper C E.c E.s=k*A-z*H := by
        rw [(formulas C E.c E.s).2,eu,ev,max_eq_left kp.le,
          max_eq_left (neg_nonneg.mpr before)]
        dsimp only [A,H]
        ring
      have last := mul_le_mul_of_nonneg_left Hlow (neg_nonneg.mpr before)
      have floor : k*(a-c)+(13/50)*z*s≤upper C E.c E.s := by
        rw [formula]
        nlinarith only [first,last]
      have scaled := mul_le_mul_of_nonneg_left (floor.trans recipient) dp.le
      have margin := TripleScalars.target_before cn en sp tp close e.close before
      change 0<k*(1-c)+(13/50)*z*s-TripleScalars.G d t at margin
      have positive := mul_pos dp margin
      have excess := mul_pos (sub_pos.mpr side)
        (show 0<d*(1+k)+t by nlinarith only [dp,tp,mul_pos dp kp])
      nlinarith only [scaled,recipientCap,positive,Gidentity,excess]
    · have formula : upper C E.c E.s=k*A-z*V := by
        rw [(formulas C E.c E.s).2,eu,ev,max_eq_left kp.le,
          max_eq_right (neg_nonpos.mpr after)]
        dsimp only [A,V]
        ring
      have last := mul_le_mul_of_nonneg_left Hhigh after
      have floor : k*(a-c)+z*(a-(7/20)*(c-s))≤upper C E.c E.s := by
        rw [formula,VH]
        nlinarith only [first,last]
      have scaled := mul_le_mul_of_nonneg_left (floor.trans recipient) dp.le
      have margin := TripleScalars.target_after cn en sp close after
      change 0<k*(1-c)+z*(1-(7/20)*(c-s))-TripleScalars.G d t at margin
      have positive := mul_pos dp margin
      have excess := mul_pos (sub_pos.mpr side)
        (show 0<d*(1+k+z)+t by
          nlinarith only [dp,tp,mul_pos dp kp,mul_nonneg dp.le after])
      nlinarith only [scaled,recipientCap,positive,Gidentity,excess]

end
#print axioms pair_impossible
end N12Compact.C1092MPPMAllNonpositive
