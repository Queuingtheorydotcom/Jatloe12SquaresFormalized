import Compact.Completion.C1092.MPPMAllNonpositiveShallow
import Compact.Completion.C1092.MPPMOnePositiveScalars
import Compact.Completion.C1092.MPPMOrdinaryNegativeHalfpointFaces

/-! ALL-NEGATIVE-MIXED-FORWARD-ENDING section 6. The single retaining
C is kept between its two actual missing neighbors. The whole foreign
bar is passed to the predecessor-angle theorem; no wall replaces it. -/
namespace N12Compact.C1092MPPMAllNonpositive
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C977CornerSectorBounds C1092WholeSupports
set_option Elab.async false
noncomputable section

theorem alternating_impossible (C W E B : OpenSquare) (h : Core C)
    (w : MissingPredecessor W) (e : MissingSuccessor E)
    (sameW : C.side=W.side) (sameE : C.side=E.side)
    (markerW : W.Inside (-7/20) (7/20))
    (markerE : E.Inside (7/20) (-7/20)) (ordinaryE : E.Inside (13/50) (-1))
    (apartW : ∀ x y,¬(C.Inside x y ∧ W.Inside x y))
    (apartE : ∀ x y,¬(C.Inside x y ∧ E.Inside x y))
    (bar : ∀ x : ℝ,-14/25≤x → x≤0 → B.Inside x (-1))
    (apartBar : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)) : False := by
  have shallow := predecessor_shallow C W B h w sameW markerW apartW bar apartBar
  have f := faces C h
  let c := C.c
  let s := -C.s
  let d := E.c
  let t := -E.s
  let k := c*d+s*t
  let z := c*t-s*d
  have cn : Normal c s := h.normal
  have en : Normal d t := e.normal
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cp : 0<c := by linarith only [cb.1]
  have dp : 0<d := by linarith only [eb.1]
  have bounds := missing_bounds en e.large
  have kp : 0<k := by
    have first := mul_pos cp dp
    have last := mul_nonneg cn.1 en.1
    dsimp only [k]
    nlinarith only [first,last]
  have large : 19/40<z := by
    have first := mul_nonneg cp.le (show 0≤t-27/40 by linarith only [bounds.sineLow])
    have last := mul_nonneg dp.le (show 0≤c/4-s by linarith only [shallow.slope])
    have cosine := mul_nonneg cp.le (show 0≤369/500-d by linarith only [bounds.cosine])
    dsimp only [z]
    nlinarith only [first,last,cosine,shallow.close]
  have zp : 0<z := by linarith only [large]
  have cf : C1092MPPMOrdinaryNegativeHalfpoint.Frame C.c (-C.s) :=
    ⟨cp,cn.1,cn.2.1,cn.2.2⟩
  have ef : C1092MPPMOrdinaryNegativeHalfpoint.Frame E.c (-E.s) :=
    ⟨dp,en.1,en.2.1,en.2.2⟩
  have cu : C.c*E.c+C.s*E.s=k := by dsimp only [c,s,d,t,k]; ring
  have cv : -C.c*E.s+C.s*E.c=z := by dsimp only [c,s,d,t,z]; ring
  have eu : E.c*C.c+E.s*C.s=k := by dsimp only [c,s,d,t,k]; ring
  have ev : -E.c*C.s+E.s*C.c= -z := by dsimp only [c,s,d,t,z]; ring
  have upperA : C.side-c≤C.loU+C.side := by
    dsimp only [c]
    linarith only [f.lowerU]
  have lowerL : E.loU≤d+t-C.side := by
    rw [sameE]
    dsimp only [d,t]
    linarith only [e.upperU]
  have lowerK : E.loV≤t-(14/25)*d-C.side := by
    rw [sameE]
    dsimp only [d,t]
    linarith only [e.upperV]
  have excess := mul_pos (sub_pos.mpr h.side)
    (show 0<1+k+z by linarith only [kp,zp])
  rcases C1092MPPMOrdinaryNegativeHalfpoint.axes C E sameE cf ef
      h.marker markerE ordinaryE apartE with current|recipient
  · have formula := lower_nn E C.c C.s k z cu cv kp.le zp.le
    have first := mul_le_mul_of_nonneg_left lowerL kp.le
    have last := mul_le_mul_of_nonneg_left lowerK zp.le
    have margin := C1092MPPMOnePositive.missing_negative_longitudinal c s d t cn
      shallow.slope.le en e.large
    have identity : 1-c+k*(1-d-t)+z*(1-t+(14/25)*d)=
        1-(2-d-t+(11/25)*d*t)*c-(1+d-t-(11/25)*d^2)*s := by
      dsimp only [k,z]
      linear_combination -(c+s)*en.2.2
    rw [formula] at current
    nlinarith only [current,upperA,first,last,margin,identity,excess]
  · have formula : upper C E.c E.s=k*(C.loU+C.side)-z*C.loV := by
      rw [(formulas C E.c E.s).2,eu,ev,max_eq_left kp.le,max_eq_right (neg_nonpos.mpr zp.le)]
      ring
    have first := mul_le_mul_of_nonneg_left upperA kp.le
    have last := mul_lt_mul_of_pos_left shallow.height zp
    have positive := mul_nonneg kp.le (show 0≤1-c by linarith only [cb.2.1])
    rw [formula] at recipient
    nlinarith only [recipient,first,last,lowerL,excess,positive,large,eb.2.2.2.2.2]

end
#print axioms alternating_impossible
end N12Compact.C1092MPPMAllNonpositive
