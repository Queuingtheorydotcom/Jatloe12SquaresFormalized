import Compact.Completion.C1092.MPPMInwardPositiveNegativeScalars
import Compact.Completion.C1092.MPPMActualNonordinaryElbow

/-! Three common support exclusions for the positive missing-center
inward endings. The fourth, the actual successor longitudinal normal,
is supplied by its origin or actual-segment argument. Every coordinate
and strict anchor remains on the same C and E. -/
namespace N12Compact.C1092MPPMInwardPositive
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports
set_option Elab.async false
noncomputable section

theorem negative_faces (C E : OpenSquare) (h : PairInput C E) (en : Normal E.c (-E.s)) :
    C1092MPPMActualNonordinary.SuccessorFaces E := by
  have p := profile C h.source
  exact C1092MPPMActualNonordinary.successor_faces E h.recipient.side en
    h.recipient.successorMarker h.recipient.near h.recipient.outer
    h.recipient.missingRight h.recipient.missingCorner h.recipient.missingBottom
    (fun own => h.apart 0 (-1/2) ⟨p.halfpoint,own⟩)

/-- A strict scalar reserve and one simultaneous upper H face reject
the actual E longitudinal separator. This is a reusable local step. -/
theorem target_support_of_cap (C E : OpenSquare) (h : PairInput C E)
    (en : Normal E.c (-E.s)) (H : ℝ) (cap : C.loV+C.side≤H)
    (scalar : 0<1-E.c+E.s+
      NegativeScalars.k C.c C.s E.c (-E.s)*(1-C.c-(2/5)*C.s)+
      NegativeScalars.ell C.c C.s E.c (-E.s)*(1-H)) :
    E.loU<upper C E.c E.s := by
  have p := profile C h.source
  have e := negative_faces C E h en
  let k := NegativeScalars.k C.c C.s E.c (-E.s)
  let l := NegativeScalars.ell C.c C.s E.c (-E.s)
  have rel := NegativeScalars.relative h.source.normal p.strictOrder p.positive en
  have formula := C1092TwoFifths.Support.upper_pos_neg C E.c E.s k (-l)
    (by dsimp [k,NegativeScalars.k]; ring)
    (by dsimp [l,NegativeScalars.ell]; ring) rel.1.le (neg_nonpos.mpr rel.2.1.le)
  have first := mul_le_mul_of_nonneg_left p.lowerU rel.1.le
  have last := mul_le_mul_of_nonneg_left cap rel.2.1.le
  have strict := mul_pos (sub_pos.mpr h.source.side)
    (show 0<1+k+l by dsimp [k,l]; linarith only [rel.1,rel.2.1])
  dsimp [k,l] at formula first last strict
  nlinarith only [formula,first,last,strict,scalar,e.upperU,h.same]

/-- The only remaining geometric input is the strict support on E's
own longitudinal normal. Both later endings produce it explicitly. -/
theorem impossible_of_target (C E : OpenSquare) (h : PairInput C E)
    (en : Normal E.c (-E.s)) (target : E.loU<upper C E.c E.s) : False := by
  have p := profile C h.source
  have e := negative_faces C E h en
  have cp : 0<C.c := by linarith only [(normal_bounds h.source.normal).1]
  have dp : 0<E.c := by linarith only [(normal_bounds en).1]
  let k := NegativeScalars.k C.c C.s E.c (-E.s)
  let l := NegativeScalars.ell C.c C.s E.c (-E.s)
  have rel := NegativeScalars.relative h.source.normal p.strictOrder p.positive en
  have kp : 0<k := rel.1
  have lp : 0<l := rel.2.1
  have capU : E.loU≤E.c-E.s-C.side := by linarith only [e.upperU,h.same]
  have capV : E.loV≤-E.s-(2/5)*E.c-C.side := by linarith only [e.upperV,h.same]
  have lowerA : C.side-C.c-(2/5)*C.s≤C.loU+C.side := by linarith only [p.lowerU]
  have lowerH : C.side+(2/5)*C.s-C.c≤C.loV+C.side := by linarith only [p.lowerV]
  have strict := mul_pos (sub_pos.mpr h.source.side)
    (show 0<1+k+l by linarith only [kp,lp])
  rcases C1092MPPMActualNonordinary.successor_axes C E h.same cp p.positive dp
      (by linarith only [en.1]) h.source.marker h.recipient.successorMarker h.apart
      with current|downward|own|transverse
  · have formula := lower_nn E C.c C.s k l
      (by dsimp [k,NegativeScalars.k]; ring) (by dsimp [l,NegativeScalars.ell]; ring) kp.le lp.le
    have first := mul_le_mul_of_nonneg_left capU kp.le
    have last := mul_le_mul_of_nonneg_left capV lp.le
    have margin := C1092MPPMActualNonordinary.source_longitudinal
      C.c C.s E.c (-E.s) h.source.normal en cp p.positive
    dsimp [k,l,NegativeScalars.k,NegativeScalars.ell] at formula first last strict
    nlinarith only [current,formula,first,last,strict,margin,lowerA]
  · have formula := lower_pn E C.s (-C.c) l (-k)
      (by dsimp [l,NegativeScalars.ell]; ring) (by dsimp [k,NegativeScalars.k]; ring)
      lp.le (neg_nonpos.mpr kp.le)
    have first := mul_le_mul_of_nonneg_left capU lp.le
    have last := mul_le_mul_of_nonneg_left e.lowerV kp.le
    have margin := NegativeScalars.downward h.source.normal en kp.le rel.2.2.1 rel.2.2.2
    have own : upper C C.s (-C.c)= -C.loV := by
      have neg := C1092TwoFifths.Support.upper_neg C (-C.s) C.c
      simpa only [neg_neg,(ownV C).1] using neg
    rw [own,formula] at downward
    rw [←h.same] at downward
    dsimp [k,l] at first last strict
    nlinarith only [downward,first,last,strict,margin,p.upperV]
  · linarith only [own,target]
  · have formula := C1092TwoFifths.Support.upper_pos_pos C (-E.s) E.c l k
      (by dsimp [l,NegativeScalars.ell]; ring) (by dsimp [k,NegativeScalars.k]; ring) lp.le kp.le
    have first := mul_le_mul_of_nonneg_left lowerA lp.le
    have last := mul_le_mul_of_nonneg_left lowerH kp.le
    have margin := NegativeScalars.transverse h.source.normal en kp.le lp.le rel.2.2.2
    dsimp [k,l] at formula first last strict
    nlinarith only [transverse,formula,first,last,strict,margin,capV]

end
#print axioms negative_faces
#print axioms target_support_of_cap
#print axioms impossible_of_target
end N12Compact.C1092MPPMInwardPositive
