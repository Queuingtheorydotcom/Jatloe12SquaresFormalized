import Compact.Completion.C1092.MPPMMissingBoundaryShallowGeometry

/-! Full local Theorem 1 of MISSING-BOUNDARY-SHALLOW-ANGLE. The three
surviving supports use the simultaneous faces of the two actual squares.
The scalar arguments cover their entire canonical ranges. This is source
translation, without compiler acceptance or a global branch claim. -/
namespace N12Compact.C1092MPPMMissingBoundaryShallow
open S12 S12Pilot C977CornerCubic FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false
noncomputable section

private theorem lower_on_negative_u (C B : OpenSquare) (h : Input C B) :
    lower C (-B.c) (-B.s)=
      -crossCos C.c C.s B.c (-B.s)*(C.loU+C.side)+
        crossSin C.c C.s B.c (-B.s)*C.loV := by
  have signs := cross_bounds h.centralNormal h.boundaryNormal
    h.centralPositive h.boundaryNegative
  rw [C981CompletionSupportForms.lower_in_bands,
    show (-B.c)*C.c+(-B.s)*C.s= -crossCos C.c C.s B.c (-B.s) by
      dsimp only [crossCos]; ring,
    show -(-B.c)*C.s+(-B.s)*C.c=crossSin C.c C.s B.c (-B.s) by
      dsimp only [crossSin]; ring,
    abs_of_nonpos (neg_nonpos.mpr signs.1),abs_of_nonneg signs.2.1.le]
  ring

private theorem upper_on_central_v (C B : OpenSquare) (h : Input C B) :
    upper B (-C.s) C.c=
      -crossSin C.c C.s B.c (-B.s)*B.loU+
        crossCos C.c C.s B.c (-B.s)*(B.loV+B.side) := by
  have signs := cross_bounds h.centralNormal h.boundaryNormal
    h.centralPositive h.boundaryNegative
  rw [C981CompletionSupportForms.upper_in_bands,
    show (-C.s)*B.c+C.c*B.s= -crossSin C.c C.s B.c (-B.s) by
      dsimp only [crossSin]; ring,
    show -(-C.s)*B.s+C.c*B.c=crossCos C.c C.s B.c (-B.s) by
      dsimp only [crossCos]; ring,
    abs_of_nonpos (neg_nonpos.mpr signs.2.1.le),abs_of_nonneg signs.1]
  ring

private theorem lower_on_boundary_v (C B : OpenSquare) (h : Input C B) :
    lower C (-B.s) B.c=
      crossSin C.c C.s B.c (-B.s)*C.loU+
        crossCos C.c C.s B.c (-B.s)*C.loV := by
  have signs := cross_bounds h.centralNormal h.boundaryNormal
    h.centralPositive h.boundaryNegative
  rw [C981CompletionSupportForms.lower_in_bands,
    show (-B.s)*C.c+B.c*C.s=crossSin C.c C.s B.c (-B.s) by
      dsimp only [crossSin]; ring,
    show -(-B.s)*C.s+B.c*C.c=crossCos C.c C.s B.c (-B.s) by
      dsimp only [crossCos]; ring,
    abs_of_nonneg signs.2.1.le,abs_of_nonneg signs.1]
  ring

/-- Section 4: the actual B northwest face cannot separate. -/
theorem no_negative_u (C B : OpenSquare) (h : Input C B)
    (sep : upper B (-B.c) (-B.s)≤lower C (-B.c) (-B.s)) : False := by
  let k := crossCos C.c C.s B.c (-B.s)
  let ell := crossSin C.c C.s B.c (-B.s)
  have signs := cross_bounds h.centralNormal h.boundaryNormal
    h.centralPositive h.boundaryNegative
  have kn : 0≤k := signs.1
  have ep : 0<ell := signs.2.1
  have rp := h.boundaryNegative
  have bb := strict_bounds h.boundaryNormal rp
  have bp : 0<B.c := by linarith only [bb.1]
  have side : 1<B.side := by rw [←h.same]; exact h.side
  have faces := boundary_faces C B h
  have cap := h.upperV
  rw [h.same] at cap
  rw [Completion.OtherCases.WallProfile.upper_neg,(ownU B).1,
    lower_on_negative_u C B h,h.same] at sep
  change -B.loU≤-k*(C.loU+B.side)+ell*C.loV at sep
  have dWeight := mul_nonneg bp.le (sub_nonneg.mpr faces.upperV)
  have jBound : (-B.s)*(B.loU+B.side)≤2-B.side*B.c-B.c^2 := by
    nlinarith only [faces.wall,dWeight]
  have first := mul_nonneg (mul_nonneg rp.le kn) (sub_nonneg.mpr h.lowerU)
  have last := mul_nonneg (mul_nonneg rp.le ep.le) (sub_nonneg.mpr cap)
  have identity :
      (-B.s)*(-B.loU+k*(C.loU+B.side)-ell*C.loV)-
        (B.side*(B.c-B.s+(-B.s)*(k+ell))-2+B.c^2-
          (-B.s)*k*(C.c+C.s/2)-(-B.s)*ell*C.s)=
      (2-B.side*B.c-B.c^2-(-B.s)*(B.loU+B.side))+
        (-B.s)*k*(C.loU+C.c+C.s/2)+
        (-B.s)*ell*(C.s-B.side-C.loV) := by ring
  have coefficient : 0<B.c-B.s+(-B.s)*(k+ell) := by
    have sum : 0≤k+ell := by linarith only [kn,ep]
    have term := mul_nonneg rp.le sum
    linarith only [bp,rp,term]
  have strict := mul_pos (sub_pos.mpr side) coefficient
  have scalar := northwest_margin h.centralNormal h.boundaryNormal
    h.centralPositive rp
  change 0<B.c+(-B.s)-2+B.c^2+
    (-B.s)*(k*(1-C.c-C.s/2)+ell*(1-C.s)) at scalar
  have separating := mul_nonneg rp.le (sub_nonneg.mpr sep)
  nlinarith only [identity,jBound,first,last,strict,scalar,separating]

/-- Section 5: the actual central northwest face cannot separate. -/
theorem no_central_v (C B : OpenSquare) (h : Input C B)
    (sep : upper B (-C.s) C.c≤lower C (-C.s) C.c) : False := by
  let k := crossCos C.c C.s B.c (-B.s)
  let ell := crossSin C.c C.s B.c (-B.s)
  have signs := cross_bounds h.centralNormal h.boundaryNormal
    h.centralPositive h.boundaryNegative
  have ep : 0<ell := signs.2.1
  have rp := h.boundaryNegative
  have bb := strict_bounds h.boundaryNormal rp
  have bp : 0<B.c := by linarith only [bb.1]
  have side : 1<B.side := by rw [←h.same]; exact h.side
  have faces := boundary_faces C B h
  have cap := h.upperV
  rw [h.same] at cap
  rw [upper_on_central_v C B h,(ownV C).1] at sep
  change -ell*B.loU+k*(B.loV+B.side)≤C.loV at sep
  have wall : (-B.s)*B.loU-B.c*(B.loV+B.side)≤2-B.side*(B.c-B.s) := by
    nlinarith only [faces.wall]
  have first := mul_nonneg ep.le (sub_nonneg.mpr wall)
  have middle := mul_nonneg h.centralPositive.le (sub_nonneg.mpr faces.upperV)
  have last := mul_nonneg rp.le (sub_nonneg.mpr cap)
  have identity :
      (-B.s)*(-ell*B.loU+k*(B.loV+B.side)-C.loV)-
        (B.side*(ell*(B.c-B.s)-B.s)-2*ell+C.s*(B.c+B.s))=
      ell*(2-B.side*(B.c-B.s)-(-B.s)*B.loU+B.c*(B.loV+B.side))+
        C.s*(-B.c-(B.loV+B.side))+
        (-B.s)*(C.s-B.side-C.loV) := by
    dsimp only [k,ell,crossCos,crossSin]
    linear_combination -C.s*(B.loV+B.side)*h.boundaryNormal.2.2
  have coefficient : 0<ell*(B.c-B.s)-B.s := by
    have term := mul_pos ep (show 0<B.c-B.s by linarith only [bp,rp])
    linarith only [term,rp]
  have strict := mul_pos (sub_pos.mpr side) coefficient
  have scalar := central_margin h.centralNormal h.boundaryNormal
    h.centralPositive rp
  change 0<ell*(B.c+(-B.s))+(-B.s)-2*ell+C.s*(B.c-(-B.s)) at scalar
  have separating := mul_nonneg rp.le (sub_nonneg.mpr sep)
  nlinarith only [identity,first,middle,last,strict,scalar,separating]

/-- Section 6: B's northeast face cannot separate at slope >=1/4. -/
theorem no_large_boundary_v (C B : OpenSquare) (h : Input C B)
    (large : B.c≤4*(-B.s))
    (sep : upper B (-B.s) B.c≤lower C (-B.s) B.c) : False := by
  let k := crossCos C.c C.s B.c (-B.s)
  let ell := crossSin C.c C.s B.c (-B.s)
  have signs := cross_bounds h.centralNormal h.boundaryNormal
    h.centralPositive h.boundaryNegative
  have kn : 0≤k := signs.1
  have ep : 0<ell := signs.2.1
  have rp := h.boundaryNegative
  have bb := strict_bounds h.boundaryNormal rp
  have bp : 0<B.c := by linarith only [bb.1]
  have side : 1<B.side := by rw [←h.same]; exact h.side
  have faces := boundary_faces C B h
  have capU := h.upperU
  have capV := h.upperV
  rw [h.same] at capU capV
  rw [(ownV B).2,lower_on_boundary_v C B h] at sep
  change B.loV+B.side≤ell*C.loU+k*C.loV at sep
  have lWeight := mul_nonneg rp.le (sub_nonneg.mpr faces.lowerU)
  have dFloor : B.side*(B.c-B.s)-2-B.c*(-B.s)+(543/500)*(-B.s)^2≤
      B.c*(B.loV+B.side) := by
    nlinarith only [faces.wall,lWeight]
  have uWeight := mul_nonneg (mul_nonneg bp.le ep.le)
    (show 0≤-B.side-C.loU by linarith only [capU])
  have vWeight := mul_nonneg (mul_nonneg bp.le kn) (sub_nonneg.mpr capV)
  have separating := mul_nonneg bp.le (sub_nonneg.mpr sep)
  have necessary :
      B.side*(B.c-B.s+B.c*(k+ell))-2-B.c*(-B.s)+
        (543/500)*(-B.s)^2-B.c*k*C.s≤0 := by
    nlinarith only [dFloor,uWeight,vWeight,separating]
  have coefficient : 0<B.c-B.s+B.c*(k+ell) := by
    have term := mul_nonneg bp.le (show 0≤k+ell by linarith only [kn,ep])
    linarith only [bp,rp,term]
  have strict := mul_pos (sub_pos.mpr side) coefficient
  have scalar := northeast_margin h.centralNormal h.boundaryNormal
    h.centralPositive rp large
  have identity : B.c-B.s+B.c*(k+ell)-2-B.c*(-B.s)+
      (543/500)*(-B.s)^2-B.c*k*C.s=
      B.c+(-B.s)-2-B.c*(-B.s)+(543/500)*(-B.s)^2+
        B.c^2*(C.c+C.s-C.c*C.s)+B.c*(-B.s)*(C.c-C.s+C.s^2) := by
    dsimp only [k,ell,crossCos,crossSin]
    ring
  nlinarith only [necessary,strict,scalar,identity]

/-- The full local theorem. It uses only the same physical side >1,
the two actual squares, their literal strict/omitted points, simultaneous
central faces and the real boundary floor. Every support contact is weak. -/
theorem shallow (C B : OpenSquare) (h : Input C B) : (-B.s)/B.c<1/4 := by
  have bb := strict_bounds h.boundaryNormal h.boundaryNegative
  have bp : 0<B.c := by linarith only [bb.1]
  apply (div_lt_iff₀ bp).mpr
  by_contra no
  have large : B.c≤4*(-B.s) := by linarith only [no]
  rcases separators C B h with central | negative | positive
  · exact no_central_v C B h central
  · exact no_negative_u C B h negative
  · exact no_large_boundary_v C B h large positive

end
#print axioms shallow
end N12Compact.C1092MPPMMissingBoundaryShallow
