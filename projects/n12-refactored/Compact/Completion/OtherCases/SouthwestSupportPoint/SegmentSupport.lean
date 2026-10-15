import Compact.Completion.OtherCases.SouthwestSupportPoint.LowerFaces
import Compact.Completion.C981.SupportForms
import Compact.Geometry.SegmentCorner

/-! C974-C976-SW-SUPPORT-POINT.md, section 3, in centered coordinates.
The positive sign already forces the upper-u face at the actual endpoint G.
For the negative sign, the whole excluded R--G segment gives the alternative
full-square support by the existing exact corner-crossing theorem.
No segment joining unrelated owners or strict separation gap is assumed.
Source translation only; compiler acceptance has not been tested. -/
namespace N12Compact.Completion.OtherCases.SouthwestSupportPoint.SegmentSupport
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C981CompletionSupportForms
set_option Elab.async false

theorem positive (q : OpenSquare) (h : Input q)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c) :
    q.loU+q.side ≤ (13/50)*q.c ∨ upper q 35 9 ≤ 91/10 := by
  left
  have missing := h.southeastSegment 1 (by norm_num) le_rfl
  norm_num at missing
  have south := h.inwardSouth
  have west := h.inwardWest
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_add,add_zero] at south west
  apply le_of_not_gt
  intro high
  apply missing
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [south.1,south.2.2.1,west.2.2.2,cp,sn,order,high]

theorem negative (q : OpenSquare) (h : Input q) (s : ℝ) (signed : q.s = -s)
    (cp : 0 < q.c) (sn : 0 ≤ s) (order : s ≤ q.c) :
    q.loU+q.side ≤ (13/50)*q.c ∨ upper q 35 9 ≤ 91/10 := by
  have unit : q.c^2+s^2=1 := by
    have normal := q.unit_normal
    rw [signed] at normal
    nlinarith only [normal]
  have bands (x y : ℝ) : q.Inside x y ↔
      q.loU < q.c*x-s*y ∧ q.c*x-s*y < q.loU+q.side ∧
      q.loV < s*x+q.c*y ∧ s*x+q.c*y < q.loV+q.side := by
    simp only [OpenSquare.Inside,InBands,signed,neg_mul,neg_neg,sub_eq_add_neg]
  let uR := (7/20)*(q.c+s)
  let vR := (7/20)*(s-q.c)
  let uG := (13/50)*q.c
  let vG := (13/50)*s
  have marker := (bands _ _).mp h.marker
  have south := (bands _ _).mp h.inwardSouth
  have west := (bands _ _).mp h.inwardWest
  have rLowerU : q.loU < uR := by
    dsimp only [uR]
    linarith only [marker.1,cp]
  have rLowerV : q.loV < vR := by
    dsimp only [vR]
    linarith only [marker.2.2.1,sn]
  have rUpperV : vR < q.loV+q.side := by
    have lowerFace := (LowerFaces.negative q h s signed cp sn order).2
    have short := (short_projections q (61/100) (13/20) (by norm_num)).2.2.2
    rw [signed,neg_neg] at short
    dsimp only [vR]
    linarith only [lowerFace,short,h.side]
  have rUpperU : q.loU+q.side ≤ uR := by
    apply le_of_not_gt
    intro high
    apply h.missingEast
    apply (bands _ _).mpr
    dsimp only [uR,vR] at rLowerU rLowerV rUpperV high
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [rLowerU,rLowerV,rUpperV,high]
  have gLowerU : q.loU < uG := by
    dsimp only [uG]
    linarith only [west.1,cp]
  have gLowerV : q.loV < vG := by
    dsimp only [vG]
    linarith only [south.2.2.1,cp,sn]
  by_cases face : q.loU+q.side ≤ uG
  · exact Or.inl face
  have gUpperU : uG < q.loU+q.side := lt_of_not_ge face
  have gUpperV : q.loV+q.side ≤ vG := by
    have missing := h.southeastSegment 1 (by norm_num) le_rfl
    norm_num at missing
    apply le_of_not_gt
    intro high
    apply missing
    apply (bands _ _).mpr
    dsimp only [uG,vG] at gLowerU gLowerV gUpperU high
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [gLowerU,gLowerV,gUpperU,high]
  have avoid (t : ℝ) (tn : 0 ≤ t) (tu : t ≤ 1) :
      ¬ (-q.loU-q.side < (1-t)*(-uR)+t*(-uG) ∧
        (1-t)*(-uR)+t*(-uG) < -q.loU ∧
        q.loV < (1-t)*vR+t*vG ∧ (1-t)*vR+t*vG < q.loV+q.side) := by
    rintro ⟨lowU,highU,lowV,highV⟩
    apply h.southeastSegment t tn tu
    apply (bands _ _).mpr
    dsimp only [uR,vR,uG,vG] at lowU highU lowV highV
    refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [lowU,highU,lowV,highV]
  have corner := SegmentCorner.crossing_order
    (-q.loU-q.side) (-q.loU) q.loV (q.loV+q.side) (-uR) vR (-uG) vG
    (by linarith only [rUpperU]) (by linarith only [gUpperU])
    (by linarith only [gLowerU]) rLowerV rUpperV gUpperV avoid
  have bandSupport :
      (35*q.c-9*s)*(q.loU+q.side)+(35*s+9*q.c)*(q.loV+q.side) ≤ 91/10 := by
    dsimp only [uR,vR,uG,vG] at corner
    nlinarith only [corner,unit]
  have first : 0 ≤ 35*q.c-9*s := by linarith only [cp,order]
  have second : 0 ≤ 35*s+9*q.c := by linarith only [sn,cp]
  have support : upper q 35 9 =
      (35*q.c-9*s)*(q.loU+q.side)+(35*s+9*q.c)*(q.loV+q.side) := by
    rw [upper_in_bands,signed]
    rw [show (35:ℝ)*q.c+9*(-s)=35*q.c-9*s by ring,
      show -(35:ℝ)*(-s)+9*q.c=35*s+9*q.c by ring,
      abs_of_nonneg first,abs_of_nonneg second]
    ring
  right
  rw [support]
  exact bandSupport

end N12Compact.Completion.OtherCases.SouthwestSupportPoint.SegmentSupport
