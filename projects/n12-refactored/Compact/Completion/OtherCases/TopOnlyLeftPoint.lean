import Compact.Completion.OtherCases.SharpPointScalars
import Compact.Completion.OtherCases.SharpBarGeometry

/-! TOP-ONLY-LEFT-POINT without a chord-formula library. The four true
face bounds follow from the strict anchors and omitted endpoints, and
the one genuine foreign bar supplies the remaining vertex obstruction. -/
namespace N12Compact.Completion.OtherCases.TopOnlyLeftPoint
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

theorem positive_faces (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (7/20)) (top : q.Inside (13/50) 1)
    (missingL : ¬q.Inside 0 (13/50)) (missingP : ¬q.Inside 0 1)
    (missingC : ¬q.Inside 1 1) (missingB : ¬q.Inside 1 (13/50)) :
    (13/50)*q.s≤q.loU ∧ -q.s+(13/50)*q.c≤q.loV ∧
      q.loU+q.side≤q.c+q.s ∧ q.loV+q.side≤q.c := by
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have lHighU : q.s*(13/50)<q.loU+q.side := by linarith only [marker.2.1,cp,sn]
  have lHighV : q.c*(13/50)<q.loV+q.side := by linarith only [top.2.2.2,cp,order]
  have pHighU : q.s<q.loU+q.side := by linarith only [top.2.1,cp]
  have pLowV : q.loV<q.c := by linarith only [marker.2.2.1,cp,sn]
  have cLowU : q.loU<q.c+q.s := by linarith only [marker.1,cp,sn]
  have cLowV : q.loV< -q.s+q.c := by linarith only [marker.2.2.1,cp,order]
  have bLowU : q.loU<q.c+q.s*(13/50) := by linarith only [marker.1,cp,order]
  have bHighV : -q.s+q.c*(13/50)<q.loV+q.side := by linarith only [top.2.2.2,cp,sn]
  have lLowV : q.loV<q.c*(13/50) := by
    by_contra failed
    have lFace : q.c*(13/50)≤q.loV := le_of_not_gt failed
    have pHighV : q.c<q.loV+q.side := by linarith only [lFace,side,cu]
    have pFace : q.s≤q.loU := by
      apply le_of_not_gt
      intro low
      apply missingP
      simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add,mul_one] using
        And.intro low (And.intro pHighU (And.intro pLowV pHighV))
    have cHighU : q.c+q.s<q.loU+q.side := by linarith only [pFace,side,cu]
    have cFace : q.loV+q.side≤ -q.s+q.c := by
      apply le_of_not_gt
      intro high
      apply missingC
      simpa only [OpenSquare.Inside,InBands,mul_one] using
        And.intro cLowU (And.intro cHighU (And.intro cLowV high))
    linarith only [lFace,cFace,side,cu,sn]
  have lFace : q.s*(13/50)≤q.loU := by
    apply le_of_not_gt
    intro low
    apply missingL
    simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add] using
      And.intro low (And.intro lHighU (And.intro lLowV lHighV))
  have bHighU : q.c+q.s*(13/50)<q.loU+q.side := by linarith only [lFace,side,cu]
  have bFace : -q.s+q.c*(13/50)≤q.loV := by
    apply le_of_not_gt
    intro low
    apply missingB
    simpa only [OpenSquare.Inside,InBands,mul_one] using
      And.intro bLowU (And.intro bHighU (And.intro low bHighV))
  have cHighV : -q.s+q.c<q.loV+q.side := by linarith only [bFace,side,cu]
  have cFace : q.loU+q.side≤q.c+q.s := by
    apply le_of_not_gt
    intro high
    apply missingC
    simpa only [OpenSquare.Inside,InBands,mul_one] using
      And.intro cLowU (And.intro high (And.intro cLowV cHighV))
  have pLowU : q.loU<q.s := by linarith only [cFace,side,cu]
  have pFace : q.loV+q.side≤q.c := by
    apply le_of_not_gt
    intro high
    apply missingP
    simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add,mul_one] using
      And.intro pLowU (And.intro pHighU (And.intro pLowV high))
  exact ⟨by linarith only [lFace],by linarith only [bFace],cFace,pFace⟩

theorem bar_face (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (7/20))
    (lowU : (13/50)*q.s≤q.loU) (lowV : -q.s+(13/50)*q.c≤q.loV)
    (highV : q.loV+q.side≤q.c)
    (avoid : ∀ y : ℝ,13/50≤y → y≤14/25 → ¬q.Inside 1 y) :
    -q.s+(14/25)*q.c≤q.loV := by
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have sp : 0<q.s := by linarith only [lowV,highV,side,cu]
  apply le_of_not_gt
  intro tLowV
  have tLowU : q.loU<q.c+q.s*(14/25) := by linarith only [marker.1,cp,sn]
  have tHighV : -q.s+q.c*(14/25)<q.loV+q.side := by linarith only [lowV,side,cu]
  have tUpperU : q.loU+q.side≤q.c+q.s*(14/25) := by
    apply le_of_not_gt
    intro high
    apply avoid (14/25) (by norm_num) le_rfl
    simpa only [OpenSquare.Inside,InBands,mul_one] using
      And.intro tLowU (And.intro high (And.intro tLowV tHighV))
  let X := q.c*(q.loU+q.side)-q.s*q.loV
  let Y := q.s*(q.loU+q.side)+q.c*q.loV
  have closed : ClosedInside q X Y :=
    WallProfile.vertex q (q.loU+q.side) q.loV
      ⟨by linarith only [q.side_pos],le_rfl⟩ ⟨le_rfl,by linarith only [q.side_pos]⟩
  have arc := SharpPointScalars.arc q.c q.s cp sp q.unit_normal
  have cross := mul_nonneg cp.le sn
  have firstX := mul_nonneg cp.le (sub_nonneg.mpr lowU)
  have lastX := mul_nonneg sn (sub_nonneg.mpr highV)
  have height := mul_pos (sub_pos.mpr side) (show 0<q.c+q.s by linarith only [cp,sn])
  have xHigh : 1<X := by
    dsimp only [X]
    nlinarith only [firstX,lastX,height,arc,cross]
  have firstY := mul_nonneg sn (sub_nonneg.mpr lowU)
  have lastY := mul_nonneg cp.le (sub_nonneg.mpr lowV)
  have length := mul_pos sp (show 0<q.side-q.c by linarith only [side,cu])
  have yLow : 13/50<Y := by
    dsimp only [Y]
    nlinarith only [firstY,lastY,length,q.unit_normal]
  have firstUpper := mul_nonneg sn (sub_nonneg.mpr tUpperU)
  have lastUpper := mul_pos cp (show 0< -q.s+(14/25)*q.c-q.loV by linarith only [tLowV])
  have yHigh : Y<14/25 := by
    dsimp only [Y]
    nlinarith only [firstUpper,lastUpper,q.unit_normal]
  exact SharpBarGeometry.vertical_crossing q X Y (7/20) (7/20) 1 (13/50) (14/25)
    closed marker (by norm_num) xHigh yLow.le yHigh.le
    (by norm_num) (by norm_num) avoid

private theorem positive (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (7/20)) (top : q.Inside (13/50) 1)
    (missingL : ¬q.Inside 0 (13/50)) (missingP : ¬q.Inside 0 1)
    (missingC : ¬q.Inside 1 1)
    (avoid : ∀ y : ℝ,13/50≤y → y≤14/25 → ¬q.Inside 1 y) :
    q.Inside 0 (31/50) := by
  have faces := positive_faces q side cp sn order marker top missingL missingP missingC
    (avoid (13/50) le_rfl (by norm_num))
  have stronger := bar_face q side cp sn order marker faces.1 faces.2.1 faces.2.2.2 avoid
  have span : 1<(11/25)*q.c+q.s := by linarith only [stronger,faces.2.2.2,side]
  have bound := SharpPointScalars.half_lower q.c q.s (11/25) cp sn order q.unit_normal span
  have cutoff : 7/18≤C1092WallProfileScalars.half q.c q.s := by linarith only [bound]
  have circle := SharpPointScalars.half_after q.c q.s (275/373) (252/373) (7/18)
    cp sn q.unit_normal (by norm_num) (by norm_num) (by norm_num) cutoff
  have projection := CommonCases.CanonicalProjection.after q.c q.s (275/373) (252/373)
    1 (19/50) q.unit_normal (by norm_num) circle (by norm_num) (by norm_num)
  have gap : q.c+(19/50)*q.s<1 := by linarith only [projection]
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [faces.2.2.1,side,gap]
  · linarith only [marker.2.1,cp,order]
  · linarith only [marker.2.2.1,cp,sn]
  · linarith only [top.2.2.2,cp,order]

theorem negative_faces (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : q.s≤0) (order : -q.s≤q.c)
    (marker : q.Inside (7/20) (7/20)) (top : q.Inside (13/50) 1)
    (sharp : q.Inside (21/40) (1/8))
    (missingL : ¬q.Inside 0 (13/50)) (missingP : ¬q.Inside 0 1)
    (missingC : ¬q.Inside 1 1)
    (avoid : ∀ y : ℝ,13/50≤y → y≤14/25 → ¬q.Inside 1 y) :
    q.s≤q.loU ∧ (13/50)*q.c≤q.loV ∧
      q.loU+q.side≤q.c+(14/25)*q.s ∧ q.loV+q.side≤q.c-q.s := by
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have pHighU : q.s<q.loU+q.side := by linarith only [top.2.1,cp]
  have pLowV : q.loV<q.c := by linarith only [marker.2.2.1,cp,order]
  have pHighV : q.c<q.loV+q.side := by linarith only [top.2.2.2,sn]
  have pLowerU : q.s≤q.loU := by
    apply le_of_not_gt
    intro low
    apply missingP
    simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add,mul_one] using
      And.intro low (And.intro pHighU (And.intro pLowV pHighV))
  have bLowU : q.loU<q.c+q.s*(13/50) := by linarith only [marker.1,cp,sn]
  have bLowV : q.loV< -q.s+q.c*(13/50) := by linarith only [sharp.2.2.1,cp,sn]
  have bHighV : -q.s+q.c*(13/50)<q.loV+q.side := by linarith only [top.2.2.2,order]
  have bUpperU : q.loU+q.side≤q.c+q.s*(13/50) := by
    apply le_of_not_gt
    intro high
    apply avoid (13/50) le_rfl (by norm_num)
    simpa only [OpenSquare.Inside,InBands,mul_one] using
      And.intro bLowU (And.intro high (And.intro bLowV bHighV))
  have lHighU : q.s*(13/50)<q.loU+q.side := by linarith only [marker.2.1,cp,order]
  have lHighV : q.c*(13/50)<q.loV+q.side := by linarith only [top.2.2.2,cp,sn]
  have lLowU : q.loU<q.s*(13/50) := by linarith only [bUpperU,side,cu]
  have lLowerV : q.c*(13/50)≤q.loV := by
    apply le_of_not_gt
    intro low
    apply missingL
    simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add] using
      And.intro lLowU (And.intro lHighU (And.intro low lHighV))
  have cLowU : q.loU<q.c+q.s := by linarith only [marker.1,cp,order]
  have cHighU : q.c+q.s<q.loU+q.side := by linarith only [pLowerU,side,cu]
  have cLowV : q.loV< -q.s+q.c := by linarith only [marker.2.2.1,cp,sn]
  have cUpperV : q.loV+q.side≤ -q.s+q.c := by
    apply le_of_not_gt
    intro high
    apply missingC
    simpa only [OpenSquare.Inside,InBands,mul_one] using
      And.intro cLowU (And.intro cHighU (And.intro cLowV high))
  have tLowU : q.loU<q.c+q.s*(14/25) := by linarith only [marker.1,cp,order]
  have tLowV : q.loV< -q.s+q.c*(14/25) := by linarith only [marker.2.2.1,cp,sn]
  have shortT := CommonCases.OutwardScalars.increasing_projection q.c (-q.s) (3/10) 1
    cp (by linarith only [sn]) order (by simpa only [neg_sq] using q.unit_normal)
    (by norm_num) (by norm_num) (by norm_num)
  have tHighV : -q.s+q.c*(14/25)<q.loV+q.side := by linarith only [lLowerV,side,shortT]
  have tUpperU : q.loU+q.side≤q.c+q.s*(14/25) := by
    apply le_of_not_gt
    intro high
    apply avoid (14/25) (by norm_num) le_rfl
    simpa only [OpenSquare.Inside,InBands,mul_one] using
      And.intro tLowU (And.intro high (And.intro tLowV tHighV))
  exact ⟨pLowerU,by linarith only [lLowerV],
    by linarith only [tUpperU],by linarith only [cUpperV]⟩

private theorem negative (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : q.s≤0) (order : -q.s≤q.c)
    (marker : q.Inside (7/20) (7/20)) (top : q.Inside (13/50) 1)
    (sharp : q.Inside (21/40) (1/8))
    (missingL : ¬q.Inside 0 (13/50)) (missingP : ¬q.Inside 0 1)
    (missingC : ¬q.Inside 1 1)
    (avoid : ∀ y : ℝ,13/50≤y → y≤14/25 → ¬q.Inside 1 y) :
    q.Inside 0 (31/50) := by
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  obtain ⟨pLowerU,lLowerV,tUpperU,cUpperV⟩ :=
    negative_faces q side cp sn order marker top sharp missingL missingP missingC avoid
  have sineLower : 13/50< -q.s := by linarith only [lLowerV,cUpperV,side,cu]
  have cosineUpper : q.c≤1-q.s^2/2 := by nlinarith only [q.unit_normal,sq_nonneg (q.c-1)]
  have product := mul_pos (show 0< -q.s by linarith only [sineLower])
    (show 0< -q.s-3/25 by linarith only [sineLower])
  have uGap : q.c-(3/50)*q.s<1 := by nlinarith only [cosineUpper,product]
  have vGap := CommonCases.OutwardScalars.increasing_projection q.c (-q.s) (19/50) 1
    cp (by linarith only [sn]) order (by simpa only [neg_sq] using q.unit_normal)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [tUpperU,side,uGap]
  · linarith only [marker.2.1,cp,sn]
  · linarith only [cUpperV,side,vGap]
  · linarith only [top.2.2.2,cp,sn]

theorem point (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (7/20) (7/20)) (top : q.Inside (13/50) 1)
    (sharp : q.Inside (21/40) (1/8))
    (missingL : ¬q.Inside 0 (13/50)) (missingP : ¬q.Inside 0 1)
    (missingC : ¬q.Inside 1 1)
    (avoid : ∀ y : ℝ,13/50≤y → y≤14/25 → ¬q.Inside 1 y) :
    q.Inside 0 (31/50) := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have g := (same _ _).mpr top
  have y := (same _ _).mpr sharp
  have l : ¬r.Inside 0 (13/50) := fun h => missingL ((same _ _).mp h)
  have p : ¬r.Inside 0 1 := fun h => missingP ((same _ _).mp h)
  have c : ¬r.Inside 1 1 := fun h => missingC ((same _ _).mp h)
  have segment (v : ℝ) (lower : 13/50≤v) (upper : v≤14/25) : ¬r.Inside 1 v :=
    fun h => avoid v lower upper ((same _ _).mp h)
  by_cases sign : 0≤r.s
  · exact (same _ _).mp (positive r side' cp sign
      (by simpa only [abs_of_nonneg sign] using range) m g l p c segment)
  · exact (same _ _).mp (negative r side' cp (le_of_not_ge sign)
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range) m g y l p c segment)

theorem point_original (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (47/20)) (top : q.Inside (113/50) 3)
    (sharp : q.Inside (101/40) (17/8))
    (missingL : ¬q.Inside 2 (113/50)) (missingP : ¬q.Inside 2 3)
    (missingC : ¬q.Inside 3 3)
    (avoid : ∀ y : ℝ,113/50≤y → y≤64/25 → ¬q.Inside 3 y) :
    q.Inside 2 (131/50) := by
  have point := point (q.translated 2 2) side
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact top)
    (by norm_num [inside_translated_iff]; exact sharp)
    (by norm_num [inside_translated_iff]; exact missingL)
    (by norm_num [inside_translated_iff]; exact missingP)
    (by norm_num [inside_translated_iff]; exact missingC)
    (by
      intro y lower upper own
      have original : q.Inside 3 (y+2) := by
        convert (inside_translated_iff q 2 2 1 y).mp own using 1 <;> ring
      exact avoid (y+2) (by linarith only [lower]) (by linarith only [upper]) original)
  norm_num [inside_translated_iff] at point
  exact point

#print axioms negative_faces
#print axioms point_original
end N12Compact.Completion.OtherCases.TopOnlyLeftPoint

