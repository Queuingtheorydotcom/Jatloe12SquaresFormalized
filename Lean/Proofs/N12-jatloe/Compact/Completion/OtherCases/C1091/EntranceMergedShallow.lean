import Compact.Completion.OtherCases.C1091.MergedMarkerSeed
import Compact.Geometry.C977CornerCubic

/-! A reconstructed C1091 entrance lemma. The genuine merged left marker
and the genuine foreign Q8 marker differ by a unit vertical displacement.
Together with the foreign Q0 inner corner this forces a shallow positive
canonical frame. Three strict points follow in the same actual Q4. No
mask256 domain, absent marker1, side upper cap or numerical search occurs.
Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1091.EntranceMergedShallow
open S12 S12Pilot C977CornerCubic
set_option Elab.async false
noncomputable section

structure Input (A : OpenSquare) : Prop where
  side : 1<A.side
  left : A.Inside (-43/500) 0
  marker : A.Inside (13/20) (13/20)
  corner : ¬A.Inside 0 0
  wall : ¬A.Inside (-43/500) 1

theorem Input.reframe {A B : OpenSquare} (h : Input A)
    (shape : B.side=A.side) (same : ∀ x y,B.Inside x y↔A.Inside x y) : Input B where
  side := by simpa only [shape] using h.side
  left := (same _ _).mpr h.left
  marker := (same _ _).mpr h.marker
  corner := fun own => h.corner ((same _ _).mp own)
  wall := fun own => h.wall ((same _ _).mp own)

private theorem nonpositive_impossible (A : OpenSquare) (h : Input A)
    (cp : 0<A.c) (sn : A.s≤0) (order : -A.s≤A.c) : False := by
  apply h.corner
  refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith only [h.left.1,h.left.2.2.1,h.marker.2.1,h.marker.2.2.2,cp,sn,order]

/-- Both face choices are consequences of the two genuine omissions.
The strict width excludes the zero-angle endpoint automatically. -/
theorem profile (A : OpenSquare) (h : Input A) (cn : Normal A.c A.s) :
    0≤A.loV ∧ 0<A.s ∧ 5*A.s<A.c := by
  have bounds := normal_bounds cn
  have cp : 0<A.c := by linarith only [bounds.1]
  have lowerV : 0≤A.loV := by
    apply le_of_not_gt
    intro low
    apply h.corner
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [h.left.1,h.left.2.2.2,h.marker.2.1,cp,cn.1,low]
  have sp : 0<A.s := by nlinarith only [lowerV,h.left.2.2.1]
  have upperV : A.loV+A.side≤A.c+(43/500)*A.s := by
    apply le_of_not_gt
    intro high
    apply h.wall
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [h.left.1,h.left.2.2.1,h.marker.2.1,cp,sp,cn.2.1,high]
  have span : 1<A.c+(43/500)*A.s := by linarith only [upperV,lowerV,h.side]
  have product := mul_pos (show 0<A.c+(43/500)*A.s-1 by linarith only [span])
    (show 0<A.c+(43/500)*A.s+1 by linarith only [span])
  have weighted : 0<A.s*((43/250)*A.c-(1-(43/500)^2)*A.s) := by
    nlinarith only [product,cn.2.2]
  have factor := pos_of_mul_pos_right weighted sp.le
  exact ⟨lowerV,sp,by nlinarith only [factor,cp]⟩

/-- These are the exact three points needed by the two genuine F5
alternatives and the residual merged profile. -/
theorem positive_points (A : OpenSquare) (h : Input A) (cn : Normal A.c A.s) :
    A.Inside (23/50) (99/100) ∧ A.Inside (1/2) 1 ∧ A.Inside (29/50) 1 := by
  have bounds := normal_bounds cn
  have cp : 0<A.c := by linarith only [bounds.1]
  have p := profile A h cn
  constructor
  · refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [h.left.1,h.left.2.2.1,h.marker.2.1,
        h.side,p.1,p.2.1,p.2.2,cp,bounds.2.1,cn.2.1]
  · constructor
    · refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [h.left.1,h.left.2.2.1,h.marker.2.1,
          h.side,p.1,p.2.1,p.2.2,cp,bounds.2.1,cn.2.1]
    · refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [h.left.1,h.left.2.2.1,h.marker.2.1,
          h.side,p.1,p.2.1,p.2.2,cp,bounds.2.1,cn.2.1]

theorem points (A : OpenSquare) (h : Input A) :
    A.Inside (23/50) (99/100) ∧ A.Inside (1/2) 1 ∧ A.Inside (29/50) 1 := by
  obtain ⟨B,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame A
  have data := h.reframe shape same
  by_cases sign : 0≤B.s
  · have normal : Normal B.c B.s :=
      ⟨sign,by simpa only [abs_of_nonneg sign] using range,B.unit_normal⟩
    have result := positive_points B data normal
    exact ⟨(same _ _).mp result.1,(same _ _).mp result.2.1,(same _ _).mp result.2.2⟩
  · exact False.elim (nonpositive_impossible B data cp (le_of_not_ge sign)
      (by linarith only [(abs_le.mp range).1]))

/-- Original chart: A is one merged258 owner. The corner and wall
omissions must be supplied by their respective genuine owners. -/
theorem original_points (A : OpenSquare) (side : 1<A.side)
    (left : A.Inside (457/500) 1) (marker : A.Inside (33/20) (33/20))
    (corner : ¬A.Inside 1 1) (wall : ¬A.Inside (457/500) 2) :
    A.Inside (73/50) (199/100) ∧ A.Inside (3/2) 2 ∧ A.Inside (79/50) 2 := by
  have data : Input (A.translated 1 1) := {
    side := side
    left := by norm_num only [inside_translated_iff]; exact left
    marker := by norm_num only [inside_translated_iff]; exact marker
    corner := by norm_num only [inside_translated_iff]; exact corner
    wall := by norm_num only [inside_translated_iff]; exact wall }
  have result := points (A.translated 1 1) data
  norm_num only [inside_translated_iff] at result
  exact result

end
#print axioms original_points
end N12Compact.Completion.OtherCases.C1091.EntranceMergedShallow
