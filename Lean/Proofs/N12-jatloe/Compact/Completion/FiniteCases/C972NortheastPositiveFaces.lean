import Compact.Completion.FiniteCases.C972NortheastSign

/-! Actual positive-NE faces. The alternate exit at F5 would force the
foreign northwest marker into this same NE square. The globally absent
top marker then has just its upper-v exit. -/
namespace N12Compact.FiniteCases.C972Local
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

structure PositiveNorth (N : OpenSquare) : Prop where
  lowerU : (13/50)*N.s≤N.loU
  upperV : N.loV+N.side≤(543/500)*N.c

theorem positive_north_faces (N : OpenSquare) (side : 1<N.side)
    (normal : Normal N.c N.s)
    (marker : N.Inside (7/20) (7/20)) (origin : N.Inside 0 1)
    (inner : ¬N.Inside 0 (13/50)) (top : ¬N.Inside 0 (543/500))
    (northwest : ¬N.Inside (-7/20) (7/20)) : PositiveNorth N := by
  have bounds := normal_bounds normal
  have cp : 0<N.c := by linarith only [bounds.1]
  have sine : N.s≤5/7 := by linarith only [normal.2.1,bounds.2.2.2.2.2]
  have short : (7/20)*N.c+(92/125)*N.s<1 := by
    linarith only [bounds.2.1,sine]
  have lowerU : (13/50)*N.s≤N.loU := by
    apply le_of_not_gt
    intro low
    have lowerV : (13/50)*N.c≤N.loV := by
      apply le_of_not_gt
      intro lowV
      apply inner
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [lowV,low,origin.2.1,origin.2.2.2,cp,normal.1]
    have upperU : N.loU+N.side≤(543/500)*N.s := by
      apply le_of_not_gt
      intro high
      apply top
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [high,low,marker.2.2.1,lowerV,side,bounds.2.1,cp,normal.1]
    apply northwest
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [upperU,side,short,origin.2.1,marker.2.2.1,
        origin.2.2.2,cp,normal.1,normal.2.1]
  have upperV : N.loV+N.side≤(543/500)*N.c := by
    apply le_of_not_gt
    intro high
    apply top
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,origin.1,lowerU,side,sine,marker.2.2.1,cp,normal.1]
  exact ⟨lowerU,upperV⟩

end N12Compact.FiniteCases.C972Local

namespace N12Compact.FiniteCases.C972
open S12 S12Pilot C977CornerCubic
set_option Elab.async false
noncomputable section

theorem northeast_positive_faces (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (N : OpenSquare) (shape : N.side=(owners p 7).side)
    (actual : ∀ x y,N.Inside x y↔(owners p 7).Inside (2+x) (2+y))
    (normal : Normal N.c N.s) : C972Local.PositiveNorth N := by
  apply C972Local.positive_north_faces N (by rw [shape]; exact side p 7) normal
  · apply (actual _ _).mpr; norm_num; exact (fixed p hf).northeastMarker
  · apply (actual _ _).mpr; norm_num; exact northeast_origin p hf
  · intro own
    apply northeast_missing_f5 p hf
    convert (actual _ _).mp own using 1 <;> norm_num
  · intro own
    apply missing_top p hf 7
    convert (actual _ _).mp own using 1 <;> norm_num
  · intro own
    apply foreign p hf 7 8 (by decide) _ _ (fixed p hf).northwestMarker
    convert (actual _ _).mp own using 1 <;> norm_num

end
#print axioms northeast_positive_faces
end N12Compact.FiniteCases.C972
