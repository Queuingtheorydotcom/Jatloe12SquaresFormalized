import Compact.Completion.OtherCases.TopOnlyLeftPoint
import Compact.Completion.C981.CornerAdvance

/-! TOP-ONLY-LEFT-POINT Corollaries 3--4: the literal positive tip
and the (p,q,r)=(.38,.026,.8) instance of OTHER-GEOMETRY Theorem 5.
The reach uses only the actual upper wall and the two omitted points. -/
namespace N12Compact.Completion.OtherCases.C976MergedLeft
open S12 S12Pilot
set_option Elab.async false

theorem positive_tip (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (7/20)) (top : q.Inside (13/50) 1)
    (missingL : ¬q.Inside 0 (13/50)) (missingP : ¬q.Inside 0 1)
    (missingC : ¬q.Inside 1 1)
    (avoid : ∀ y : ℝ,13/50≤y → y≤14/25 → ¬q.Inside 1 y) :
    q.Inside (13/500) 1 := by
  have faces := TopOnlyLeftPoint.positive_faces q side cp sn order marker top
    missingL missingP missingC (avoid (13/50) le_rfl (by norm_num))
  have lower := TopOnlyLeftPoint.bar_face q side cp sn order marker
    faces.1 faces.2.1 faces.2.2.2 avoid
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have su : q.s≤1 := le_trans order cu
  have upperGap := CommonCases.OutwardScalars.increasing_projection q.c q.s
    (11/25) (487/500) cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [faces.1,faces.2.2.1,lower,marker.2.2.1,side,cp,sn,cu,su,upperGap]

private theorem reach_positive (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s)
    (wall : q.s*(q.loU+q.side)+q.c*(q.loV+q.side)≤1)
    (origin : q.Inside 0 0) (left : ¬q.Inside (-(13/500)) 0)
    (below : ¬q.Inside 0 (-(19/50))) : q.Inside (4/5) 0 := by
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have su : q.s≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.c,sn]
  have cross := mul_nonneg cp.le sn
  have sum : 1≤q.c+q.s := by nlinarith only [q.unit_normal,cross,cp,sn]
  have high : q.c+q.s≤283/200 := by nlinarith only [q.unit_normal,sq_nonneg (q.c-q.s),cp,sn]
  have product := mul_nonneg (sub_nonneg.mpr sum) (sub_nonneg.mpr high)
  have arc : 1+(207/250)*q.c*q.s≤q.c+q.s := by
    nlinarith only [product,q.unit_normal,cross]
  have leftHighU : -(13/500)*q.c<q.loU+q.side := by linarith only [origin.2.1,cp]
  have leftLowV : q.loV<(13/500)*q.s := by linarith only [origin.2.2.1,sn]
  have modes : -(13/500)*q.c≤q.loU ∨ q.loV+q.side≤(13/500)*q.s := by
    by_cases first : -(13/500)*q.c≤q.loU
    · exact Or.inl first
    · right
      apply le_of_not_gt
      intro upper
      exact left ⟨by linarith only [first],by linarith only [leftHighU],
        by linarith only [leftLowV],by linarith only [upper]⟩
  have lowU : q.loU<(4/5)*q.c := by linarith only [origin.1,cp]
  have highV : -(4/5)*q.s<q.loV+q.side := by linarith only [origin.2.2.2,sn]
  rcases modes with lowerU | upperV
  · have highU : (4/5)*q.c<q.loU+q.side := by linarith only [lowerU,side,cu,cp]
    have lowV : q.loV< -(4/5)*q.s := by
      apply lt_of_not_ge
      intro lowerV
      have first := mul_nonneg sn (sub_nonneg.mpr lowerU)
      have last := mul_nonneg cp.le (show 0≤q.loV+(4/5)*q.s by linarith only [lowerV])
      have strict := mul_pos (sub_pos.mpr side) (show 0<q.c+q.s by linarith only [sum])
      nlinarith only [first,last,strict,wall,arc,cross]
    exact ⟨by linarith only [lowU],by linarith only [highU],
      by linarith only [lowV],by linarith only [highV]⟩
  · have lowV : q.loV< -(4/5)*q.s := by linarith only [upperV,side,su,sn]
    have belowHighU : -(19/50)*q.s<q.loU+q.side := by linarith only [origin.2.1,sn]
    have belowHighV : -(19/50)*q.c<q.loV+q.side := by linarith only [origin.2.2.2,cp]
    have belowLowV : q.loV< -(19/50)*q.c := by
      have gap := (short_projections q (19/50) (13/500) (by norm_num)).2.1
      linarith only [upperV,gap,side]
    have belowFace : -(19/50)*q.s≤q.loU := by
      apply le_of_not_gt
      intro low
      exact below ⟨by linarith only [low],by linarith only [belowHighU],
        by linarith only [belowLowV],by linarith only [belowHighV]⟩
    have gap := (short_projections q (4/5) (19/50) (by norm_num)).2.1
    have highU : (4/5)*q.c<q.loU+q.side := by linarith only [belowFace,gap,side]
    exact ⟨by linarith only [lowU],by linarith only [highU],
      by linarith only [lowV],by linarith only [highV]⟩

theorem top_only_reach (q : OpenSquare) (side : 1<q.side)
    (wall : ∀ x y,q.Inside x y → y≤1)
    (origin : q.Inside 0 0) (left : ¬q.Inside (-(13/500)) 0)
    (below : ¬q.Inside 0 (-(19/50))) : q.Inside (4/5) 0 := by
  obtain ⟨r,cp,sn,sideEq,inside,_⟩ := ClosedFrames.positive_frame q
  have wall' : ∀ x y,r.Inside x y → y≤1 := fun x y h => wall x y ((inside _ _).mp h)
  exact (inside _ _).mp (reach_positive r (by simpa only [sideEq] using side) cp sn
    (C981CompletionCornerAdvance.upper_wall r wall') ((inside _ _).mpr origin)
    (fun h => left ((inside _ _).mp h)) (fun h => below ((inside _ _).mp h)))

#print axioms positive_tip
#print axioms top_only_reach
end N12Compact.Completion.OtherCases.C976MergedLeft
