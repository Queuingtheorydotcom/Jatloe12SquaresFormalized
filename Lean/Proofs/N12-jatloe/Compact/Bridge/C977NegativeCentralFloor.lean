import Compact.Bridge.C977SignedCentralCorner
import Compact.Geometry.CentralNegativeIncomingBottom

/-! The actual farther bottom-wall point forces the lower V face of
the negative southeast central square for either central orientation
and either incoming longitudinal axis. -/
namespace N12Compact.C977NegativeCentralFloor

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

theorem frame_floor (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (t : ℝ) (signed : (q 6).s=-t) (bn : Normal (q 6).c t)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (center : (p.square (orderedOwner p 5)).Inside 2 2) :
    (q 6).c+(13/5)*t≤(q 6).loV := by
  have side : 1<(q 6).side := by rw [shape,p.congruent]; exact p.side_gt_one
  have markers := coded_exact p (orderedOwner p 6)
  rw [ordered_owner_code p hf 6] at markers
  have marker : (q 6).Inside (47/20) (33/20) := (equivalent 6 _ _).mpr (by
    have point := (markers 9).mpr (by decide)
    simpa [Owns,marker] using point)
  have outer : (q 6).Inside 3 (8/5) :=
    (equivalent 6 _ _).mpr (C977OuterWings.points p hf).1
  have marked := (negative_bands (q 6) t _ _ signed).mp marker
  have wall := (negative_bands (q 6) t _ _ signed).mp outer
  have missingMiddle : ¬(q 6).Inside 3 2 := fun h => p.disjoint _ _
    (fun eq => (by decide : (6 : Fin 12)≠10) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent 6 _ _).mp h,C977WallMiddle.right_point p hf⟩
  have capV : (q 6).loV+(q 6).side≤2*(q 6).c+3*t := by
    apply le_of_not_gt
    intro high
    apply missingMiddle
    apply (negative_bands (q 6) t _ _ signed).mpr
    refine ⟨?_,?_,?_,by linarith only [high]⟩ <;>
      nlinarith only [marked.1,marked.2.2.1,wall.2.1,bn.1,bn.2.1,(canonical 6).1]
  have highMissing : ¬(q 6).Inside (13/5) 1 := fun h => p.disjoint _ _
    (fun eq => (by decide : (6 : Fin 12)≠9) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent 6 _ _).mp h,C977BottomExtendedReach.point p hf missingCorner⟩
  have aCenter := (equivalent 5 _ _).mpr center
  have aLow := (equivalent 5 _ _).mpr (C977CentralReach.central_points p hf).1
  rcases (C977CenterIncoming.frame_cover p hf q shape equivalent canonical center).1 with
      own | neighboring | transverse
  · by_cases positive : 0≤(q 5).s
    · have an : Normal (q 5).c (q 5).s :=
        ⟨positive,by simpa only [abs_of_nonneg positive] using (canonical 5).2,
          (q 5).unit_normal⟩
      exact CentralNegativeBottomUpper.lower_face (q 6) t an bn signed side.le marker capV
        (by linarith only [aCenter.2.1,own]) highMissing
    · have negative : (q 5).s<0 := lt_of_not_ge positive
      have an : Normal (q 5).c (-(q 5).s) :=
        ⟨by linarith only [negative],
          by simpa only [abs_of_neg negative] using (canonical 5).2,
          by nlinarith only [(q 5).unit_normal]⟩
      apply CentralNegativeIncomingBottom.lower_face (q 6) t an bn signed side.le marker capV
      · simp only [neg_neg]
        linarith only [aLow.2.1,own]
      · exact highMissing
  · have noUpper : ¬(q 6).loU+(q 6).side≤(13/5)*(q 6).c-t := by
      intro cap
      have strict := strict_bounds (q 5) _ _ (q 6).c (-t)
        (by nlinarith only [bn.2.2]) aLow
      rw [signed] at neighboring
      have short : (3/5)*(q 6).c+t/2≤1 := by
        nlinarith only [bn.2.2,sq_nonneg ((q 6).c-3/5),sq_nonneg (t-1/2)]
      nlinarith only [strict.2,neighboring,cap,side,short]
    have b := normal_bounds bn
    apply le_of_not_gt
    intro low
    apply highMissing
    apply (negative_bands (q 6) t _ _ signed).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [marked.1,marked.2.2.2,noUpper,low,b.1,bn.1,bn.2.1]
  · exfalso
    nlinarith only [transverse.1,signed,bn.1,(canonical 6).1]

#print axioms frame_floor
end N12Compact.C977NegativeCentralFloor
