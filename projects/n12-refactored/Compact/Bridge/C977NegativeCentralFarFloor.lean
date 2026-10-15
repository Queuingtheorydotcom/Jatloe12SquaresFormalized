import Compact.Bridge.C977NegativeCentralFloor
import Compact.Bridge.C977BottomNegativeExtendedReach
import Compact.Geometry.CentralNegativeFarIncoming

/-! The full negative bottom wall advances the actual negative central
lower face to 2.86. Every central sign and incoming axis is retained;
the resulting small central tilt is a consequence, not an assumption. -/
namespace N12Compact.C977NegativeCentralFarFloor

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

theorem frame_bounds (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (r t : ℝ) (ds : (q 9).s=-r) (dn : Normal (q 9).c r)
    (bs : (q 6).s=-t) (bn : Normal (q 6).c t)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (center : (p.square (orderedOwner p 5)).Inside 2 2) :
    (q 6).c+(143/50)*t≤(q 6).loV ∧ t<3/10 := by
  have side : 1<(q 6).side := by rw [shape,p.congruent]; exact p.side_gt_one
  have same : (q 9).side=(q 6).side := by rw [shape,shape,p.congruent,p.congruent]
  have bm := coded_exact p (orderedOwner p 6)
  rw [ordered_owner_code p hf 6] at bm
  have marker : (q 6).Inside (47/20) (33/20) := (equivalent 6 _ _).mpr (by
    have point := (bm 9).mpr (by decide)
    simpa [Owns,marker] using point)
  have wall : (q 6).Inside 3 (87/50) := (equivalent 6 _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 6, 8∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 6)
    have point := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have outer : (q 6).Inside 3 (8/5) :=
    (equivalent 6 _ _).mpr (C977OuterWings.points p hf).1
  have marked := (negative_bands (q 6) t _ _ bs).mp marker
  have wing := (negative_bands (q 6) t _ _ bs).mp outer
  have missingMiddle : ¬(q 6).Inside 3 2 := fun h => p.disjoint _ _
    (fun eq => (by decide : (6 : Fin 12)≠10) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent 6 _ _).mp h,C977WallMiddle.right_point p hf⟩
  have capV : (q 6).loV+(q 6).side≤2*(q 6).c+3*t := by
    apply le_of_not_gt
    intro high
    apply missingMiddle
    apply (negative_bands (q 6) t _ _ bs).mpr
    refine ⟨?_,?_,?_,high⟩ <;>
      nlinarith only [marked.1,marked.2.2.1,wing.2.1,bn.1,bn.2.1,(canonical 6).1]
  have cap := (C977SignedCentralCorner.frame_cap p hf q shape equivalent canonical
    missingCorner center).2
  rw [bs] at cap
  have lower := C977NegativeCentralFloor.frame_floor p hf q shape equivalent canonical
    t bs bn missingCorner center
  have dm := coded_exact p (orderedOwner p 9)
  rw [ordered_owner_code p hf 9] at dm
  have dMarker : (q 9).Inside 2 (457/500) := (equivalent 9 _ _).mpr (by
    have point := (dm 13).mpr (by decide)
    simpa [Owns,marker] using point)
  have dHigh := (equivalent 9 _ _).mpr (C977BottomExtendedReach.point p hf missingCorner)
  have far := C977BottomNegativeExtendedReach.frame_point p hf (q 9) r ds dn
    (shape 9) (equivalent 9) missingCorner
  have apart : ∀ x y, ¬((q 9).Inside x y ∧ (q 6).Inside x y) := fun x y h =>
    p.disjoint _ _ (fun eq => (by decide : (9 : Fin 12)≠6)
      (ordered_owner_injective p hf eq)) x y
      ⟨(equivalent 9 _ _).mp h.1,(equivalent 6 _ _).mp h.2⟩
  have separation := CentralNegativeBottomAxes.alternatives (q 9) (q 6) t bs bn
    (canonical 9).1 (canonical 9).2 same side dMarker dHigh marker wall
    (by linarith only [cap]) capV apart
  rw [ds,neg_neg] at separation
  have missingFar : ¬(q 6).Inside (143/50) 1 := fun h => apart _ _ ⟨far,h⟩
  have aCenter := (equivalent 5 _ _).mpr center
  have aLow := (equivalent 5 _ _).mpr (C977CentralReach.central_points p hf).1
  have noUpper : ¬(q 6).loU+(q 6).side≤(143/50)*(q 6).c-t := by
    intro upperCap
    rcases (C977CenterIncoming.frame_cover p hf q shape equivalent canonical center).1 with
        own | neighboring | transverse
    · by_cases positive : 0≤(q 5).s
      · have an : Normal (q 5).c (q 5).s :=
          ⟨positive,by simpa only [abs_of_nonneg positive] using (canonical 5).2,
            (q 5).unit_normal⟩
        exact CentralNegativeFarUpper.impossible (q 9) (q 6) r t an bn dn bs ds side.le
          far upperCap capV (by linarith only [aCenter.2.1,own]) separation
      · have negative : (q 5).s<0 := lt_of_not_ge positive
        have an : Normal (q 5).c (-(q 5).s) :=
          ⟨by linarith only [negative],
            by simpa only [abs_of_neg negative] using (canonical 5).2,
            by nlinarith only [(q 5).unit_normal]⟩
        apply CentralNegativeFarIncoming.impossible (q 9) (q 6) r t an bn dn bs ds side.le
          marker far upperCap capV lower
        · simp only [neg_neg]
          linarith only [aLow.2.1,own]
        · exact separation
    · have strict := strict_bounds (q 5) _ _ (q 6).c (-t)
        (by nlinarith only [bn.2.2]) aLow
      rw [bs] at neighboring
      have short : (43/50)*(q 6).c+t/2≤1 := by
        nlinarith only [bn.2.2,sq_nonneg ((q 6).c-43/50),sq_nonneg (t-1/2)]
      nlinarith only [strict.2,neighboring,upperCap,side,short]
    · nlinarith only [transverse.1,bs,bn.1,(canonical 6).1]
  have bb := normal_bounds bn
  have floor : (q 6).c+(143/50)*t≤(q 6).loV := by
    apply le_of_not_gt
    intro low
    apply missingFar
    apply (negative_bands (q 6) t _ _ bs).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [marked.1,marked.2.2.2,noUpper,low,bb.1,bn.1,bn.2.1]
  refine ⟨floor,?_⟩
  have narrow : 1<(q 6).c+(7/50)*t := by linarith only [floor,capV,side]
  have product := mul_pos (show 0<1+(q 6).c by linarith only [bb.1]) (sub_pos.mpr narrow)
  have order := mul_nonneg bn.1 (sub_nonneg.mpr bb.2.1)
  by_contra no
  have large : 3/10≤t := le_of_not_gt no
  have last := mul_nonneg bn.1 (show 0≤t-7/25 by linarith only [large])
  nlinarith only [product,order,last,bn.2.2]

#print axioms frame_bounds
end N12Compact.C977NegativeCentralFarFloor
