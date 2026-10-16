import Compact.Bridge.C977RightCornerSupport
import Compact.Geometry.CentralRightChain
import Compact.Geometry.CornerBudgetReach

/-! Original center-owned C977 entrance to the complete positive B/R
chain. The conditional southeast inner point and the incoming A/B axis
are explicit; no other original center-owned mode is discarded. -/
namespace N12Compact.C977CenterRightChain

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic
set_option Elab.async false

private theorem original_apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y, ¬((p.square (orderedOwner p i)).Inside x y ∧
      (p.square (orderedOwner p j)).Inside x y) := by
  apply p.disjoint
  exact fun h => different (ordered_owner_injective p hf h)

/-- The original northeast pair reaches rightwards. Both foreign points
come from the actual top/right wall owners, without an orientation choice. -/
theorem corner_outward (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (p.square (orderedOwner p 3)).Inside (16/5) 3 := by
  let E := p.square (orderedOwner p 3)
  have markers := coded_exact p (orderedOwner p 3)
  rw [ordered_owner_code p hf 3] at markers
  have top : E.Inside 3 (1543/500) := by
    have h := (markers 4).mpr (by decide)
    simpa [E,Owns,marker] using h
  have right : E.Inside (1543/500) 3 := by
    have h := (markers 5).mpr (by decide)
    simpa [E,Owns,marker] using h
  have topWall : (p.square (orderedOwner p 11)).Inside (12/5) 3 := by
    have check : ∀ owned∈pruningDomain4 11, 7∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 11)
    have point := (nat_combined_exact p (orderedOwner p 11) 7 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point
  have rightWall : (p.square (orderedOwner p 10)).Inside 3 (12/5) := by
    have check : ∀ owned∈pruningDomain4 10, 19∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 10)
    have point := (nat_combined_exact p (orderedOwner p 10) 19 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point
  have pTop : (pullX E).Inside 1 (1543/500) := (inside_pullX E _ _).mpr (by
    convert top using 1 <;> norm_num)
  have pRight : (pullX E).Inside (457/500) 3 := (inside_pullX E _ _).mpr (by
    convert right using 1 <;> norm_num)
  have missingRight : ¬(pullX E).Inside (8/5) 3 := by
    intro h
    have point : E.Inside (12/5) 3 := by
      convert (inside_pullX E _ _).mp h using 1 <;> norm_num
    exact original_apart p hf 3 11 (by decide) _ _ ⟨point,topWall⟩
  have missingBelow : ¬(pullX E).Inside 1 (12/5) := by
    intro h
    have point : E.Inside 3 (12/5) := by
      convert (inside_pullX E _ _).mp h using 1 <;> norm_num
    exact original_apart p hf 3 10 (by decide) _ _ ⟨point,rightWall⟩
  have reach := CornerBudgetReach.upper_left (pullX E)
    (by change 1<E.side; dsimp only [E]; rw [p.congruent]; exact p.side_gt_one)
    (container_pullX E (p.contained _)) pTop pRight missingRight missingBelow
  convert (inside_pullX E _ _).mp reach using 1 <;> norm_num

theorem frame_shift (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (bn : Normal (q 6).c (q 6).s) (rn : Normal (q 10).c (q 10).s)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (inner : (p.square (orderedOwner p 6)).Inside (113/50) 2)
    (incoming : upper (q 5) (q 6).c (q 6).s≤(q 6).loU) :
    3*(q 10).c+2*(q 10).s<(q 10).loU := by
  have bm := coded_exact p (orderedOwner p 6)
  rw [ordered_owner_code p hf 6] at bm
  have bMarker : (q 6).Inside (47/20) (33/20) := (equivalent 6 _ _).mpr (by
    have h := (bm 9).mpr (by decide)
    simpa [Owns,marker] using h)
  have rm := coded_exact p (orderedOwner p 10)
  rw [ordered_owner_code p hf 10] at rm
  have rMarker : (q 10).Inside (1543/500) 2 := (equivalent 10 _ _).mpr (by
    have h := (rm 14).mpr (by decide)
    simpa [Owns,marker] using h)
  have bLow : (q 6).Inside 3 (87/50) := (equivalent 6 _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 6, 8∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 6)
    have point := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have rHigh : (q 10).Inside 3 (12/5) := (equivalent 10 _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 10, 19∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 10)
    have point := (nat_combined_exact p (orderedOwner p 10) 19 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have corner : ¬(q 10).Inside 3 3 := by
    intro h
    exact p.disjoint _ _ (fun h => (by decide : (10 : Fin 12)≠3)
      (ordered_owner_injective p hf h)) _ _
      ⟨(equivalent 10 _ _).mp h,C977RightCornerSupport.northeast_corner p hf⟩
  have apart : ∀ x y, ¬((q 6).Inside x y ∧ (q 10).Inside x y) := by
    intro x y h
    exact p.disjoint _ _ (fun h => (by decide : (6 : Fin 12)≠10)
      (ordered_owner_injective p hf h)) _ _
      ⟨(equivalent 6 _ _).mp h.1,(equivalent 10 _ _).mp h.2⟩
  have aCenter := (equivalent 5 _ _).mpr center
  have strict := (strict_bounds (q 5) 2 2 (q 6).c (q 6).s
    (q 6).unit_normal aCenter).2
  exact CentralRightChain.lower_shift (q 6) (q 10) bn rn
    (by rw [shape,shape,p.congruent,p.congruent])
    (by rw [shape,p.congruent]; exact p.side_gt_one)
    (fun x y h => p.contained _ x y ((equivalent 10 x y).mp h))
    bMarker ((equivalent 6 _ _).mpr inner) bLow rMarker rHigh corner apart
    (by linarith only [strict,incoming])

/-- The complete negative right-wall sign is excluded. The central inner
point and incoming central axis remain explicit original obligations. -/
theorem negative_frame_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (t : ℝ) (bn : Normal (q 6).c (q 6).s)
    (rn : Normal (q 10).c t) (signed : (q 10).s=-t) (positive : 0<t)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (inner : (p.square (orderedOwner p 6)).Inside (113/50) 2)
    (incoming : upper (q 5) (q 6).c (q 6).s≤(q 6).loU) : False := by
  have rm := coded_exact p (orderedOwner p 10)
  rw [ordered_owner_code p hf 10] at rm
  have rMarker : (q 10).Inside (1543/500) 2 := (equivalent 10 _ _).mpr (by
    have h := (rm 14).mpr (by decide)
    simpa [Owns,marker] using h)
  have bLow : (q 6).Inside 3 (87/50) := (equivalent 6 _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 6, 8∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 6)
    have point := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have rHigh : (q 10).Inside 3 (12/5) := (equivalent 10 _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 10, 19∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 10)
    have point := (nat_combined_exact p (orderedOwner p 10) 19 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have em := coded_exact p (orderedOwner p 3)
  rw [ordered_owner_code p hf 3] at em
  have eRight : (q 3).Inside (1543/500) 3 := (equivalent 3 _ _).mpr (by
    have h := (em 5).mpr (by decide)
    simpa [Owns,marker] using h)
  have eTop : (q 3).Inside 3 (1543/500) := (equivalent 3 _ _).mpr (by
    have h := (em 4).mpr (by decide)
    simpa [Owns,marker] using h)
  have br : ∀ x y, ¬((q 6).Inside x y ∧ (q 10).Inside x y) :=
    fun x y h => original_apart p hf 6 10 (by decide) x y
      ⟨(equivalent 6 _ _).mp h.1,(equivalent 10 _ _).mp h.2⟩
  have er : ∀ x y, ¬((q 3).Inside x y ∧ (q 10).Inside x y) :=
    fun x y h => original_apart p hf 3 10 (by decide) x y
      ⟨(equivalent 3 _ _).mp h.1,(equivalent 10 _ _).mp h.2⟩
  have aCenter := (equivalent 5 _ _).mpr center
  have strict := (strict_bounds (q 5) 2 2 (q 6).c (q 6).s
    (q 6).unit_normal aCenter).2
  exact CentralRightChain.negative_impossible (q 6) (q 10) (q 3) t bn rn signed positive
    (by rw [shape,shape,p.congruent,p.congruent])
    (by rw [shape,p.congruent]; exact p.side_gt_one)
    (fun x y h => p.contained _ x y ((equivalent 10 x y).mp h))
    ((equivalent 6 _ _).mpr inner) bLow rMarker rHigh
    ((equivalent 3 _ _).mpr (corner_outward p hf))
    ((equivalent 3 _ _).mpr (C977RightCornerSupport.northeast_corner p hf))
    eRight eTop br er (by linarith only [strict,incoming])

/-- Both right-wall signs and all right-pair SAT axes are accounted for.
The surviving positive sign has the genuine strict inward U displacement. -/
theorem canonical_frame_shift (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (bn : Normal (q 6).c (q 6).s) (canonical : |(q 10).s|≤(q 10).c)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (inner : (p.square (orderedOwner p 6)).Inside (113/50) 2)
    (incoming : upper (q 5) (q 6).c (q 6).s≤(q 6).loU) :
    0≤(q 10).s ∧ 3*(q 10).c+2*(q 10).s<(q 10).loU := by
  by_cases sign : 0≤(q 10).s
  · have rn : Normal (q 10).c (q 10).s :=
      ⟨sign,by simpa only [abs_of_nonneg sign] using canonical,(q 10).unit_normal⟩
    exact ⟨sign,frame_shift p hf q shape equivalent bn rn center inner incoming⟩
  · have negative : (q 10).s<0 := lt_of_not_ge sign
    have rn : Normal (q 10).c (-(q 10).s) :=
      ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using canonical,
        by nlinarith only [(q 10).unit_normal]⟩
    exact False.elim (negative_frame_excludes p hf q shape equivalent (-(q 10).s)
      bn rn (by ring) (by linarith only [negative]) center inner incoming)

#print axioms corner_outward
#print axioms frame_shift
#print axioms negative_frame_excludes
#print axioms canonical_frame_shift
end N12Compact.C977CenterRightChain
