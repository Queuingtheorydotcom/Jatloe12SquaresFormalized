import Compact.Bridge.C977OuterWings
import Compact.Geometry.CentralRightCornerSupport

/-! Actual C977 right/top wall support bounds from the paired northeast
owner's genuine corner. These bounds retain both global A-center branches;
the explicit center-owned corollary closes one complete support-chain mode. -/
namespace N12Compact.C977RightCornerSupport
open S12 S12Pilot S12Completion.C977 FourSquareAnchors ABTransverse C977CornerCubic
set_option Elab.async false

theorem northeast_corner (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (p.square (orderedOwner p 3)).Inside 3 3 := by
  have markers := coded_exact p (orderedOwner p 3)
  rw [ordered_owner_code p hf 3] at markers
  have point := seed_points_sound (p.square (orderedOwner p 3))
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_le) (p.contained _)
    _ markers ((3,3) : ℚ×ℚ) (by decide +kernel)
  simpa using point

theorem southeast_corner (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (p.square (orderedOwner p 2)).Inside 3 1 := by
  have markers := coded_exact p (orderedOwner p 2)
  rw [ordered_owner_code p hf 2] at markers
  have point := seed_points_sound (p.square (orderedOwner p 2))
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_le) (p.contained _)
    _ markers ((3,1) : ℚ×ℚ) (by decide +kernel)
  simpa using point

theorem northwest_corner (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (p.square (orderedOwner p 4)).Inside 1 3 := by
  have markers := coded_exact p (orderedOwner p 4)
  rw [ordered_owner_code p hf 4] at markers
  have point := seed_points_sound (p.square (orderedOwner p 4))
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_le) (p.contained _)
    _ markers ((1,3) : ℚ×ℚ) (by decide +kernel)
  simpa using point

private theorem missing_corner (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (i : Fin 12) (different : i≠3) :
    ¬(p.square (orderedOwner p i)).Inside 3 3 := by
  intro point
  exact p.disjoint _ _ (fun h => different (ordered_owner_injective p hf h))
    _ _ ⟨point,northeast_corner p hf⟩

/-- All signed canonical right-wall frames obey the bound in every positive canonical
direction. The corner exclusion is an actual different owner, not a
proposed endpoint or a premise imported from a saved pose. -/
theorem right_canonical_support (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (R : OpenSquare) (canonical : |R.s|≤R.c)
    (shape : R.side=(p.square (orderedOwner p 10)).side)
    (equivalent : ∀ x y, R.Inside x y↔(p.square (orderedOwner p 10)).Inside x y)
    {c s : ℝ} (normal : Normal c s) : lower R c s≤2*(c+s)+1 := by
  have markers := coded_exact p (orderedOwner p 10)
  rw [ordered_owner_code p hf 10] at markers
  have marker : R.Inside (1543/500) 2 := (equivalent _ _).mpr (by
    have point := (markers 14).mpr (by decide)
    simpa [Owns,marker] using point)
  exact CentralRightCornerSupport.canonical_lower_support R normal canonical
    (by rw [shape,p.congruent]; exact p.side_gt_one.le)
    (fun x y h => p.contained _ x y ((equivalent x y).mp h)) marker
    (fun h => missing_corner p hf 10 (by decide) ((equivalent _ _).mp h))

theorem right_support (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (R : OpenSquare) (rn : Normal R.c R.s)
    (shape : R.side=(p.square (orderedOwner p 10)).side)
    (equivalent : ∀ x y, R.Inside x y↔(p.square (orderedOwner p 10)).Inside x y)
    {c s : ℝ} (normal : Normal c s) : lower R c s≤2*(c+s)+1 :=
  right_canonical_support p hf R
    (by simpa only [abs_of_nonneg rn.1] using rn.2.1) shape equivalent normal

/-- The top wall is represented after a coordinate swap of that square
alone. No symmetry of the complete missing-corner packing is asserted. -/
theorem top_canonical_support (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (T : OpenSquare) (canonical : |T.s|≤T.c)
    (shape : T.side=(p.square (orderedOwner p 11)).side)
    (equivalent : ∀ x y, T.Inside x y↔(p.square (orderedOwner p 11)).Inside y x)
    {c s : ℝ} (normal : Normal c s) : lower T c s≤2*(c+s)+1 := by
  have markers := coded_exact p (orderedOwner p 11)
  rw [ordered_owner_code p hf 11] at markers
  have marker : T.Inside (1543/500) 2 := (equivalent _ _).mpr (by
    have point := (markers 15).mpr (by decide)
    simpa [Owns,marker] using point)
  have box : InsideContainer T := by
    intro x y h
    have bound := p.contained _ y x ((equivalent x y).mp h)
    exact ⟨bound.2.2.1,bound.2.2.2,bound.1,bound.2.1⟩
  exact CentralRightCornerSupport.canonical_lower_support T normal canonical
    (by rw [shape,p.congruent]; exact p.side_gt_one.le) box marker
    (fun h => missing_corner p hf 11 (by decide) ((equivalent _ _).mp h))

theorem top_support (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (T : OpenSquare) (tn : Normal T.c T.s)
    (shape : T.side=(p.square (orderedOwner p 11)).side)
    (equivalent : ∀ x y, T.Inside x y↔(p.square (orderedOwner p 11)).Inside y x)
    {c s : ℝ} (normal : Normal c s) : lower T c s≤2*(c+s)+1 :=
  top_canonical_support p hf T
    (by simpa only [abs_of_nonneg tn.1] using tn.2.1) shape equivalent normal

/-- Both direction signs and both right-wall signs are covered, using
the two different actual paired corners. -/
theorem right_signed_support (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (R : OpenSquare) (canonical : |R.s|≤R.c)
    (shape : R.side=(p.square (orderedOwner p 10)).side)
    (equivalent : ∀ x y, R.Inside x y↔(p.square (orderedOwner p 10)).Inside x y)
    {c s : ℝ} (direction : |s|≤c) (unit : c^2+s^2=1) :
    lower R c s≤2*(c+s)+1 := by
  have markers := coded_exact p (orderedOwner p 10)
  rw [ordered_owner_code p hf 10] at markers
  have marker : R.Inside (1543/500) 2 := (equivalent _ _).mpr (by
    have point := (markers 14).mpr (by decide)
    simpa [Owns,marker] using point)
  have lowerMissing : ¬R.Inside 3 1 := by
    intro h
    exact p.disjoint _ _ (fun h => (by decide : (10 : Fin 12)≠2)
      (ordered_owner_injective p hf h)) _ _
      ⟨(equivalent _ _).mp h,southeast_corner p hf⟩
  exact CentralRightCornerSupport.signed_direction_support R direction unit canonical
    (by rw [shape,p.congruent]; exact p.side_gt_one.le)
    (fun x y h => p.contained _ x y ((equivalent x y).mp h)) marker
    (fun h => missing_corner p hf 10 (by decide) ((equivalent _ _).mp h)) lowerMissing

theorem top_signed_support (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (T : OpenSquare) (canonical : |T.s|≤T.c)
    (shape : T.side=(p.square (orderedOwner p 11)).side)
    (equivalent : ∀ x y, T.Inside x y↔(p.square (orderedOwner p 11)).Inside y x)
    {c s : ℝ} (direction : |s|≤c) (unit : c^2+s^2=1) :
    lower T c s≤2*(c+s)+1 := by
  have markers := coded_exact p (orderedOwner p 11)
  rw [ordered_owner_code p hf 11] at markers
  have marker : T.Inside (1543/500) 2 := (equivalent _ _).mpr (by
    have point := (markers 15).mpr (by decide)
    simpa [Owns,marker] using point)
  have box : InsideContainer T := by
    intro x y h
    have bound := p.contained _ y x ((equivalent x y).mp h)
    exact ⟨bound.2.2.1,bound.2.2.2,bound.1,bound.2.1⟩
  have lowerMissing : ¬T.Inside 3 1 := by
    intro h
    exact p.disjoint _ _ (fun h => (by decide : (11 : Fin 12)≠4)
      (ordered_owner_injective p hf h)) _ _
      ⟨(equivalent _ _).mp h,northwest_corner p hf⟩
  exact CentralRightCornerSupport.signed_direction_support T direction unit canonical
    (by rw [shape,p.congruent]; exact p.side_gt_one.le) box marker
    (fun h => missing_corner p hf 11 (by decide) ((equivalent _ _).mp h)) lowerMissing

/-- The common-axis center-owned chain is excluded for every signed
canonical B/R pair. Only the choice of support axes remains explicit. -/
theorem center_chain_signed_excludes (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12 → OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonicalB : |(q 6).s|≤(q 6).c) (canonicalR : |(q 10).s|≤(q 10).c)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (incoming : upper (q 5) (q 6).c (q 6).s≤(q 6).loU)
    (outgoing : (q 6).loU+(q 6).side≤lower (q 10) (q 6).c (q 6).s) : False := by
  have point := (equivalent 5 2 2).mpr center
  have strict := (strict_bounds (q 5) 2 2 (q 6).c (q 6).s (q 6).unit_normal point).2
  have bound := right_signed_support p hf (q 10) canonicalR
    (shape 10) (equivalent 10) canonicalB (q 6).unit_normal
  have side : 1<(q 6).side := by rw [shape,p.congruent]; exact p.side_gt_one
  linarith only [strict,bound,incoming,outgoing,side]

/-- The common-axis center-owned chain is excluded for either sign of
the actual right-wall frame. The other SAT selectors remain obligations. -/
theorem center_chain_canonical_excludes (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12 → OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (bn : Normal (q 6).c (q 6).s) (canonical : |(q 10).s|≤(q 10).c)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (incoming : upper (q 5) (q 6).c (q 6).s≤(q 6).loU)
    (outgoing : (q 6).loU+(q 6).side≤lower (q 10) (q 6).c (q 6).s) : False := by
  have point := (equivalent 5 2 2).mpr center
  have strict := (strict_bounds (q 5) 2 2 (q 6).c (q 6).s (q 6).unit_normal point).2
  have bound := right_canonical_support p hf (q 10) canonical
    (shape 10) (equivalent 10) bn
  have side : 1<(q 6).side := by rw [shape,p.congruent]; exact p.side_gt_one
  linarith only [strict,bound,incoming,outgoing,side]

/-- The actual A/B/R chain cannot use B's forward U face for both pairs
when A owns the center. Other SAT selectors and wall signs remain live. -/
theorem center_chain_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12 → OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (bn : Normal (q 6).c (q 6).s) (rn : Normal (q 10).c (q 10).s)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (incoming : upper (q 5) (q 6).c (q 6).s≤(q 6).loU)
    (outgoing : (q 6).loU+(q 6).side≤lower (q 10) (q 6).c (q 6).s) : False := by
  have point := (equivalent 5 2 2).mpr center
  have strict := (strict_bounds (q 5) 2 2 (q 6).c (q 6).s (q 6).unit_normal point).2
  have bound := right_support p hf (q 10) rn (shape 10) (equivalent 10) bn
  have side : 1<(q 6).side := by rw [shape,p.congruent]; exact p.side_gt_one
  linarith only [strict,bound,incoming,outgoing,side]

#print axioms northeast_corner
#print axioms southeast_corner
#print axioms northwest_corner
#print axioms right_canonical_support
#print axioms top_canonical_support
#print axioms right_support
#print axioms top_support
#print axioms right_signed_support
#print axioms top_signed_support
#print axioms center_chain_signed_excludes
#print axioms center_chain_canonical_excludes
#print axioms center_chain_excludes
end N12Compact.C977RightCornerSupport
