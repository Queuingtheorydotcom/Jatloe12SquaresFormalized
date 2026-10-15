import Compact.Bridge.C981DoubleWallElbows
import Compact.Geometry.FullAuxWallNegativeCycle
import Compact.Geometry.FullAuxWallPositiveCNegativeB
import Compact.Geometry.FullAuxWallRightSupport
import Compact.Geometry.FullAuxWallSharpClearance
import Compact.Geometry.FullAuxWallSmallOffset
import Compact.Geometry.FullAuxWallPositiveLowerAngleSupport
import Compact.Geometry.FullAuxWallNegativeLeft
import Compact.Geometry.FullAuxWallPositiveLeft
import Compact.Geometry.SouthwestCentralReach
import Compact.Geometry.SteepElbowTopSegment

/-! Shared original C981 representatives, in the chart
`(x,y)=(4-oldY,oldX)`. Every marker, auxiliary point, corner seed,
container and disjointness premise is derived from the original packing.
Every signed canonical frame is included. The exact right-wall clearance
and the full C/B/L support cycle close the entire original vector. -/
namespace N12Compact.C981FullAuxNegative
open S12 S12Pilot S12Completion.C981 FourSquareAnchors C977CornerCubic
open ThreeSquare ABTransverse
set_option Elab.async false

def transform : Transform := ⟨true,false,true⟩
noncomputable def chart (p : NormalizedPacking) (i : Fin 12) : OpenSquare :=
  transform.pull (owners p i)

def insidePoints : Fin 12 → List (ℚ × ℚ)
  | 3 => [(1,3)]
  | 5 => [(2,113/50),(113/50,2),(47/20,47/20)]
  | 6 => [(33/20,47/20),(1,113/50),(1,12/5)]
  | 7 => [(33/20,33/20),(87/50,2),(2,87/50)]
  | 8 => [(8/5,1)]
  | 9 => [(1543/500,2),(3,12/5)]
  | 10 => [(2,1543/500),(8/5,3)]
  | 11 => [(457/500,2),(1,8/5),(1,87/50)]
  | _ => []

def outsidePoints : Fin 12 → List (ℚ × ℚ)
  | 5 => [(47/20,33/20),(33/20,47/20),(12/5,3)]
  | 7 => [(47/20,47/20),(33/20,47/20),(47/20,33/20)]
  | 9 => [(3,87/50)]
  | _ => []

def DataCheck (v : List (Finset Nat)) : Prop :=
  (∀ i, ∀ P ∈ insidePoints i, transform.applyRat P ∈
    queryInsidePoints (ownerMasks i) 2 (v[i.val]!)) ∧
  (∀ i, ∀ P ∈ outsidePoints i, transform.applyRat P ∈
    queryOutsidePoints (ownerMasks i) 2 (v[i.val]!))
instance (v : List (Finset Nat)) : Decidable (DataCheck v) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem data_checked : DataCheck (representativeVectors[4]!) := by decide +kernel
theorem center_checked : C981DoubleWallElbows.PlacementCheck (representativeVectors[4]!) 2 := by
  decide +kernel


/-- The steep-angle entrance has two genuine alternatives: the original
long wall endpoint, or the shorter strict segment ending at 2.26. -/
def TopCheck (v : List (Finset Nat)) : Prop :=
  transform.applyRat (12/5,3) ∈ queryInsidePoints (ownerMasks 10) 2 (v[10]!) ∨
  transform.applyRat (113/50,3) ∈ queryInsidePoints (ownerMasks 10) 2 (v[10]!)

def Check (v : List (Finset Nat)) : Prop :=
  DataCheck v ∧ C981DoubleWallElbows.PlacementCheck v 2 ∧ TopCheck v

instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ (_ ∨ _)))

theorem representative3_checked : Check (representativeVectors[3]!) := by decide +kernel
theorem representative4_checked : Check (representativeVectors[4]!) := by decide +kernel

structure CanonicalFrame (p : NormalizedPacking) (i : Fin 12) where
  square : OpenSquare
  side : square.side=(chart p i).side
  inside : ∀ x y, square.Inside x y ↔ (chart p i).Inside x y
  cosine : 0<square.c
  canonical : |square.s|≤square.c

theorem canonical_exists (p : NormalizedPacking) (i : Fin 12) :
    Nonempty (CanonicalFrame p i) := by
  obtain ⟨q,hc,hs,side,inside,_⟩ := ClosedFrames.canonical_frame (chart p i)
  exact ⟨⟨q,side,inside,hc,hs⟩⟩

section CheckedVector
variable {v : List (Finset Nat)}

private theorem input (checked : Check v) (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hv : ownershipVector p=v)
    (i : Fin 12) (P : ℚ × ℚ) (member : P∈insidePoints i) :
    (chart p i).Inside P.1 P.2 := by
  have he := ownership_entry_at p _ hv i
  have aux : AuxExact (owners p i) 2 (v[i.val]!) := by
    simpa only [owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks i))
  apply (rat_inside_transform transform (owners p i) P).mpr
  exact query_inside_sound _ 2 _ _ (owners_side_gt p i) (owners_side_le p i)
    (owners_contained p i) (owners_markers p hf i) aux _ (checked.1.1 i P member)

private theorem absent (checked : Check v) (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hv : ownershipVector p=v)
    (i : Fin 12) (P : ℚ × ℚ) (member : P∈outsidePoints i) :
    ¬(chart p i).Inside P.1 P.2 := by
  have he := ownership_entry_at p _ hv i
  have aux : AuxExact (owners p i) 2 (v[i.val]!) := by
    simpa only [owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks i))
  intro point
  exact query_outside_sound _ 2 _ _ (owners_markers p hf i) aux _
    (checked.1.2 i P member) ((rat_inside_transform transform _ _).mp point)

private theorem side (p : NormalizedPacking) (i : Fin 12) :
    (chart p i).side=p.commonSide := by
  dsimp [chart]
  rw [pull_same_side]
  exact p.congruent _

private theorem box (p : NormalizedPacking) (i : Fin 12) : InsideContainer (chart p i) :=
  container_transform _ _ (owners_contained p i)

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y, ¬((chart p i).Inside x y ∧ (chart p j).Inside x y) := by
  intro x y both
  exact owners_disjoint p hf i j different _ _
    ⟨(inside_pull _ _ _ _).mp both.1,(inside_pull _ _ _ _).mp both.2⟩

private theorem center (checked : Check v) (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hv : ownershipVector p=v) : (chart p 7).Inside 2 2 := by
  have point := C981DoubleWallElbows.center _ 2 checked.2.1 p hf hv
  apply (rat_inside_transform transform (owners p 7) ((2,2) : ℚ × ℚ)).mpr
  simpa [C981DoubleWallElbows.placements,transform,Transform.applyRat] using point

private theorem bottom (checked : Check v) (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hv : ownershipVector p=v) : (chart p 7).Inside 2 (3/2) := by
  let D := chart p 7
  let L := chart p 11
  have marker : L.Inside (457/500) 2 := by
    simpa [L] using input checked p hf hv 11 (457/500,2) (by norm_num [insidePoints])
  have low : L.Inside 1 (8/5) := by
    simpa [L] using input checked p hf hv 11 (1,8/5) (by norm_num [insidePoints])
  have dn : D.Inside (87/50) 2 := by
    simpa [D] using input checked p hf hv 7 (87/50,2) (by norm_num [insidePoints])
  have bn : (chart p 6).Inside 1 (113/50) := by
    simpa using input checked p hf hv 6 (1,113/50) (by norm_num [insidePoints])
  have strong := WallLowerReach.point (pullY L)
    (by change 1<L.side; dsimp [L]; rw [side]; exact p.side_gt_one)
    (container_pullY L (box p 11))
    ((inside_pullY L _ _).mpr (by convert marker using 1 <;> norm_num))
    ((inside_pullY L _ _).mpr (by convert low using 1 <;> norm_num))
    (fun h => apart p hf 11 6 (by decide) 1 (113/50)
      ⟨by convert (inside_pullY L _ _).mp h using 1 <;> norm_num,bn⟩)
    (fun h => apart p hf 11 7 (by decide) (87/50) 2
      ⟨by convert (inside_pullY L _ _).mp h using 1 <;> norm_num,dn⟩)
  have near : L.Inside 1 (36/25) := by
    convert (inside_pullY L _ _).mp strong using 1 <;> norm_num
  have halfway : L.Inside 1 (3/2) := by
    convert inside_segment L 1 (36/25) 1 (8/5) (3/8)
      near low (by norm_num) (by norm_num) using 1 <;> norm_num
  have missingLow : ¬D.Inside 1 (3/2) :=
    fun h => apart p hf 7 11 (by decide) _ _ ⟨h,halfway⟩
  have missingHigh : ¬D.Inside 1 (8/5) :=
    fun h => apart p hf 7 11 (by decide) _ _ ⟨h,low⟩
  have reach := SouthwestCentralReach.northeast (pullX (pullY D))
    (by change 1<D.side; dsimp [D]; rw [side]; exact p.side_gt_one)
    (by rw [inside_pullX,inside_pullY]; norm_num only
        simpa [D] using input checked p hf hv 7 (2,87/50) (by norm_num [insidePoints]))
    (by rw [inside_pullX,inside_pullY]; norm_num only; exact dn)
    (by rw [inside_pullX,inside_pullY]; norm_num only
        simpa [D] using input checked p hf hv 7 (33/20,33/20) (by norm_num [insidePoints]))
    (by rw [inside_pullX,inside_pullY]; norm_num only
        simpa [D] using absent checked p hf hv 7 (47/20,47/20) (by norm_num [outsidePoints]))
    (by rw [inside_pullX,inside_pullY]; norm_num only
        simpa [D] using absent checked p hf hv 7 (33/20,47/20) (by norm_num [outsidePoints]))
    (by rw [inside_pullX,inside_pullY]; norm_num only
        simpa [D] using absent checked p hf hv 7 (47/20,33/20) (by norm_num [outsidePoints]))
    (by rw [inside_pullX,inside_pullY]; norm_num only; exact missingHigh)
    (by rw [inside_pullX,inside_pullY]; norm_num only; exact missingLow)
  rw [inside_pullX,inside_pullY] at reach
  norm_num only at reach
  exact reach

/-- The same actual escaping A is used by both signed C sectors. -/
structure EscapingFrame (p : NormalizedPacking) where
  square : OpenSquare
  side : square.side=p.commonSide
  inside : ∀ x y, square.Inside x y ↔ (chart p 5).Inside x y
  normal : Normal square.c square.s
  positive : 0<square.s
  narrow : 4*square.s≤square.c
  escape : 2*(square.c+square.s)≤square.loU
  point : square.Inside 2 (113/50)
  marker : square.Inside (47/20) (47/20)
  high : square.Inside (5/2) 3
  top : square.loV+square.side≤3*square.c-(12/5)*square.s
  excess : square.loU-2*(square.c+square.s)<square.s^2/5
  clearance : square.c*(square.loU-2*(square.c+square.s))+
    (2/5)*square.s^2-(1-square.c)*(1-square.s)<0
  sharpExcess : square.loU-2*(square.c+square.s)<square.s^2/10

/-- All normalization and narrow-A premises follow from the checked
original ownership, including the exact absent auxiliary point. -/
theorem escaping_exists (checked : Check v) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hv : ownershipVector p=v)
    : Nonempty (EscapingFrame p) := by
  let R := chart p 9
  let T := chart p 10
  obtain ⟨A,ac,as,aside,ainside,_⟩ := ClosedFrames.positive_frame (chart p 5)
  have aSide : A.side=p.commonSide := aside.trans (side p 5)
  have ha : 1<A.side := by rw [aSide]; exact p.side_gt_one
  have sameR : A.side=R.side := aSide.trans (side p 9).symm
  have sameT : A.side=T.side := aSide.trans (side p 10).symm
  have ap : A.Inside 2 (113/50) := (ainside _ _).mpr
    (by simpa using input checked p hf hv 5 (2,113/50) (by norm_num [insidePoints]))
  have aq : A.Inside (113/50) 2 := (ainside _ _).mpr
    (by simpa using input checked p hf hv 5 (113/50,2) (by norm_num [insidePoints]))
  have am : A.Inside (47/20) (47/20) := (ainside _ _).mpr
    (by simpa using input checked p hf hv 5 (47/20,47/20) (by norm_num [insidePoints]))
  have ag : ¬A.Inside (47/20) (33/20) := fun h =>
    absent checked p hf hv 5 (47/20,33/20) (by norm_num [outsidePoints]) ((ainside _ _).mp h)
  have ab : ¬A.Inside (33/20) (47/20) := fun h =>
    absent checked p hf hv 5 (33/20,47/20) (by norm_num [outsidePoints]) ((ainside _ _).mp h)
  have ar : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y) := fun x y h =>
    apart p hf 5 9 (by decide) x y ⟨(ainside _ _).mp h.1,h.2⟩
  have apartTop : ∀ x y, ¬(A.Inside x y ∧ T.Inside x y) := fun x y h =>
    apart p hf 5 10 (by decide) x y ⟨(ainside _ _).mp h.1,h.2⟩
  have missing : ¬A.Inside 2 2 := fun h =>
    apart p hf 5 7 (by decide) 2 2 ⟨(ainside _ _).mp h,center checked p hf hv⟩
  have rm : R.Inside (1543/500) 2 := by
    simpa [R] using input checked p hf hv 9 (1543/500,2) (by norm_num [insidePoints])
  have rh : R.Inside 3 (12/5) := by
    simpa [R] using input checked p hf hv 9 (3,12/5) (by norm_num [insidePoints])
  have tm : T.Inside 2 (1543/500) := by
    simpa [T] using input checked p hf hv 10 (2,1543/500) (by norm_num [insidePoints])
  have topInput (P : ℚ × ℚ)
      (member : transform.applyRat P ∈ queryInsidePoints (ownerMasks 10) 2 (v[10]!)) :
      T.Inside P.1 P.2 := by
    have he := ownership_entry_at p v hv 10
    have aux : AuxExact (owners p 10) 2 (v[10]!) := by
      simpa only [owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks 10))
    apply (rat_inside_transform transform (owners p 10) P).mpr
    exact query_inside_sound _ 2 _ _ (owners_side_gt p 10) (owners_side_le p 10)
      (owners_contained p 10) (owners_markers p hf 10) aux _ member
  have missingTop : ¬ A.Inside (12/5) 3 := fun h =>
    absent checked p hf hv 5 (12/5,3) (by norm_num [outsidePoints]) ((ainside _ _).mp h)
  have rstrong := CentralWallCenter.right_high R (by rw [←sameR]; exact ha) (box p 9) rm rh
    (by simpa [R] using absent checked p hf hv 9 (3,87/50) (by norm_num [outsidePoints]))
    (fun h => ar _ _ ⟨aq,h⟩)
  have order : A.s≤A.c := by
    apply le_of_not_gt
    intro steep
    rcases checked.2.2 with highMember | innerMember
    · have th : T.Inside (12/5) 3 := topInput _ highMember
      have h := CentralWallCenter.shallow (pullSwap A) (pullSwap T) ha sameT
        (container_pullSwap T (box p 10)) (by simpa [pullSwap] using ac.trans steep) ac.le
        (by simpa [pullSwap] using steep.le)
        ((inside_pullSwap A _ _).mpr aq) ((inside_pullSwap A _ _).mpr ap)
        ((inside_pullSwap A _ _).mpr am)
        (fun h => ab ((inside_pullSwap A _ _).mp h))
        (fun h => ag ((inside_pullSwap A _ _).mp h))
        (fun h => apartTop _ _ ⟨(inside_pullSwap A _ _).mp h,th⟩)
        (fun h => ar _ _ ⟨(inside_pullSwap A _ _).mp h,rh⟩)
        (fun h => ar _ _ ⟨(inside_pullSwap A _ _).mp h,rstrong⟩)
        ((inside_pullSwap T _ _).mpr tm) ((inside_pullSwap T _ _).mpr th)
        (fun x y h => apartTop y x ⟨(inside_pullSwap A _ _).mp h.1,(inside_pullSwap T _ _).mp h.2⟩)
      exact missing ((inside_pullSwap A _ _).mp h)
    · exact SteepElbowTopSegment.impossible A T ha ac as steep.le ap aq am
        missing (fun h => ar _ _ ⟨h,rh⟩) (fun h => ar _ _ ⟨h,rstrong⟩)
        (by simpa [T] using input checked p hf hv 10 (8/5,3) (by norm_num [insidePoints]))
        (topInput _ innerMember) apartTop
  have narrow := FullAuxWallEscape.narrow_faces_of_missing A R ha sameR (box p 9) ac as order
    ap aq am ag ab rm rh missingTop ar missing
  have bounds := FullAuxWallRightSupport.original_bounds_of_missing A R ha sameR (box p 9)
    ac as order ap aq am ag ab rm rh missingTop ar missing
  have sharp := FullAuxWallRightSupport.quadratic_of_clearance
    ⟨as,order,A.unit_normal⟩ narrow.2.1.le bounds.2
  exact ⟨⟨A,aSide,ainside,⟨as,order,A.unit_normal⟩,narrow.1,narrow.2.1.le,
    by nlinarith only [narrow.2.2.1],ap,am,narrow.2.2.2.2.2.2,
    narrow.2.2.2.2.2.1,
    by simpa only [div_eq_mul_inv,one_mul,mul_comm] using bounds.1,
    bounds.2,sharp⟩⟩

/-- Any nonpositive canonical opposite frame is impossible. -/
theorem negative_frame_impossible (checked : Check v) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hv : ownershipVector p=v)
    (d : CanonicalFrame p 7) (negative : d.square.s≤0) : False := by
  obtain ⟨⟨A,aSide,ainside,an,asp,anarrow,aescape,ap,am,ahigh,atop,asharp,aclear,atenth⟩⟩ :=
    escaping_exists checked p hf hv
  have ha : 1<A.side := by rw [aSide]; exact p.side_gt_one
  obtain ⟨B,bc,bcanon,bside,binside,_⟩ := ClosedFrames.canonical_frame (chart p 6)
  let S := -d.square.s
  have ds : d.square.s=-S := by dsimp [S]; ring
  have dn : Normal d.square.c S := ⟨by dsimp [S]; linarith only [negative],
    by dsimp [S]; simpa only [abs_of_nonpos negative] using d.canonical,
    by dsimp [S]; nlinarith only [d.square.unit_normal]⟩
  have sidesD : d.square.side=p.commonSide := d.side.trans (side p 7)
  have sidesB : B.side=p.commonSide := bside.trans (side p 6)
  apply FullAuxWallNegativeCycle.negative_opposite_impossible A d.square B S
    an asp anarrow ds dn bc
    (abs_le.mp bcanon).1 (abs_le.mp bcanon).2 ha
    (aSide.trans sidesD.symm) (sidesD.trans sidesB.symm) ap am
    ahigh atop
  · exact (d.inside _ _).mpr (center checked p hf hv)
  · exact (d.inside _ _).mpr (by simpa using input checked p hf hv 7 (33/20,33/20) (by norm_num [insidePoints]))
  · exact (d.inside _ _).mpr (bottom checked p hf hv)
  · intro h
    exact apart p hf 7 11 (by decide) _ _ ⟨(d.inside _ _).mp h,
      by simpa using input checked p hf hv 11 (1,87/50) (by norm_num [insidePoints])⟩
  · exact (binside _ _).mpr (by simpa using input checked p hf hv 6 (33/20,47/20) (by norm_num [insidePoints]))
  · exact (binside _ _).mpr (by simpa using input checked p hf hv 6 (1,113/50) (by norm_num [insidePoints]))
  · exact (binside _ _).mpr (by simpa using input checked p hf hv 6 (1,12/5) (by norm_num [insidePoints]))
  · intro h
    exact apart p hf 6 10 (by decide) _ _ ⟨(binside _ _).mp h,
      by simpa using input checked p hf hv 10 (8/5,3) (by norm_num [insidePoints])⟩
  · intro h
    exact apart p hf 6 3 (by decide) _ _ ⟨(binside _ _).mp h,
      by simpa using input checked p hf hv 3 (1,3) (by norm_num [insidePoints])⟩
  · intro h
    exact apart p hf 6 11 (by decide) _ _ ⟨(binside _ _).mp h,
      by simpa using input checked p hf hv 11 (457/500,2) (by norm_num [insidePoints])⟩
  · intro x y h
    exact apart p hf 5 7 (by decide) x y ⟨(ainside _ _).mp h.1,(d.inside _ _).mp h.2⟩
  · intro x y h
    exact apart p hf 7 6 (by decide) x y ⟨(d.inside _ _).mp h.1,(binside _ _).mp h.2⟩

/-- The exact residual: every canonical frame of the original opposite
owner has strictly positive sine. This intermediate conclusion feeds the whole signed support cycle. -/
theorem positive_residual (checked : Check v) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hv : ownershipVector p=v)
    (d : CanonicalFrame p 7) : 0<d.square.s := by
  apply lt_of_not_ge
  exact negative_frame_impossible checked p hf hv d

/-- The opposite owner is already positive by the preceding whole signed
sector. The genuine bottom, top and paired corner points then exclude
every nonpositive canonical frame of the upper central owner as well. -/
theorem negative_upper_frame_impossible (checked : Check v) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hv : ownershipVector p=v)
    (d : CanonicalFrame p 7) (b : CanonicalFrame p 6)
    (negative : b.square.s≤0) : False := by
  obtain ⟨⟨A,aSide,ainside,an,asp,anarrow,aescape,ap,am,ahigh,atop,asharp,aclear,atenth⟩⟩ :=
    escaping_exists checked p hf hv
  have ha : 1<A.side := by rw [aSide]; exact p.side_gt_one
  have dpositive := positive_residual checked p hf hv d
  have dn : Normal d.square.c d.square.s :=
    ⟨dpositive.le,by simpa only [abs_of_pos dpositive] using d.canonical,
      d.square.unit_normal⟩
  let t := -b.square.s
  have bs : b.square.s=-t := by dsimp [t]; ring
  have bn : Normal b.square.c t :=
    ⟨by dsimp [t]; linarith only [negative],
      by dsimp [t]; simpa only [abs_of_nonpos negative] using b.canonical,
      by dsimp [t]; nlinarith only [b.square.unit_normal]⟩
  have sidesD : d.square.side=p.commonSide := d.side.trans (side p 7)
  have sidesB : b.square.side=p.commonSide := b.side.trans (side p 6)
  apply FullAuxWallPositiveCNegativeB.impossible A d.square b.square t an dn bs bn ha
    (aSide.trans sidesD.symm) (sidesD.trans sidesB.symm) asp anarrow aescape
    ap am ahigh atop
  · exact (d.inside _ _).mpr (center checked p hf hv)
  · exact (d.inside _ _).mpr (by simpa using input checked p hf hv 7 (33/20,33/20) (by norm_num [insidePoints]))
  · exact (d.inside _ _).mpr (bottom checked p hf hv)
  · intro h
    exact apart p hf 7 8 (by decide) _ _ ⟨(d.inside _ _).mp h,
      by simpa using input checked p hf hv 8 (8/5,1) (by norm_num [insidePoints])⟩
  · exact (b.inside _ _).mpr (by simpa using input checked p hf hv 6 (33/20,47/20) (by norm_num [insidePoints]))
  · exact (b.inside _ _).mpr (by simpa using input checked p hf hv 6 (1,12/5) (by norm_num [insidePoints]))
  · intro h
    exact apart p hf 6 10 (by decide) _ _ ⟨(b.inside _ _).mp h,
      by simpa using input checked p hf hv 10 (8/5,3) (by norm_num [insidePoints])⟩
  · intro h
    exact apart p hf 6 3 (by decide) _ _ ⟨(b.inside _ _).mp h,
      by simpa using input checked p hf hv 3 (1,3) (by norm_num [insidePoints])⟩
  · intro x y h
    exact apart p hf 5 7 (by decide) x y ⟨(ainside _ _).mp h.1,(d.inside _ _).mp h.2⟩
  · intro x y h
    exact apart p hf 7 6 (by decide) x y ⟨(d.inside _ _).mp h.1,(b.inside _ _).mp h.2⟩

/-- The exact remaining original sector has both canonical central
frames strictly positive. The complementary signed sectors are handled below. -/
theorem upper_positive_residual (checked : Check v) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hv : ownershipVector p=v)
    (b : CanonicalFrame p 6) : 0<b.square.s := by
  obtain ⟨d⟩ := canonical_exists p 7
  apply lt_of_not_ge
  exact negative_upper_frame_impossible checked p hf hv d b

/-- Consequences of the full original row, shared by the two remaining
left-wall signs. These are derived bounds, not replacement hypotheses. -/
structure PositiveBounds (D B : OpenSquare) : Prop where
  oppositeNormal : Normal D.c D.s
  upperNormal : Normal B.c B.s
  same : D.side=B.side
  side : 1<D.side
  center : D.Inside 2 2
  southwest : D.Inside (33/20) (33/20)
  bottom : D.Inside 2 (3/2)
  left : D.Inside (6/5) (19/10)
  lowerV : D.c-(8/5)*D.s≤D.loV
  upperMarker : B.Inside (33/20) (47/20)
  upperLow : B.Inside 1 (113/50)
  upperHigh : B.Inside 1 (12/5)
  upperU : B.loU+B.side≤(8/5)*B.c+3*B.s
  upperV : B.loV+B.side≤3*B.c-B.s
  lowerU : (457/500)*B.c+2*B.s≤B.loU
  steep : 3/10<B.s
  width : 1<(343/500)*B.c+B.s
  ordered : D.s*B.c<D.c*B.s
  modes : D.loV+D.side≤lower B (-D.s) D.c ∨ upper D (-B.s) B.c≤B.loV
  offset : D.loU+D.side-2*(D.c+D.s)<1/1000
  lowerSine : 1/20<D.s
  upperSlope : 50*D.s<11*D.c
  upperSine : B.s<23/50

/-- The small displacement and narrow-angle bounds retain the actual
opposite and upper owners, with their common side and both BC selectors. -/
theorem positive_bounds (checked : Check v) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hv : ownershipVector p=v)
    (d : CanonicalFrame p 7) (b : CanonicalFrame p 6) : PositiveBounds d.square b.square := by
  obtain ⟨a⟩ := escaping_exists checked p hf hv
  have dp := positive_residual checked p hf hv d
  have bp := upper_positive_residual checked p hf hv b
  have dn : Normal d.square.c d.square.s :=
    ⟨dp.le,by simpa only [abs_of_pos dp] using d.canonical,d.square.unit_normal⟩
  have bn : Normal b.square.c b.square.s :=
    ⟨bp.le,by simpa only [abs_of_pos bp] using b.canonical,b.square.unit_normal⟩
  have ds : d.square.side=p.commonSide := d.side.trans (side p 7)
  have bs : b.square.side=p.commonSide := b.side.trans (side p 6)
  have ha : 1<a.square.side := by rw [a.side]; exact p.side_gt_one
  have hd : 1<d.square.side := by rw [ds]; exact p.side_gt_one
  have hb : 1<b.square.side := by rw [bs]; exact p.side_gt_one
  have sameAD : a.square.side=d.square.side := a.side.trans ds.symm
  have sameDB : d.square.side=b.square.side := ds.trans bs.symm
  have dCenter := (d.inside _ _).mpr (center checked p hf hv)
  have dBottom := (d.inside _ _).mpr (bottom checked p hf hv)
  have dMarker : d.square.Inside (33/20) (33/20) := (d.inside _ _).mpr
    (by simpa using input checked p hf hv 7 (33/20,33/20) (by norm_num [insidePoints]))
  have bMarker : b.square.Inside (33/20) (47/20) := (b.inside _ _).mpr
    (by simpa using input checked p hf hv 6 (33/20,47/20) (by norm_num [insidePoints]))
  have bLow : b.square.Inside 1 (113/50) := (b.inside _ _).mpr
    (by simpa using input checked p hf hv 6 (1,113/50) (by norm_num [insidePoints]))
  have bHigh : b.square.Inside 1 (12/5) := (b.inside _ _).mpr
    (by simpa using input checked p hf hv 6 (1,12/5) (by norm_num [insidePoints]))
  have axes := FullAuxWallPositiveOpposite.alternatives a.square d.square ha sameAD
    a.normal dn a.positive a.narrow a.escape a.point a.marker a.high a.top
    dMarker dCenter (fun x y h => apart p hf 5 7 (by decide) x y
      ⟨(a.inside _ _).mp h.1,(d.inside _ _).mp h.2⟩)
  have projected := FullAuxWallPositiveAngleOrder.projected_excess a.square d.square
    a.normal dn ha a.positive a.narrow a.escape a.high a.top dCenter axes
  have slope := FullAuxWallSharpClearance.opposite_slope a.square d.square a.normal dn
    ha a.narrow a.escape a.clearance a.top dCenter dBottom axes
  have slopeOld : 25*d.square.s≤9*d.square.c := by
    linarith only [slope,d.cosine]
  have ecap := FullAuxWallSharpClearance.excess a.normal a.narrow a.clearance
  have offset := FullAuxWallSmallOffset.offset a.normal dn a.narrow slopeOld ecap projected
  have coarse : d.square.loU+d.square.side-2*(d.square.c+d.square.s)<1/10 := by
    linarith only [offset]
  have bottomU := FullAuxWallPositiveReach.bottom_u a.square d.square ha hd a.normal dn
    a.positive a.narrow a.point a.high a.top dBottom axes
  have bottomV := FullAuxWallPositiveReach.bottom_face d.square dn dCenter bottomU
    (fun h => apart p hf 7 8 (by decide) _ _ ⟨(d.inside _ _).mp h,
      by simpa using input checked p hf hv 8 (8/5,1) (by norm_num [insidePoints])⟩)
  have left := FullAuxWallPositiveReach.point d.square dn hd dCenter dBottom coarse bottomV
  have modes := FullAuxWallPositiveTransverse.alternatives d.square b.square dn b.cosine
    (abs_le.mp b.canonical).1 (abs_le.mp b.canonical).2 sameDB
    dCenter left dMarker bMarker bHigh (fun x y h => apart p hf 7 6 (by decide) x y
      ⟨(d.inside _ _).mp h.1,(b.inside _ _).mp h.2⟩)
  have faces := FullAuxWallPositiveTop.faces d.square b.square dn bn hd hb dCenter
    coarse bottomV bLow bHigh bMarker modes
    (fun h => apart p hf 6 10 (by decide) _ _ ⟨(b.inside _ _).mp h,
      by simpa using input checked p hf hv 10 (8/5,3) (by norm_num [insidePoints])⟩)
    (fun h => apart p hf 6 3 (by decide) _ _ ⟨(b.inside _ _).mp h,
      by simpa using input checked p hf hv 3 (1,3) (by norm_num [insidePoints])⟩)
    (fun h => apart p hf 6 11 (by decide) _ _ ⟨(b.inside _ _).mp h,
      by simpa using input checked p hf hv 11 (457/500,2) (by norm_num [insidePoints])⟩)
  have width : 1<(343/500)*b.square.c+b.square.s := by
    linarith only [faces.1,faces.2.2.1,hb]
  have ordered := FullAuxWallPositiveAngleOrder.ordered dn bn
    (by linarith only [slope,d.cosine]) width
  have sine := FullAuxWallPositiveLowerAngleSupport.sine d.square b.square dn bn hd sameDB
    bottomV faces.1 faces.2.1 faces.2.2.2 (by linarith only [offset]) ordered.le modes
  have upperSine := FullAuxWallPositiveUpperAngleSupport.sine d.square b.square dn bn hd sameDB
    bottomV faces.1 faces.2.1
    (by linarith only [slope,(normal_bounds dn).2.1]) offset.le ordered.le modes
  exact ⟨dn,bn,sameDB,hd,dCenter,dMarker,dBottom,left,bottomV,bMarker,bLow,bHigh,
    faces.1,faces.2.1,faces.2.2.1,faces.2.2.2,width,ordered,modes,offset,sine,slope,upperSine⟩

/-- Every nonpositive left-wall frame is now excluded with the full
original B/C/L squares. Both central frames are normalized consequences
of the same row, not additional orientation hypotheses. -/
theorem negative_left_frame_impossible (checked : Check v) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hv : ownershipVector p=v)
    (l : CanonicalFrame p 11) (negative : l.square.s≤0) : False := by
  obtain ⟨d⟩ := canonical_exists p 7
  obtain ⟨b⟩ := canonical_exists p 6
  have bounds := positive_bounds checked p hf hv d b
  let r := -l.square.s
  have signed : l.square.s=-r := by dsimp [r]; ring
  have ln : Normal l.square.c r :=
    ⟨by dsimp [r]; linarith only [negative],
      by dsimp [r]; simpa only [abs_of_nonpos negative] using l.canonical,
      by dsimp [r]; nlinarith only [l.square.unit_normal]⟩
  have ls := l.side.trans (side p 11)
  have ds := d.side.trans (side p 7)
  apply FullAuxWallNegativeLeft.impossible l.square d.square b.square r signed ln
    bounds.oppositeNormal bounds.upperNormal bounds.side (ls.trans ds.symm) bounds.same
    (fun x y h => box p 11 x y ((l.inside _ _).mp h))
    (by linarith only [bounds.upperSlope,(normal_bounds bounds.oppositeNormal).2.1])
    bounds.lowerSine
  · exact (l.inside _ _).mpr (by simpa using input checked p hf hv 11 (457/500,2)
      (by norm_num [insidePoints]))
  · exact (l.inside _ _).mpr (by simpa using input checked p hf hv 11 (1,8/5)
      (by norm_num [insidePoints]))
  · exact bounds.center
  · exact bounds.bottom
  · exact bounds.left
  · exact bounds.lowerV
  · exact bounds.offset.le
  · exact bounds.upperMarker
  · exact bounds.upperHigh
  · exact bounds.upperU
  · exact bounds.upperV
  · exact bounds.steep
  · exact bounds.ordered.le
  · exact bounds.modes
  · intro x y h
    exact apart p hf 11 7 (by decide) x y
      ⟨(l.inside _ _).mp h.1,(d.inside _ _).mp h.2⟩
  · intro x y h
    exact apart p hf 11 6 (by decide) x y
      ⟨(l.inside _ _).mp h.1,(b.inside _ _).mp h.2⟩

/-- A useful intermediate signed reduction for the original row. -/
theorem left_positive_residual (checked : Check v) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hv : ownershipVector p=v)
    (l : CanonicalFrame p 11) : 0<l.square.s := by
  apply lt_of_not_ge
  exact negative_left_frame_impossible checked p hf hv l

/-- The complementary positive left-wall orientation closes with the
same original central frames, exact displacement and common side. -/
theorem positive_left_frame_impossible (checked : Check v) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hv : ownershipVector p=v)
    (l : CanonicalFrame p 11) (positive : 0≤l.square.s) : False := by
  obtain ⟨d⟩ := canonical_exists p 7
  obtain ⟨b⟩ := canonical_exists p 6
  have bounds := positive_bounds checked p hf hv d b
  have ln : Normal l.square.c l.square.s :=
    ⟨positive,by simpa only [abs_of_nonneg positive] using l.canonical,l.square.unit_normal⟩
  have ls := l.side.trans (side p 11)
  have ds := d.side.trans (side p 7)
  apply FullAuxWallPositiveLeft.impossible l.square d.square b.square ln
    bounds.oppositeNormal bounds.upperNormal bounds.side (ls.trans ds.symm) bounds.same
    (fun x y h => box p 11 x y ((l.inside _ _).mp h))
    (by linarith only [bounds.upperSlope,(normal_bounds bounds.oppositeNormal).2.1])
    bounds.lowerSine
  · exact (l.inside _ _).mpr (by simpa using input checked p hf hv 11 (457/500,2)
      (by norm_num [insidePoints]))
  · exact (l.inside _ _).mpr (by simpa using input checked p hf hv 11 (1,8/5)
      (by norm_num [insidePoints]))
  · exact bounds.center
  · exact bounds.bottom
  · exact bounds.left
  · exact bounds.lowerV
  · exact bounds.offset.le
  · exact bounds.upperHigh
  · exact bounds.upperU
  · exact bounds.upperV
  · exact bounds.lowerU
  · exact bounds.steep
  · exact bounds.ordered.le
  · exact bounds.modes
  · intro x y h
    exact apart p hf 11 7 (by decide) x y
      ⟨(l.inside _ _).mp h.1,(d.inside _ _).mp h.2⟩
  · intro x y h
    exact apart p hf 11 6 (by decide) x y
      ⟨(l.inside _ _).mp h.1,(b.inside _ _).mp h.2⟩

/-- The full shared signed support cycle closes every original vector
whose entrance was established by the finite query check. -/
theorem excludes (checked : Check v) : ExcludesVector v := by
  intro p hf hv
  obtain ⟨l⟩ := canonical_exists p 11
  exact positive_left_frame_impossible checked p hf hv l
    (left_positive_residual checked p hf hv l).le

end CheckedVector

theorem representative3_excluded : ExcludesVector (representativeVectors[3]!) :=
  excludes representative3_checked

/-- The original row-4 public theorem keeps its exact statement. -/
theorem representative4_excluded : ExcludesVector (representativeVectors[4]!) :=
  excludes representative4_checked

#print axioms escaping_exists
#print axioms negative_frame_impossible
#print axioms positive_residual
#print axioms negative_upper_frame_impossible
#print axioms upper_positive_residual
#print axioms positive_bounds
#print axioms negative_left_frame_impossible
#print axioms left_positive_residual
#print axioms positive_left_frame_impossible
#print axioms representative3_excluded
#print axioms representative4_excluded
end N12Compact.C981FullAuxNegative
