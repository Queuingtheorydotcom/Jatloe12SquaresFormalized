import Compact.Geometry.C868UpperPointNegative
import Compact.Geometry.SouthwestNegativeCorner
import Compact.Completion.CommonCases.OriginalOwners

/-! A local upper-merged reduction with literal physical inputs. The two
upper markers stay in one square H. The foreign singleton bars stay in
their respective owners O and L. The final negative-upper sector and the
negative-lower/corner-owned sector are retained explicitly. Source only. -/
namespace N12Compact.MergedPending
open S12 S12Pilot C977CornerCubic CommonCases.OriginalOwners
set_option Elab.async false

structure UpperData (A H O L : OpenSquare) : Prop where
  size : 1<A.side
  sameUpper : A.side=H.side
  sameBottom : O.side=A.side
  bottomBox : InsideContainer O
  southwest : A.Inside (33/20) (33/20)
  south : A.Inside 2 (87/50)
  west : A.Inside (87/50) 2
  halfWest : A.Inside (3/2) 2
  northwest : H.Inside (33/20) (47/20)
  northeast : H.Inside (47/20) (47/20)
  bottomMarker : O.Inside 1 (457/500)
  bottomOffrow : O.Inside (187/100) (19/25)
  bottomBar : ∀ x : ℝ,28/25≤x → x≤87/50 → O.Inside x 1
  leftBar : ∀ y : ℝ,28/25≤y → y≤87/50 → L.Inside 1 y
  bottomMissing : ¬O.Inside 2 (457/500)
  apartUpper : ∀ x y,¬(A.Inside x y ∧ H.Inside x y)
  apartBottom : ∀ x y,¬(O.Inside x y ∧ A.Inside x y)
  apartLeft : ∀ x y,¬(A.Inside x y ∧ L.Inside x y)
  missingTop : ¬H.Inside (87/50) 3

theorem UpperData.positive_impossible {A H O L : OpenSquare}
    (h : UpperData A H O L) (an : Normal A.c A.s) (hn : Normal H.c H.s) : False := by
  apply h.missingTop
  exact C868UpperPoint.point A H an hn h.sameUpper h.size h.southwest
    h.south h.west h.northwest h.northeast
    (fun own => h.apartBottom _ _
      ⟨h.bottomBar _ (by norm_num) (by norm_num),own⟩)
    (fun own => h.apartLeft _ _
      ⟨own,h.leftBar _ (by norm_num) (by norm_num)⟩) h.apartUpper

theorem UpperData.negative_corner_impossible {A H O L : OpenSquare}
    (h : UpperData A H O L) (an : Normal A.c (-A.s)) (hn : Normal H.c H.s)
    (corner : ¬O.Inside 1 1) : False := by
  have center := SouthwestNegativeCorner.point O A L (-A.s) (by ring)
    an h.sameBottom h.size h.bottomBox h.bottomMarker
    (h.bottomBar _ le_rfl (by norm_num)) h.bottomOffrow corner h.bottomMissing
    h.southwest h.south h.west h.halfWest
    (h.leftBar _ le_rfl (by norm_num)) (h.leftBar _ (by norm_num) le_rfl)
    h.apartBottom h.apartLeft
  exact h.missingTop (C868UpperPointNegative.point A H an hn h.sameUpper h.size
    h.southwest h.south h.west center h.northwest h.northeast h.apartUpper)

theorem UpperData.reframe {A H O L : OpenSquare} (h : UpperData A H O L)
    (a b : OpenSquare) (sa : a.side=A.side) (sb : b.side=H.side)
    (ia : ∀ x y,a.Inside x y↔A.Inside x y)
    (ib : ∀ x y,b.Inside x y↔H.Inside x y) : UpperData a b O L := by
  refine ⟨?_,?_,?_,h.bottomBox,(ia _ _).mpr h.southwest,
    (ia _ _).mpr h.south,(ia _ _).mpr h.west,(ia _ _).mpr h.halfWest,
    (ib _ _).mpr h.northwest,(ib _ _).mpr h.northeast,
    h.bottomMarker,h.bottomOffrow,h.bottomBar,h.leftBar,h.bottomMissing,?_,?_,?_,?_⟩
  · simpa only [sa] using h.size
  · exact sa.trans (h.sameUpper.trans sb.symm)
  · exact h.sameBottom.trans sa.symm
  · intro x y points
    exact h.apartUpper x y ⟨(ia x y).mp points.1,(ib x y).mp points.2⟩
  · intro x y points
    exact h.apartBottom x y ⟨points.1,(ia x y).mp points.2⟩
  · intro x y points
    exact h.apartLeft x y ⟨(ia x y).mp points.1,points.2⟩
  · exact fun own => h.missingTop ((ib _ _).mp own)

/-- Canonicalization is a change of the description of A and H, not a
packing symmetry. The indicated alternatives are the honest residue. -/
def UpperResidue (A H O : OpenSquare) : Prop :=
  ∃ a b : OpenSquare,
    0<a.c ∧ |a.s|≤a.c ∧ 0<b.c ∧ |b.s|≤b.c ∧
    a.side=A.side ∧ b.side=H.side ∧
    (∀ x y,a.Inside x y↔A.Inside x y) ∧
    (∀ x y,b.Inside x y↔H.Inside x y) ∧
    (b.s<0 ∨ a.s<0 ∧ O.Inside 1 1)

theorem UpperData.remaining {A H O L : OpenSquare} (h : UpperData A H O L) :
    UpperResidue A H O := by
  classical
  obtain ⟨a,ac,asc,sa,ia,_⟩ := ClosedFrames.canonical_frame A
  obtain ⟨b,bc,bsc,sb,ib,_⟩ := ClosedFrames.canonical_frame H
  have d := h.reframe a b sa sb ia ib
  refine ⟨a,b,ac,asc,bc,bsc,sa,sb,ia,ib,?_⟩
  by_cases bn : 0≤b.s
  · have normalB : Normal b.c b.s :=
      ⟨bn,by simpa only [abs_of_nonneg bn] using bsc,b.unit_normal⟩
    by_cases an : 0≤a.s
    · exact (d.positive_impossible
        ⟨an,by simpa only [abs_of_nonneg an] using asc,a.unit_normal⟩ normalB).elim
    · have negative : a.s<0 := lt_of_not_ge an
      refine Or.inr ⟨negative,?_⟩
      by_contra missing
      exact d.negative_corner_impossible
        ⟨by linarith only [negative],
          by simpa only [abs_of_neg negative] using asc,
          by nlinarith only [a.unit_normal]⟩ normalB missing
  · exact Or.inl (lt_of_not_ge bn)

#print axioms UpperData.remaining
end N12Compact.MergedPending
