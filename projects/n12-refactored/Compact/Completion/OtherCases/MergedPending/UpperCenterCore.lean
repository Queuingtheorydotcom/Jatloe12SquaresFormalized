import Compact.Geometry.MergedLeftNegative
import Compact.Completion.OtherCases.MergedPending.UpperSectorCore

/-! Family-independent content of the upper-merged center transfer.
The antidiagonal change of coordinates transports the whole real top
wall and each foreign point. No missing right wall or split merged owner
is introduced. The canonical upper frame must be nonnegative. -/
namespace N12Compact.MergedPending
open S12 S12Pilot
set_option Elab.async false

private def antidiagonal (q : OpenSquare) : OpenSquare :=
  pullSwap (pullX (pullY q))

private theorem inside_antidiagonal (q : OpenSquare) (x y : ℝ) :
    (antidiagonal q).Inside x y↔q.Inside (4-y) (4-x) := by
  simp only [antidiagonal,inside_pullSwap,inside_pullX,inside_pullY]

theorem upper_center (H T : OpenSquare) (size : 1<H.side)
    (same : H.side=T.side) (box : InsideContainer T)
    (hc : 0<H.c) (hs : 0≤H.s) (canonical : H.s≤H.c)
    (northwest : H.Inside (33/20) (47/20))
    (northeast : H.Inside (47/20) (47/20))
    (missingTopRight : ¬H.Inside (113/50) 3)
    (missingTopLeft : ¬H.Inside (87/50) 3)
    (missingLeft : ¬H.Inside 1 (12/5))
    (topMarker : T.Inside 2 (1543/500))
    (topFar : T.Inside (8/5) 3)
    (apart : ∀ x y,¬(H.Inside x y ∧ T.Inside x y)) : H.Inside 2 2 := by
  let A := turnFrame (antidiagonal H)
  let L := antidiagonal T
  have ai (x y : ℝ) : A.Inside x y↔H.Inside (4-y) (4-x) := by
    simp only [A,turnFrame_inside,inside_antidiagonal]
  have ac : A.c=H.c := by
    dsimp only [A,antidiagonal,turnFrame,pullSwap,pullX,pullY]
    ring
  have asine : A.s= -H.s := rfl
  have center := MergedLeftNegative.point A L size same
    (container_pullSwap _ (container_pullX _ (container_pullY _ box)))
    (by simpa only [ac] using hc)
    (by rw [asine]; linarith only [hs])
    (by rw [asine,ac]; linarith only [canonical])
    (by apply (ai _ _).mpr; norm_num only; exact northeast)
    (by apply (ai _ _).mpr; norm_num only; exact northwest)
    (by
      intro own
      have point := (ai _ _).mp own
      norm_num only at point
      exact missingTopRight point)
    (by
      intro own
      have point := (ai _ _).mp own
      norm_num only at point
      exact missingTopLeft point)
    (by
      intro own
      have point := (ai _ _).mp own
      norm_num only at point
      exact missingLeft point)
    (by apply (inside_antidiagonal _ _ _).mpr; norm_num only; exact topMarker)
    (by apply (inside_antidiagonal _ _ _).mpr; norm_num only; exact topFar)
    (by
      intro x y own
      exact apart (4-y) (4-x)
        ⟨(ai x y).mp own.1,(inside_antidiagonal _ _ _).mp own.2⟩)
  have original := (ai 2 2).mp center
  norm_num only at original
  exact original

/-- A negative canonical southwest square disjoint from that strict
center can only omit it through this upper V face. Equality is retained. -/
theorem southwest_upper_face (A : OpenSquare) (hc : 0<A.c)
    (negative : A.s<0) (canonical : -A.s≤A.c)
    (marker : A.Inside (33/20) (33/20))
    (half : A.Inside 2 (3/2)) (missing : ¬A.Inside 2 2) :
    A.loV+A.side≤2*(A.c-A.s) := by
  apply le_of_not_gt
  intro high
  apply missing
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [marker.1,canonical]
  · linarith only [half.2.1,negative]
  · linarith only [marker.2.2.1,hc,negative]
  · linarith only [high]

theorem UpperData.nonnegative_residue {A H O L : OpenSquare}
    (h : UpperData A H O L) (ac : 0<A.c) (canonical : |A.s|≤A.c)
    (normalH : C977CornerCubic.Normal H.c H.s)
    (center : H.Inside 2 2) (halfBelow : A.Inside 2 (3/2)) :
    A.s<0 ∧ O.Inside 1 1 ∧ A.loV+A.side≤2*(A.c-A.s) := by
  have negative : A.s<0 := by
    apply lt_of_not_ge
    intro nonnegative
    exact h.positive_impossible
      ⟨nonnegative,by simpa only [abs_of_nonneg nonnegative] using canonical,
        A.unit_normal⟩ normalH
  have order : -A.s≤A.c := by simpa only [abs_of_neg negative] using canonical
  have normalA : C977CornerCubic.Normal A.c (-A.s) :=
    ⟨by linarith only [negative],order,by nlinarith only [A.unit_normal]⟩
  have corner : O.Inside 1 1 := by
    by_contra absent
    exact h.negative_corner_impossible normalA normalH absent
  have missing : ¬A.Inside 2 2 := fun own => h.apartUpper _ _ ⟨own,center⟩
  exact ⟨negative,corner,southwest_upper_face A ac negative order
    h.southwest halfBelow missing⟩

#print axioms upper_center
#print axioms southwest_upper_face
end N12Compact.MergedPending
