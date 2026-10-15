import Compact.Bridge.C977NortheastShift
import Compact.Bridge.C977CenterCornerAlternatives

/-! The all-angle paired-corner ending forces the actual wall midpoints.
No central orientation, incoming axis, or missing-corner root is assumed. -/
namespace N12Compact.C977WallMiddle
open S12 S12Pilot S12Completion.C977 FourSquareAnchors C977CornerCubic
set_option Elab.async false

theorem right_frame_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, |(q i).s|≤(q i).c) : (q 10).Inside 3 2 := by
  by_cases sign : 0≤(q 10).s
  · have rn : Normal (q 10).c (q 10).s :=
      ⟨sign,by simpa only [abs_of_nonneg sign] using canonical 10,(q 10).unit_normal⟩
    by_contra missing
    have markers := coded_exact p (orderedOwner p 10)
    rw [ordered_owner_code p hf 10] at markers
    have marker : (q 10).Inside (1543/500) 2 := (equivalent 10 _ _).mpr (by
      have point := (markers 14).mpr (by decide)
      simpa [Owns,marker] using point)
    have high : (q 10).Inside 3 (12/5) := (equivalent 10 _ _).mpr (by
      have check : ∀ owned∈pruningDomain4 10, 19∈owned := by decide
      have owned := check _ (pruned_auxiliary_domain_actual p hf 10)
      have point := (nat_combined_exact p (orderedOwner p 10) 19 (by decide)).mpr owned
      simpa [auxPoints,fPoints,gPoints] using point)
    exact C977NortheastShift.right_shift_excludes p hf q shape equivalent
      (canonical 3) (canonical 11) rn
      (CentralRightCornerAlternatives.positive_wall_missing (q 10) rn marker high missing)
  · have rn : Normal (q 10).c (-(q 10).s) :=
      ⟨by linarith only [sign],
        by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical 10,
        by nlinarith only [(q 10).unit_normal]⟩
    exact C977CenterCornerAlternatives.negative_wall_point p hf (q 10) (-(q 10).s)
      rn (by ring) (shape 10) (equivalent 10)

/-- This is a point of the original physical owner, not a normalized
orientation hypothesis to be supplied by the caller. -/
theorem right_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (p.square (orderedOwner p 10)).Inside 3 2 := by
  classical
  choose q positive canonical shape equivalent closed using
    (fun i : Fin 12 => ClosedFrames.canonical_frame (p.square (orderedOwner p i)))
  exact (equivalent 10 3 2).mp (right_frame_point p hf q shape equivalent canonical)

theorem top_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (p.square (orderedOwner p 11)).Inside 2 3 := by
  have index : orderedOwner (transposePacking p) 10=orderedOwner p 11 := by
    apply markerCode_injective (transposePacking p)
    rw [ordered_owner_code _ (transpose_family p hf) 10,transpose_code p hf,
      ordered_owner_code p hf 11]
    decide
  have point := right_point (transposePacking p) (transpose_family p hf)
  rw [index,transpose_inside] at point
  exact point

#print axioms right_point
#print axioms top_point
end N12Compact.C977WallMiddle
