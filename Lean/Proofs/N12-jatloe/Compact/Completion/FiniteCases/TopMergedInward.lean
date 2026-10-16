import Compact.Completion.CommonCases.OutwardPoint
import Compact.Completion.FiniteCases.WallHighFromMarker
import Compact.Completion.FiniteCases.TopElbowCompletion
import Compact.Completion.C981.UpperPoint
import S12.Convex

/-! One all-orientation ending for the merged NW/top owner's incoming F5
alternative. The right segment and corner exclusions are premises to be
supplied by their actual owners. No remaining ownership alternative is
silently dropped, and this lemma alone is not a whole C975 exclusion. -/
namespace N12Compact.FiniteCases.TopMergedInward
open S12 S12Pilot
set_option Elab.async false

private def commonTriangle : TriangleCertificate :=
  ⟨(2,113/50),(2,1543/500),(33/20,47/20),(199/100,123/50),3455/14042,1/35⟩

private theorem triangle_checked : commonTriangle.Check := by decide +kernel

theorem impossible (h n : OpenSquare) (sideN : 1<n.side)
    (hMarker : h.Inside (33/20) (47/20))
    (hTop : h.Inside 2 (1543/500)) (hInward : h.Inside 2 (113/50))
    (nMarker : n.Inside (47/20) (47/20))
    (nOutward : n.Inside (12/5) 3)
    (nOptions : n.Inside (113/50) 2 ∨ n.Inside (113/50) 3)
    (nCornerMissing : ¬n.Inside 3 3)
    (nHighCornerMissing : ¬n.Inside 3 (1543/500))
    (nAvoidRight : ∀ z : ℝ, 113/50≤z → z≤14/5 → ¬n.Inside 3 z)
    (apart : ∀ x y, ¬(h.Inside x y ∧ n.Inside x y)) : False := by
  have missingF : ¬n.Inside 2 (113/50) := fun owned => apart _ _ ⟨hInward,owned⟩
  have missingTop : ¬n.Inside 2 (1543/500) := fun owned => apart _ _ ⟨hTop,owned⟩
  have missingG : ¬n.Inside (113/50) 2 := by
    intro inward
    let turn : Transform := ⟨true,true,false⟩
    apply N12Compact.C981CompletionOutwardAnchor.impossible (turn.pull n)
      (by simpa only [pull_same_side] using sideN)
    · norm_num [turn,Transform.pull,inside_pullSwap,inside_pullX]
      exact nMarker
    · norm_num [turn,Transform.pull,inside_pullSwap,inside_pullX]
      exact inward
    · norm_num [turn,Transform.pull,inside_pullSwap,inside_pullX]
      exact nOutward
    · norm_num [turn,Transform.pull,inside_pullSwap,inside_pullX]
      exact nCornerMissing
    · norm_num [turn,Transform.pull,inside_pullSwap,inside_pullX]
      exact missingTop
    · norm_num [turn,Transform.pull,inside_pullSwap,inside_pullX]
      exact missingF
    · intro z lo hi own
      exact nAvoidRight z lo hi
        (by norm_num [turn,Transform.pull,inside_pullSwap,inside_pullX] at own; exact own)
  have elbow : n.Inside (113/50) 3 := nOptions.resolve_left missingG
  have pointN := N12Compact.CommonCases.OutwardPoint.point_original (pullSwap n) sideN
    (by norm_num [inside_pullSwap]; exact nMarker)
    (by norm_num [inside_pullSwap]; exact elbow)
    (by norm_num [inside_pullSwap]; exact nOutward)
    (by norm_num [inside_pullSwap]; exact missingF)
    (by norm_num [inside_pullSwap]; exact missingTop)
    (by norm_num [inside_pullSwap]; exact nCornerMissing)
    (by norm_num [inside_pullSwap]; exact nHighCornerMissing)
    (by
      intro z lo hi own
      exact nAvoidRight z lo hi (by simpa only [inside_pullSwap] using own))
  norm_num [inside_pullSwap] at pointN
  have pointH := triangle_certificate_sound commonTriangle triangle_checked h
    (by norm_num [commonTriangle]; exact hInward)
    (by norm_num [commonTriangle]; exact hTop)
    (by norm_num [commonTriangle]; exact hMarker)
  norm_num [commonTriangle] at pointH
  exact apart _ _ ⟨pointH,pointN⟩

#print axioms impossible

/-- The same incoming merged-top alternative has a shorter genuine ending.
The actual right wall supplies 2.56 in both of its inward-label alternatives;
no singleton corner seed or whole right segment up to 2.8 is required. -/
theorem short_impossible (h n r : OpenSquare)
    (sideN : 1<n.side) (sideR : 1<r.side) (boxR : InsideContainer r)
    (hTop : h.Inside 2 (1543/500)) (hInward : h.Inside 2 (113/50))
    (nMarker : n.Inside (47/20) (47/20))
    (nOutward : n.Inside (12/5) 3)
    (nOptions : n.Inside (113/50) 2 ∨ n.Inside (113/50) 3)
    (nCornerMissing : ¬n.Inside 3 3)
    (rMarker : r.Inside (1543/500) 2) (rHigh : r.Inside 3 (12/5))
    (rLowMissing : ¬r.Inside 3 (87/50))
    (apartHN : ∀ x y, ¬(h.Inside x y ∧ n.Inside x y))
    (apartNR : ∀ x y, ¬(n.Inside x y ∧ r.Inside x y)) : False := by
  have hLow : h.Inside 2 (12/5) := by
    have point := inside_segment h 2 (113/50) 2 (1543/500) (70/413)
      hInward hTop (by norm_num) (by norm_num)
    norm_num at point; exact point
  have hHigh : h.Inside 2 3 := by
    have point := inside_segment h 2 (113/50) 2 (1543/500) (370/413)
      hInward hTop (by norm_num) (by norm_num)
    norm_num at point; exact point
  have leftMissing : ¬n.Inside 2 (12/5) := fun point => apartHN _ _ ⟨hLow,point⟩
  have upperMissing : ¬n.Inside 2 3 := fun point => apartHN _ _ ⟨hHigh,point⟩
  have rightMissing : ¬n.Inside 3 (12/5) := fun point => apartNR _ _ ⟨point,rHigh⟩
  have nTop : n.Inside (113/50) 3 := by
    rcases nOptions with inward | outward
    · exact TopElbowCompletion.point n sideN nMarker nOutward inward leftMissing rightMissing
    · exact outward
  have rStrong : r.Inside 3 (64/25) := by
    have point := WallHighFromMarker.point (pullX r) sideR (container_pullX r boxR)
      (by norm_num [inside_pullX]; exact rMarker)
      (by norm_num [inside_pullX]; exact rHigh)
      (by norm_num [inside_pullX]; exact rLowMissing)
      (by norm_num [inside_pullX]; exact (fun own => apartNR _ _ ⟨nMarker,own⟩))
    norm_num [inside_pullX] at point; exact point
  have pointN := C981CompletionUpperPoint.point n sideN nMarker nTop
    leftMissing upperMissing rightMissing nCornerMissing
    (fun point => apartNR _ _ ⟨point,rStrong⟩)
  have pointH : h.Inside 2 (131/50) := by
    have point := inside_segment h 2 (113/50) 2 (1543/500) (180/413)
      hInward hTop (by norm_num) (by norm_num)
    norm_num at point; exact point
  exact apartHN _ _ ⟨pointH,pointN⟩

#print axioms short_impossible
end N12Compact.FiniteCases.TopMergedInward
