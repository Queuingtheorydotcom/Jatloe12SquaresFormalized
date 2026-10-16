import Compact.Completion.FiniteCases.C972UpperReduction
import Compact.Completion.C981.UpperPoint
import S12.ShortCluster.Projections

/-! The actual northwest square must own F5. If it omitted F5, the
whole left bar forces a point also supplied by the northeast square's
top origin and outward pair. No top boundary square is introduced. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private theorem upper_anchor_canonical (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (canonical : |q.s|≤q.c)
    (marker : q.Inside (7/20) (7/20)) (origin : q.Inside 0 1)
    (outward : q.Inside (2/5) 1) (corner : ¬q.Inside 1 1) :
    q.Inside (1/10) (3/5) := by
  by_cases sign : 0≤q.s
  · have order : q.s≤q.c := by simpa only [abs_of_nonneg sign] using canonical
    have lowU : q.loU<q.c+q.s := by linarith only [marker.1,cp,sign]
    have lowV : q.loV< -q.s+q.c := by linarith only [marker.2.2.1,order]
    have highV : -q.s+q.c<q.loV+q.side := by linarith only [origin.2.2.2,sign]
    have face : q.loU+q.side≤q.c+q.s := by
      apply le_of_not_gt
      intro highU
      apply corner
      simpa only [OpenSquare.Inside,InBands,mul_one] using
        And.intro lowU (And.intro highU (And.intro lowV highV))
    have short := (short_projections q (9/10) (2/5) (by norm_num)).2.1
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [face,side,short]
    · linarith only [outward.2.1,cp,sign]
    · linarith only [marker.2.2.1,cp,sign]
    · linarith only [origin.2.2.2,cp,sign]
  · have negative : q.s≤0 := (lt_of_not_ge sign).le
    have order : -q.s≤q.c := by simpa only [abs_of_nonpos negative] using canonical
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [origin.1,cp,negative]
    · linarith only [marker.2.1,cp,negative]
    · linarith only [marker.2.2.1,order]
    · linarith only [origin.2.2.2,cp,order]

/-- A local northeast point, valid for both canonical signs and the
diagonal endpoints. The omitted corner is the actual paired NE corner. -/
theorem northeast_upper_anchor (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (47/20)) (origin : q.Inside 2 3)
    (outward : q.Inside (12/5) 3) (corner : ¬q.Inside 3 3) :
    q.Inside (21/10) (13/5) := by
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame (q.translated 2 2)
  have localPoint := upper_anchor_canonical r (by rw [shape]; exact side)
    cp canonical
    (by apply (same _ _).mpr; norm_num [inside_translated_iff]; exact marker)
    (by apply (same _ _).mpr; norm_num [inside_translated_iff]; exact origin)
    (by apply (same _ _).mpr; norm_num [inside_translated_iff]; exact outward)
    (by intro own; apply corner; have own' := (same _ _).mp own
        norm_num [inside_translated_iff] at own'; exact own')
  have actual := (same _ _).mp localPoint
  norm_num [inside_translated_iff] at actual
  exact actual

/-- The optional NW forward auxiliary is compulsory. The contradiction
uses one strict point in each of two distinct original squares. -/
theorem northwest_forward (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 8).Inside 2 (113/50) := by
  by_contra missing
  have origin := (remaining_alternative p hf).resolve_left missing
  have h := fixed p hf
  have northwest := CommonCases.NorthwestSharpPoint.upper_point_original _ (side p 8)
    h.northwestMarker (northwest_pair p hf).1 (northwest_pair p hf).2 missing
    (foreign p hf 8 7 (by decide) _ _ origin)
    (foreign p hf 8 4 (by decide) _ _ h.northwestCorner) (missing_top p hf 8)
    (fun y low high => foreign p hf 8 9 (by decide) _ _ (left_bar p hf y low high))
  have northeast := northeast_upper_anchor _ (side p 7) h.northeastMarker origin
    (northeast_f7 p hf) (foreign p hf 7 3 (by decide) _ _ h.northeastCorner)
  exact apart p hf 8 7 (by decide) _ _ ⟨northwest,northeast⟩

/-- NW's compulsory F5 cannot be joined to the top origin: the resulting
strict segment would meet the NE square's all-angle upper point. -/
theorem northwest_missing_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ¬(owners p 8).Inside 2 3 := by
  intro origin
  have h := fixed p hf
  have vertical (y : ℝ) (low : 113/50≤y) (high : y≤3) : (owners p 8).Inside 2 y := by
    let t := (50/37)*(y-113/50)
    have tn : 0≤t := by dsimp only [t]; linarith only [low]
    have tu : t≤1 := by dsimp only [t]; linarith only [high]
    convert inside_segment (owners p 8) 2 (113/50) 2 3 t
      (northwest_forward p hf) origin tn tu using 1 <;> dsimp only [t] <;> ring
  have point := C981CompletionUpperPoint.point _ (side p 7) h.northeastMarker
    (northeast_g7 p hf)
    (foreign p hf 7 8 (by decide) _ _ (vertical _ (by norm_num) (by norm_num)))
    (foreign p hf 7 8 (by decide) _ _ origin)
    (foreign p hf 7 11 (by decide) _ _ h.rightG9)
    (foreign p hf 7 3 (by decide) _ _ h.northeastCorner)
    (foreign p hf 7 11 (by decide) _ _ (right_reach p hf))
  exact apart p hf 7 8 (by decide) _ _ ⟨point,vertical _ (by norm_num) (by norm_num)⟩

end
#print axioms northwest_forward
#print axioms northwest_missing_origin
end N12Compact.FiniteCases.C972
