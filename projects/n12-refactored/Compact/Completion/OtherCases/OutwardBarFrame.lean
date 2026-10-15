import Compact.Completion.OtherCases.OutwardBarPoint

/-! The actual canonical frame and full faces underlying OutwardBarPoint.
Reindexing preserves the physical square, so the same frame supplies both
its half-angle and every support inequality in a coupled application. -/
namespace N12Compact.Completion.OtherCases.OutwardBarFrame
open S12 S12Pilot
set_option Elab.async false

theorem faces_original (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (47/20) (47/20)) (outward : q.Inside 3 (113/50))
    (missingG : ¬q.Inside (113/50) 2)
    (missingR : ¬q.Inside (1543/500) 2)
    (missingP : ¬q.Inside 3 3) (missingH : ¬q.Inside (1543/500) 3)
    (avoid : ∀ z : ℝ,113/50≤z → z≤14/5 → ¬q.Inside z 3) :
    OutwardBarPoint.Faces (q.translated 2 2) :=
  OutwardBarPoint.positive_faces (q.translated 2 2) side cp sn order
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact outward)
    (by norm_num [inside_translated_iff]; exact missingG)
    (by norm_num [inside_translated_iff]; exact missingR)
    (by norm_num [inside_translated_iff]; exact missingP)
    (by norm_num [inside_translated_iff]; exact missingH)
    (by
      intro z lower upper own
      have original : q.Inside (z+2) 3 := by
        convert (inside_translated_iff q 2 2 z 1).mp own using 1 <;> ring
      exact avoid (z+2) (by linarith only [lower]) (by linarith only [upper]) original)

theorem frame_original (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (47/20))
    (outward : q.Inside 3 (113/50)) (upper : q.Inside 3 (12/5))
    (missingG : ¬q.Inside (113/50) 2)
    (missingR : ¬q.Inside (1543/500) 2)
    (missingP : ¬q.Inside 3 3) (missingH : ¬q.Inside (1543/500) 3)
    (avoid : ∀ z : ℝ,113/50≤z → z≤14/5 → ¬q.Inside z 3) :
    ∃ r : OpenSquare,0<r.c ∧ 0≤r.s ∧ r.s≤r.c ∧ r.side=q.side ∧
      (∀ x y,r.Inside x y ↔ q.Inside x y) ∧ OutwardBarPoint.Faces (r.translated 2 2) := by
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have a := (same _ _).mpr outward
  have b := (same _ _).mpr upper
  have g : ¬r.Inside (113/50) 2 := fun h => missingG ((same _ _).mp h)
  have rr : ¬r.Inside (1543/500) 2 := fun h => missingR ((same _ _).mp h)
  have p : ¬r.Inside 3 3 := fun h => missingP ((same _ _).mp h)
  have h : ¬r.Inside (1543/500) 3 := fun h => missingH ((same _ _).mp h)
  have segment (z : ℝ) (low : 113/50≤z) (high : z≤14/5) : ¬r.Inside z 3 :=
    fun own => avoid z low high ((same _ _).mp own)
  by_cases sign : 0≤r.s
  · have order : r.s≤r.c := by simpa only [abs_of_nonneg sign] using canonical
    exact ⟨r,cp,sign,order,shape,same,
      faces_original r side' cp sign order m a g rr p h segment⟩
  · exfalso
    apply C981CompletionOutwardAnchor.nonnegative_impossible (pullY r) side' cp
      (by change 0≤ -r.s; linarith only [sign])
      (by change -r.s≤r.c; simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical)
    · norm_num [inside_pullY]; exact m
    · norm_num [inside_pullY]; exact b
    · norm_num [inside_pullY]; exact p
    · norm_num [inside_pullY]; exact rr
    · norm_num [inside_pullY]; exact g
    · intro z low high own
      exact segment z low high (by norm_num [inside_pullY] at own; exact own)

#print axioms frame_original
end N12Compact.Completion.OtherCases.OutwardBarFrame

