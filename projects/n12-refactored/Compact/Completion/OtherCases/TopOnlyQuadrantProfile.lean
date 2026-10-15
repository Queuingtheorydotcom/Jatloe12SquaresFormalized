import Compact.Completion.OtherCases.TopOnlyLeftPoint

/-! The complete top-only entrance has one downward-quadrant support profile.
Its two canonical signs are related by face reindexing of the same physical
square. No order is imposed on the resulting two positive normal components. -/
namespace N12Compact.Completion.OtherCases.TopOnlyQuadrantProfile
open S12 S12Pilot
set_option Elab.async false

structure Data (q : OpenSquare) : Prop where
  cosine_pos : 0<q.c
  sine_neg : q.s<0
  lowerU : q.s≤q.loU
  lowerV : (13/50)*q.c≤q.loV
  upperU : q.loU+q.side≤q.c+(14/25)*q.s
  upperV : q.loV+q.side≤q.c-q.s

theorem frame (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (7/20) (7/20)) (top : q.Inside (13/50) 1)
    (sharp : q.Inside (21/40) (1/8))
    (missingL : ¬q.Inside 0 (13/50)) (missingP : ¬q.Inside 0 1)
    (missingC : ¬q.Inside 1 1)
    (avoid : ∀ y : ℝ,13/50≤y → y≤14/25 → ¬q.Inside 1 y) :
    ∃ r : OpenSquare,r.side=q.side ∧
      (∀ x y,r.Inside x y ↔ q.Inside x y) ∧ Data r := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have g := (same _ _).mpr top
  have y := (same _ _).mpr sharp
  have l : ¬r.Inside 0 (13/50) := fun h => missingL ((same _ _).mp h)
  have p : ¬r.Inside 0 1 := fun h => missingP ((same _ _).mp h)
  have c : ¬r.Inside 1 1 := fun h => missingC ((same _ _).mp h)
  have segment (v : ℝ) (lower : 13/50≤v) (upper : v≤14/25) : ¬r.Inside 1 v :=
    fun h => avoid v lower upper ((same _ _).mp h)
  by_cases sign : 0≤r.s
  · have order : r.s≤r.c := by simpa only [abs_of_nonneg sign] using range
    have faces := TopOnlyLeftPoint.positive_faces r side' cp sign order m g l p c
      (segment (13/50) le_rfl (by norm_num))
    have stronger := TopOnlyLeftPoint.bar_face r side' cp sign order m
      faces.1 faces.2.1 faces.2.2.2 segment
    have cu : r.c≤1 := by nlinarith only [r.unit_normal,sq_nonneg r.s,cp]
    have sp : 0<r.s := by linarith only [faces.2.1,faces.2.2.2,side',cu]
    refine ⟨turnFrame (turnFrame (turnFrame r)),by simpa only [turnFrame] using shape,?_,?_⟩
    · intro x z
      simpa only [turnFrame_inside] using same x z
    · constructor
      · simpa only [turnFrame] using sp
      · dsimp only [turnFrame]
        linarith only [cp]
      · dsimp only [turnFrame]
        linarith only [faces.2.2.2]
      · dsimp only [turnFrame]
        linarith only [faces.1]
      · dsimp only [turnFrame]
        linarith only [stronger]
      · dsimp only [turnFrame]
        linarith only [faces.2.2.1]
  · have order : -r.s≤r.c := by
      simpa only [abs_of_neg (lt_of_not_ge sign)] using range
    have faces := TopOnlyLeftPoint.negative_faces r side' cp (le_of_not_ge sign) order
      m g y l p c segment
    exact ⟨r,shape,same,cp,lt_of_not_ge sign,faces.1,faces.2.1,
      faces.2.2.1,faces.2.2.2⟩

#print axioms frame
end N12Compact.Completion.OtherCases.TopOnlyQuadrantProfile
