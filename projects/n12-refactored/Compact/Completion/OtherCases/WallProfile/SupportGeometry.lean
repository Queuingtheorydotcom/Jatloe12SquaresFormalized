import Compact.Geometry.ABTransverse
import Compact.Geometry.ClosedFrames

/-! Frame bookkeeping and exact support values for actual open squares.
The frame changes preserve the physical square, all strict incidences and
every support value. -/
namespace N12Compact.Completion.OtherCases.WallProfile
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

theorem upper_in_bands (q : OpenSquare) (nx ny : ℝ) :
    upper q nx ny =
      (nx*q.c+ny*q.s)*(q.loU+q.side/2)+
      (-nx*q.s+ny*q.c)*(q.loV+q.side/2)+
      q.side/2*(|nx*q.c+ny*q.s|+|-nx*q.s+ny*q.c|) := by
  unfold upper supportRadius centerX centerY
  ring

@[simp] theorem upper_turnFrame (q : OpenSquare) (nx ny : ℝ) :
    upper (turnFrame q) nx ny = upper q nx ny := by
  have radius : supportRadius (turnFrame q) nx ny = supportRadius q nx ny := by
    dsimp [supportRadius,turnFrame]
    rw [show nx*(-q.s)+ny*q.c = -nx*q.s+ny*q.c by ring,
      show -nx*q.c+ny*(-q.s) = -(nx*q.c+ny*q.s) by ring,abs_neg]
    ring
  unfold upper
  rw [turnFrame_centerX,turnFrame_centerY,radius]

private theorem nonnegative_frame (q : OpenSquare) :
    ∃ r : OpenSquare, 0 ≤ r.c ∧ 0 ≤ r.s ∧ r.side=q.side ∧
      (∀ x y, r.Inside x y ↔ q.Inside x y) ∧
      (∀ nx ny, upper r nx ny=upper q nx ny) := by
  by_cases hc : 0 ≤ q.c
  · by_cases hs : 0 ≤ q.s
    · exact ⟨q,hc,hs,rfl,by intros; rfl,by intros; rfl⟩
    · refine ⟨turnFrame q,?_,hc,by simp,by simp,by simp⟩
      dsimp [turnFrame]; linarith only [hs]
  · by_cases hs : 0 ≤ q.s
    · refine ⟨turnFrame (turnFrame (turnFrame q)),?_,?_,by simp,by simp,by simp⟩ <;>
        dsimp [turnFrame] <;> linarith only [hc,hs]
    · refine ⟨turnFrame (turnFrame q),?_,?_,by simp,by simp,by simp⟩ <;>
        dsimp [turnFrame] <;> linarith only [hc,hs]

/-- Reindex the actual faces into the first quadrant, retaining support
values as well as the strict point equivalence. No reflection is used. -/
theorem positive_frame (q : OpenSquare) :
    ∃ r : OpenSquare, 0 < r.c ∧ 0 ≤ r.s ∧ r.side=q.side ∧
      (∀ x y, r.Inside x y ↔ q.Inside x y) ∧
      (∀ nx ny, upper r nx ny=upper q nx ny) := by
  obtain ⟨r,hc,hs,shape,inside,support⟩ := nonnegative_frame q
  rcases hc.eq_or_lt with zero | positive
  · have cZero : r.c=0 := zero.symm
    have sp : 0 < r.s := by nlinarith only [r.unit_normal,hs,cZero]
    refine ⟨turnFrame (turnFrame (turnFrame r)),?_,?_,by simpa using shape,?_,?_⟩
    · simpa only [turnFrame,neg_neg] using sp
    · simp only [turnFrame,cZero,neg_zero,le_refl]
    · intro x y; simpa only [turnFrame_inside] using inside x y
    · intro nx ny; simpa only [upper_turnFrame] using support nx ny
  · exact ⟨r,positive,hs,shape,inside,support⟩

/-- Exact full support in a right-and-down target direction. -/
theorem downward_upper (q : OpenSquare) (c s : ℝ)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s) (cn : 0 ≤ c) (sn : 0 ≤ s) :
    upper q c (-s) =
      (c*q.c-s*q.s)*q.loU-(c*q.s+s*q.c)*q.loV+
        q.side*max (c*q.c-s*q.s) 0 := by
  let d := c*q.c-s*q.s
  let e := c*q.s+s*q.c
  have en : 0 ≤ e := add_nonneg (mul_nonneg cn hs) (mul_nonneg sn hc)
  have alpha : c*q.c+(-s)*q.s=d := by dsimp [d]; ring
  have beta : -c*q.s+(-s)*q.c = -e := by dsimp [e]; ring
  rw [upper_in_bands,alpha,beta,abs_neg,abs_of_nonneg en]
  change d*(q.loU+q.side/2)+(-e)*(q.loV+q.side/2)+
    q.side/2*(|d|+e)=d*q.loU-e*q.loV+q.side*max d 0
  by_cases dn : 0 ≤ d
  · rw [abs_of_nonneg dn,max_eq_left dn]
    ring
  · rw [abs_of_nonpos (le_of_not_ge dn),max_eq_right (le_of_not_ge dn)]
    ring

end N12Compact.Completion.OtherCases.WallProfile

