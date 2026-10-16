import Compact.Completion.C1092.TwoFifthsSupport
import Compact.Completion.C1092.MPPMCenteredPositiveHeightScalars
import Compact.Completion.C1092.MPPMInwardFinalPredecessor

/-! The complete actual C--W separating-axis list for a nonnegative
center-owned C. Both predecessor signs and all axial endpoints remain. -/
namespace N12Compact.C1092MPPMCenteredPositive
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092MPPMInwardFinal
set_option Elab.async false
noncomputable section

structure HeightInput (C W : OpenSquare) : Prop where
  side : 1<C.side
  same : C.side=W.side
  normal : Normal C.c C.s
  close : 99/100<C.c
  small : C.s<7/50
  center : C.Inside 0 0
  marker : C.Inside (-7/20) (-7/20)
  cap : C.loU+C.side≤(7/50)*C.c-C.s/2
  previous : PredecessorPoints W
  apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)

private theorem upward (C W : OpenSquare) (h : HeightInput C W)
    (nx ny : ℝ) (unit : nx^2+ny^2=1)
    (sep : upper C nx ny≤lower W nx ny) : 0<ny := by
  have first := (strict_bounds C _ _ nx ny unit h.marker).2
  have last := (strict_bounds W _ _ nx ny unit h.previous.marker).1
  linarith only [first,last,sep]

private theorem center_reject (C W : OpenSquare) (h : HeightInput C W)
    (nx ny : ℝ) (unit : nx^2+ny^2=1) (order : ny≤nx)
    (sep : upper C nx ny≤lower W nx ny) : False := by
  have first := (strict_bounds C _ _ nx ny unit h.center).2
  have last := (strict_bounds W _ _ nx ny unit h.previous.marker).1
  linarith only [first,last,sep,order]

theorem positive_height_axes (C W : OpenSquare) (h : HeightInput C W)
    (wn : Normal W.c W.s) :
    C.loV+C.side≤lower W (-C.s) C.c ∨ upper C (-W.s) W.c≤W.loV := by
  have wp : 0<W.c := by linarith only [(normal_bounds wn).1]
  have axes := CongruentSAT.faceSeparation_of_disjoint C W h.same h.apart
  change pairRadius C W≤|C.c*(centerX W-centerX C)+C.s*(centerY W-centerY C)| ∨
    pairRadius C W≤|-C.s*(centerX W-centerX C)+C.c*(centerY W-centerY C)| ∨
    pairRadius W C≤|W.c*(centerX W-centerX C)+W.s*(centerY W-centerY C)| ∨
    pairRadius W C≤|-W.s*(centerX W-centerX C)+W.c*(centerY W-centerY C)| at axes
  have split (nx ny radius : ℝ)
      (eq : supportRadius C nx ny+supportRadius W nx ny=radius)
      (sep : radius≤|nx*(centerX W-centerX C)+ny*(centerY W-centerY C)|) :=
    separated C W nx ny (by rwa [eq])
  rcases axes with cu|cv|wu|wv
  · rcases split _ _ _ (parallel_radius C W) cu with direct|back
    · exact False.elim (center_reject C W h _ _ C.unit_normal h.normal.2.1 direct)
    · have no := upward C W h (-C.c) (-C.s) (by nlinarith only [C.unit_normal])
        (C1092TwoFifths.Support.reverse C W _ _ back)
      exact False.elim (by linarith only [no,h.normal.1])
  · rcases split _ _ _ (transverse_radius C W) cv with direct|back
    · exact Or.inl (by simpa only [(ownV C).2] using direct)
    · have no := upward C W h C.s (-C.c) (by nlinarith only [C.unit_normal])
        (by simpa only [neg_neg] using C1092TwoFifths.Support.reverse C W _ _ back)
      exact False.elim (by linarith only [no,h.close])
  · have radius : supportRadius C W.c W.s+supportRadius W W.c W.s=pairRadius W C := by
      rw [add_comm]; exact parallel_radius W C
    rcases split _ _ _ radius wu with direct|back
    · exact False.elim (center_reject C W h _ _ W.unit_normal wn.2.1 direct)
    · have no := upward C W h (-W.c) (-W.s) (by nlinarith only [W.unit_normal])
        (C1092TwoFifths.Support.reverse C W _ _ back)
      exact False.elim (by linarith only [no,wn.1])
  · have radius : supportRadius C (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W C := by
      rw [add_comm]; exact transverse_radius W C
    rcases split _ _ _ radius wv with direct|back
    · exact Or.inr (by simpa only [(ownV W).1] using direct)
    · have no := upward C W h W.s (-W.c) (by nlinarith only [W.unit_normal])
        (by simpa only [neg_neg] using C1092TwoFifths.Support.reverse C W _ _ back)
      exact False.elim (by linarith only [no,wp])

theorem nonpositive_height_axes (C W : OpenSquare) (h : HeightInput C W)
    (wn : Normal W.c (-W.s)) :
    C.loV+C.side≤lower W (-C.s) C.c ∨
      upper C (-W.c) (-W.s)≤-(W.loU+W.side) ∨ upper C (-W.s) W.c≤W.loV := by
  have wp : 0<W.c := by linarith only [(normal_bounds wn).1]
  have axes := CongruentSAT.faceSeparation_of_disjoint C W h.same h.apart
  change pairRadius C W≤|C.c*(centerX W-centerX C)+C.s*(centerY W-centerY C)| ∨
    pairRadius C W≤|-C.s*(centerX W-centerX C)+C.c*(centerY W-centerY C)| ∨
    pairRadius W C≤|W.c*(centerX W-centerX C)+W.s*(centerY W-centerY C)| ∨
    pairRadius W C≤|-W.s*(centerX W-centerX C)+W.c*(centerY W-centerY C)| at axes
  have split (nx ny radius : ℝ)
      (eq : supportRadius C nx ny+supportRadius W nx ny=radius)
      (sep : radius≤|nx*(centerX W-centerX C)+ny*(centerY W-centerY C)|) :=
    separated C W nx ny (by rwa [eq])
  rcases axes with cu|cv|wu|wv
  · rcases split _ _ _ (parallel_radius C W) cu with direct|back
    · exact False.elim (center_reject C W h _ _ C.unit_normal h.normal.2.1 direct)
    · have no := upward C W h (-C.c) (-C.s) (by nlinarith only [C.unit_normal])
        (C1092TwoFifths.Support.reverse C W _ _ back)
      exact False.elim (by linarith only [no,h.normal.1])
  · rcases split _ _ _ (transverse_radius C W) cv with direct|back
    · exact Or.inl (by simpa only [(ownV C).2] using direct)
    · have no := upward C W h C.s (-C.c) (by nlinarith only [C.unit_normal])
        (by simpa only [neg_neg] using C1092TwoFifths.Support.reverse C W _ _ back)
      exact False.elim (by linarith only [no,h.close])
  · have radius : supportRadius C W.c W.s+supportRadius W W.c W.s=pairRadius W C := by
      rw [add_comm]; exact parallel_radius W C
    rcases split _ _ _ radius wu with direct|back
    · have no := upward C W h W.c W.s W.unit_normal direct
      exact False.elim (by linarith only [no,wn.1])
    · right; left
      have result := C1092TwoFifths.Support.reverse C W _ _ back
      simpa only [C1092TwoFifths.Support.lower_neg,(ownU W).2] using result
  · have radius : supportRadius C (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W C := by
      rw [add_comm]; exact transverse_radius W C
    rcases split _ _ _ radius wv with direct|back
    · exact Or.inr (Or.inr (by simpa only [(ownV W).1] using direct))
    · have no := upward C W h W.s (-W.c) (by nlinarith only [W.unit_normal])
        (by simpa only [neg_neg] using C1092TwoFifths.Support.reverse C W _ _ back)
      exact False.elim (by linarith only [no,wp])

end
end N12Compact.C1092MPPMCenteredPositive
