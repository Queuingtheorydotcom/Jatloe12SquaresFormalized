import Compact.Completion.OtherCases.C976NegativeTop.Faces

/-! Section 2 of C976-NEGATIVE-NE-TOP-ENDING: retain the two possible
actual square normals. The cone follows from strict owned points; supports
remain weak, so closed-square tangencies are included. -/
namespace N12Compact.Completion.OtherCases.C976NegativeTop
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
set_option Elab.async false

theorem separating_axes (N W : OpenSquare) (s : ℝ)
    (signed : N.s= -s) (cp : 0<N.c) (sp : 0<s)
    (Cn : 0≤W.c) (Sn : 0≤W.s) (sameSide : N.side=W.side)
    (elbow : N.Inside (13/50) 0) (anchor : ∃ y : ℝ,y<0 ∧ N.Inside 0 y)
    (origin : W.Inside 0 0)
    (apart : ∀ x y,¬(N.Inside x y ∧ W.Inside x y)) :
    upper W N.c N.s≤lower N N.c N.s ∨
      upper N (-W.s) W.c≤lower W (-W.s) W.c := by
  obtain ⟨y,yn,owned⟩ := anchor
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (separation : upper N nx ny≤lower W nx ny) : nx<0 ∧ 0<ny := by
    have e := strict_bounds N _ _ nx ny unit elbow
    have a := strict_bounds N _ _ nx ny unit owned
    have o := strict_bounds W _ _ nx ny unit origin
    have product : 0<ny*(-y) := by nlinarith only [a.2,o.1,separation]
    exact ⟨by nlinarith only [e.2,o.1,separation],
      (mul_pos_iff_of_pos_right (by linarith only [yn])).mp product⟩
  have reverse (nx ny : ℝ) (sep : upper W nx ny≤lower N nx ny) :
      upper N (-nx) (-ny)≤lower W (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have axes := CongruentSAT.faceSeparation_of_disjoint N W sameSide apart
  change pairRadius N W≤|N.c*(centerX W-centerX N)+N.s*(centerY W-centerY N)| ∨
    pairRadius N W≤|-N.s*(centerX W-centerX N)+N.c*(centerY W-centerY N)| ∨
    pairRadius W N≤|W.c*(centerX W-centerX N)+W.s*(centerY W-centerY N)| ∨
    pairRadius W N≤|-W.s*(centerX W-centerX N)+W.c*(centerY W-centerY N)| at axes
  have separateAxis (nx ny R : ℝ)
      (radius : supportRadius N nx ny+supportRadius W nx ny=R)
      (axis : R≤|nx*(centerX W-centerX N)+ny*(centerY W-centerY N)|) :=
    separated N W nx ny (by rwa [radius])
  rcases axes with nu | nv | wu | wv
  · rcases separateAxis _ _ _ (parallel_radius N W) nu with forward | backward
    · have bad := (cone N.c N.s N.unit_normal forward).1
      linarith only [bad,cp]
    · exact Or.inl backward
  · rcases separateAxis _ _ _ (transverse_radius N W) nv with forward | backward
    · have bad := (cone (-N.s) N.c (by nlinarith only [N.unit_normal]) forward).1
      rw [signed] at bad
      linarith only [bad,sp]
    · have bad := (cone (-(-N.s)) (-N.c) (by nlinarith only [N.unit_normal])
        (reverse _ _ backward)).2
      linarith only [bad,cp]
  · have radius : supportRadius N W.c W.s+supportRadius W W.c W.s=pairRadius W N := by
      rw [add_comm]
      exact parallel_radius W N
    rcases separateAxis _ _ _ radius wu with forward | backward
    · have bad := (cone W.c W.s W.unit_normal forward).1
      linarith only [bad,Cn]
    · have bad := (cone (-W.c) (-W.s) (by nlinarith only [W.unit_normal])
        (reverse _ _ backward)).2
      linarith only [bad,Sn]
  · have radius : supportRadius N (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W N := by
      rw [add_comm]
      exact transverse_radius W N
    rcases separateAxis _ _ _ radius wv with forward | backward
    · exact Or.inr forward
    · have bad := (cone (-(-W.s)) (-W.c) (by nlinarith only [W.unit_normal])
        (reverse _ _ backward)).1
      linarith only [bad,Sn]

#print axioms separating_axes
end N12Compact.Completion.OtherCases.C976NegativeTop
