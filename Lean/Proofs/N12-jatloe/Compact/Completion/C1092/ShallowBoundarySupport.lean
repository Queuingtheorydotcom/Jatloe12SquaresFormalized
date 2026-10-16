import Compact.Completion.C1092.ShallowWidths
import Compact.Geometry.ABTransverse
import S12.SquareSupportBase

/-! Actual-square boundary support bounds for the shallow wall order.
Every face direction is an original square normal; both real container
walls are inequalities on the full actual square. -/
namespace N12Compact.C1092ShallowBoundarySupport
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
set_option Elab.async false

noncomputable def width0 (Q : OpenSquare) : ℝ := |Q.c|+|Q.s|

def FaceNormal (Q : OpenSquare) (nx ny : ℝ) : Prop :=
  (nx=Q.c ∧ ny=Q.s) ∨ (nx=-Q.c ∧ ny=-Q.s) ∨
    (nx=-Q.s ∧ ny=Q.c) ∨ (nx=Q.s ∧ ny=-Q.c)

theorem bottom_center (Q : OpenSquare)
    (wall : ∀ x y, Q.Inside x y → -2≤y) :
    -2+Q.side*width0 Q/2≤centerY Q := by
  have bound := square_support_bound Q 0 (-1) 2
    (by intro x y h; have hy := wall x y h; linarith only [hy])
  have radius : squareRadius Q 0 (-1)=Q.side*width0 Q/2 := by
    dsimp [squareRadius,width0]
    simp only [zero_mul,zero_add,neg_mul,one_mul,abs_neg]
    ring_nf
    simp only [abs_neg]
  rw [radius] at bound
  linarith only [bound]

theorem left_center (Q : OpenSquare)
    (wall : ∀ x y, Q.Inside x y → -2≤x) :
    -2+Q.side*width0 Q/2≤centerX Q := by
  have bound := square_support_bound Q (-1) 0 2
    (by intro x y h; have hx := wall x y h; linarith only [hx])
  have radius : squareRadius Q (-1) 0=Q.side*width0 Q/2 := by
    dsimp [squareRadius,width0]
    simp only [zero_mul,mul_zero,add_zero,zero_add,neg_mul,neg_neg,one_mul,abs_neg]
    ring
  rw [radius] at bound
  linarith only [bound]

theorem width_bounds (Q : OpenSquare) {c s : ℝ} (normal : Normal c s) :
    Q.side*(1+c*(c+s))/2≤c*(Q.side*width0 Q/2)+supportRadius Q (-s) c ∧
      Q.side*(1+s*(c+s))/2≤s*(Q.side*width0 Q/2)+supportRadius Q (-s) c := by
  have widths := C1092ShallowWidths.signed_widths normal Q.c Q.s Q.unit_normal
  have first : |c*Q.s-s*Q.c|=|(-s)*Q.c+c*Q.s| := by congr 1; ring
  have last : |c*Q.c+s*Q.s|=|-(-s)*Q.s+c*Q.c| := by congr 1; ring
  have scale := (div_pos Q.side_pos (by norm_num : (0:ℝ)<2)).le
  have a := mul_le_mul_of_nonneg_left widths.1 scale
  have b := mul_le_mul_of_nonneg_left widths.2 scale
  rw [first,last] at a b
  constructor
  · dsimp [width0,supportRadius]
    convert a using 1 <;> ring
  · dsimp [width0,supportRadius]
    convert b using 1 <;> ring

theorem face_width (Q : OpenSquare) (nx ny : ℝ) (face : FaceNormal Q nx ny) :
    width0 Q=|nx|+|ny| := by
  rcases face with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    simp only [width0,abs_neg,add_comm]

private theorem radius_neg (Q : OpenSquare) (nx ny : ℝ) :
    supportRadius Q (-nx) (-ny)=supportRadius Q nx ny := by
  dsimp [supportRadius]
  rw [show (-nx)*Q.c+(-ny)*Q.s=-(nx*Q.c+ny*Q.s) by ring,
    show -(-nx)*Q.s+(-ny)*Q.c=-(-nx*Q.s+ny*Q.c) by ring,abs_neg,abs_neg]

theorem face_radius (Q : OpenSquare) (nx ny : ℝ) (face : FaceNormal Q nx ny) :
    supportRadius Q nx ny=Q.side/2 := by
  have longitudinal : supportRadius Q Q.c Q.s=Q.side/2 := by
    have a := (ownU Q).1
    have b := (ownU Q).2
    dsimp [lower,upper] at a b
    linarith only [a,b]
  have transverse : supportRadius Q (-Q.s) Q.c=Q.side/2 := by
    have a := (ownV Q).1
    have b := (ownV Q).2
    dsimp [lower,upper] at a b
    linarith only [a,b]
  rcases face with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact longitudinal
  · rw [radius_neg]
    exact longitudinal
  · exact transverse
  · have same : supportRadius Q Q.s (-Q.c)=supportRadius Q (-Q.s) Q.c := by
      simpa only [neg_neg] using radius_neg Q (-Q.s) Q.c
    exact same.trans transverse

theorem bottom_face (Q : OpenSquare) (h t : ℝ) (hn : 0≤h) (tn : 0≤t)
    (wall : ∀ x y, Q.Inside x y → -2≤y) (face : FaceNormal Q (-h) t) :
    -h*centerX Q-2*t+(Q.side/2)*(1+t^2+h*t)≤upper Q (-h) t := by
  have width := face_width Q (-h) t face
  simp only [abs_neg,abs_of_nonneg hn,abs_of_nonneg tn] at width
  have center := bottom_center Q wall
  rw [width] at center
  have weighted := mul_le_mul_of_nonneg_left center tn
  rw [show upper Q (-h) t=(-h)*centerX Q+t*centerY Q+supportRadius Q (-h) t by rfl,
    face_radius Q (-h) t face]
  nlinarith only [weighted]

theorem left_face (Q : OpenSquare) (r d : ℝ) (rn : 0≤r) (dn : 0≤d)
    (wall : ∀ x y, Q.Inside x y → -2≤x) (face : FaceNormal Q (-r) d) :
    lower Q (-r) d≤2*r+d*centerY Q-(Q.side/2)*(1+r^2+r*d) := by
  have width := face_width Q (-r) d face
  simp only [abs_neg,abs_of_nonneg rn,abs_of_nonneg dn] at width
  have center := left_center Q wall
  rw [width] at center
  have weighted := mul_le_mul_of_nonneg_left center rn
  rw [show lower Q (-r) d=(-r)*centerX Q+d*centerY Q-supportRadius Q (-r) d by rfl,
    face_radius Q (-r) d face]
  nlinarith only [weighted]

#print axioms width_bounds
#print axioms bottom_face
#print axioms left_face
end N12Compact.C1092ShallowBoundarySupport
