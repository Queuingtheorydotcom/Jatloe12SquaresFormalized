import S12.SquareSupportBase
namespace S12
noncomputable section
set_option maxHeartbeats 0

def planeL1 (c s x y : ℝ) : ℝ := |c*x+s*y|+|-s*x+c*y|
def AxisOverlap (a b c s dx dy : ℝ) : Prop :=
  |dx|<a+b*(c+s) ∧ |dy|<a+b*(c+s) ∧
  |c*dx+s*dy|<b+a*(c+s) ∧ |-s*dx+c*dy|<b+a*(c+s)

theorem weighted_two_lt (x y u v A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hn : A≠0 ∨ B≠0) (hx : x<u) (hy : y<v) : A*x+B*y<A*u+B*v := by
  rcases hn with hn|hn
  · have h0 := mul_lt_mul_of_pos_left hx (lt_of_le_of_ne hA (Ne.symm hn))
    have h1 := mul_le_mul_of_nonneg_left (le_of_lt hy) hB
    linarith
  · have h0 := mul_le_mul_of_nonneg_left (le_of_lt hx) hA
    have h1 := mul_lt_mul_of_pos_left hy (lt_of_le_of_ne hB (Ne.symm hn))
    linarith

/-- On a cone bounded by adjacent square normals, the support function is linear. -/
theorem positive_normal_gap (a b c s dx dy nx ny : ℝ)
    (hc : 0≤c) (hs : 0≤s) (hunit : c^2+s^2=1)
    (h : AxisOverlap a b c s dx dy) (hx : 0≤nx) (hy : 0≤ny)
    (hn : nx≠0 ∨ ny≠0) :
    nx*dx+ny*dy<a*(nx+ny)+b*planeL1 c s nx ny := by
  have hdx := lt_of_le_of_lt (le_abs_self dx) h.1
  have hdy := lt_of_le_of_lt (le_abs_self dy) h.2.1
  have hdr := lt_of_le_of_lt (le_abs_self (c*dx+s*dy)) h.2.2.1
  by_cases hc0 : c=0
  · have hs1 : s=1 := by rw [hc0] at hunit; nlinarith
    subst c; subst s
    have hw := weighted_two_lt dx dy (a+b) (a+b) nx ny hx hy hn
      (by simpa using hdx) (by simpa using hdy)
    simp only [planeL1,zero_mul,one_mul,neg_zero,neg_mul,zero_add,add_zero,abs_neg,abs_of_nonneg hx,abs_of_nonneg hy]
    nlinarith [hw]
  by_cases hs0 : s=0
  · have hc1 : c=1 := by rw [hs0] at hunit; nlinarith
    subst s; subst c
    have hw := weighted_two_lt dx dy (a+b) (a+b) nx ny hx hy hn
      (by simpa using hdx) (by simpa using hdy)
    simp only [planeL1,zero_mul,one_mul,neg_zero,neg_mul,zero_add,add_zero,abs_neg,abs_of_nonneg hx,abs_of_nonneg hy]
    nlinarith [hw]
  have hcp : 0<c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hsp : 0<s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hu : 0≤c*nx+s*ny := add_nonneg (mul_nonneg hc hx) (mul_nonneg hs hy)
  by_cases hcone : c*ny≤s*nx
  · have hA : 0≤s*nx-c*ny := sub_nonneg.mpr hcone
    have hne : s*nx-c*ny≠0 ∨ ny≠0 := by
      by_cases hny : ny=0
      · left
        intro he
        have hnx : nx=0 := by nlinarith [he]
        exact hn.elim (fun hh => hh hnx) (fun hh => hh hny)
      · exact Or.inr hny
    have hw := weighted_two_lt dx (c*dx+s*dy) (a+b*(c+s)) (b+a*(c+s))
      (s*nx-c*ny) ny hA hy hne hdx hdr
    have habs : planeL1 c s nx ny=c*nx+s*ny+s*nx-c*ny := by
      unfold planeL1
      rw [abs_of_nonneg hu,abs_of_nonpos (by linarith : -s*nx+c*ny≤0)]
      ring
    have he : (s*nx-c*ny)*(a+b*(c+s))+ny*(b+a*(c+s))=
        s*(a*(nx+ny)+b*(c*nx+s*ny+s*nx-c*ny)) := by
      linear_combination -b*ny*hunit
    rw [habs]
    nlinarith [he]
  · have hA : 0≤c*ny-s*nx := by linarith
    have hne : nx≠0 ∨ c*ny-s*nx≠0 := by
      by_cases hnx : nx=0
      · right
        intro he
        have hny : ny=0 := by nlinarith [he]
        exact hn.elim (fun hh => hh hnx) (fun hh => hh hny)
      · exact Or.inl hnx
    have hw := weighted_two_lt (c*dx+s*dy) dy (b+a*(c+s)) (a+b*(c+s))
      nx (c*ny-s*nx) hx hA hne hdr hdy
    have habs : planeL1 c s nx ny=c*nx+s*ny-s*nx+c*ny := by
      unfold planeL1
      rw [abs_of_nonneg hu,abs_of_nonneg (by linarith : 0≤-s*nx+c*ny)]
      ring
    have he : nx*(b+a*(c+s))+(c*ny-s*nx)*(a+b*(c+s))=
        c*(a*(nx+ny)+b*(c*nx+s*ny-s*nx+c*ny)) := by
      linear_combination -b*nx*hunit
    rw [habs]
    nlinarith [he]

#print axioms positive_normal_gap
end
end S12
