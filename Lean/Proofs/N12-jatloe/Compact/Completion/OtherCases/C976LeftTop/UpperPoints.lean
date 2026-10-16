import Compact.Completion.OtherCases.C976LeftTop.PointSupport
import Compact.Completion.OtherCases.C976LeftTop.Main

/-! C976-LEFT-UPPER-POINTS Theorem 1 and Corollary 2. The original
physical square is reframed, not reflected, and retains every strict
point and whole-segment exclusion. No compiler acceptance is asserted. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints
open S12 S12Pilot
set_option Elab.async false

theorem high_point (q : OpenSquare) (h : Input q) (p : Profile q)
    (x : ℝ) (low : 1/4≤x) (high : x≤7/25) : q.Inside x 1 := by
  have upperV := upper_v_span q.c q.s q.unit_normal p.angleLower.le
  have farUpperU : (7/25)*q.c+q.s<q.loU+q.side := by
    by_cases small : q.s≤(37/65)*q.c
    · linarith only [h.marker.2.1,small]
    · have large : (1/3)*q.c≤q.s := by linarith only [lt_of_not_ge small,p.cosine]
      have segment := upperU_strict q h p large
      have margin := farther_margin q.c q.s p.cosine p.sine q.unit_normal
        (le_of_lt (lt_of_not_ge small)) p.angleUpper.le
      have identity : lowerAlpha q.c q.s+lowerBeta q.c q.s*(1-q.c)-39/625-
          lowerAlpha q.c q.s*((7/25)*q.c+q.s)=
          (37/100)*q.c+(11/100)*q.s-189/625-(91/2500)*q.c^2-(42/625)*q.c*q.s := by
        dsimp only [lowerAlpha,lowerBeta]
        linear_combination -(6/25)*q.unit_normal
      have weighted : lowerAlpha q.c q.s*((7/25)*q.c+q.s)<
          lowerAlpha q.c q.s*(q.loU+q.side) := by linarith only [segment,identity,margin]
      have ap : 0<lowerAlpha q.c q.s := by dsimp only [lowerAlpha]; linarith only [p.cosine,p.sine]
      exact (mul_lt_mul_iff_right₀ ap).mp weighted
  have xLower := mul_nonneg p.cosine.le (sub_nonneg.mpr low)
  have xUpper := mul_nonneg p.cosine.le (sub_nonneg.mpr high)
  have vLower := mul_nonneg p.sine.le (sub_nonneg.mpr high)
  have vUpper := mul_nonneg p.sine.le (sub_nonneg.mpr low)
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [h.left.1,xLower,p.cosine,p.sine]
  · nlinarith only [farUpperU,xUpper]
  · nlinarith only [h.inward.2.2.1,vLower,p.cosine,p.canonical]
  · nlinarith only [vUpper,p.lowerV,upperV,h.side]

theorem inward_point (q : OpenSquare) (h : Input q) (p : Profile q) : q.Inside 0 (4/5) := by
  have span := inward_span q.c q.s q.unit_normal
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [h.left.1,h.marker.2.1,h.inward.2.2.1,p.lowerV,h.side,
      span,p.cosine,p.sine,p.canonical]

theorem frame (q : OpenSquare) (h : Input q) :
    ∃ r : OpenSquare,r.side=q.side ∧ (∀ x y,r.Inside x y↔q.Inside x y) ∧
      Profile r ∧ r.Inside (1/4) 1 ∧ r.Inside 0 (4/5) ∧ r.Inside (7/25) 1 := by
  obtain ⟨r,cp,range,side,inside,_⟩ := ClosedFrames.canonical_frame q
  have data := h.reframe side inside
  by_cases sign : 0≤r.s
  · have order : r.s≤r.c := by simpa only [abs_of_nonneg sign] using range
    have profile := positive_profile r data cp sign order
    exact ⟨r,side,inside,profile,
      high_point r data profile (1/4) le_rfl (by norm_num),
      inward_point r data profile,
      high_point r data profile (7/25) (by norm_num) le_rfl⟩
  · exact False.elim (nonpositive_impossible r data (-r.s) (by ring) cp
      (by linarith only [sign]) (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range))

theorem points (q : OpenSquare) (h : Input q) :
    q.Inside (1/4) 1 ∧ q.Inside 0 (4/5) ∧ q.Inside (7/25) 1 := by
  obtain ⟨r,_,inside,_,first,second,third⟩ := frame q h
  exact ⟨(inside _ _).mp first,(inside _ _).mp second,(inside _ _).mp third⟩

theorem left_input (q : OpenSquare) (h : Input q) (p : Profile q) : LeftInput q where
  side := h.side
  cosine := p.cosine
  sine := p.sine
  canonical := p.canonical
  angleLower := p.angleLower
  upperV := p.upperV
  lowerV := p.lowerV
  marker := h.marker
  left := by simpa only [neg_div] using h.left
  inward := h.inward
  high := high_point q h p (1/4) le_rfl (by norm_num)
  segment := h.segment

/-- The two completed local chapters joined without assuming any of the
left square's support faces or its upper target point. -/
theorem steep_negative (N W : OpenSquare) (n : Input N) (t : TopInput W)
    (cosine : 0<W.c) (sine : W.s≤0) (same : N.side=W.side)
    (apart : ∀ x y,¬(N.Inside x y ∧ W.Inside x y)) : (2/3)*W.c< -W.s := by
  obtain ⟨R,side,inside,profile,_,_,_⟩ := frame N n
  exact C976LeftTop.steep_negative R W
    (left_input R (n.reframe side inside) profile) t cosine sine
    (by simpa only [side] using same)
    (fun x y pair => apart x y ⟨(inside x y).mp pair.1,pair.2⟩)

#print axioms frame
#print axioms points
#print axioms steep_negative
end N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints
