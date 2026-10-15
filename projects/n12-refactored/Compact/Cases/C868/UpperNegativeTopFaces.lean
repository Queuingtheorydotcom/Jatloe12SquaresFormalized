import Compact.Geometry.C868CentralSeparation

/-! A compact whole-square region for the surviving top owner.  The
orientation is a full first-quadrant frame; only the stated shallow
subinterval is used here.  The two anchors and omitted northwest marker
belong to the actual top-square ledger in the applications. -/
namespace N12Compact.C868.UpperNegativeTopFaces
open S12 S12Pilot
set_option Elab.async false

theorem shallow_lower_v (T : OpenSquare) (cp : 0<T.c) (sn : 0≤T.s)
    (shallow : T.s≤(2/5)*T.c)
    (far : T.Inside (-4/5) 1) (marker : T.Inside 0 (543/500))
    (missing : ¬T.Inside (-7/20) (7/20)) :
    (7/20)*(T.c+T.s)≤T.loV := by
  apply le_of_not_gt
  intro low
  apply missing
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [far.1,cp,shallow]
  · linarith only [marker.2.1,cp,sn]
  · linarith only [low]
  · linarith only [far.2.2.2,cp,sn]

/-- Points above the exact far-marker chord lie above the lower V face.
The chord is used with its closed horizontal interval, including both
possible orders of the two anchor projections. -/
theorem above_chord_lower_v (T : OpenSquare) (cp : 0<T.c) (sn : 0≤T.s)
    (far : T.Inside (-4/5) 1) (marker : T.Inside 0 (543/500))
    (x y : ℝ) (left : -4/5≤x) (right : x≤0)
    (above : (543/500)+(43/400)*x<y) :
    T.loV< -T.s*x+T.c*y := by
  have rise : 0<T.c*(y-(543/500)-(43/400)*x) :=
    mul_pos cp (by linarith only [above])
  by_cases small : T.s≤(43/400)*T.c
  · have offset := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤x+4/5 by linarith only [left])
    nlinarith only [far.2.2.1,rise,offset]
  · have offset := mul_nonneg (show 0≤T.s-(43/400)*T.c by linarith only [small])
      (show 0≤-x by linarith only [right])
    nlinarith only [marker.2.2.1,rise,offset]

/-- A small rectangle above the far-marker chord is strictly inside the
same top square.  Its upper V band uses the whole side, not just the
convex hull of the two wall anchors. -/
theorem shallow_region (T : OpenSquare) (side : 1<T.side)
    (cp : 0<T.c) (sn : 0≤T.s) (shallow : T.s≤(2/5)*T.c)
    (far : T.Inside (-4/5) 1) (marker : T.Inside 0 (543/500))
    (missing : ¬T.Inside (-7/20) (7/20))
    (x y : ℝ) (left : -2/5≤x) (right : x≤-7/100)
    (bottom : 1≤y) (top : y≤61/50)
    (above : (543/500)+(43/400)*x<y) : T.Inside x y := by
  have floor := shallow_lower_v T cp sn shallow far marker missing
  have dc : T.c≤1 := by nlinarith only [T.unit_normal,sq_nonneg T.s,cp]
  have sk : T.s≤1 := by nlinarith only [T.unit_normal,sq_nonneg T.c,sn]
  refine ⟨?_,?_,?_,?_⟩
  · have along : 0<T.c*(x+4/5) :=
      mul_pos cp (by linarith only [left])
    have upward := mul_nonneg sn (sub_nonneg.mpr bottom)
    nlinarith only [far.1,along,upward]
  · have horizontal := mul_nonneg (le_of_lt cp)
      (show 0≤-7/100-x by linarith only [right])
    have vertical := mul_nonneg sn (sub_nonneg.mpr top)
    nlinarith only [marker.2.1,horizontal,vertical,shallow,cp]
  · exact above_chord_lower_v T cp sn far marker x y
      (by linarith only [left]) (by linarith only [right]) above
  · have horizontal := mul_nonneg sn
      (show 0≤x+2/5 by linarith only [left])
    have vertical := mul_nonneg (le_of_lt cp) (sub_nonneg.mpr top)
    nlinarith only [floor,side,horizontal,vertical,dc,sk]

/-- The shorter-height variant reaches farther right and contains the
sharp top vertex supplied by the upper-square profile. -/
theorem shallow_region_tight (T : OpenSquare) (side : 1<T.side)
    (cp : 0<T.c) (sn : 0≤T.s) (shallow : T.s≤(2/5)*T.c)
    (far : T.Inside (-4/5) 1) (marker : T.Inside 0 (543/500))
    (missing : ¬T.Inside (-7/20) (7/20))
    (x y : ℝ) (left : -2/5≤x) (right : x≤-1/25)
    (bottom : 1≤y) (top : y≤59/50)
    (above : (543/500)+(43/400)*x<y) : T.Inside x y := by
  have floor := shallow_lower_v T cp sn shallow far marker missing
  have dc : T.c≤1 := by nlinarith only [T.unit_normal,sq_nonneg T.s,cp]
  have sk : T.s≤1 := by nlinarith only [T.unit_normal,sq_nonneg T.c,sn]
  refine ⟨?_,?_,?_,?_⟩
  · have along : 0<T.c*(x+4/5) :=
      mul_pos cp (by linarith only [left])
    have upward := mul_nonneg sn (sub_nonneg.mpr bottom)
    nlinarith only [far.1,along,upward]
  · have horizontal := mul_nonneg (le_of_lt cp)
      (show 0≤-1/25-x by linarith only [right])
    have vertical := mul_nonneg sn (sub_nonneg.mpr top)
    nlinarith only [marker.2.1,horizontal,vertical,shallow,cp]
  · exact above_chord_lower_v T cp sn far marker x y
      (by linarith only [left]) (by linarith only [right]) above
  · have horizontal := mul_nonneg sn
      (show 0≤x+2/5 by linarith only [left])
    have vertical := mul_nonneg (le_of_lt cp) (sub_nonneg.mpr top)
    nlinarith only [floor,side,horizontal,vertical,dc,sk]

/-- For every remaining first-quadrant direction the two genuine wall
anchors already force the short horizontal segment at height 1.06.
No canonical angle bound, side bound, or missing point is needed. -/
theorem steep_region (T : OpenSquare) (cp : 0<T.c) (sn : 0≤T.s)
    (steep : (2/5)*T.c≤T.s)
    (far : T.Inside (-4/5) 1) (marker : T.Inside 0 (543/500))
    (x : ℝ) (left : -13/50≤x) (right : x≤-7/100) :
    T.Inside x (53/50) := by
  have dcLeft := mul_nonneg (le_of_lt cp)
    (show 0≤x+13/50 by linarith only [left])
  have dcRight := mul_nonneg (le_of_lt cp)
    (show 0≤-7/100-x by linarith only [right])
  have skLeft := mul_nonneg sn
    (show 0≤x+13/50 by linarith only [left])
  have skRight := mul_nonneg sn
    (show 0≤-7/100-x by linarith only [right])
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [far.1,dcLeft,cp,sn]
  · nlinarith only [marker.2.1,dcRight,cp,sn]
  · nlinarith only [marker.2.2.1,skRight,steep,cp]
  · nlinarith only [far.2.2.2,skLeft,steep,cp]

#print axioms shallow_lower_v
#print axioms above_chord_lower_v
#print axioms shallow_region
#print axioms shallow_region_tight
#print axioms steep_region
end N12Compact.C868.UpperNegativeTopFaces
