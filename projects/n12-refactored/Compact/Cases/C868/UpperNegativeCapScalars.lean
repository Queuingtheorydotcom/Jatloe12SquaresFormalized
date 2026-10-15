import Compact.Geometry.C977CornerCubic
import Compact.Completion.CommonCases.CanonicalProjection
import Compact.Completion.CommonCases.UnitCircleChord

/-! Exact full-arc vertex bounds in the remaining upper-V branch. Both
spans come from actual faces. Rational unit endpoints and one finite chord
identity suffice; no sampled angles or additional angle enclosure is used. -/
namespace N12Compact.C868.UpperNegativeCapScalars
open C977CornerCubic
set_option Elab.async false
noncomputable section

private def c0 : ℝ := 609/641
private def s0 : ℝ := 200/641

theorem angle (c s : ℝ) (normal : Normal c s)
    (span : 1<(18/25)*c+(99/100)*s)
    (nearTop : 1<(142/125)*c+(1/20)*s) : 5*s<3*c := by
  have cp : 0<c := by linarith only [(normal_bounds normal).1]
  apply lt_of_not_ge
  intro steep
  have bound := CommonCases.CanonicalProjection.after c s
    (3901/4549) (2340/4549) (142/125) (1/20) normal.2.2
    (by norm_num) (by linarith only [steep,cp]) (by norm_num) (by norm_num)
  norm_num at bound
  linarith only [nearTop,bound]

private theorem region (c s : ℝ) (normal : Normal c s)
    (span : 1<(18/25)*c+(99/100)*s)
    (nearTop : 1<(142/125)*c+(1/20)*s) :
    17/20≤c ∧ c≤c0 ∧ s0≤s ∧ s≤13/25 := by
  have bounds := normal_bounds normal
  have cp : 0<c := by linarith only [bounds.1]
  have tilt := angle c s normal span nearTop
  have unit0 : c0^2+s0^2=1 := by norm_num [c0,s0]
  have lowerS : s0≤s := by
    apply le_of_not_gt
    intro small
    have support := CommonCases.UnitCircleChord.increasing
      (c:=c0) (s:=s0) (d:=c) (t:=s) (A:=18/25) (B:=99/100)
      (by norm_num [c0]) cp.le unit0 normal.2.2
      (by norm_num [s0]) normal.1 small.le
      (by norm_num) (by norm_num) (by norm_num [c0,s0])
    norm_num [c0,s0] at support
    linarith only [span,support]
  have upperC := CommonCases.UnitCircleChord.cosine_order
    (c:=(609/641:ℝ)) (s:=200/641) (d:=c) (t:=s)
    (by norm_num) cp.le (by norm_num) normal.2.2
    (by norm_num) normal.1 lowerS
  have orderSquare := mul_pos (show 0<3*c-5*s by linarith only [tilt])
    (show 0<3*c+5*s by linarith only [cp,normal.1])
  have lowerC : 17/20≤c := by
    apply le_of_not_gt
    intro small
    have product := mul_neg_of_neg_of_pos (show c-17/20<0 by linarith only [small])
      (show 0<c+17/20 by linarith only [cp])
    nlinarith only [product,orderSquare,normal.2.2]
  have upperS : s≤13/25 := by
    apply le_of_not_gt
    intro large
    have product := mul_pos (show 0<s-13/25 by linarith only [large])
      (show 0<s+13/25 by linarith only [normal.1])
    nlinarith only [product,orderSquare,normal.2.2]
  exact ⟨lowerC,upperC,lowerS,upperS⟩

private theorem chord_slope (c s : ℝ) (normal : Normal c s)
    (span : 1<(18/25)*c+(99/100)*s)
    (nearTop : 1<(142/125)*c+(1/20)*s) :
    c0-c≤(47/100)*(s-s0) := by
  have r := region c s normal span nearTop
  have circle : (c0-c)*(c+c0)=(s-s0)*(s+s0) := by
    have unit0 : c0^2+s0^2=1 := by norm_num [c0,s0]
    nlinarith only [unit0,normal.2.2]
  have bracket : 0≤(47/100)*(c+c0)-(s+s0) := by
    norm_num [c0,s0]
    linarith only [r.1,r.2.2.2]
  have product := mul_nonneg (sub_nonneg.mpr r.2.2.1) bracket
  have weighted : 0≤((47/100)*(s-s0)-(c0-c))*(c+c0) := by
    nlinarith only [circle,product]
  have positive : 0<c+c0 := by norm_num [c0]; linarith only [r.1]
  have result := nonneg_of_mul_nonneg_left weighted positive
  linarith only [result]

private def heightValue (c s : ℝ) : ℝ :=
  c+s-(51/100)*c*s+(1/100)*s^2-(1/20)*c^2

theorem height (c s : ℝ) (normal : Normal c s)
    (span : 1<(18/25)*c+(99/100)*s)
    (nearTop : 1<(142/125)*c+(1/20)*s) :
    53/50<c+s-(51/100)*c*s+(1/100)*s^2-(1/20)*c^2 := by
  have r := region c s normal span nearTop
  have chord := chord_slope c s normal span nearTop
  let K := 1-(51/100)*s-(1/20)*(c+c0)
  let L := 1-(51/100)*c0+(1/100)*(s+s0)
  have kcap : K≤1 := by
    dsimp only [K]
    norm_num [c0]
    linarith only [normal.1,r.1]
  have lfloor : 47/100≤L := by
    dsimp only [L]
    norm_num [c0,s0]
    linarith only [normal.1]
  have first := mul_nonneg (sub_nonneg.mpr r.2.1) (sub_nonneg.mpr kcap)
  have last := mul_nonneg (sub_nonneg.mpr r.2.2.1) (sub_nonneg.mpr lfloor)
  have identity : heightValue c s-heightValue c0 s0=
      -(c0-c)*K+(s-s0)*L := by dsimp only [heightValue,K,L]; ring
  have comparison : heightValue c0 s0≤heightValue c s := by
    nlinarith only [identity,first,last,chord]
  have endpoint : 53/50<heightValue c0 s0 := by norm_num [heightValue,c0,s0]
  exact lt_of_lt_of_le endpoint comparison

theorem edge (c s : ℝ) (normal : Normal c s)
    (span : 1<(18/25)*c+(99/100)*s)
    (nearTop : 1<(142/125)*c+(1/20)*s) : (53/100)*c+(21/20)*s<1 := by
  have tilt := angle c s normal span nearTop
  have cp : 0<c := by linarith only [(normal_bounds normal).1]
  have bound := CommonCases.CanonicalProjection.before c s
    (299/349) (180/349) (53/100) (21/20) normal.2.2
    (by norm_num) (by linarith only [tilt,cp]) (by norm_num) (by norm_num)
  norm_num at bound
  linarith only [bound]

theorem left (c s : ℝ) (normal : Normal c s)
    (span : 1<(18/25)*c+(99/100)*s)
    (nearTop : 1<(142/125)*c+(1/20)*s) :
    (23/50)*c^2+(269/250)*c*s-c< -(1/25) := by
  have r := region c s normal span nearTop
  have tilt := angle c s normal span nearTop
  have cp : 0<c := by linarith only [r.1]
  have bound := CommonCases.CanonicalProjection.before c s
    (299/349) (180/349) (23/50) (269/250) normal.2.2
    (by norm_num) (by linarith only [tilt,cp]) (by norm_num) (by norm_num)
  have cap : (23/50)*c+(269/250)*s≤19/20 := by
    norm_num at bound
    linarith only [bound]
  have weighted := mul_nonneg cp.le (sub_nonneg.mpr cap)
  nlinarith only [weighted,r.1]

theorem top (c s : ℝ) (normal : Normal c s)
    (span : 1<(18/25)*c+(99/100)*s)
    (nearTop : 1<(142/125)*c+(1/20)*s) :
    1+(43/500)*c^2+(13/50)*c*s<59/50 := by
  have cp : 0<c := by linarith only [(normal_bounds normal).1]
  have tilt := angle c s normal span nearTop
  have order := mul_nonneg (show 0≤3*c-5*s by linarith only [tilt])
    (show 0≤5*c+3*s by linarith only [cp,normal.1])
  have doubleUnit : (c^2-s^2)^2+(2*c*s)^2=1 := by
    calc
      _ = (c^2+s^2)^2 := by ring
      _ = 1 := by rw [normal.2.2]; norm_num
  have bound := CommonCases.CanonicalProjection.before (c^2-s^2) (2*c*s)
    (8/17) (15/17) (43/1000) (13/100) doubleUnit
    (by norm_num) (by nlinarith only [order]) (by norm_num) (by norm_num)
  norm_num at bound
  nlinarith only [bound,normal.2.2]

private def chordValue (c s : ℝ) : ℝ :=
  (443/400)*c+(357/400)*s-(10071/20000)*c*s-
    (1989/20000)*c^2+(123/8000)*s^2

theorem chord (c s : ℝ) (normal : Normal c s)
    (span : 1<(18/25)*c+(99/100)*s)
    (nearTop : 1<(142/125)*c+(1/20)*s) :
    543/500<(443/400)*c+(357/400)*s-(10071/20000)*c*s-
      (1989/20000)*c^2+(123/8000)*s^2 := by
  have r := region c s normal span nearTop
  have slope := chord_slope c s normal span nearTop
  let K := 443/400-(10071/20000)*s-(1989/20000)*(c+c0)
  let L := 357/400-(10071/20000)*c0+(123/8000)*(s+s0)
  have kcap : K≤4/5 := by
    dsimp only [K]
    norm_num [c0]
    have lowS : 200/641≤s := r.2.2.1
    linarith only [r.1,lowS]
  have lfloor : 2/5≤L := by
    dsimp only [L]
    norm_num [c0,s0]
    linarith only [normal.1]
  have first := mul_nonneg (sub_nonneg.mpr r.2.1) (sub_nonneg.mpr kcap)
  have last := mul_nonneg (sub_nonneg.mpr r.2.2.1) (sub_nonneg.mpr lfloor)
  have reserve := mul_nonneg (by norm_num : (0:ℝ)≤3/125)
    (sub_nonneg.mpr r.2.2.1)
  have identity : chordValue c s-chordValue c0 s0=
      -(c0-c)*K+(s-s0)*L := by dsimp only [chordValue,K,L]; ring
  have comparison : chordValue c0 s0≤chordValue c s := by
    nlinarith only [identity,first,last,slope,reserve]
  have endpoint : 543/500<chordValue c0 s0 := by norm_num [chordValue,c0,s0]
  exact lt_of_lt_of_le endpoint comparison

end
#print axioms angle
#print axioms height
#print axioms edge
#print axioms left
#print axioms top
#print axioms chord
end N12Compact.C868.UpperNegativeCapScalars
