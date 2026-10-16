import Compact.Cases.C868.UpperNegativeOutwardScalars

/-! The remaining longitudinal margin for the same outward pair. An exact
finite difference compares the real SE angle to its genuine span endpoint.
The additional NE-corner face restricts the upper angle by one rational
unit-circle projection. No sampled angles or new finite certificates occur. -/
namespace N12Compact.C868.UpperNegativeOutwardScalars
open C977CornerCubic
set_option Elab.async false
noncomputable section

def leftMargin (c s d t : ℝ) : ℝ :=
  1-c-(1043/500)*s+(c+s)*d+(s-c)*t-(1/5)*t*(s*d-c*t)

private def endpointCosine : ℝ := 229551/270449
private def endpointSine : ℝ := 143000/270449
private def alpha : ℝ := 45645230202/73142661601
private def beta : ℝ := 29192352650343/36571330800500

private theorem endpoint_value (c s : ℝ) :
    leftMargin c s endpointCosine endpointSine=1-alpha*c-beta*s := by
  norm_num [leftMargin,endpointCosine,endpointSine,alpha,beta]
  ring

private theorem endpoint_comparison (c s d t : ℝ)
    (h : Normal c s) (b : Normal d t)
    (projection : 1000<525*c+961*s) (span : 1<d+(143/500)*t) :
    leftMargin c s endpointCosine endpointSine≤leftMargin c s d t := by
  have hb := normal_bounds h
  have bb := normal_bounds b
  have cn : 0≤c := by linarith only [hb.1]
  have dn : 0≤d := by linarith only [bb.1]
  have cap : t≤endpointSine := (outward_sine_cap d t b span).le
  have cosine : endpointCosine≤d :=
    CommonCases.UnitCircleChord.cosine_order dn (by norm_num [endpointCosine])
      b.2.2 (by norm_num [endpointCosine,endpointSine]) b.1
      (by norm_num [endpointSine]) cap
  let delta := d-endpointCosine
  let gap := endpointSine-t
  have deltaNonneg : 0≤delta := sub_nonneg.mpr cosine
  have gapNonneg : 0≤gap := sub_nonneg.mpr cap
  have circle : delta*(d+endpointCosine)=gap*(endpointSine+t) := by
    dsimp only [delta,gap]
    have unit : endpointCosine^2+endpointSine^2=1 := by
      norm_num [endpointCosine,endpointSine]
    nlinarith only [unit,b.2.2]
  have first := mul_nonneg deltaNonneg
    (show 0≤2-d-endpointCosine by norm_num [endpointCosine]; linarith only [bb.2.1])
  have last := mul_nonneg gapNonneg b.1
  have chord : endpointSine*gap≤2*delta := by
    nlinarith only [circle,first,last]
  let K := c+s-s*t/5
  let L := c-s+s*endpointCosine/5-c*(t+endpointSine)/5
  have st : s*t≤1 := by
    have product := mul_nonneg h.1 (show 0≤1-t by linarith only [bb.2.2.2.1])
    nlinarith only [product,hb.2.2.2.1]
  have Kfloor : 4/5≤K := by
    dsimp only [K]
    linarith only [st,hb.2.2.2.2.1]
  have Lfloor : -(8/25)*endpointSine≤L := by
    have cosineHigh := (steep_of_projection c s h projection).2.le
    have p := mul_nonneg cn (sub_nonneg.mpr cap)
    have q := mul_nonneg (show 0≤4/5-c by linarith only [cosineHigh])
      (show 0≤2*endpointSine by norm_num [endpointSine])
    have r := mul_nonneg h.1 (show 0≤endpointCosine/5 by norm_num [endpointCosine])
    dsimp only [L]
    nlinarith only [p,q,r,h.2.1]
  have identity : leftMargin c s d t-leftMargin c s endpointCosine endpointSine=
      delta*K+gap*L := by
    dsimp only [leftMargin,delta,gap,K,L]
    ring
  have p := mul_nonneg deltaNonneg (sub_nonneg.mpr Kfloor)
  have q := mul_nonneg gapNonneg (sub_nonneg.mpr Lfloor)
  have correction := mul_nonneg (by norm_num : (0:ℝ)≤2/5)
    (show 0≤2*delta-endpointSine*gap by linarith only [chord])
  have reserve := mul_nonneg
    (show 0≤(2/25)*endpointSine by norm_num [endpointSine]) gapNonneg
  nlinarith only [identity,p,q,correction,reserve]

private theorem normal_sum_cap (c s : ℝ) (h : Normal c s) : c+s≤99/70 := by
  have bounds := normal_bounds h
  apply le_of_not_gt
  intro large
  have product := mul_pos (show 0<c+s-99/70 by linarith only [large])
    (show 0<c+s+99/70 by linarith only [bounds.1,h.1])
  nlinarith only [product,h.2.2,sq_nonneg (c-s)]

theorem left_axis_weak (c s d t : ℝ) (h : Normal c s) (b : Normal d t)
    (projection : 1000<525*c+961*s) (span : 1<d+(143/500)*t) :
    -(3/500)≤leftMargin c s d t := by
  have comparison := endpoint_comparison c s d t h b projection span
  rw [endpoint_value] at comparison
  have sumCap := normal_sum_cap c s h
  have asymmetry := mul_nonneg (show 0≤(beta-alpha)/2 by norm_num [alpha,beta])
    (sub_nonneg.mpr h.2.1)
  have average := mul_nonneg (show 0≤(alpha+beta)/2 by norm_num [alpha,beta])
    (sub_nonneg.mpr sumCap)
  norm_num [alpha,beta] at comparison asymmetry average
  nlinarith only [comparison,asymmetry,average]

theorem left_axis_margin (c s d t : ℝ) (h : Normal c s) (b : Normal d t)
    (projection : 1000<525*c+961*s) (span : 1<d+(143/500)*t)
    (cornerSpan : 1<(21/20)*c+(31/100)*s) : 1/250≤leftMargin c s d t := by
  have bounds := normal_bounds h
  have cn : 0≤c := by linarith only [bounds.1]
  have sineCap : s<48/73 := by
    apply lt_of_not_ge
    intro steep
    have bound := CommonCases.UnitCircleChord.decreasing
      (c := (55/73:ℝ)) (s := (48/73:ℝ)) (d := c) (t := s)
      (A := (21/20:ℝ)) (B := (31/100:ℝ))
      (by norm_num) cn (by norm_num) h.2.2 (by norm_num) h.1 steep
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at bound
    linarith only [cornerSpan,bound]
  have support := CommonCases.UnitCircleChord.increasing
    (c := (55/73:ℝ)) (s := (48/73:ℝ)) (d := c) (t := s)
    (A := alpha) (B := beta)
    (by norm_num) cn (by norm_num) h.2.2 (by norm_num) h.1 sineCap.le
    (by norm_num [alpha]) (by norm_num [beta]) (by norm_num [alpha,beta])
  have comparison := endpoint_comparison c s d t h b projection span
  rw [endpoint_value] at comparison
  norm_num [alpha,beta] at support comparison
  linarith only [support,comparison]

end
#print axioms left_axis_weak
#print axioms left_axis_margin
end N12Compact.C868.UpperNegativeOutwardScalars
