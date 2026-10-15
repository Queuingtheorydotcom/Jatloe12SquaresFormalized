import Compact.Completion.OtherCases.C983.F4MergedCenter

/-! Direct translation of §§6–7 of `C983-F4-MERGED-CENTER.md`.
The merged square has the manuscript's putative positive-angle missing
center; the actual singleton has a nonpositive canonical angle. All three
retained separating directions are excluded with the displayed full-square
supports. This leaves the nonnegative singleton argument of §§4–5 separate.
Source only: no compiler replay has been performed. -/
namespace N12Compact.Completion.OtherCases.C983.F4MergedCenter
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false
noncomputable section

private theorem normal_coefficients (d r b t : ℝ)
    (dp : 0<d) (rp : 0<r) (gap : r<d)
    (bp : 0<b) (tn : 0≤t) (order : t≤b) :
    0<d*b-r*t ∧ 0<d*t+r*b := by
  have first := mul_pos (sub_pos.mpr gap) bp
  have second := mul_nonneg rp.le (sub_nonneg.mpr order)
  constructor
  · nlinarith only [first,second]
  · exact add_pos_of_nonneg_of_pos (mul_nonneg dp.le tn) (mul_pos rp bp)

/-- Equation (19), with the actual singleton corner supplying the
strict upper-support inequality. -/
theorem singleton_negative_u (W K : OpenSquare) (h : Input W K)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c)
    (missing : ¬W.Inside 0 0) (t : ℝ) (signed : K.s= -t)
    (bp : 0<K.c) (tn : 0≤t) (canonical : t≤K.c)
    (sep : upper K K.c (-t)≤lower W K.c (-t)) : False := by
  obtain ⟨zl,zu,zrel,dc,rl,ru,sum,gap⟩ := angle_window W K h cp sn order missing
  have rp : 0<W.s := by linarith only [rl]
  obtain ⟨kp,ep⟩ := normal_coefficients W.c W.s K.c t cp rp
    (by linarith only [gap]) bp tn canonical
  have ku : K.c^2+t^2=1 := by simpa only [signed,neg_sq] using K.unit_normal
  have form : lower W K.c (-t)=
      (W.c*K.c-W.s*t)*W.loU-(W.s*K.c+W.c*t)*(W.loV+W.side) := by
    rw [C981CompletionSupportForms.lower_in_bands]
    rw [show K.c*W.c+(-t)*W.s=W.c*K.c-W.s*t by ring,
      show -K.c*W.s+(-t)*W.c= -(W.s*K.c+W.c*t) by ring,
      abs_of_pos kp,abs_neg,abs_of_pos (by nlinarith only [ep])]
    ring
  have point := (strict_bounds K _ _ K.c (-t) (by simpa only [neg_sq] using ku)
    h.corner).2
  have uLow := (missing_faces W K h cp sn order missing).2.1
  have q := h.north
  have hHigh : (7/20)*(W.c+W.s)<W.loV+W.side := by
    linarith only [q.2.2.2]
  have first := mul_pos kp (show 0< -1-W.loU by linarith only [uLow])
  have second := mul_pos (show 0<W.s*K.c+W.c*t by nlinarith only [ep])
    (sub_pos.mpr hHigh)
  have aPositive : 0<W.c-1+(7/20)*W.s*(W.c+W.s) := by
    have margin := mul_pos rp
      (show 0<(7/20)*(W.c+W.s)-W.s/(1+W.c) by linarith only [sum,zu])
    nlinarith only [margin,zrel]
  have bPositive : 0<1-W.s+(7/20)*W.c*(W.c+W.s) := by
    have product := mul_pos cp (show 0<W.c+W.s by linarith only [cp,rp])
    nlinarith only [product,ru]
  have margin := add_pos_of_pos_of_nonneg (mul_pos bp aPositive)
    (mul_nonneg tn bPositive.le)
  rw [form] at sep
  nlinarith only [point,sep,first,second,margin]

/-- Equation (20), including the retained axial singleton endpoint. -/
theorem singleton_negative_v (W K : OpenSquare) (h : Input W K)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c)
    (missing : ¬W.Inside 0 0) (t : ℝ) (signed : K.s= -t)
    (bp : 0<K.c) (tn : 0≤t) (canonical : t≤K.c)
    (sep : upper K t K.c≤lower W t K.c) : False := by
  obtain ⟨zl,zu,zrel,dc,rl,ru,sum,gap⟩ := angle_window W K h cp sn order missing
  have rp : 0<W.s := by linarith only [rl]
  obtain ⟨kp,ep⟩ := normal_coefficients W.c W.s K.c t cp rp
    (by linarith only [gap]) bp tn canonical
  have ku : t^2+K.c^2=1 := by
    have unit : K.c^2+t^2=1 := by simpa only [signed,neg_sq] using K.unit_normal
    linarith only [unit]
  have form : lower W t K.c=
      (W.c*t+W.s*K.c)*W.loU+(W.c*K.c-W.s*t)*W.loV := by
    rw [C981CompletionSupportForms.lower_in_bands]
    rw [show t*W.c+K.c*W.s=W.c*t+W.s*K.c by ring,
      show -t*W.s+K.c*W.c=W.c*K.c-W.s*t by ring,
      abs_of_pos ep,abs_of_pos kp]
    ring
  have point := (strict_bounds K _ _ t K.c ku h.seed).2
  have uLow := (missing_faces W K h cp sn order missing).2.1
  have p := h.south
  have vLow : W.loV< -(7/20)*(W.c-W.s) := by linarith only [p.2.2.1]
  have first := mul_pos ep (show 0< -1-W.loU by linarith only [uLow])
  have second := mul_pos kp (sub_pos.mpr vLow)
  let B := W.s+(7/20)*W.c*(W.c-W.s)-13/100
  let T := W.c-(7/20)*W.s*(W.c-W.s)-31/25
  have cSmall : W.c≤1 := by nlinarith only [W.unit_normal,sq_nonneg W.s,cp]
  have tNegative : T<0 := by
    have product := mul_pos rp (show 0<W.c-W.s by linarith only [gap])
    dsimp only [T]
    nlinarith only [product,cSmall]
  have together : 0<B+T := by
    have square := (sq_lt_sq₀ (show (0:ℝ)≤19/50 by norm_num)
      (show 0≤W.c-W.s by linarith only [gap])).mpr gap
    dsimp only [B,T]
    nlinarith only [square,sum]
  have leading := mul_pos bp together
  have remainder := mul_nonneg (sub_nonneg.mpr canonical) (neg_nonneg.mpr tNegative.le)
  have margin : 0<K.c*B+t*T := by nlinarith only [leading,remainder]
  dsimp only [B,T] at margin
  rw [form] at sep
  nlinarith only [point,sep,first,second,margin]

/-- The positive endpoint/chord comparison in §7. Writing
x=cos(2q)=b²-t² and y=sin(2q)=2bt makes the manuscript's concavity
bound the exact unit-circle inequality x+y≥1. -/
theorem negative_singleton_chord (d r b t z : ℝ)
    (dp : 0<d) (rp : 0<r) (du : d^2+r^2=1)
    (bp : 0<b) (tn : 0≤t) (order : t≤b) (ku : b^2+t^2=1)
    (zLower : 1/4<z) (half : r*z=1-d)
    (dLower : 87/100<d) (rLower : 47/100<r) :
    d+r-1<(d*t+r*b)*((87/100)*b-(6/25)*t) := by
  let x := b^2-t^2
  let y := 2*b*t
  let m := (28/25)*d+(113/200)*r-1
  let P := (87/200)*r+(3/25)*d
  let Q := (87/200)*d-(3/25)*r
  have xn : 0≤x := by
    dsimp only [x]
    exact sub_nonneg.mpr ((sq_le_sq₀ tn bp.le).mpr order)
  have yn : 0≤y := by dsimp only [y]; positivity
  have xyUnit : x^2+y^2=1 := by
    dsimp only [x,y]
    linear_combination (b^2+t^2+1)*ku
  have span : 1≤x+y := by
    have product := mul_nonneg xn yn
    nlinarith only [xyUnit,product,xn,yn]
  have mn : 0≤m := by dsimp only [m]; linarith only [dLower,rLower]
  have first : m<P := by
    have positive := mul_pos rp (show 0<z-13/100 by linarith only [zLower])
    dsimp only [m,P]
    nlinarith only [positive,half]
  have last : m<Q := by
    have norm : (d+r)^2≤2 := by nlinarith only [du,sq_nonneg (d-r)]
    have endpoint : 0<1-(137/200)*(d+r) := by nlinarith only [norm,dp,rp]
    dsimp only [m,Q]
    linarith only [endpoint]
  have strict : 0<x*(P-m)+y*(Q-m) := by
    rcases xn.eq_or_lt with zero | positive
    · have yp : 0<y := by linarith only [span,zero]
      have lastWeight := mul_pos yp (sub_pos.mpr last)
      nlinarith only [lastWeight,zero]
    · have firstWeight := mul_pos positive (sub_pos.mpr first)
      have lastWeight := mul_nonneg yn (sub_nonneg.mpr last.le)
      linarith only [firstWeight,lastWeight]
  have extra := mul_nonneg mn (sub_nonneg.mpr span)
  have identity : (d*t+r*b)*((87/100)*b-(6/25)*t)-(d+r-1)=P*x+Q*y-m := by
    dsimp only [x,y,m,P,Q]
    linear_combination ((87/200)*r-(3/25)*d)*ku
  nlinarith only [strict,extra,identity]

/-- Equation (21) and its two endpoint margins exclude the W normal
for every nonpositive canonical singleton angle. -/
theorem singleton_negative_w (W K : OpenSquare) (h : Input W K)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c)
    (missing : ¬W.Inside 0 0) (t : ℝ) (signed : K.s= -t)
    (bp : 0<K.c) (tn : 0≤t) (canonical : t≤K.c)
    (sep : upper K W.c W.s≤lower W W.c W.s) : False := by
  obtain ⟨zl,zu,zrel,dc,rl,ru,sum,gap⟩ := angle_window W K h cp sn order missing
  have rp : 0<W.s := by linarith only [rl]
  obtain ⟨kp,ep⟩ := normal_coefficients W.c W.s K.c t cp rp
    (by linarith only [gap]) bp tn canonical
  have ku : K.c^2+t^2=1 := by simpa only [signed,neg_sq] using K.unit_normal
  have form : upper K W.c W.s=
      (W.c*K.c-W.s*t)*(K.loU+K.side)+(W.c*t+W.s*K.c)*(K.loV+K.side) := by
    rw [WallProfile.upper_in_bands,signed]
    rw [show W.c*K.c+W.s*(-t)=W.c*K.c-W.s*t by ring,
      show -W.c*(-t)+W.s*K.c=W.c*t+W.s*K.c by ring,
      abs_of_pos kp,abs_of_pos ep]
    ring
  have lower : lower W W.c W.s=W.loU := by
    rw [C981CompletionSupportForms.lower_in_bands]
    rw [show W.c*W.c+W.s*W.s=1 by nlinarith only [W.unit_normal],
      show -W.c*W.s+W.s*W.c=0 by ring]
    norm_num <;> ring
  have e := h.corner
  have s := h.seed
  simp only [OpenSquare.Inside,InBands,signed] at e s
  have first := mul_pos kp
    (show 0<K.loU+K.side-(-K.c+t) by linarith only [e.2.1])
  have second := mul_pos ep
    (show 0<K.loV+K.side-(-(31/25)*t-(13/100)*K.c) by linarith only [s.2.2.2])
  have chord := negative_singleton_chord W.c W.s K.c t (W.s/(1+W.c))
    cp rp W.unit_normal bp tn canonical ku zl zrel dc rl
  have identity :
      (W.c*K.c-W.s*t)*(-K.c+t)+
        (W.c*t+W.s*K.c)*(-(31/25)*t-(13/100)*K.c)=
      -(W.c+W.s)+(W.c*t+W.s*K.c)*((87/100)*K.c-(6/25)*t) := by
    linear_combination -(W.c+W.s)*ku
  have uLow := (missing_faces W K h cp sn order missing).2.1
  rw [form,lower] at sep
  nlinarith only [first,second,chord,identity,sep,uLow]

/-- The exhaustive actual-axis conclusion of §§3,6,7. -/
theorem nonpositive_singleton_impossible (W K : OpenSquare) (h : Input W K)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c)
    (missing : ¬W.Inside 0 0) (t : ℝ) (signed : K.s= -t)
    (bp : 0<K.c) (tn : 0≤t) (canonical : t≤K.c) : False := by
  have reverse (nx ny : ℝ) (sep : upper W nx ny≤lower K nx ny) :
      upper K (-nx) (-ny)≤lower W (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have noReverse (nx ny : ℝ) (unit : nx^2+ny^2=1) (xn : 0≤nx)
      (sep : upper W nx ny≤lower K nx ny) : False := by
    have cone := separator_cone W K h (-nx) (-ny)
      (by simpa only [neg_sq] using unit) (reverse nx ny sep)
    linarith only [cone.1,xn]
  have axes := CongruentSAT.faceSeparation_of_disjoint K W h.sameSide.symm h.apart
  change pairRadius K W≤|K.c*(centerX W-centerX K)+K.s*(centerY W-centerY K)| ∨
    pairRadius K W≤|-K.s*(centerX W-centerX K)+K.c*(centerY W-centerY K)| ∨
    pairRadius W K≤|W.c*(centerX W-centerX K)+W.s*(centerY W-centerY K)| ∨
    pairRadius W K≤|-W.s*(centerX W-centerX K)+W.c*(centerY W-centerY K)| at axes
  have separate (nx ny radius : ℝ)
      (eq : supportRadius K nx ny+supportRadius W nx ny=radius)
      (axis : radius≤|nx*(centerX W-centerX K)+ny*(centerY W-centerY K)|) :=
    separated K W nx ny (by rwa [eq])
  rcases axes with ku | kv | wu | wv
  · rcases separate _ _ _ (parallel_radius K W) ku with forward | backward
    · rw [signed] at forward
      exact singleton_negative_u W K h cp sn order missing t signed bp tn canonical forward
    · exact noReverse K.c K.s K.unit_normal bp.le backward
  · rcases separate _ _ _ (transverse_radius K W) kv with forward | backward
    · rw [signed,neg_neg] at forward
      exact singleton_negative_v W K h cp sn order missing t signed bp tn canonical forward
    · exact noReverse (-K.s) K.c (by nlinarith only [K.unit_normal])
        (by rw [signed,neg_neg]; exact tn) backward
  · have radius : supportRadius K W.c W.s+supportRadius W W.c W.s=pairRadius W K := by
      rw [add_comm]
      exact parallel_radius W K
    rcases separate _ _ _ radius wu with forward | backward
    · exact singleton_negative_w W K h cp sn order missing t signed bp tn canonical forward
    · exact noReverse W.c W.s W.unit_normal cp.le backward
  · have radius : supportRadius K (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W K := by
      rw [add_comm]
      exact transverse_radius W K
    rcases separate _ _ _ radius wv with forward | backward
    · have cone := separator_cone W K h (-W.s) W.c
        (by nlinarith only [W.unit_normal]) forward
      linarith only [cone.1,sn]
    · have cone := separator_cone W K h W.s (-W.c)
        (by nlinarith only [W.unit_normal]) (by simpa only [neg_neg] using reverse _ _ backward)
      linarith only [cone.2,order]

end
#print axioms singleton_negative_u
#print axioms singleton_negative_v
#print axioms singleton_negative_w
#print axioms nonpositive_singleton_impossible
end N12Compact.Completion.OtherCases.C983.F4MergedCenter
