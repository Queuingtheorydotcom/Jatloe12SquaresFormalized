import Compact.Completion.OtherCases.C983.F4MergedCenter
import Compact.Completion.OtherCases.DerivedWalls

/-! The physical wall and support algebra of §§4–5 of
`C983-F4-MERGED-CENTER.md`. `PositiveComparisons` records precisely the
one-variable monotonicity interface proved in `F4MergedCenterMonotone`;
it is an explicit premise here, not an axiom. The joining margin (14)–(15)
is proved here by the manuscript's exact half-angle polynomial.
Source only: no compiler replay has been performed. -/
namespace N12Compact.Completion.OtherCases.C983.F4MergedCenter
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false
noncomputable section

/-- The four monotonicity conclusions in §§4–5, with the two B branches
combined by a maximum; `positive_comparisons` supplies this interface. -/
structure PositiveComparisons (d r : ℝ) : Prop where
  wallNormal : ∀ b t : ℝ, 0<b → 0≤t → t≤b → b^2+t^2=1 →
    1+(r-1)/d-(43/500)*r≤
      (d*b+r*t)+(r-(d*b+r*t))/b-(43/500)*r+max (d*t-r*b) 0
  lowerOrder : ∀ b t : ℝ, 0<b → 0≤t → t≤b → b^2+t^2=1 →
    0≤r*b-d*t →
    0<1-b-t+(t-1)/b-(43/500)*t+(d*b+r*t)+(7/20)*(r*b-d*t)*(d+r)
  upperOrder : ∀ b t : ℝ, 0<b → 0≤t → t≤b → b^2+t^2=1 →
    0≤d*t-r*b →
    0<1-b-t+(t-1)/b-(43/500)*t+(d*b+r*t)+(7/20)*(d*t-r*b)*(d-r)

/-- The exact cubic margin (14)–(15). -/
theorem joining_margin (d r z : ℝ) (dp : 0<d) (rp : 0<r)
    (unit : d^2+r^2=1) (short : r*z=1-d) (relation : z*(1+d)=r)
    (lower : 1/4≤z) (upper : z≤13/50) :
    0<1+(r-1)/d-(43/500)*r-(d+r-1) := by
  have zp : 0≤z := by linarith only [lower]
  have zSquare := (sq_le_sq₀ zp (show (0:ℝ)≤13/50 by norm_num)).mpr upper
  let P := -2*z^3+(1043/500)*z^2-43/500
  have factorPositive : 0< -2*z^2+(793/500)*z+793/2000 := by
    nlinarith only [zSquare,zp]
  have factor := mul_nonneg (sub_nonneg.mpr lower) factorPositive.le
  have polynomial : 0<P := by
    have identity : P-21/1600=(z-1/4)*(-2*z^2+(793/500)*z+793/2000) := by
      dsimp only [P]
      ring
    linarith only [factor,identity]
  have rIdentity : r*(1+z^2)=2*z := by
    have weighted := congrArg (fun x : ℝ => z*x) short
    nlinarith only [weighted,relation]
  have dIdentity : d=1-r*z := by linarith only [short]
  let M := 1+(r-1)/d-(43/500)*r-(d+r-1)
  have base : d*M=r*(-43/500+r*((543/500)*z-z^2)) := by
    have expanded : d*M=2*d+r-1-d^2-(543/500)*d*r := by
      dsimp only [M]
      field_simp [dp.ne']
      ring
    rw [expanded,dIdentity]
    ring
  have identity : (1+z^2)*(d*M)=r*P := by
    rw [base]
    calc
      (1+z^2)*(r*(-43/500+r*((543/500)*z-z^2)))=
          r*(-(43/500)*(1+z^2)+(r*(1+z^2))*((543/500)*z-z^2)) := by ring
      _=r*P := by rw [rIdentity]; dsimp only [P]; ring
  have positive := mul_pos rp polynomial
  have denominator : 0<(1+z^2)*d := mul_pos (by positivity) dp
  change 0<M
  have product : 0<((1+z^2)*d)*M := by nlinarith only [identity,positive]
  exact (mul_pos_iff_of_pos_left denominator).mp product

/-- The foreign Q0 marker gives the lower-v exit in §4. The faces
are displayed in the E-centered chart used by the manuscript. -/
theorem positive_singleton_faces (W K : OpenSquare) (h : Input W K)
    (bp : 0<K.c) (tn : 0≤K.s) (canonical : K.s≤K.c) :
    K.side-(43/500)*K.c≤K.loV+K.side+K.c-K.s ∧
      K.c*(K.loU+K.side+K.c+K.s)≥
        K.c*K.side+K.s*(K.loV+K.side+K.c-K.s)-1 := by
  have e := h.corner
  have p := h.marker
  have vLower : K.s-(543/500)*K.c≤K.loV := by
    apply le_of_not_gt
    intro low
    apply h.missingMarker
    simp only [OpenSquare.Inside,InBands]
    refine ⟨?_,?_,by linarith only [low],?_⟩
    · linarith only [p.1,canonical]
    · linarith only [e.2.1,tn]
    · linarith only [e.2.2.2,bp]
  have closed := WallProfile.vertex K K.loU (K.loV+K.side)
    ⟨le_rfl,by linarith only [K.side_pos]⟩
    ⟨by linarith only [K.side_pos],le_rfl⟩
  have wall := DerivedWalls.closed_affine_bound K 1 0 (-2) (-1) (-1)
    (by intro x y own; simpa only [one_mul,zero_mul,add_zero] using h.leftWall x y own)
    h.corner _ _ closed
  constructor
  · linarith only [vLower]
  · nlinarith only [wall,K.unit_normal]

/-- Equations (11)–(13), using the exact wallNormal comparison as an
explicit pending scalar premise. -/
theorem singleton_positive_w (W K : OpenSquare) (h : Input W K)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c)
    (missing : ¬W.Inside 0 0) (bp : 0<K.c) (tn : 0≤K.s)
    (canonical : K.s≤K.c) (scalars : PositiveComparisons W.c W.s)
    (sep : upper K W.c W.s≤lower W W.c W.s) : False := by
  obtain ⟨zl,zu,zrel,dc,rl,ru,sum,gap⟩ := angle_window W K h cp sn order missing
  have rp : 0<W.s := by linarith only [rl]
  let k := W.c*K.c+W.s*K.s
  let beta := W.s*K.c-W.c*K.s
  let J := K.loU+K.side+K.c+K.s
  let H := K.loV+K.side+K.c-K.s
  let gamma := max (-beta) 0
  have kp : 0<k := add_pos_of_pos_of_nonneg (mul_pos cp bp) (mul_nonneg sn tn)
  have gn : 0≤gamma := le_max_right _ _
  have faces := positive_singleton_faces W K h bp tn canonical
  have wall : K.c*K.side+K.s*H-1≤K.c*J := faces.2
  have height : K.side-(43/500)*K.c≤H := faces.1
  have form : upper K W.c W.s+(W.c+W.s)=k*J+beta*H+K.side*gamma := by
    rw [WallProfile.upper_in_bands]
    rw [show W.c*K.c+W.s*K.s=k by rfl,
      show -W.c*K.s+W.s*K.c=beta by dsimp only [beta]; ring,abs_of_pos kp]
    by_cases bn : 0≤beta
    · have gn' : -beta≤0 := by linarith only [bn]
      dsimp only [gamma]
      rw [abs_of_nonneg bn,max_eq_right gn']
      dsimp only [k,beta,J,H]
      linear_combination -(W.c+W.s)*K.unit_normal
    · have bn' : beta≤0 := le_of_not_ge bn
      dsimp only [gamma]
      rw [abs_of_nonpos bn',max_eq_left (neg_nonneg.mpr bn')]
      dsimp only [k,beta,J,H]
      linear_combination -(W.c+W.s)*K.unit_normal
  have coefficient : k*K.s+K.c*beta=W.s := by
    dsimp only [k,beta]
    linear_combination W.s*K.unit_normal
  have wallWeight := mul_nonneg kp.le (sub_nonneg.mpr wall)
  have heightWeight := mul_nonneg rp.le (sub_nonneg.mpr height)
  have side : 1<K.side := by simpa only [h.sameSide] using h.sideLarge
  have coefficientPositive : 0<K.c*k+W.s+K.c*gamma := by positivity
  have sideWeight := mul_pos (sub_pos.mpr side) coefficientPositive
  let B := k+(W.s-k)/K.c-(43/500)*W.s+gamma
  have bIdentity : K.c*B=K.c*k+W.s-k-(43/500)*K.c*W.s+K.c*gamma := by
    dsimp only [B]
    field_simp [bp.ne']
    ring
  have coefficientWeight := congrArg (fun x : ℝ => x*H) coefficient
  have formWeight := congrArg (fun x : ℝ => K.c*x) form
  have floor : B<upper K W.c W.s+(W.c+W.s) := by
    apply (mul_lt_mul_iff_right₀ bp).mp
    nlinarith only [wallWeight,heightWeight,sideWeight,bIdentity,coefficientWeight,formWeight]
  have scalar := scalars.wallNormal K.c K.s bp tn canonical K.unit_normal
  have comparison : 1+(W.s-1)/W.c-(43/500)*W.s≤B := by
    simpa only [B,k,gamma,beta,show -(W.s*K.c-W.c*K.s)=W.c*K.s-W.s*K.c by ring] using scalar
  have relation : (W.s/(1+W.c))*(1+W.c)=W.s := div_mul_cancel₀ _ (by linarith only [cp])
  have margin := joining_margin W.c W.s (W.s/(1+W.c)) cp rp W.unit_normal zrel relation zl.le zu.le
  have lower : lower W W.c W.s=W.loU := by
    rw [C981CompletionSupportForms.lower_in_bands]
    rw [show W.c*W.c+W.s*W.s=1 by nlinarith only [W.unit_normal],
      show -W.c*W.s+W.s*W.c=0 by ring]
    norm_num
  have uLow := (missing_faces W K h cp sn order missing).2.1
  rw [lower] at sep
  linarith only [floor,comparison,margin,sep,uLow]

/-- Equations (16)–(18), keeping both actual relative-angle orders. -/
theorem singleton_positive_u (W K : OpenSquare) (h : Input W K)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c)
    (missing : ¬W.Inside 0 0) (bp : 0<K.c) (tn : 0≤K.s)
    (canonical : K.s≤K.c) (scalars : PositiveComparisons W.c W.s)
    (sep : upper K K.c K.s≤lower W K.c K.s) : False := by
  have faces := positive_singleton_faces W K h bp tn canonical
  have side : 1<K.side := by simpa only [h.sameSide] using h.sideLarge
  have sideWeight := mul_pos (sub_pos.mpr side) (show 0<K.c+K.s by linarith only [bp,tn])
  have heightWeight := mul_nonneg tn (sub_nonneg.mpr faces.1)
  have own : upper K K.c K.s=K.loU+K.side := by
    rw [WallProfile.upper_in_bands]
    rw [show K.c*K.c+K.s*K.s=1 by nlinarith only [K.unit_normal],
      show -K.c*K.s+K.s*K.c=0 by ring]
    norm_num; ring
  let L := 1-K.c-K.s+(K.s-1)/K.c-(43/500)*K.s
  have identity : K.c*L=K.c-K.c^2-K.c*K.s+K.s-1-(43/500)*K.c*K.s := by
    dsimp only [L]
    field_simp [bp.ne']
    ring
  have upperBound : L<upper K K.c K.s := by
    rw [own]
    apply (mul_lt_mul_iff_right₀ bp).mp
    nlinarith only [faces.2,heightWeight,sideWeight,identity]
  have kp : 0<W.c*K.c+W.s*K.s := add_pos_of_pos_of_nonneg (mul_pos cp bp) (mul_nonneg sn tn)
  have uLow := (missing_faces W K h cp sn order missing).2.1
  have uWeight := mul_pos kp (show 0< -1-W.loU by linarith only [uLow])
  by_cases relative : 0≤W.s*K.c-W.c*K.s
  · have q := h.north
    have hHigh : (7/20)*(W.c+W.s)<W.loV+W.side := by linarith only [q.2.2.2]
    have weight := mul_nonneg relative (sub_nonneg.mpr hHigh.le)
    have form : lower W K.c K.s=
        (W.c*K.c+W.s*K.s)*W.loU-(W.s*K.c-W.c*K.s)*(W.loV+W.side) := by
      rw [C981CompletionSupportForms.lower_in_bands]
      rw [show K.c*W.c+K.s*W.s=W.c*K.c+W.s*K.s by ring,
        show -K.c*W.s+K.s*W.c= -(W.s*K.c-W.c*K.s) by ring,
        abs_of_pos kp,abs_neg,abs_of_nonneg relative]
      ring
    have margin := scalars.lowerOrder K.c K.s bp tn canonical K.unit_normal relative
    dsimp only [L] at upperBound
    rw [form] at sep
    nlinarith only [upperBound,margin,uWeight,weight,sep]
  · have relative' : 0≤W.c*K.s-W.s*K.c := by linarith only [relative]
    have p := h.south
    have vLow : W.loV< -(7/20)*(W.c-W.s) := by linarith only [p.2.2.1]
    have weight := mul_nonneg relative' (sub_nonneg.mpr vLow.le)
    have form : lower W K.c K.s=
        (W.c*K.c+W.s*K.s)*W.loU+(W.c*K.s-W.s*K.c)*W.loV := by
      rw [C981CompletionSupportForms.lower_in_bands]
      rw [show K.c*W.c+K.s*W.s=W.c*K.c+W.s*K.s by ring,
        show -K.c*W.s+K.s*W.c=W.c*K.s-W.s*K.c by ring,
        abs_of_pos kp,abs_of_nonneg relative']
      ring
    have margin := scalars.upperOrder K.c K.s bp tn canonical K.unit_normal relative'
    dsimp only [L] at upperBound
    rw [form] at sep
    nlinarith only [upperBound,margin,uWeight,weight,sep]

end
#print axioms joining_margin
#print axioms positive_singleton_faces
#print axioms singleton_positive_w
#print axioms singleton_positive_u
end N12Compact.Completion.OtherCases.C983.F4MergedCenter
