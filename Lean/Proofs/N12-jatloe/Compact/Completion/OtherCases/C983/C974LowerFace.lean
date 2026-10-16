import Compact.Completion.OtherCases.C983.C974LowerFaceScalars
import Compact.Completion.OtherCases.C983.C974LowerFaceLarge
import Compact.Completion.OtherCases.WallProfile.VertexGeometry

/-! The actual K–W lower-face argument, §2 of
`C974-THREE-SQUARE-ENDING.md`. Both squares are in the original chart.
The adjacent wall square's translated lower faces are L=W.loU-W.c and
H=W.loV+W.s. The already-established positive-frame and wall reductions
are explicit hypotheses; no missing prerequisite chapter is assumed.
Source translation only: this file has not been compiled. -/
namespace N12Compact.Completion.OtherCases.C983.C974LowerFace
open C977ChainBridge S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false
noncomputable section

/-- Exactly the reduced physical premises used by manuscript §2. The K
marker/excluded-origin argument and the W missing-point argument supplying
the frame and face bounds belong to preceding manuscript chapters. -/
structure Input (K W : OpenSquare) : Prop where
  sideLarge : 1<W.side
  sameSide : K.side=W.side
  kSine : 0<K.s
  kCanonical : K.s≤K.c
  kSlope : 4*K.s<3*K.c
  wSine : 0<W.s
  wCanonical : W.s≤W.c
  wSlope : 3*W.s<2*W.c
  kA : K.Inside (41/50) 0
  kS : K.Inside (24/25) (-6/25)
  wO : W.Inside 1 0
  kUpperV : K.loV+K.side≤0
  kWall : K.side*K.c-1≤K.s*K.loU+K.c*(K.loV+K.side)
  wUpperU : W.loU+W.side-W.c≤W.c
  wUpperV : W.loV+W.side+W.s≤W.c/2
  apart : ∀ x y,¬(K.Inside x y ∧ W.Inside x y)

/-- Strict A/O and S/O give nx>0 and nx+6ny>0, including all boundary
directions of the actual square-axis separation theorem. -/
theorem separator_cone (K W : OpenSquare) (h : Input K W)
    (nx ny : ℝ) (unit : nx^2+ny^2=1)
    (sep : upper K nx ny≤lower W nx ny) : 0<nx ∧ 0<nx+6*ny := by
  have a := (strict_bounds K _ _ nx ny unit h.kA).2
  have s := (strict_bounds K _ _ nx ny unit h.kS).2
  have o := (strict_bounds W _ _ nx ny unit h.wO).1
  constructor <;> linarith only [a,s,o,sep]

/-- Only the two actual positive u axes survive the cone. -/
theorem separating_u (K W : OpenSquare) (h : Input K W) :
    upper K K.c K.s≤lower W K.c K.s ∨
      upper K W.c W.s≤lower W W.c W.s := by
  have kp : 0<K.c := lt_of_lt_of_le h.kSine h.kCanonical
  have wp : 0<W.c := lt_of_lt_of_le h.wSine h.wCanonical
  have reverse (nx ny : ℝ) (sep : upper W nx ny≤lower K nx ny) :
      upper K (-nx) (-ny)≤lower W (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have noReverse (nx ny : ℝ) (unit : nx^2+ny^2=1) (xn : 0≤nx)
      (sep : upper W nx ny≤lower K nx ny) : False := by
    have cone := separator_cone K W h (-nx) (-ny)
      (by simpa only [neg_sq] using unit) (reverse nx ny sep)
    linarith only [cone.1,xn]
  have axes := CongruentSAT.faceSeparation_of_disjoint K W h.sameSide h.apart
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
    · exact Or.inl forward
    · exact (noReverse K.c K.s K.unit_normal kp.le backward).elim
  · rcases separate _ _ _ (transverse_radius K W) kv with forward | backward
    · have cone := separator_cone K W h (-K.s) K.c
        (by nlinarith only [K.unit_normal]) forward
      linarith only [cone.1,h.kSine]
    · have cone := separator_cone K W h K.s (-K.c)
        (by nlinarith only [K.unit_normal])
        (by simpa only [neg_neg] using reverse _ _ backward)
      linarith only [cone.2,h.kCanonical,kp]
  · have radius : supportRadius K W.c W.s+supportRadius W W.c W.s=pairRadius W K := by
      rw [add_comm]
      exact parallel_radius W K
    rcases separate _ _ _ radius wu with forward | backward
    · exact Or.inr forward
    · exact (noReverse W.c W.s W.unit_normal wp.le backward).elim
  · have radius : supportRadius K (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W K := by
      rw [add_comm]
      exact transverse_radius W K
    rcases separate _ _ _ radius wv with forward | backward
    · have cone := separator_cone K W h (-W.s) W.c
        (by nlinarith only [W.unit_normal]) forward
      linarith only [cone.1,h.wSine]
    · have cone := separator_cone K W h W.s (-W.c)
        (by nlinarith only [W.unit_normal])
        (by simpa only [neg_neg] using reverse _ _ backward)
      linarith only [cone.2,h.wCanonical,wp]

private theorem upper_self (K : OpenSquare) : upper K K.c K.s=K.loU+K.side := by
  rw [C981CompletionSupportForms.upper_in_bands,
    show K.c*K.c+K.s*K.s=1 by nlinarith only [K.unit_normal],
    show -K.c*K.s+K.s*K.c=0 by ring]
  norm_num <;> ring

private theorem lower_self (W : OpenSquare) : lower W W.c W.s=W.loU := by
  rw [C981CompletionSupportForms.lower_in_bands,
    show W.c*W.c+W.s*W.s=1 by nlinarith only [W.unit_normal],
    show -W.c*W.s+W.s*W.c=0 by ring]
  norm_num <;> ring

/-- The manuscript's equation (6), with both relative-angle signs and
all four full-square support alternatives retained. -/
theorem lower_face (K W : OpenSquare) (e : Input K W) :
    -(W.s/(1+W.c))*(1-W.s)<W.loU-W.c := by
  let l := K.c
  let h := K.s
  let d := W.c
  let t := W.s
  let a := K.side
  let U := K.loU
  let B := K.loV+K.side
  let L := W.loU-W.c
  let H := W.loV+W.s
  let x := h/(1+l)
  let z := t/(1+d)
  let kappa := l*d+h*t
  let sigma := h*d-l*t
  change -z*(1-t)<L
  have hp : 0<h := e.kSine
  have tp : 0<t := e.wSine
  have lp : 0<l := lt_of_lt_of_le hp e.kCanonical
  have dp : 0<d := lt_of_lt_of_le tp e.wCanonical
  have ku : l^2+h^2=1 := K.unit_normal
  have wu : d^2+t^2=1 := W.unit_normal
  have side : 1<a := by dsimp only [a]; rw [e.sameSide]; exact e.sideLarge
  have Bcap : B≤0 := e.kUpperV
  have wall : a*l-1≤h*U+l*B := e.kWall
  have Jcap : L+a≤d := by
    dsimp only [L,a]
    rw [e.sameSide]
    linarith only [e.wUpperU]
  have Tcap : H+a≤d/2 := by
    dsimp only [H,a]
    rw [e.sameSide]
    linarith only [e.wUpperV]
  have origin := e.wO
  simp only [OpenSquare.Inside,InBands,mul_one,mul_zero,add_zero] at origin
  have Tpos : 0<H+a := by dsimp only [H,a]; rw [e.sameSide]; linarith only [origin.2.2.2]
  obtain ⟨xp,xt,hx,lc,hs⟩ := half_data l h lp hp ku e.kSlope
  obtain ⟨zp,zt,tz,dc,ts⟩ := half_data d t dp tp wu (by linarith only [e.wSlope,tp])
  have xRelation : x*(1+l)=h := div_mul_cancel₀ _ (by positivity : (1+l:ℝ)≠0)
  have zRelation : z*(1+d)=t := div_mul_cancel₀ _ (by positivity : (1+d:ℝ)≠0)
  have hSmall : h<1 := by nlinarith only [ku,sq_pos_of_pos lp,hp]
  have tSmall : t<1 := by nlinarith only [wu,sq_pos_of_pos dp,tp]
  have kp : 0<kappa := add_pos (mul_pos lp dp) (mul_pos hp tp)
  have width : 1-x<U+a := by
    have wallB := mul_nonneg lp.le (neg_nonneg.mpr Bcap)
    have strict := mul_pos (sub_pos.mpr side) (add_pos lp hp)
    have scaled : 0<h*(U+a-(1-x)) := by nlinarith only [wall,wallB,strict,hx]
    exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp scaled)
  have deltaIdentity := sigma_identity l h d t x z lc hs dc ts
  have denom : 0<(1+x^2)*(1+z^2) := by positivity
  have relativeFactor : 0<1+x*z := by positivity
  rcases separating_u K W e with alongK | alongW
  · rw [upper_self] at alongK
    by_cases large : z≤x
    · have sn : 0≤sigma := by
        have sign := mul_nonneg (sub_nonneg.mpr large) relativeFactor.le
        apply (mul_nonneg_iff_of_pos_right denom).mp
        change 0≤(h*d-l*t)*((1+x^2)*(1+z^2))
        rw [deltaIdentity]
        linarith only [sign]
      have lowerForm : lower W K.c K.s=l+kappa*L+sigma*H := by
        rw [C981CompletionSupportForms.lower_in_bands]
        change (l*d+h*t)*(W.loU+W.side/2)+(-l*t+h*d)*(W.loV+W.side/2)-
          W.side/2*(|l*d+h*t|+|-l*t+h*d|)=l+kappa*L+sigma*H
        rw [abs_of_pos kp,show -l*t+h*d=sigma by dsimp only [sigma]; ring,abs_of_nonneg sn]
        dsimp only [kappa,sigma,L,H,l,h,d,t]
        linear_combination K.c*W.unit_normal
      rw [lowerForm] at alongK
      have capWeight := mul_nonneg sn (sub_nonneg.mpr Tcap)
      have excess := mul_nonneg sn (sub_nonneg.mpr side.le)
      have necessary : sigma*(1-d/2)-x*(1-h)<kappa*L := by
        change U+a≤l+kappa*L+sigma*H at alongK
        nlinarith only [alongK,width,capWeight,excess,hx]
      have scalar := forward_k_large l h d t x z xp zp xt zt large lc hs dc ts
      apply (mul_lt_mul_iff_right₀ kp).mp
      dsimp only [kappa,sigma] at necessary ⊢
      nlinarith only [necessary,scalar]
    · have small : x<z := lt_of_not_ge large
      have sn : sigma<0 := by
        have sign := mul_pos (sub_pos.mpr small) relativeFactor
        apply (mul_lt_mul_iff_left₀ denom).mp
        change (h*d-l*t)*((1+x^2)*(1+z^2))<0*((1+x^2)*(1+z^2))
        rw [deltaIdentity]
        nlinarith only [sign]
      have lowerForm : lower W K.c K.s=l+kappa*L+sigma*(H+a) := by
        rw [C981CompletionSupportForms.lower_in_bands]
        change (l*d+h*t)*(W.loU+W.side/2)+(-l*t+h*d)*(W.loV+W.side/2)-
          W.side/2*(|l*d+h*t|+|-l*t+h*d|)=l+kappa*L+sigma*(H+a)
        rw [abs_of_pos kp,show -l*t+h*d=sigma by dsimp only [sigma]; ring,abs_of_neg sn]
        dsimp only [kappa,sigma,L,H,l,h,d,t,a]
        rw [e.sameSide]
        linear_combination K.c*W.unit_normal
      rw [lowerForm] at alongK
      have weighted := mul_neg_of_neg_of_pos sn Tpos
      have necessary : -x*(1-h)<kappa*L := by
        change U+a≤l+kappa*L+sigma*(H+a) at alongK
        nlinarith only [alongK,width,weighted,hx]
      by_cases shallow : z≤2/7
      · have scalar := forward_k_small l h d t x z xp zp small shallow lc hs dc ts
        apply (mul_lt_mul_iff_right₀ kp).mp
        dsimp only [kappa] at necessary ⊢
        nlinarith only [necessary,scalar]
      · have deep : 2/7≤z := le_of_lt (lt_of_not_ge shallow)
        have scalar := large_half l h d t x z lp hp dp tp ku wu e.kCanonical
          xp small zt deep lc hs dc ts (cosine_lower d t dp tp wu e.wSlope) e.wSlope
        have upper : L<d-1 := by linarith only [Jcap,side]
        have weighted := mul_lt_mul_of_pos_left upper kp
        dsimp only [kappa] at necessary weighted
        exact (False.elim (by nlinarith only [necessary,weighted,scalar]))
  · rw [lower_self] at alongW
    by_cases large : z≤x
    · have sn : 0≤sigma := by
        have sign := mul_nonneg (sub_nonneg.mpr large) relativeFactor.le
        apply (mul_nonneg_iff_of_pos_right denom).mp
        change 0≤(h*d-l*t)*((1+x^2)*(1+z^2))
        rw [deltaIdentity]
        linarith only [sign]
      have upperForm : upper K W.c W.s=kappa*(U+a)+sigma*(a-B) := by
        rw [C981CompletionSupportForms.upper_in_bands]
        change (d*l+t*h)*(U+a/2)+(-d*h+t*l)*(K.loV+a/2)+
          a/2*(|d*l+t*h|+|-d*h+t*l|)=kappa*(U+a)+sigma*(a-B)
        rw [show d*l+t*h=kappa by dsimp only [kappa]; ring,
          show -d*h+t*l= -sigma by dsimp only [sigma]; ring,
          abs_of_pos kp,abs_neg,abs_of_nonneg sn]
        dsimp only [B,a]
        ring
      rw [upperForm] at alongW
      have first := mul_lt_mul_of_pos_left width kp
      have second := mul_nonneg sn (show 0≤a-B-1 by linarith only [side,Bcap])
      have necessary : kappa*(1-x)+sigma-d<L := by
        have along : kappa*(U+a)+sigma*(a-B)≤d+L := by
          dsimp only [d,L]
          linarith only [alongW]
        nlinarith only [along,first,second]
      have scalar := forward_w_large l h d t x z dp hp tp hSmall tSmall
        xp zp xt zt large hx tz xRelation zRelation hs ts
      dsimp only [kappa,sigma] at necessary
      exact lt_of_le_of_lt scalar necessary
    · have small : x<z := lt_of_not_ge large
      have sn : sigma<0 := by
        have sign := mul_pos (sub_pos.mpr small) relativeFactor
        apply (mul_lt_mul_iff_left₀ denom).mp
        change (h*d-l*t)*((1+x^2)*(1+z^2))<0*((1+x^2)*(1+z^2))
        rw [deltaIdentity]
        nlinarith only [sign]
      have upperForm : upper K W.c W.s=kappa*(U+a)-sigma*B := by
        rw [C981CompletionSupportForms.upper_in_bands]
        change (d*l+t*h)*(U+a/2)+(-d*h+t*l)*(K.loV+a/2)+
          a/2*(|d*l+t*h|+|-d*h+t*l|)=kappa*(U+a)-sigma*B
        rw [show d*l+t*h=kappa by dsimp only [kappa]; ring,
          show -d*h+t*l= -sigma by dsimp only [sigma]; ring,
          abs_of_pos kp,abs_of_pos (neg_pos.mpr sn)]
        dsimp only [B,a]
        ring
      have wallWeight := mul_nonneg kp.le (sub_nonneg.mpr wall)
      have wallB := mul_nonneg dp.le (neg_nonneg.mpr Bcap)
      have strict := mul_pos (mul_pos kp (sub_pos.mpr side)) (add_pos lp hp)
      have identity : h*(kappa*(U+a)-sigma*B-kappa*(1-x))=
          kappa*(h*U+l*B-(a*l-1))-d*B+kappa*(a-1)*(l+h) := by
        dsimp only [kappa,sigma]
        linear_combination -B*d*ku+(l*d+h*t)*hx
      have support : kappa*(1-x)<upper K W.c W.s := by
        rw [upperForm]
        have positive : 0<h*(kappa*(U+a)-sigma*B-kappa*(1-x)) := by
          nlinarith only [wallWeight,wallB,strict,identity]
        exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp positive)
      have necessary : kappa*(1-x)-d<L := by
        have along : upper K W.c W.s≤d+L := by
          dsimp only [d,L]
          linarith only [alongW]
        linarith only [support,along]
      have scalar := forward_w_small l h d t x z xp zp xt small lc hs dc ts
      dsimp only [kappa] at necessary
      linarith only [scalar,necessary]

end
#print axioms lower_face
end N12Compact.Completion.OtherCases.C983.C974LowerFace
