import Compact.Completion.OtherCases.C983.C974MissingCornerData
import Compact.Completion.C981.SupportForms

/-! The complete actual-axis reduction shared by WALL-SIGN Theorem 2
and MIDPOINT §1.4. The K transverse normal is excluded using the whole
square support and its upper-v face, with no unproved canonical order.
Source translation only; no compiler replay has been performed. -/
namespace N12Compact.Completion.OtherCases.C983.C974MissingCorner
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false
noncomputable section

theorem separator_cone (K W : OpenSquare) (e : Input K W)
    (nx ny : ℝ) (unit : nx^2+ny^2=1)
    (sep : upper K nx ny≤lower W nx ny) :
    0<nx ∧ 0<nx+6*ny ∧ 0<90*nx-43*ny := by
  have a := (strict_bounds K _ _ nx ny unit e.a).2
  have s := (strict_bounds K _ _ nx ny unit e.s).2
  have o := (strict_bounds W _ _ nx ny unit e.o).1
  have p := (strict_bounds W _ _ nx ny unit e.pw).1
  refine ⟨?_,?_,?_⟩ <;> linarith only [a,s,o,p,sep]

theorem upper_self (K : OpenSquare) : upper K K.c K.s=K.loU+K.side := by
  rw [C981CompletionSupportForms.upper_in_bands,
    show K.c*K.c+K.s*K.s=1 by nlinarith only [K.unit_normal],
    show -K.c*K.s+K.s*K.c=0 by ring]
  norm_num <;> ring

theorem lower_self (K : OpenSquare) : lower K K.c K.s=K.loU := by
  rw [C981CompletionSupportForms.lower_in_bands,
    show K.c*K.c+K.s*K.s=1 by nlinarith only [K.unit_normal],
    show -K.c*K.s+K.s*K.c=0 by ring]
  norm_num <;> ring

theorem no_reverse_v (K W : OpenSquare) (e : Input K W)
    (cap : K.loV+K.side≤0)
    (sep : upper K K.s (-K.c)≤lower W K.s (-K.c)) : False := by
  have support : upper K K.s (-K.c)= -K.loV := by
    rw [C981CompletionSupportForms.upper_in_bands,
      show K.s*K.c+(-K.c)*K.s=0 by ring,
      show -K.s*K.s+(-K.c)*K.c= -1 by nlinarith only [K.unit_normal]]
    norm_num <;> ring
  have point := (strict_bounds W _ _ K.s (-K.c)
    (by nlinarith only [K.unit_normal]) e.o).1
  have bound : K.s≤1 := by nlinarith only [K.unit_normal,sq_nonneg K.c]
  rw [support] at sep
  linarith only [point,sep,cap,e.sideLarge,bound]

/-- All four actual square axes, in both directions, with the two W-v
directions supplied explicitly. This helper is also used for negative W. -/
theorem separating_u (K W : OpenSquare) (e : Input K W)
    (lp : 0<K.c) (hp : 0<K.s) (dp : 0<W.c) (cap : K.loV+K.side≤0)
    (noV : upper K (-W.s) W.c≤lower W (-W.s) W.c → False)
    (noNegV : upper K W.s (-W.c)≤lower W W.s (-W.c) → False) :
    upper K K.c K.s≤lower W K.c K.s ∨
      upper K W.c W.s≤lower W W.c W.s := by
  have reverse (nx ny : ℝ) (sep : upper W nx ny≤lower K nx ny) :
      upper K (-nx) (-ny)≤lower W (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have noReverse (nx ny : ℝ) (unit : nx^2+ny^2=1) (xn : 0≤nx)
      (sep : upper W nx ny≤lower K nx ny) : False := by
    have cone := separator_cone K W e (-nx) (-ny)
      (by simpa only [neg_sq] using unit) (reverse nx ny sep)
    linarith only [cone.1,xn]
  have axes := CongruentSAT.faceSeparation_of_disjoint K W e.sameSide e.apart
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
    · exact (noReverse K.c K.s K.unit_normal lp.le backward).elim
  · rcases separate _ _ _ (transverse_radius K W) kv with forward | backward
    · have cone := separator_cone K W e (-K.s) K.c
        (by nlinarith only [K.unit_normal]) forward
      linarith only [cone.1,hp]
    · exact (no_reverse_v K W e cap
        (by simpa only [neg_neg] using reverse _ _ backward)).elim
  · have radius : supportRadius K W.c W.s+supportRadius W W.c W.s=pairRadius W K := by
      rw [add_comm]
      exact parallel_radius W K
    rcases separate _ _ _ radius wu with forward | backward
    · exact Or.inr forward
    · exact (noReverse W.c W.s W.unit_normal dp.le backward).elim
  · have radius : supportRadius K (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W K := by
      rw [add_comm]
      exact transverse_radius W K
    rcases separate _ _ _ radius wv with forward | backward
    · exact (noV forward).elim
    · exact (noNegV (by simpa only [neg_neg] using reverse _ _ backward)).elim

/-- Equations (17),(18) of WALL-SIGN and the identical two expressions
in MIDPOINT §1.4, derived from the actual wall and full square supports. -/
theorem positive_support_obstruction (K W : OpenSquare) (e : Input K W)
    (lp : 0<K.c) (hp : 0<K.s) (dp : 0<W.c) (tn : 0≤W.s)
    (order : W.s≤W.c) (cap : K.loV+K.side≤0)
    (relative : 0≤K.s*W.c-K.c*W.s) :
    let x := K.s/(1+K.c)
    1-W.c+(1-K.s)*(W.c*x-W.s)<0 ∨
      (K.c*W.c+K.s*W.s)*(1-W.c)+(K.s*W.c-K.c*W.s)*(1-W.c/2)-x*(1-K.s)<0 := by
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
  let k := l*d+h*t
  let s := h*d-l*t
  have kp : 0<k := add_pos_of_pos_of_nonneg (mul_pos lp dp) (mul_nonneg hp.le tn)
  have sn : 0≤s := relative
  have relation : x*(1+l)=h := div_mul_cancel₀ _ (by positivity : (1+l:ℝ)≠0)
  have half : h*x=1-l := by
    apply (mul_right_cancel₀ (by positivity : (1+l:ℝ)≠0))
    linear_combination h*relation+K.unit_normal
  have wall : a*l-1≤h*U+l*B := singleton_wall K W e
  have nonpositive : B≤0 := cap
  have side : 1<a := e.sideLarge
  have caps := wall_positive_caps K W e dp tn order
  have uCap : L+a≤d := by dsimp only [L,a]; rw [e.sameSide]; linarith only [caps.1]
  have vCap : H+a≤d/2 := by dsimp only [H,a]; rw [e.sameSide]; linarith only [caps.2]
  have axes := separating_u K W e lp hp dp cap
    (fun sep => by
      have cone := separator_cone K W e (-W.s) W.c (by nlinarith only [W.unit_normal]) sep
      linarith only [cone.1,tn])
    (fun sep => by
      have cone := separator_cone K W e W.s (-W.c) (by nlinarith only [W.unit_normal]) sep
      linarith only [cone.2.1,order,dp])
  rcases axes with alongK | alongW
  · right
    rw [upper_self] at alongK
    have lowerForm : lower W K.c K.s=l+k*L+s*H := by
      rw [C981CompletionSupportForms.lower_in_bands]
      change (l*d+h*t)*(W.loU+W.side/2)+(-l*t+h*d)*(W.loV+W.side/2)-
        W.side/2*(|l*d+h*t|+|-l*t+h*d|)=l+k*L+s*H
      rw [abs_of_pos kp,show -l*t+h*d=s by dsimp only [s]; ring,abs_of_nonneg sn]
      dsimp only [k,s,L,H,l,h,d,t]
      linear_combination K.c*W.unit_normal
    rw [lowerForm] at alongK
    have width : 1-x<U+a := by
      have wallB := mul_nonneg lp.le (neg_nonneg.mpr nonpositive)
      have strict := mul_pos (sub_pos.mpr side) (add_pos lp hp)
      have scaled : 0<h*(U+a-(1-x)) := by nlinarith only [wall,wallB,strict,half]
      exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp scaled)
    have first := mul_nonneg kp.le (sub_nonneg.mpr uCap)
    have last := mul_nonneg sn (sub_nonneg.mpr vCap)
    have excess := mul_pos (sub_pos.mpr side) (add_pos_of_pos_of_nonneg kp sn)
    change k*(1-d)+s*(1-d/2)-x*(1-h)<0
    change U+a≤l+k*L+s*H at alongK
    nlinarith only [alongK,width,first,last,excess,half]
  · left
    have upperForm : upper K W.c W.s=k*U+a*(k+s)-s*B := by
      rw [C981CompletionSupportForms.upper_in_bands]
      change (d*l+t*h)*(U+a/2)+(-d*h+t*l)*(K.loV+a/2)+
        a/2*(|d*l+t*h|+|-d*h+t*l|)=k*U+a*(k+s)-s*B
      rw [show d*l+t*h=k by dsimp only [k]; ring,
        show -d*h+t*l= -s by dsimp only [s]; ring,
        abs_of_pos kp,abs_of_nonpos (neg_nonpos.mpr sn)]
      dsimp only [B,a]
      ring
    rw [upperForm,lower_self] at alongW
    have sep : k*U+a*(k+s)-s*B≤2*d-a := by
      change k*U+a*(k+s)-s*B≤W.loU at alongW
      dsimp only [L] at uCap
      linarith only [alongW,uCap]
    have wallWeight := mul_nonneg kp.le (sub_nonneg.mpr wall)
    have capWeight := mul_nonneg (add_nonneg (mul_nonneg hp.le sn) (mul_nonneg kp.le lp.le))
      (neg_nonneg.mpr nonpositive)
    have sepWeight := mul_nonneg hp.le (sub_nonneg.mpr sep)
    have coeff : 0<h*(k+s)+k*l+h := by positivity
    have excess := mul_pos (sub_pos.mpr side) coeff
    have necessary : h*(k*(1-x)+s+1-2*d)<0 := by
      nlinarith only [wallWeight,capWeight,sepWeight,excess,
        show k*(h*x-(1-l))=0 by rw [half]; ring]
    have identity : k*(1-x)+s-d=(1-h)*(d*x-t) := by
      dsimp only [k,s]
      linear_combination (d-t)*half-d*relation
    change 1-d+(1-h)*(d*x-t)<0
    have result := (mul_neg_iff_of_pos_left hp).mp necessary
    linarith only [result,identity]

end
#print axioms positive_support_obstruction
end N12Compact.Completion.OtherCases.C983.C974MissingCorner
