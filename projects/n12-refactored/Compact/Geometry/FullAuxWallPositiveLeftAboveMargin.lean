import Compact.Geometry.C977CornerSectorBounds

/-! Upper relative-angle support margin. The first half of the canonical
arc is compared with its diagonal. On the remaining arc, an inscribed
affine cosine bound reduces the claim to two quadratic endpoints. All
bounds are rational and checked by ordinary algebraic proofs. -/
namespace N12Compact.FullAuxWallPositiveLeftAboveMargin
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

private theorem diagonal {l r : ℝ} (ln : Normal l r)
    (large : 4/25≤r) (small : r≤1/2) :
    2-(543/500)*r^2-2*l+l/1000<0 := by
  have lb := normal_bounds ln
  have lp : 0<l := by linarith only [lb.1]
  have width := mul_nonneg (sub_nonneg.mpr lb.2.1)
    (show 0≤l+2 by linarith only [lp])
  have identity :
      (1+l)*(2-(543/500)*r^2-2*l+l/1000)=
      -r^2*((543/500)*(1+l)-2)+l*(1+l)/1000 := by
    linear_combination -2*ln.2.2
  have scaled : (1+l)*(2-(543/500)*r^2-2*l+l/1000)<0 := by
    by_cases low : r≤3/10
    · have square := mul_nonneg (sub_nonneg.mpr low)
        (show 0≤3/10+r by linarith only [ln.1])
      have cosine : 19/20≤l := by
        apply le_of_not_gt
        intro wrong
        have other := mul_nonneg (sub_nonneg.mpr wrong.le)
          (show 0≤19/20+l by linarith only [lp])
        nlinarith only [square,other,ln.2.2]
      have coefficient := mul_nonneg (sq_nonneg r)
        (show 0≤(543/500)*(1+l)-2-117/1000 by linarith only [cosine])
      have rSquare := mul_nonneg (sub_nonneg.mpr large)
        (show 0≤r+4/25 by linarith only [ln.1])
      nlinarith only [identity,width,coefficient,rSquare]
    · have rLower : 3/10≤r := le_of_lt (lt_of_not_ge low)
      have square := mul_nonneg (sub_nonneg.mpr small)
        (show 0≤1/2+r by linarith only [ln.1])
      have cosine : 433/500≤l := by
        apply le_of_not_gt
        intro wrong
        have other := mul_nonneg (sub_nonneg.mpr wrong.le)
          (show 0≤433/500+l by linarith only [lp])
        nlinarith only [square,other,ln.2.2]
      have coefficient := mul_nonneg (sq_nonneg r)
        (show 0≤(543/500)*(1+l)-2-13/500 by linarith only [cosine])
      have rSquare := mul_nonneg (sub_nonneg.mpr rLower)
        (show 0≤r+3/10 by linarith only [ln.1])
      nlinarith only [identity,width,coefficient,rSquare]
  exact (mul_neg_iff_of_pos_left (show 0<1+l by linarith only [lp])).mp scaled

private theorem cosine_line {l r : ℝ} (ln : Normal l r)
    (lower : 1/2≤r) : 5/4-(77/100)*r≤l := by
  have lb := normal_bounds ln
  have lp : 0<l := by linarith only [lb.1]
  have normalOrder := mul_nonneg (sub_nonneg.mpr ln.2.1)
    (show 0≤l+r by linarith only [lp,ln.1])
  have upper : r≤71/100 := by
    apply le_of_not_gt
    intro wrong
    have square := mul_pos (sub_pos.mpr wrong)
      (show 0<r+71/100 by linarith only [ln.1])
    nlinarith only [square,normalOrder,ln.2.2]
  let N (x : ℝ) := (5/4-(77/100)*x)^2+x^2
  have first : N (1/2)≤1 := by norm_num [N]
  have second : N (71/100)≤1 := by norm_num [N]
  have left := mul_nonneg (sub_nonneg.mpr upper) (sub_nonneg.mpr first)
  have right := mul_nonneg (sub_nonneg.mpr lower) (sub_nonneg.mpr second)
  have remainder := mul_nonneg (sub_nonneg.mpr lower) (sub_nonneg.mpr upper)
  have identity :
      (21/100)*(1-N r)=
      (71/100-r)*(1-N (1/2))+(r-1/2)*(1-N (71/100))+
        (21/100)*(15929/10000)*(r-1/2)*(71/100-r) := by
    dsimp [N]; ring
  have normBound : N r≤1 := by nlinarith only [identity,left,right,remainder]
  apply le_of_not_gt
  intro wrong
  have difference := mul_pos (sub_pos.mpr wrong)
    (show 0<5/4-(77/100)*r+l by linarith only [upper,lp])
  dsimp [N] at normBound
  nlinarith only [difference,normBound,ln.2.2]

theorem margin {l r C S u : ℝ}
    (ln : Normal l r) (dn : Normal C S)
    (large : 4/25≤r) (lower : 1/20≤S) (small : S≤11/50)
    (nonnegative : 0≤u) (offset : u≤1/1000)
    (order : 0≤r*C-l*S) :
    2-(543/500)*r^2-l*(1+(l*C+r*S))-
      (1/2)*l*C*(r*C-l*S)+l*(l*C+r*S)*u≤0 := by
  have lb := normal_bounds ln
  have db := normal_bounds dn
  have lp : 0<l := by linarith only [lb.1]
  have cp : 0<C := by linarith only [db.1]
  let alpha := l*C+r*S
  let H := r*C-l*S
  let E := 2-(543/500)*r^2-l*(1+alpha)-(1/2)*l*C*H+l*alpha/1000
  have ap : 0≤alpha := by
    exact add_nonneg (mul_nonneg lp.le cp.le) (mul_nonneg ln.1 dn.1)
  have au : alpha≤1 := dot_le_one ln dn
  have hp : 0≤H := order
  have offsetWeight := mul_nonneg (mul_nonneg lp.le ap) (sub_nonneg.mpr offset)
  have bounded : E≤0 := by
    by_cases half : r≤1/2
    · have diagonalBound := diagonal ln large half
      have unit : alpha^2+H^2=1 := by
        dsimp [alpha,H]
        calc
          _ = (l^2+r^2)*(C^2+S^2) := by ring
          _ = 1 := by rw [ln.2.2,dn.2.2]; norm_num
      have defectProduct := mul_nonneg ap (sub_nonneg.mpr au)
      have defect : 1-alpha≤H^2 := by nlinarith only [unit,defectProduct]
      have first := mul_nonneg cp.le (sub_nonneg.mpr half)
      have second := mul_nonneg lp.le dn.1
      have hCap : H≤C/2 := by dsimp [H]; nlinarith only [first,second]
      have comparison := mul_nonneg hp (sub_nonneg.mpr hCap)
      have weighted := mul_nonneg lp.le
        (show 0≤C*H/2-(1-alpha) by nlinarith only [defect,comparison])
      have correction := mul_nonneg lp.le (sub_nonneg.mpr au)
      dsimp [E]
      nlinarith only [weighted,correction,diagonalBound]
    · have rLower : 1/2≤r := le_of_lt (lt_of_not_ge half)
      have normalOrder := mul_nonneg (sub_nonneg.mpr ln.2.1)
        (show 0≤l+r by linarith only [lp,ln.1])
      have rUpper : r≤71/100 := by
        apply le_of_not_gt
        intro wrong
        have square := mul_pos (sub_pos.mpr wrong)
          (show 0<r+71/100 by linarith only [ln.1])
        nlinarith only [square,normalOrder,ln.2.2]
      have square := mul_nonneg (sub_nonneg.mpr small)
        (show 0≤11/50+S by linarith only [dn.1])
      have cosine : 97/100≤C := by
        apply le_of_not_gt
        intro wrong
        have other := mul_nonneg (sub_nonneg.mpr wrong.le)
          (show 0≤97/100+C by linarith only [cp])
        nlinarith only [square,other,dn.2.2]
      have defectProduct := mul_nonneg (sub_nonneg.mpr db.2.1)
        (show 0≤(51/100)*C-49/100 by linarith only [cosine])
      have defect : 1-(51/100)*S^2≤C := by
        nlinarith only [defectProduct,dn.2.2]
      let p := 999/1000-S/2
      let g := 1/2+(999/1000)*S-S^2/2
      let K := 2-p*C
      let f := p*C-543/500
      let P (x : ℝ) := K-(5/4-(77/100)*x)+f*x^2-g*(5/4-(77/100)*x)*x
      have pp : 0≤p := by dsimp [p]; linarith only [small]
      have gProduct := mul_nonneg dn.1
        (show 0≤999/1000-S/2 by linarith only [small])
      have gLower : 1/2≤g := by dsimp [g]; nlinarith only [gProduct]
      have fProduct := mul_nonneg pp (sub_nonneg.mpr cosine)
      have fLower : -(1/4)≤f := by
        dsimp [f,p] at fProduct ⊢
        nlinarith only [fProduct,small]
      have coefficient : 0≤f+(77/100)*g := by linarith only [fLower,gLower]
      have line := cosine_line ln rLower
      have weightedLine := mul_nonneg (sub_nonneg.mpr line)
        (show 0≤1+g*r by
          have product := mul_nonneg (show 0≤g by linarith only [gLower]) ln.1
          linarith only [product])
      have actual : E=K-l+f*r^2-g*l*r := by
        dsimp [E,K,f,g,p,alpha,H]
        linear_combination (-(999/1000-S/2)*C)*ln.2.2-(1/2)*l*r*dn.2.2
      have domination : E≤P r := by
        dsimp [P] at ⊢
        nlinarith only [actual,weightedLine]
      have cosineWeight := mul_nonneg pp (sub_nonneg.mpr defect)
      have cubic := mul_nonneg dn.1 (sq_nonneg S)
      have firstBound : P (1/2)≤-(1/10)+(3/5)*S^2 := by
        dsimp [P,K,f,g,p] at cosineWeight ⊢
        nlinarith only [cosineWeight,dn.1,sq_nonneg S,cubic]
      have first : P (1/2)≤0 := by nlinarith only [firstBound,square]
      have secondBound : P (71/100)≤21/5000-S/4+(503/1000)*S^2 := by
        dsimp [P,K,f,g,p] at cosineWeight ⊢
        nlinarith only [cosineWeight,dn.1,sq_nonneg S,cubic]
      have endpoint := mul_nonneg (sub_nonneg.mpr lower)
        (show 0≤1/4-(503/1000)*(S+1/20) by linarith only [small])
      have second : P (71/100)≤0 := by nlinarith only [secondBound,endpoint]
      have firstWeight := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr rUpper) first
      have secondWeight := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr rLower) second
      have remainder := mul_nonneg coefficient
        (mul_nonneg (sub_nonneg.mpr rLower) (sub_nonneg.mpr rUpper))
      have chord : (21/100)*P r=
          (71/100-r)*P (1/2)+(r-1/2)*P (71/100)-
            (21/100)*(f+(77/100)*g)*(r-1/2)*(71/100-r) := by
        dsimp [P]; ring
      nlinarith only [domination,chord,firstWeight,secondWeight,remainder]
  dsimp [E,alpha,H] at bounded offsetWeight
  nlinarith only [bounded,offsetWeight]

#print axioms margin
end N12Compact.FullAuxWallPositiveLeftAboveMargin
