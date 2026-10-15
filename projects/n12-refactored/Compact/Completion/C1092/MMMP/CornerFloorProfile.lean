import Compact.Completion.C1092.MMMP.CenterCorner
import Compact.Completion.C1092.WallProfileScalars

/-! A scaled lower corner face supplies the complete directional profile
needed by the actual top-wall transfer. The target direction ranges over
the whole first quadrant; it is not assumed canonical. -/
namespace N12Compact.C1092MMMPCornerFloorProfile
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092MixedCornerSupports
set_option Elab.async false

private theorem direction_data (x y : ℝ) (xn : 0≤x) (yn : 0≤y)
    (unit : x^2+y^2=1) :
    x≤1 ∧ y≤1 ∧ 1≤x+y ∧
      1/2+(9/20)*y≤(x+y)/(1+x) ∧
      y*(2-(x+y)/(1+x))≤1 := by
  have xu : x≤1 := by nlinarith only [unit,sq_nonneg y,sq_nonneg (x-1)]
  have yu : y≤1 := by nlinarith only [unit,sq_nonneg x,sq_nonneg (y-1)]
  have sum : 1≤x+y := by
    by_contra low
    have small := mul_pos (show 0<1-x-y by linarith only [low])
      (show 0<1+x+y by linarith only [xn,yn])
    nlinarith only [small,unit,mul_nonneg xn yn]
  have xp : 0<1+x := by linarith only [xn]
  have yp : 0<1+y := by linarith only [yn]
  have first : 0≤10*x-10+11*y-9*x*y := by
    have positive := mul_nonneg yn
      (show 0≤(3*y-2)^2+2*(x+y-1) by nlinarith only [sq_nonneg (3*y-2),sum])
    have identity : (1+x)*(10*x-10+11*y-9*x*y)=
        y*((3*y-2)^2+2*(x+y-1)) := by
      linear_combination (10-9*y)*unit
    exact nonneg_of_mul_nonneg_right (by rw [identity]; exact positive) xp
  have lower : 1/2+(9/20)*y≤(x+y)/(1+x) := by
    apply (le_div_iff₀ xp).mpr
    nlinarith only [first]
  have second : 0≤1+x-2*y-x*y+y^2 := by
    have positive := mul_nonneg (sq_nonneg x)
      (show 0≤1+x-y by linarith only [xn,yu])
    have identity : (1+y)*(1+x-2*y-x*y+y^2)=x^2*(1+x-y) := by
      linear_combination -(1+x-y)*unit
    exact nonneg_of_mul_nonneg_right (by rw [identity]; exact positive) yp
  have top : y*(2-(x+y)/(1+x))≤1 := by
    have identity : (1+x)*(1-y*(2-(x+y)/(1+x)))=
        1+x-2*y-x*y+y^2 := by
      field_simp [xp.ne']
      ring
    have scaled : 0≤(1+x)*(1-y*(2-(x+y)/(1+x))) := by rw [identity]; exact second
    have h := nonneg_of_mul_nonneg_right scaled xp
    linarith only [h]
  exact ⟨xu,yu,sum,lower,top⟩

private theorem face_scalar {c s : ℝ} (cn : Normal c s) :
    c*(11/4-(5/4)*(c+s))≤1+(c+s)/2-s*(c+s) := by
  have cb := normal_bounds cn
  have elementary := C1092MixedCornerScalars.elementary cn
  have bracket : 0≤(2+c)*(1+c)-9*c*s := by
    nlinarith only [elementary.1,elementary.2.1,elementary.2.2,cn.2.2]
  have positive := mul_nonneg cn.1 bracket
  have identity : (1+c)*(4+2*(c+s)-4*s*(c+s)-11*c+5*c*(c+s))=
      s*((2+c)*(1+c)-9*c*s) := by
    linear_combination (5*c-4)*cn.2.2
  have h : 0≤4+2*(c+s)-4*s*(c+s)-11*c+5*c*(c+s) :=
    nonneg_of_mul_nonneg_right (by rw [identity]; exact positive)
      (by linarith only [cb.1])
  linarith only [h]

private theorem positive_scalar {c s x y : ℝ} (cn : Normal c s)
    (xn : 0≤x) (yn : 0≤y) (unit : x^2+y^2=1)
    (relative : 0≤x*c-y*s) :
    c*(C1092WallProfileScalars.profile x y+2*y)≤
      (x*c-y*s)*(c+s)+y*(1+(c+s)/2) := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have data := direction_data x y xn yn unit
  have product := mul_nonneg relative
    (add_nonneg (mul_nonneg xn cp.le) (mul_nonneg yn cn.1))
  have identity : (x*c-y*s)*(x*c+y*s)=x^2-s^2 := by
    linear_combination x^2*cn.2.2-s^2*unit
  have order : s≤x := by
    by_contra low
    have gap := mul_pos (show 0<s-x by linarith only [low])
      (show 0<s+x by linarith only [low,xn])
    rw [identity] at product
    nlinarith only [product,gap]
  have short : c+s-1≤x := by linarith only [cb.2.1,order]
  have scalar : 0≤(c+s-1)*(x-(5/4)*y)+(9/20)*y^2 := by
    by_cases sign : 0≤x-(5/4)*y
    · have first := mul_nonneg (sub_nonneg.mpr cb.2.2.2.2.1) sign
      nlinarith only [first,sq_nonneg y]
    · have first := mul_le_mul_of_nonpos_right short (le_of_not_ge sign)
      nlinarith only [first,sq_nonneg (x-(5/8)*y),sq_nonneg y]
  have face := mul_le_mul_of_nonneg_left (face_scalar cn) yn
  have kappa := mul_le_mul_of_nonneg_left data.2.2.2.1 (mul_nonneg cp.le yn)
  have weighted := mul_nonneg cp.le scalar
  dsimp [C1092WallProfileScalars.profile]
  nlinarith only [face,kappa,weighted]

/-- The full support profile follows from a scaled lower transverse
face, actual corner anchors, and the true left wall. -/
theorem support_profile (K : OpenSquare) (side : 1<K.side)
    (cn : Normal K.c (-K.s))
    (wall : ∀ x y, K.Inside x y → -1≤x)
    (H : K.Inside 0 (1/2)) (P : K.Inside 0 1)
    (floor : K.side*(K.c+(-K.s))/2-(-K.s)≤K.loV)
    (x y : ℝ) (xn : 0≤x) (yn : 0≤y) (unit : x^2+y^2=1) :
    K.side*C1092WallProfileScalars.profile x y-x+2*y≤upper K x y := by
  let c := K.c
  let s := -K.s
  let alpha := x*c-y*s
  let beta := x*s+y*c
  have cb := normal_bounds cn
  have cp : 0<c := by dsimp [c]; linarith only [cb.1]
  have sn : 0≤s := cn.1
  have bp : 0≤beta := add_nonneg (mul_nonneg xn sn) (mul_nonneg yn cp.le)
  have data := direction_data x y xn yn unit
  have vFloor : K.side*(1+(c+s)/2)-s≤K.loV+K.side := by
    dsimp [c,s]
    linarith only [floor]
  by_cases sign : 0≤alpha
  · have formula := upper_nn K x y alpha beta
      (by dsimp [alpha,c,s]; ring) (by dsimp [beta,c,s]; ring) sign bp
    have box := square_support_bound K (-1) 0 1
      (by intro u v own; have h := wall u v own; linarith only [h])
    have nonpositive : K.s≤0 := by linarith only [cn.1]
    norm_num [squareRadius,abs_of_pos cp,abs_of_nonpos nonpositive] at box
    have left : -1≤c*K.loU+s*K.loV := by
      dsimp [c,s,centerX] at box ⊢
      nlinarith only [box]
    have vertex : K.side*(c+s)-1≤c*(K.loU+K.side)+s*(K.loV+K.side) := by
      nlinarith only [left]
    have horizontal := mul_le_mul_of_nonneg_left vertex sign
    have vertical := mul_le_mul_of_nonneg_left vFloor yn
    have scalar := positive_scalar cn xn yn unit sign
    have scaled := mul_le_mul_of_nonneg_left scalar K.side_pos.le
    have extra := mul_nonneg (sub_nonneg.mpr side.le) (mul_nonneg cp.le yn)
    have identity : c*upper K x y=
        alpha*(c*(K.loU+K.side)+s*(K.loV+K.side))+y*(K.loV+K.side) := by
      rw [formula]
      dsimp [alpha,beta,c,s]
      linear_combination y*(K.loV+K.side)*K.unit_normal
    apply (mul_le_mul_left cp).mp
    dsimp [alpha,c,s] at horizontal scalar scaled
    dsimp [alpha] at identity
    nlinarith only [identity,horizontal,vertical,scaled,extra]
  · have an : alpha≤0 := le_of_not_ge sign
    have formula := upper_np K x y alpha beta
      (by dsimp [alpha,c,s]; ring) (by dsimp [beta,c,s]; ring) an bp
    have lowU : K.loU< -s := by dsimp [s]; linarith only [P.1]
    have first := mul_le_mul_of_nonpos_left lowU.le an
    have last := mul_le_mul_of_nonneg_left vFloor bp
    have relativeUnit : alpha^2+beta^2=1 := by
      calc
        _ = (x^2+y^2)*(c^2+s^2) := by dsimp [alpha,beta]; ring
        _ = 1 := by rw [unit,cn.2.2]; norm_num
    have hSmall : -alpha≤s := by
      have a := mul_nonneg (sub_nonneg.mpr data.2.1) sn
      have b := mul_nonneg xn cp.le
      dsimp [alpha]
      nlinarith only [a,b]
    have close : c≤beta := by
      have square := mul_nonneg (show 0≤s+alpha by linarith only [hSmall])
        (show 0≤s-alpha by linarith only [sn,an])
      by_contra low
      have gap := mul_pos (show 0<c-beta by linarith only [low])
        (show 0<c+beta by linarith only [cp,bp])
      nlinarith only [square,gap,relativeUnit,cn.2.2]
    have arc : 1≤beta+s*(-alpha) := by
      have small := mul_nonneg (show 0≤-alpha by linarith only [an])
        (show 0≤s*(1+beta)-(-alpha) by
          have h := mul_nonneg sn bp
          nlinarith only [h,hSmall])
      have identity : (1+beta)*(beta+s*(-alpha)-1)=
          (-alpha)*(s*(1+beta)-(-alpha)) := by
        linear_combination relativeUnit
      have h : 0≤beta+s*(-alpha)-1 :=
        nonneg_of_mul_nonneg_right (by rw [identity]; exact small)
          (by linarith only [bp])
      linarith only [h]
    have derivative : 1≤beta*(1+(c+s)/2) := by
      have first := mul_le_mul_of_nonneg_right close
        (show 0≤1+(c+s)/2 by linarith only [cp,sn])
      have last := mul_nonneg cp.le
        (show 0≤c+s-1 from sub_nonneg.mpr cb.2.2.2.2.1)
      dsimp [c,s] at first last ⊢
      nlinarith only [first,last,cb.1]
    have tail := mul_nonneg bp (sub_nonneg.mpr cn.2.1)
    have base : 1≤(-alpha)*s+beta*(1+(c-s)/2) := by
      nlinarith only [arc,tail]
    have excess := mul_nonneg (sub_nonneg.mpr side.le) (sub_nonneg.mpr derivative)
    have bound : K.side≤upper K x y := by
      rw [formula]
      nlinarith only [first,last,base,excess]
    have kappa : 0≤(x+y)/(1+x) := div_nonneg (add_nonneg xn yn)
      (by linarith only [xn])
    have profileCap : C1092WallProfileScalars.profile x y≤1 := by
      have weight := mul_nonneg yn kappa
      dsimp [C1092WallProfileScalars.profile]
      nlinarith only [weight,data.1]
    have extra := mul_nonneg (sub_nonneg.mpr side.le) (sub_nonneg.mpr profileCap)
    have target : K.side*C1092WallProfileScalars.profile x y-x+2*y≤K.side := by
      dsimp [C1092WallProfileScalars.profile] at extra ⊢
      nlinarith only [extra,data.2.2.2.2]
    exact target.trans bound

#print axioms support_profile
end N12Compact.C1092MMMPCornerFloorProfile
