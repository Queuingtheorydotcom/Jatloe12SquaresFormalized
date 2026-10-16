import Compact.Geometry.PositiveCentralPositiveLeftBounds
import Compact.Geometry.PositiveCentralCrossMargin

/-! The central-equals-left endpoint of the genuine own-V entrance.
Two continuous cosine ranges give elementary nonnegative products.
There is no numerical search or saved angular enclosure. -/
namespace N12Compact.PositiveLeftOwnVEndpoint

open C977CornerCubic C977CornerSectorBounds
open PositiveCentralPositiveLeftBounds PositiveCentralCrossMargin

theorem endpoint_left {p q l r : ℝ}
    (on : Normal p q) (ln : Normal l r)
    (shallow : 9/10≤p) (order : q≤r) :
    l^2*(1-vertexDefect l r-r*(1-p))+l*r*(2-r*(1-l))≤
      l+r*F p q l r := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have pp : 0<p := by linarith only [ob.1]
  have lp : 0<l := by linarith only [lb.1]
  have cosine := cosine_order ln on order
  have cross : q*l-p*r≤0 := by
    have first := mul_nonneg lp.le (sub_nonneg.mpr order)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr cosine)
    nlinarith only [first,second]
  have form : F p q l r=1-2*r-(457/500)*q*r/p+r/p+p*l+q*r := by
    dsimp [F]
    rw [max_eq_right cross]
    ring
  let δ := 1-p
  let D := r*F p q l r-2*l*r+l*(1-l)*(2-r+r^2)+l^2*r*δ
  let D₀ := (1-l)^2*(l*(1+l)-(1-r))
  let Dbase := r-r^2-l*r+l*(1-l)*(2-r+r^2)
  have baseIdentity : Dbase=D₀ := by
    dsimp [Dbase,D₀]
    linear_combination -(l^2-l+1)*ln.2.2
  have difference :
      p*(D-D₀)=r*(r*(δ+q*(p-457/500))-p*δ*l*(1-l)) := by
    rw [←baseIdentity]
    dsimp [D,Dbase,δ]
    rw [form]
    field_simp [ne_of_gt pp] <;> ring
  have targetIdentity :
      l+r*F p q l r-
        (l^2*(1-vertexDefect l r-r*(1-p))+l*r*(2-r*(1-l)))=D := by
    dsimp [D,δ,vertexDefect]
    field_simp [ne_of_gt lp] <;> ring
  have δp : 0≤δ := sub_nonneg.mpr ob.2.1
  have defect : 0≤l*(1-l) := mul_nonneg lp.le (sub_nonneg.mpr lb.2.1)
  have replacement := mul_nonneg (sub_nonneg.mpr ob.2.1) defect
  have pl : p*l≤1 := by
    have first := mul_nonneg lp.le (sub_nonneg.mpr ob.2.1)
    nlinarith only [first,lb.2.1]
  have leftDefect : p*l*(1-l)≤r := by
    have first := mul_nonneg (sub_nonneg.mpr pl) (sub_nonneg.mpr lb.2.1)
    nlinarith only [first,lb.2.2.2.2.1]
  have bracket : 0≤r*(δ+q*(p-457/500))-p*δ*l*(1-l) := by
    by_cases large : 457/500≤p
    · have first := mul_nonneg δp (sub_nonneg.mpr leftDefect)
      have second := mul_nonneg (mul_nonneg ln.1 on.1) (sub_nonneg.mpr large)
      nlinarith only [first,second]
    · have psmall : p≤457/500 := le_of_lt (lt_of_not_ge large)
      have qlarge : 2/5≤q := by
        by_contra no
        have first := mul_nonneg (sub_nonneg.mpr psmall)
          (show 0≤457/500+p by linarith only [pp])
        have second := mul_nonneg
          (show 0≤2/5-q by linarith only [no])
          (show 0≤2/5+q by linarith only [on.1])
        nlinarith only [first,second,on.2.2]
      have quarter : p*l*(1-l)≤1/4 := by
        nlinarith only [replacement,sq_nonneg (l-1/2)]
      have gap : 3/20≤r-p*l*(1-l) := by
        linarith only [quarter,qlarge,order]
      have δlower : 43/500≤δ := by dsimp [δ]; linarith only [psmall]
      have first := mul_nonneg (sub_nonneg.mpr δlower)
        (show 0≤r-p*l*(1-l) by linarith only [gap])
      have rq : 0≤r*q := mul_nonneg ln.1 on.1
      have rqbound : r*q≤1/2 := by
        have one := mul_nonneg ln.1 (sub_nonneg.mpr order)
        have two := mul_nonneg (sub_nonneg.mpr ln.2.1)
          (show 0≤l+r by linarith only [lp,ln.1])
        nlinarith only [one,two,ln.2.2]
      have second := mul_nonneg rq
        (show 0≤7/500-(457/500-p) by linarith only [shallow])
      nlinarith only [first,second,gap,rqbound]
  have weighted := mul_nonneg ln.1 bracket
  have increment : 0≤D-D₀ := by
    have scaled : 0≤p*(D-D₀) := by nlinarith only [difference,weighted]
    exact nonneg_of_mul_nonneg_right scaled pp
  have base : 0≤D₀ := by
    have product := mul_nonneg ln.1 (sub_nonneg.mpr lb.2.2.2.1)
    have inner : 0≤l*(1+l)-(1-r) := by
      nlinarith only [product,lp,ln.2.2]
    exact mul_nonneg (sq_nonneg (1-l)) inner
  nlinarith only [targetIdentity,increment,base]

#print axioms endpoint_left
end N12Compact.PositiveLeftOwnVEndpoint
