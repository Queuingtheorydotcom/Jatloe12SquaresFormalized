import Compact.Completion.C1092.ShortWallScalars

/-! The cubic allowance compares the same physical central upper face
against every first-quadrant top-wall orientation. The final own-normal
margin covers the full ordered arc by an exact concave chord. -/
namespace N12Compact.C1092ShortWallAllowance
open C977CornerCubic C977CornerSectorBounds C1092ShortWallScalars
set_option Elab.async false

private theorem quadrant_bounds {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    (unit : r^2+t^2=1) : r ≤ 1 ∧ t ≤ 1 ∧ 1 ≤ r+t ∧ r+t ≤ 3/2 := by
  have product := mul_nonneg hr ht
  exact ⟨by nlinarith only [unit,sq_nonneg t,hr],
    by nlinarith only [unit,sq_nonneg r,ht],
    by nlinarith only [unit,product,hr,ht],
    by nlinarith only [unit,sq_nonneg (r-t),sq_nonneg (r+t-3/2)]⟩

private theorem relative_bounds {c s r t : ℝ} (cn : Normal c s)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (unit : r^2+t^2=1) :
    0 ≤ c*r+s*t ∧ c*r+s*t ≤ 1 ∧
      (c*r+s*t)^2+(c*t-s*r)^2=1 := by
  have cb := normal_bounds cn
  have dp := add_nonneg (mul_nonneg (show 0 ≤ c by linarith only [cb.1]) hr)
    (mul_nonneg cn.1 ht)
  have relative : (c*r+s*t)^2+(c*t-s*r)^2=1 := by
    calc
      _ = (c^2+s^2)*(r^2+t^2) := by ring
      _ = 1 := by rw [cn.2.2,unit]; norm_num
  exact ⟨dp,by nlinarith only [relative,sq_nonneg (c*t-s*r),dp],relative⟩

private theorem positive_order {c s r t : ℝ} (cn : Normal c s)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (unit : r^2+t^2=1)
    (order : 0 ≤ c*t-s*r) : r ≤ c ∧ s ≤ t := by
  have cb := normal_bounds cn
  have product := mul_nonneg order
    (add_nonneg (mul_nonneg (show 0 ≤ c by linarith only [cb.1]) ht)
      (mul_nonneg cn.1 hr))
  have identity : (c*t-s*r)*(c*t+s*r)=t^2-s^2 := by
    linear_combination t^2*cn.2.2-s^2*unit
  exact ⟨by nlinarith only [identity,product,cn.2.2,unit,hr,cb.1],
    by nlinarith only [identity,product,ht,cn.1]⟩

theorem above {c s r t : ℝ} (cn : Normal c s) (narrow : 4*s ≤ c)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (unit : r^2+t^2=1)
    (order : 0 ≤ c*t-s*r) :
    allowance r t ≤ (c*r+s*t)*allowance c s+(7/20)*(c*t-s*r) := by
  have cb := normal_bounds cn
  have nb := narrow_bounds cn narrow
  have ab := allowance_bounds cn narrow
  have rb := quadrant_bounds hr ht unit
  have db := relative_bounds cn hr ht unit
  have ordered := positive_order cn hr ht unit order
  let d := c*r+s*t
  let k := c*t-s*r
  have dp : 0 ≤ d := db.1
  have du : d ≤ 1 := db.2.1
  have kp : 0 ≤ k := order
  have relative : d^2+k^2=1 := db.2.2
  have defect : 1-d ≤ k := by
    apply le_of_not_gt
    intro bad
    have first : 0 < 1-d-k := by linarith only [bad]
    have second : 0 < 1+d+k := by linarith only [dp,kp]
    nlinarith only [relative,mul_pos first second,mul_nonneg dp kp]
  have id0 : c-r=c*(1-d)+s*k := by
    dsimp [d,k]
    linear_combination r*cn.2.2
  have id1 : t-s=c*k-s*(1-d) := by
    dsimp [d,k]
    linear_combination -t*cn.2.2
  have weight0 := mul_nonneg (show 0 ≤ c by linarith only [cb.1])
    (sub_nonneg.mpr defect)
  have weight1 := mul_nonneg kp (show 0 ≤ 5/4-(c+s) by linarith only [cb.2.1,nb.2.1])
  have upper0 : c-r ≤ (5/4)*k := by
    calc
      c-r = c*(1-d)+s*k := id0
      _ ≤ c*k+s*k := add_le_add_right
        (mul_le_mul_of_nonneg_left defect (by linarith only [cb.1])) _
      _ = (c+s)*k := by ring
      _ ≤ (5/4)*k := mul_le_mul_of_nonneg_right
        (by linarith only [cb.2.1,nb.2.1]) kp
  have weight2 := mul_nonneg cn.1 (sub_nonneg.mpr du)
  have weight3 := mul_nonneg kp (sub_nonneg.mpr cb.2.1)
  have upper1 : t-s ≤ k := by nlinarith only [id1,weight2,weight3]
  have first := mul_nonneg (sub_nonneg.mpr ordered.1)
    (show 0 ≤ 5/2-r-c-t by linarith only [rb.2.2.2,cb.2.1])
  have second := mul_nonneg (sub_nonneg.mpr ordered.2)
    (show 0 ≤ 1/25-(1-c) by linarith only [nb.1])
  have identity : allowance r t-allowance c s =
      ((r-c)*(2-r-c-t)+(t-s)*(1-c))/2 := by unfold allowance; ring
  have base : allowance r t-allowance c s ≤ (c-r)/4+(t-s)/50 := by
    nlinarith only [first,second,identity]
  have gain : allowance r t-allowance c s ≤ (27/80)*k := by
    calc
      allowance r t-allowance c s ≤ (c-r)/4+(t-s)/50 := base
      _ = (c-r)*(1/4)+(t-s)*(1/50) := by ring
      _ ≤ ((5/4)*k)*(1/4)+k*(1/50) := add_le_add
        (mul_le_mul_of_nonneg_right upper0 (by norm_num))
        (mul_le_mul_of_nonneg_right upper1 (by norm_num))
      _ = (133/400)*k := by ring
      _ ≤ (27/80)*k := mul_le_mul_of_nonneg_right (by norm_num) kp
  have cost0 := mul_nonneg ab.1 (sub_nonneg.mpr defect)
  have cost1 := mul_nonneg kp (sub_nonneg.mpr ab.2.2)
  have cost : (1-d)*allowance c s ≤ k/200 := by
    calc
      (1-d)*allowance c s ≤ k*allowance c s :=
        mul_le_mul_of_nonneg_right defect ab.1
      _ ≤ k*(1/200) := mul_le_mul_of_nonneg_left ab.2.2 kp
      _ = k/200 := by ring
  have finalMargin := mul_nonneg kp (by norm_num : (0 : ℝ) ≤ 7/20-27/80-1/200)
  change allowance r t ≤ d*allowance c s+(7/20)*k
  nlinarith only [gain,cost,finalMargin]

theorem below {c s r t : ℝ} (cn : Normal c s) (narrow : 4*s ≤ c)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (unit : r^2+t^2=1)
    (order : c*t-s*r ≤ 0) :
    allowance r t ≤ (c*r+s*t)*allowance c s-(c*t-s*r)/200 := by
  have cb := normal_bounds cn
  have nb := narrow_bounds cn narrow
  have rb := quadrant_bounds hr ht unit
  have db := relative_bounds cn hr ht unit
  have ab := allowance_bounds cn narrow
  have product := mul_nonneg (show 0 ≤ s*r-c*t by linarith only [order])
    (add_nonneg (mul_nonneg cn.1 hr)
      (mul_nonneg (show 0 ≤ c by linarith only [cb.1]) ht))
  have identity : (s*r-c*t)*(s*r+c*t)=s^2-t^2 := by
    linear_combination s^2*unit-t^2*cn.2.2
  have tilt : t ≤ s := by nlinarith only [identity,product,ht,cn.1]
  have cosine : c ≤ r := by nlinarith only [identity,product,cn.2.2,unit,hr,cb.1]
  have rn : Normal r t := ⟨ht,by linarith only [tilt,cosine,cn.2.1],unit⟩
  have sumProduct := mul_nonneg (sub_nonneg.mpr tilt)
    (show 0 ≤ c+r-s-t by linarith only [cn.2.1,rn.2.1])
  have sumIdentity : (c+r)*(c+s-r-t)=(s-t)*(c+r-s-t) := by
    linear_combination cn.2.2-unit
  have sum : r+t ≤ c+s := by
    have scaled : 0 ≤ (c+r)*(c+s-r-t) := by linarith only [sumProduct,sumIdentity]
    have difference := nonneg_of_mul_nonneg_right scaled (by linarith only [cb.1,hr])
    linarith only [difference]
  have fcompare := mul_le_mul
    (show 1-r ≤ 1-c by linarith only [cosine])
    (show r+t-1 ≤ c+s-1 by linarith only [sum])
    (show 0 ≤ r+t-1 by linarith only [rb.2.2.1])
    (sub_nonneg.mpr cb.2.1)
  have monotone : allowance r t ≤ allowance c s := by
    dsimp [allowance]
    nlinarith only [fcompare]
  have defect : 1-(c*r+s*t) ≤ -(c*t-s*r) := by
    nlinarith only [db.2.2,db.1,order,
      mul_nonneg db.1 (show 0 ≤ -(c*t-s*r) by linarith only [order])]
  have cost0 := mul_nonneg ab.1 (sub_nonneg.mpr defect)
  have cost1 := mul_nonneg (show 0 ≤ -(c*t-s*r) by linarith only [order])
    (sub_nonneg.mpr ab.2.2)
  nlinarith only [monotone,cost0,cost1]

#print axioms above
#print axioms below
end N12Compact.C1092ShortWallAllowance
