import Compact.Geometry.C849NegativeLeftScalar
import Mathlib.Tactic.FieldSimp

/-! Uniform wall support for the negative-B transverse axis. The signed
L frame is retained; one relative-angle branch closes for every B slope.
The other two use only the continuous split t ≤ (4/5)c. -/
namespace N12Compact.C849NegativeSupport
open C849NegativeLeftScalar

private theorem positive_shallow (C S : ℝ) (hC : 0 < C) (hS : 0 ≤ S)
    (order : S ≤ C) (unit : C^2+S^2=1) :
    0 ≤ 1-(19/25)*S+C*S-(9/5)*C+(4/5)*C^2 := by
  have bounds := frame_bounds C S hC hS order unit
  have height : 19/25 ≤ C+S/10 := by
    by_cases low : S ≤ 3/5
    · have square := mul_nonneg hS (sub_nonneg.mpr low)
      have cmin : 4/5 ≤ C := by
        nlinarith only [unit,square,low,hS,hC,sq_nonneg (C-4/5)]
      linarith only [cmin,hS]
    · linarith only [bounds.1,le_of_not_ge low]
  have product := mul_nonneg hS (sub_nonneg.mpr height)
  nlinarith only [unit,product,sq_nonneg (1-C)]

private theorem positive_steep (C S : ℝ) (hC : 0 < C) (hS : 0 ≤ S)
    (order : S ≤ C) (unit : C^2+S^2=1) :
    0 ≤ 1-(19/25)*S+C*S+C^2-2*C := by
  have bounds := frame_bounds C S hC hS order unit
  by_cases high : 19/25 ≤ C
  · have product := mul_nonneg hS (sub_nonneg.mpr high)
    nlinarith only [product,sq_nonneg (1-C)]
  · have square := mul_nonneg
      (show 0 ≤ 19/25-C by linarith only [le_of_not_ge high])
      (show 0 ≤ 31/25-C by linarith only [bounds.2.1])
    have product := mul_nonneg hS
      (show 0 ≤ C-7/10 by linarith only [bounds.1])
    nlinarith only [square,product,bounds.2.2.1]

private theorem negative_margin (C u : ℝ) (hC : 0 < C) (hu : 0 ≤ u)
    (order : u ≤ C) (unit : C^2+u^2=1) :
    0 ≤ (19/25)*u-(9/5)*C+(9/5)*C^2-(1/5)*C*u := by
  have bounds := frame_bounds C u hC hu order unit
  have q : 0 ≤ 14/25+(14/25)*C+(1/5)*u^2-(9/5)*C*u := by
    nlinarith only [bounds.1,bounds.2.2.2.1,sq_nonneg u]
  have product := mul_nonneg hu q
  have identity :
      (1+C)*((19/25)*u-(9/5)*C+(9/5)*C^2-(1/5)*C*u) =
      u*(14/25+(14/25)*C+(1/5)*u^2-(9/5)*C*u) := by
    calc
      _ = u*(14/25+(14/25)*C+(1/5)*u^2-(9/5)*C*u)+
        ((9/5)*C-(1/5)*u)*(C^2+u^2-1) := by ring
      _ = _ := by rw [unit]; ring
  rw [← identity] at product
  exact nonneg_of_mul_nonneg_right product (by linarith only [hC])

private theorem sum_bound (C u : ℝ) (unit : C^2+u^2=1) : C+u ≤ 10/7 := by
  nlinarith only [unit,sq_nonneg (C-u),sq_nonneg (C+u-10/7)]

/-- `R` is the full support of the actual L square in direction `(t,c)`.
Its face-coordinate wall and compulsory-point bounds imply one of the two
strict support estimates needed by the negative-B proof. -/
theorem support (a c t C S X Y R : ℝ)
    (ha : 1 < a) (hc : 0 < c) (ht : 0 ≤ t) (order : t ≤ c)
    (hC : 0 < C) (canonical : |S| ≤ C) (unit : C^2+S^2=1)
    (wall : a*(C+|S|)/2 ≤ C*(X+a/2)-S*(Y+a/2))
    (low : -(19/25)*S+(187/100)*C ≤ Y)
    (left : X ≤ (457/500)*C+2*S)
    (value : R=(t*C+c*S)*(X+a/2)+(c*C-t*S)*(Y+a/2)+
      a/2*(|t*C+c*S|+|c*C-t*S|)) :
    (33/20)*t+(47/20)*c < R ∨
      ((4/5)*c ≤ t ∧ t+(287/100)*c < R) := by
  have sbounds := abs_le.mp canonical
  by_cases positive : 0 ≤ S
  · have sc : S ≤ C := sbounds.2
    have A : 0 ≤ t*C+c*S := by positivity
    have B : 0 ≤ c*C-t*S := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr order) hC.le,
        mul_nonneg ht (sub_nonneg.mpr sc)]
    rw [abs_of_nonneg positive] at wall
    rw [abs_of_nonneg A,abs_of_nonneg B] at value
    have scaledValue := congrArg (fun z : ℝ => C*z) value
    dsimp only at scaledValue
    have wp := mul_nonneg A
      (show 0 ≤ C*X-S*Y-a*S by linarith only [wall])
    have lp := mul_nonneg hc.le (sub_nonneg.mpr low)
    have gain := mul_pos (sub_pos.mpr ha)
      (show 0 < c+C*(t*C+c*S) by positivity)
    have normal := congrArg (fun z : ℝ => c*(Y+a)*z) unit
    dsimp only at normal
    have lower : c*(1-(19/25)*S+(187/100)*C+C*S)+t*C^2 < C*R := by
      nlinarith only [wp,lp,gain,scaledValue,normal]
    have cmax := (frame_bounds C S hC positive sc unit).2.1
    by_cases shallow : t ≤ (4/5)*c
    · have margin := positive_shallow C S hC positive sc unit
      have margin' := mul_nonneg hc.le margin
      have slope := mul_nonneg (sub_nonneg.mpr shallow)
        (mul_nonneg hC.le (show 0 ≤ 33/20-C by linarith only [cmax]))
      left
      have scaled : C*((33/20)*t+(47/20)*c) < C*R := by
        nlinarith only [lower,margin',slope]
      exact (mul_lt_mul_left hC).mp scaled
    · have margin := positive_steep C S hC positive sc unit
      have margin' := mul_nonneg hc.le margin
      have slope := mul_nonneg (sub_nonneg.mpr order)
        (mul_nonneg hC.le (sub_nonneg.mpr cmax))
      right
      refine ⟨le_of_not_ge shallow,?_⟩
      have scaled : C*(t+(287/100)*c) < C*R := by
        nlinarith only [lower,margin',slope]
      exact (mul_lt_mul_left hC).mp scaled
  · let u := -S
    have hu : 0 ≤ u := by dsimp [u]; linarith only [le_of_not_ge positive]
    have uC : u ≤ C := by dsimp [u]; linarith only [sbounds.1]
    have unit' : C^2+u^2=1 := by dsimp [u]; nlinarith only [unit]
    have low' : (19/25)*u+(187/100)*C ≤ Y := by dsimp [u]; linarith only [low]
    have left' : X ≤ (457/500)*C-2*u := by dsimp [u]; linarith only [left]
    have wall' : 0 ≤ C*X+u*Y := by
      rw [abs_of_nonpos (le_of_not_ge positive)] at wall
      dsimp [u]; linarith only [wall]
    have B : 0 < c*C+t*u := by positivity
    have value' : R=(t*C-c*u)*(X+a/2)+(c*C+t*u)*(Y+a/2)+
        a/2*(|t*C-c*u|+(c*C+t*u)) := by
      have absB : |c*C-t*S|=c*C-t*S := abs_of_pos (by dsimp [u] at B; linarith only [B])
      rw [absB] at value
      simpa only [u,mul_neg,sub_neg_eq_add,neg_mul] using value
    have bounds := frame_bounds C u hC hu uC unit'
    by_cases relative : 0 ≤ t*C-c*u
    · rw [abs_of_nonneg relative] at value'
      have scaledValue := congrArg (fun z : ℝ => C*z) value'
      dsimp only at scaledValue
      have wp := mul_nonneg relative wall'
      have lp := mul_nonneg hc.le (sub_nonneg.mpr low')
      have gain := mul_pos (sub_pos.mpr ha)
        (show 0 < C*((t*C-c*u)+(c*C+t*u)) by positivity)
      have normal := congrArg (fun z : ℝ => c*Y*z) unit'
      dsimp only at normal
      have lower : c*((19/25)*u+(187/100)*C+C^2-C*u)+t*(C^2+C*u) < C*R := by
        nlinarith only [wp,lp,gain,scaledValue,normal]
      have margin := negative_margin C u hC hu uC unit'
      have margin' := mul_nonneg hc.le margin
      by_cases shallow : t ≤ (4/5)*c
      · have sum := sum_bound C u unit'
        have slope := mul_nonneg (sub_nonneg.mpr shallow)
          (mul_nonneg hC.le (show 0 ≤ 33/20-C-u by linarith only [sum]))
        left
        have scaled : C*((33/20)*t+(47/20)*c) < C*R := by
          nlinarith only [lower,margin',slope]
        exact (mul_lt_mul_left hC).mp scaled
      · have sum : 1 ≤ C+u := by
          have cp := mul_nonneg hC.le (sub_nonneg.mpr bounds.2.1)
          have up := mul_nonneg hu (show 0 ≤ 1-u by linarith only [uC,bounds.2.1])
          nlinarith only [unit',cp,up]
        have slope := mul_nonneg (show 0 ≤ t-(4/5)*c by linarith only [le_of_not_ge shallow])
          (mul_nonneg hC.le (sub_nonneg.mpr sum))
        right
        refine ⟨le_of_not_ge shallow,?_⟩
        have scaled : C*(t+(287/100)*c) < C*R := by
          nlinarith only [lower,margin',slope]
        exact (mul_lt_mul_left hC).mp scaled
    · have relative' := le_of_not_ge relative
      rw [abs_of_nonpos relative'] at value'
      have up := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr left') relative'
      have lp := mul_nonneg B.le (sub_nonneg.mpr low')
      have gain := mul_pos (sub_pos.mpr ha) B
      have normalC := congrArg (fun z : ℝ => c*z) unit'
      have normalT := congrArg (fun z : ℝ => t*z) unit'
      dsimp only at normalC normalT
      let F := C-12/25+(13/100)*u^2-(77/500)*C*u
      let G := u-92/125-(77/500)*u^2-(13/100)*C*u
      have lower : c*F+t*G+(33/20)*t+(47/20)*c < R := by
        dsimp [F,G]
        nlinarith only [up,lp,gain,value',normalC,normalT]
      have Gneg : G ≤ 0 := by
        dsimp [G]
        nlinarith only [bounds.2.2.1,mul_nonneg hC.le hu,sq_nonneg u]
      have angle := mul_nonneg (neg_nonneg.mpr Gneg) (neg_nonneg.mpr relative')
      have sum := sum_bound C u unit'
      have strictMargin : 0 < 1-(12/25)*C-(89/100)*u := by
        linarith only [sum,uC]
      have identity : C*F+u*G=1-(12/25)*C-(89/100)*u := by
        dsimp [F,G]
        calc
          _ = (C^2+u^2)-(12/25)*C-(92/125)*u-(77/500)*u*(C^2+u^2) := by ring
          _ = _ := by rw [unit']; ring
      have strict := mul_pos hc strictMargin
      have nonnegative : 0 ≤ c*F+t*G := by
        have scaled : 0 < C*(c*F+t*G) := by
          rw [← identity] at strict
          nlinarith only [angle,strict]
        exact (pos_of_mul_pos_right scaled hC.le).le
      left
      linarith only [lower,nonnegative]

#print axioms support
end N12Compact.C849NegativeSupport
