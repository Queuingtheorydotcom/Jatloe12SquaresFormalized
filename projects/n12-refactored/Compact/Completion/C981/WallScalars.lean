import S12.ShortCluster.Projections
import S12.WallGeometry
import Mathlib.Tactic.FieldSimp

/-! Rational scalar inequalities for the continuous C981 wall advance.
The quarter-circle parameter is eliminated by exact identities. -/
namespace N12Compact.C981CompletionWallScalars

open S12 S12Pilot
set_option Elab.async false

/-- The whole first quadrant, including both axes. -/
theorem wall_arc (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (unit : c^2+s^2=1) :
    (93/100)*c*s ≤ c+s-1+(6/25)*s^2 := by
  have cp : 0 < 1+c := by linarith only [hc]
  have sone : s ≤ 1 := by nlinarith only [unit,sq_nonneg c,sq_nonneg (s-1)]
  let t := s/(1+c)
  have tn : 0 ≤ t := div_nonneg hs cp.le
  have tu : t ≤ 1 := (div_le_iff₀ cp).mpr (by linarith only [sone,hc])
  have relation : t*(1+c)=s := by dsimp [t]; field_simp [cp.ne']
  have relation_sq := congrArg (fun x : ℝ => x^2) relation
  dsimp at relation_sq
  have zero : (1+c)*((1+c)*(1+t^2)-2)=0 := by
    nlinarith only [relation_sq,unit]
  have denominator : (1+c)*(1+t^2)=2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left cp.ne')
  have cform : (1+t^2)*c=1-t^2 := by nlinarith only [denominator]
  have sform : (1+t^2)*s=2*t := by
    calc
      _ = (1+t^2)*(t*(1+c)) := by rw [relation]
      _ = t*((1+c)*(1+t^2)) := by ring
      _ = 2*t := by rw [denominator]; ring
  have bracket : 0 < 7/100-(13/25)*t+(193/100)*t^2-t^3 := by
    by_cases low : t ≤ 1/2
    · have remainder := mul_nonneg (show 0 ≤ 1/2-t by linarith only [low])
        (sq_nonneg t)
      have square := sq_nonneg (t-2/11)
      nlinarith only [remainder,square]
    · have remainder := mul_nonneg (show 0 ≤ 1-t by linarith only [tu])
        (sq_nonneg t)
      have square := sq_nonneg (t-1/2)
      have positive : 0 < t-1/2 := by linarith only [low]
      nlinarith only [remainder,square,positive]
  have identity :
      (1+t^2)^2*(c+s-1+(6/25)*s^2-(93/100)*c*s) =
        2*t*(7/100-(13/25)*t+(193/100)*t^2-t^3) := by
    calc
      _ = (1+t^2)*((1+t^2)*c+(1+t^2)*s-(1+t^2)) +
          (6/25)*((1+t^2)*s)^2-(93/100)*((1+t^2)*c)*((1+t^2)*s) := by ring
      _ = _ := by rw [cform,sform]; ring
  have rhs : 0 ≤ 2*t*(7/100-(13/25)*t+(193/100)*t^2-t^3) :=
    mul_nonneg (by linarith only [tn]) bracket.le
  have scale : 0 < (1+t^2)^2 := sq_pos_of_pos (by nlinarith only [sq_nonneg t])
  have gap : 0 ≤ c+s-1+(6/25)*s^2-(93/100)*c*s :=
    nonneg_of_mul_nonneg_right (by rwa [identity]) scale
  linarith only [gap]

/-- A small-sine bound with an exact rational factorization. -/
theorem small_projection (c s : ℝ) (hc : 50/53 < c) (hs : 0 ≤ s)
    (unit : c^2+s^2=1) : (89/100)*c+(12/25)*s < 1 := by
  have cp : 0 < c := by linarith only [hc]
  have sine : s < 1/3 := by
    have cosine_square := mul_pos (show 0 < c-50/53 by linarith only [hc])
      (show 0 < c+50/53 by linarith only [cp])
    by_contra no
    have sine_square := mul_nonneg (show 0 ≤ s-1/3 by linarith only [no])
      (show 0 ≤ s+1/3 by linarith only [hs])
    nlinarith only [cosine_square,sine_square,unit]
  have slope : 150*s ≤ 53*c := by linarith only [sine,hc]
  have twice : 2*s ≤ c := by linarith only [sine,hc]
  have factor : 0 ≤ 983899*c-1295382*s := by linarith only [twice,cp]
  have product := mul_nonneg (show 0 ≤ 53*c-150*s by linarith only [slope]) factor
  have identity :
      252619236*(c^2+s^2)-25309*(89*c+48*s)^2 =
        (53*c-150*s)*(983899*c-1295382*s) := by ring
  rw [unit] at identity
  by_contra no
  have large : 100 ≤ 89*c+48*s := by linarith only [no]
  have square := mul_nonneg (show 0 ≤ 89*c+48*s-100 by linarith only [large])
    (show 0 ≤ 89*c+48*s+100 by linarith only [cp,hs])
  nlinarith only [identity,product,square]

/-- The canonical interval gives a short projection even when its
coefficient vector has Euclidean norm greater than one. -/
theorem canonical_projection (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) : (143/500)*c+s < 1 := by
  have square : ((143/500)*c+s)^2 ≤ (643/500)^2/2 := by
    have identity :
        (643/500)^2*(c^2+s^2)-2*((143/500)*c+s)^2 =
          (c-s)*((1+2*(143/500)-(143/500)^2)*c+
            (1-2*(143/500)-(143/500)^2)*s) := by ring
    have second : 0 ≤ (1+2*(143/500)-(143/500)^2)*c+
        (1-2*(143/500)-(143/500)^2)*s := by linarith only [hc,hs]
    have product := mul_nonneg (sub_nonneg.mpr order) second
    rw [unit] at identity
    nlinarith only [identity,product]
  by_contra no
  have large : 1 ≤ (143/500)*c+s := by linarith only [no]
  have product := mul_nonneg (sub_nonneg.mpr large)
    (show 0 ≤ (143/500)*c+s+1 by linarith only [hc,hs])
  nlinarith only [square,product]

end N12Compact.C981CompletionWallScalars
