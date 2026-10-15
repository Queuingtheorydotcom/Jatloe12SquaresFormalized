import Compact.Completion.OtherCases.WallProfile.VertexGeometry
import Compact.Completion.C1092.WallProfileScalars

/-! The strict full boundary-square support cap from its genuine lower
wall and the face forced by a missing upper origin. No canonical component
order or neighboring-square support is assumed. -/
namespace N12Compact.Completion.OtherCases.WallProfile
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C1092WallProfileScalars
set_option Elab.async false

private theorem lower_in_bands (q : OpenSquare) (nx ny : ℝ) :
    lower q nx ny =
      (nx*q.c+ny*q.s)*(q.loU+q.side/2)+
      (-nx*q.s+ny*q.c)*(q.loV+q.side/2)-
      q.side/2*(|nx*q.c+ny*q.s|+|-nx*q.s+ny*q.c|) := by
  unfold lower supportRadius centerX centerY
  ring

theorem negative_lower_vertex (B : OpenSquare) (t c s : ℝ)
    (signed : B.s = -t) (pn : 0 ≤ B.c) (tn : 0 ≤ t)
    (cn : 0 ≤ c) (sn : 0 ≤ s) :
    lower B c (-s) =
      c*(B.c*B.loU+t*B.loV)-s*(-t*B.loU+B.c*B.loV)+
        B.side*min (c*t-s*B.c) 0 := by
  let α := c*B.c+s*t
  let β := c*t-s*B.c
  have an : 0 ≤ α := add_nonneg (mul_nonneg cn pn) (mul_nonneg sn tn)
  have first : c*B.c+(-s)*B.s=α := by rw [signed]; dsimp [α]; ring
  have second : -c*B.s+(-s)*B.c=β := by rw [signed]; dsimp [β]; ring
  rw [lower_in_bands,first,second,abs_of_nonneg an]
  by_cases sign : 0 ≤ β
  · rw [abs_of_nonneg sign,min_eq_right sign]
    dsimp only [α,β]
    ring
  · rw [abs_of_nonpos (le_of_not_ge sign),min_eq_left (le_of_not_ge sign)]
    dsimp only [α,β]
    ring

/-- Section4.2's exact support cap over the whole nonaxis boundary
orientation quadrant. Its strictness comes from the actual side excess. -/
theorem negative_boundary_cap (B : OpenSquare) (t c s : ℝ)
    (signed : B.s = -t) (pp : 0 < B.c) (tp : 0 < t)
    (side : 1 < B.side) (wall : ∀ x y, B.Inside x y → 0 ≤ y)
    (upperFace : B.loV+B.side ≤ 2*t+B.c)
    (cp : 0 < c) (sn : 0 ≤ s) (unit : c^2+s^2=1) :
    lower B c (-s) < B.side*profile c s := by
  have normal : B.c^2+t^2=1 := by simpa only [signed,neg_sq] using B.unit_normal
  let X := B.c*B.loU+t*B.loV
  let Y := -t*B.loU+B.c*B.loV
  let α := c*B.c+s*t
  let τ := half B.c t
  let R := c*(2-B.c-τ)-s*t+min (c*t-s*B.c) 0
  have formula : lower B c (-s)=c*X-s*Y+B.side*min (c*t-s*B.c) 0 :=
    negative_lower_vertex B t c s signed pp.le tp.le cp.le sn
  have coordinate : t*X+B.c*Y=B.loV := by
    dsimp only [X,Y]
    linear_combination B.loV*normal
  have wallBound := lower_wall_vertex B wall
  have yWall : B.side*t ≤ Y := by
    rw [signed] at wallBound
    dsimp only [Y]
    nlinarith only [wallBound]
  have alphaPositive : 0 < α :=
    add_pos_of_pos_of_nonneg (mul_pos cp pp) (mul_nonneg sn tp.le)
  have faceWeight := mul_nonneg cp.le
    (show 0 ≤ 2*t+B.c-B.side-(t*X+B.c*Y) by
      linarith only [upperFace,coordinate])
  have wallWeight := mul_nonneg alphaPositive.le (sub_nonneg.mpr yWall)
  have scalar : R ≤ profile c s := by
    simpa only [R,τ] using boundary_cap c s B.c t cp.le sn pp.le tp.le unit normal
  have scalarWeight := mul_nonneg
    (mul_nonneg B.side_pos.le tp.le) (sub_nonneg.mpr scalar)
  have extra : 0 < (B.side-1)*c*(2*t+B.c) :=
    mul_pos (mul_pos (sub_pos.mpr side) cp) (by linarith only [tp,pp])
  have tauData := quarter_data B.c t pp.le tp.le normal
  have tauScale : τ*(1+B.c)=t := tauData.2.2.1
  have tauRelation : t*τ=1-B.c := by
    have scale := congrArg (fun z : ℝ => t*z) tauScale
    dsimp at scale
    have zero : (1+B.c)*(t*τ-(1-B.c))=0 := by
      nlinarith only [scale,normal]
    exact sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left
      (show 1+B.c ≠ 0 by linarith only [pp]))
  have identity : t*(B.side*profile c s-lower B c (-s)) =
      c*(2*t+B.c-B.side-(t*X+B.c*Y))+
      α*(Y-B.side*t)+B.side*t*(profile c s-R)+
      (B.side-1)*c*(2*t+B.c) := by
    rw [formula]
    dsimp only [α,R]
    linear_combination -B.side*c*tauRelation
  have scaled : t*lower B c (-s) < t*(B.side*profile c s) := by
    nlinarith only [identity,faceWeight,wallWeight,scalarWeight,extra]
  exact (mul_lt_mul_left tp).mp scaled

#print axioms negative_boundary_cap
end N12Compact.Completion.OtherCases.WallProfile

